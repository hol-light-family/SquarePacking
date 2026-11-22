(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerMixed.lean                       *)
(* (namespace N12Compact.CornerWallMarkerMixed).                             *)
(* Full positive-L O-v / L-v selector with genuine marker faces.  Squares    *)
(* are 5-tuples; Lean upper/lower are ABT_upper/ABT_lower; boundary is       *)
(* cwmmb_boundary (CornerWallMarkerMixedBounds); low/high_margin are         *)
(* CWMMB_LOW_MARGIN / CWMMB_HIGH_MARGIN; left_wall is FSBL_LEFT_WALL;        *)
(* CornerWallMarkerShared.wall_support is CWMS_WALL_SUPPORT.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallMarkerMixedBounds.ml";;
needs "n12/geometry/CornerWallMarkerShared.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMM_clear_poly dens k t =
  let mul = `( * ):real->real->real` in
  let rec repl tm = match tm with
      Comb(Comb(Const("real_div",_),x),v) when exists (fun (x,_) -> x = v) dens ->
        mk_binop mul (repl x) (assoc v dens)
    | Comb(f,x) -> mk_comb(repl f, repl x)
    | _ -> tm in
  let t2 = repl (mk_binop mul k t) in
  nlin_atoms := [];
  let p = poly_of_term t2 in
  let atoms = !nlin_atoms in
  let index_of tm =
    let rec go i l = match l with [] -> -1 | h::r -> if aconv h tm then i else go (i+1) r in
    go 0 atoms in
  let pairs = map (fun (v,iv) -> (index_of v, index_of iv)) dens in
  let cancel m =
    itlist (fun (vi,ii) m ->
      if vi < 0 || ii < 0 then m else
      let a = try assoc vi m with Failure _ -> 0
      and b = try assoc ii m with Failure _ -> 0 in
      let e = min a b in
      let m' = filter (fun (x,_) -> x <> vi && x <> ii) m in
      let m' = (if a - e > 0 then [vi, a - e] else []) @
               (if b - e > 0 then [ii, b - e] else []) @ m' in
      sort (fun (x,_) (y,_) -> x < y) m') pairs m in
  let p' = pnorm (map (fun (m,c) -> (cancel m, c)) p) in
  if exists (fun (m,_) -> exists (fun (_,ii) -> ii >= 0 && exists (fun (x,_) -> x = ii) m) pairs) p'
  then failwith "CWMM_clear_poly: denominators remain" else
  let atom i = el i atoms in
  let mono (m,c) =
    let fs = map (fun (i,e) -> if e = 1 then atom i
                    else mk_binop `(pow):real->num->real` (atom i) (mk_small_numeral e)) m in
    let ct = term_of_rat c in
    if fs = [] then ct else
    let pr = end_itlist (fun a b -> mk_binop mul a b) fs in
    if c =/ num 1 then pr else mk_binop mul ct pr in
  if p' = [] then `&0` else
  end_itlist (fun a b -> mk_binop `(+):real->real->real` a b) (map mono p');;

(* prove |- ~(v1 = &0) /\ ... ==> k * t = P *)
let CWMM_CLEAR_EQ dens k t =
  let p = CWMM_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMM_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMM_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWMM_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMM_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMM_LT_BY_POS else CWMM_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWMM_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMM_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMM_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMM_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWMM_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMM_SCALE_LT else CWMM_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMM_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: low_sector *)
let CWMM_LOW_SECTOR = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aL = aW /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     cwmmb_boundary cO sO < vO + aO /\
     vW + aW <= t + &3 * cW /\
     sO <= t /\ sL <= sO /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `sL:real`; `t + &3 * cW`] CWMS_WALL_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `sL:real`]
    CWMMB_LOW_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cL:real`; `sL:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  REWRITE_TAC[lcx] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `abs sL = sL` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cO * (sO - sL)`; `&0 <= sO * (cL - cO)`; `cO * sL - sO * cL <= &0`;
    `&0 <= cO * cL`; `&0 <= sO * sL`; `&0 <= cO * cL + sO * sL`] THEN
  SUBGOAL_THEN `ABT_lower cL sL uL vL aL (--sO) cO =
                (cO * sL - sO * cL) * (uL + aL) + (cO * cL + sO * sL) * vL` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(--sO * cL + cO * sL) = --(cO * sL - sO * cL) /\
                  abs(-- --sO * sL + cO * cL) = cO * cL + sO * sL` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cL * uL - sL * (vL + aL)`;
    `&0 <= --(cO * sL - sO * cL) * (cL * uL - sL * (vL + aL))`;
    `&0 <= cL * (ABT_lower cL sL uL vL aL (--sO) cO - (vO + aO))`] THEN
  SUBGOAL_THEN `cL * (vO + aO) - aL * (cO * sL - sO * cL) * (cL + sL) <= cO * vL`
    ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CWMM_EQ_HINT `--cO * vL` (ASSUME `cL pow 2 + sL pow 2 = &1`);
      CWMM_EQ_HINT `cL:real` (ASSUME `ABT_lower cL sL uL vL aL (--sO) cO =
                (cO * sL - sO * cL) * (uL + aL) + (cO * cL + sO * sL) * vL`)];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cO = &0) /\ ~(cW = &0) /\ &0 < cO * cW` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWMM_CLEAR_ASSUME_TAC [`cO:real`,`iO:real`; `cW:real`,`iW:real`] `cO * cW`
    (ASSUME `&0 <= &1 + (cL / cO) * cwmmb_boundary cO sO + (sO * cL - cO * sL) * (cL + sL) / cO +
              sL * cW + cL * t + cL / cW - &3 * cL - cL * t / cW`) THEN
  let qc = `cO * cW - cW * (cO * sL - sO * cL) * (cL + sL) +
            cO * (cW * (sL * cW + cL * t) + cL)` in
  let sub tm = subst [qc,`QC:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= cW * (cO * vL - (cL * (vO + aO) - aL * (cO * sL - sO * cL) * (cL + sL)))`;
    `&0 <= cO * ((cL * (t + &3 * cW) - aL * (cW * (sL * cW + cL * t) + cL)) -
                 cW * ABT_lower cW sW uW vW aL (--sL) cL)`;
    `&0 <= cO * cW`;
    `&0 <= (cO * cW) * (ABT_lower cW sW uW vW aL (--sL) cL - (vL + aL))`;
    `cW * cL * (vO + aO) + aL * QC <= cO * cL * (t + &3 * cW)`;
    `&0 < cW * cL`; `&0 < (cW * cL) * ((vO + aO) - cwmmb_boundary cO sO)`;
    `&0 <= cL + sL`; `&0 <= --(cO * sL - sO * cL) * (cL + sL)`;
    `&0 <= cW * (--(cO * sL - sO * cL) * (cL + sL))`;
    `&0 <= sL * cW + cL * t`; `&0 <= cO * (cW * (sL * cW + cL * t) + cL)`;
    `&0 < QC`; `&0 < (aL - &1) * QC`]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: high_sector *)
let CWMM_HIGH_SECTOR = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aL = aW /\
     lcont cW sW uW vW aW /\ linside cL sL uL vL aL (&457 / &500) (&1) /\
     cwmmb_boundary cO sO < vO + aO /\
     vW + aW <= t + &3 * cW /\
     sO <= t /\ sO <= sL /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `sL:real`; `t + &3 * cW`] CWMS_WALL_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `sL:real`]
    CWMMB_HIGH_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `cO:real`; `sO:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  UNDISCH_TAC `linside cL sL uL vL aL (&457 / &500) (&1)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= cO * (sL - sO)`; `&0 <= sO * (cO - cL)`; `&0 <= cO * sL - sO * cL`;
    `&0 < cO * cL`; `&0 <= sO * sL`; `&0 < cO * cL + sO * sL`] THEN
  SUBGOAL_THEN `ABT_lower cL sL uL vL aL (--sO) cO =
                (cO * sL - sO * cL) * uL + (cO * cL + sO * sL) * vL` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(--sO * cL + cO * sL) = cO * sL - sO * cL /\
                  abs(-- --sO * sL + cO * cL) = cO * cL + sO * sL` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (cO * sL - sO * cL) * (((&457 / &500) * cL + sL) - uL)`;
    `vO + aO - (cO * sL - sO * cL) * ((&457 / &500) * cL + sL) <= (cO * cL + sO * sL) * vL`] THEN
  SUBGOAL_THEN `~(cW = &0) /\ ~(cO * cL + sO * sL = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = (cwmmb_boundary cO sO - (cO * sL - sO * cL) * ((&457 / &500) * cL + sL)) /
                  (cO * cL + sO * sL)` THEN
  SUBGOAL_THEN `(cO * cL + sO * sL) * q =
                cwmmb_boundary cO sO - (cO * sL - sO * cL) * ((&457 / &500) * cL + sL)`
    ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `~(cO * cL + sO * sL = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  CWMM_CLEAR_ASSUME_TAC [`cW:real`,`iW:real`] `cW:real`
    (ASSUME `&0 <= q + &1 + sL * cW + cL * t + cL / cW - &3 * cL - cL * t / cW`) THEN
  let qc = `(cO * cL + sO * sL) * (cW + cW * (sL * cW + cL * t) + cL)` in
  let sub tm = subst [qc,`QC:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= (cO * cL + sO * sL) * (cW * q + cW + sL * cW pow 2 + cL * t * cW + cL -
                                   &3 * cL * cW - cL * t)`;
    `&0 <= cW * ((cO * cL + sO * sL) * vL -
                 (vO + aO - (cO * sL - sO * cL) * ((&457 / &500) * cL + sL)))`;
    `&0 <= (cO * cL + sO * sL) * ((cL * (t + &3 * cW) - aL * (cW * (sL * cW + cL * t) + cL)) -
                 cW * ABT_lower cW sW uW vW aL (--sL) cL)`;
    `&0 <= (cO * cL + sO * sL) * cW`;
    `&0 <= ((cO * cL + sO * sL) * cW) * (ABT_lower cW sW uW vW aL (--sL) cL - (vL + aL))`;
    `&0 < cW * ((vO + aO) - cwmmb_boundary cO sO)`;
    `&0 <= sL * cW + cL * t`; `&0 < cW + cW * (sL * cW + cL * t) + cL`;
    `&0 < QC`; `&0 < (aL - &1) * QC`]) THEN
  NLIN_TAC ~deg2:false
   [CWMM_EQ_HINT `cW:real` (ASSUME `(cO * cL + sO * sL) * q =
                cwmmb_boundary cO sO - (cO * sL - sO * cL) * ((&457 / &500) * cL + sL)`)]);;

(* Lean: sector *)
let CWMM_SECTOR = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aL = aW /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     cwmmb_boundary cO sO < vO + aO /\
     vW + aW <= t + &3 * cW /\
     sO <= t /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `sL <= sO` THENL
   [MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
      CWMM_LOW_SECTOR);
    MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
      CWMM_HIGH_SECTOR)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
