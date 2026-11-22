(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerOtherMixed.lean                  *)
(* (namespace N12Compact.CornerWallMarkerOtherMixed).                        *)
(* Positive-L L-axis / W-axis separator with the genuine foreign marker.     *)
(* Squares are 5-tuples; Lean upper/lower are ABT_upper/ABT_lower;           *)
(* CornerWallMarkerShared.bottom_support is CWMS_BOTTOM_SUPPORT, the scalar  *)
(* margin is CWMOMB_MARGIN, left_wall is FSBL_LEFT_WALL.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallMarkerShared.ml";;
needs "n12/geometry/CornerWallMarkerOtherMixedBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMOM_clear_poly dens k t =
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
  then failwith "CWMOM_clear_poly: denominators remain" else
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
let CWMOM_CLEAR_EQ dens k t =
  let p = CWMOM_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMOM_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMOM_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWMOM_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMOM_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMOM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMOM_LT_BY_POS else CWMOM_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWMOM_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMOM_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMOM_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMOM_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMOM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWMOM_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMOM_SCALE_LT else CWMOM_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMOM_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: sector *)
let CWMOM_SECTOR = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW (uW:real) vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     sO <= t /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     ABT_upper cO sO uO vO aO (--sL) cL <= vL /\
     ABT_upper cL sL uL vL aL t cW <= vW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ex = (sO * cL - cO * sL + abs(sO * cL - cO * sL)) / &2` THEN
  SUBGOAL_THEN `&0 <= ex /\ sO * cL - cO * sL <= ex` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ex" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cL:real`; `sL:real`;
                `&2 * cO + (&457 / &500) * sO`] CWMS_BOTTOM_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `sL:real`; `ex:real`]
    CWMOMB_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  REWRITE_TAC[lcx] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `abs sL = sL` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= t * cL`; `&0 <= cW * sL`; `&0 <= t * cL + cW * sL`;
    `&0 <= cW * (cL - sL)`; `&0 <= sL * (cW - t)`; `&0 <= cW * cL - t * sL`] THEN
  SUBGOAL_THEN `ABT_upper cL sL uL vL aL t cW =
                (t * cL + cW * sL) * (uL + aL) + (cW * cL - t * sL) * (vL + aL)` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(t * cL + cW * sL) = t * cL + cW * sL /\
                  abs(--t * sL + cW * cL) = cW * cL - t * sL` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cL * uL - sL * (vL + aL)`;
    `&0 <= (t * cL + cW * sL) * (cL * uL - sL * (vL + aL))`] THEN
  SUBGOAL_THEN `cW * (vL + aL) + aL * cL * (t * cL + cW * sL) <= cL * ABT_upper cL sL uL vL aL t cW`
    ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false
     [CWMOM_EQ_HINT `cW * (vL + aL)` (ASSUME `cL pow 2 + sL pow 2 = &1`);
      CWMOM_EQ_HINT `cL:real` (ASSUME `ABT_upper cL sL uL vL aL t cW =
                (t * cL + cW * sL) * (uL + aL) + (cW * cL - t * sL) * (vL + aL)`)];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cO = &0) /\ ~(cL = &0) /\ &0 < cO * cL` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWMOM_CLEAR_ASSUME_TAC [`cO:real`,`iO:real`; `cL:real`,`iL:real`] `cO * cL`
    (ASSUME `&0 <= &1 + cW * cO + t * cL + cW * sL + cW / cL +
              (cW * sL / cL) * (sO - &2 + (&1 - (&457 / &500) * sO) / cO) -
              (&457 / &500) * t - &3 * cW + (cW / cL) * ex`) THEN
  let qc = `cW * (cO * (cO * cL + sO * sL) + sL + cO * ex) + cO * cW +
            cO * cL * (t * cL + cW * sL) + cO * cL`
  and rc = `cW * sL * (&2 * cO + (&457 / &500) * sO) +
            cO * cL * ((&457 / &500) * t + &3 * cW)` in
  let sub tm = subst [qc,`QC:real`; rc,`RC:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= cO * cW`; `&0 <= cO * cL`;
    `&0 <= (cO * cW) * (vL - ABT_upper cO sO uO vO aL (--sL) cL)`;
    `&0 <= (cO * cL) * (vW - ABT_upper cL sL uL vL aL t cW)`;
    `&0 <= cO * (cL * ABT_upper cL sL uL vL aL t cW -
                 (cW * (vL + aL) + aL * cL * (t * cL + cW * sL)))`;
    `&0 <= cW * (cO * ABT_upper cO sO uO vO aL (--sL) cL -
                 (aL * (cO * (cO * cL + sO * sL) + sL + cO * ex) -
                  sL * (&2 * cO + (&457 / &500) * sO)))`;
    `&0 <= (cO * cL) * (((&457 / &500) * t + &3 * cW) - (vW + aL))`;
    `aL * QC <= RC`;
    `&0 <= sO * sL`; `&0 <= cO * (cO * cL + sO * sL) + sL + cO * ex`;
    `&0 <= cW * (cO * (cO * cL + sO * sL) + sL + cO * ex)`;
    `&0 <= (cO * cL) * (t * cL + cW * sL)`;
    `&0 < QC`; `&0 < (aL - &1) * QC`]) THEN
  NLIN_TAC ~deg2:false []);;
