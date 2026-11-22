(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerShared.lean                      *)
(* (namespace N12Compact.CornerWallMarkerShared).                            *)
(* Common positive-L transverse selector with the genuine marker faces.      *)
(* Squares are 5-tuples; Lean upper/lower are ABT_upper/ABT_lower;           *)
(* bottom_wall is TSS_BOTTOM_WALL, left_wall is FSBL_LEFT_WALL; the scalar   *)
(* margin is CWMSB_MARGIN.  Normal c s is c977cc_normal c s.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallMarkerSharedBounds.ml";;
needs "n12/geometry/CornerWallSharedAxis.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMS_clear_poly dens k t =
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
  then failwith "CWMS_clear_poly: denominators remain" else
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
let CWMS_CLEAR_EQ dens k t =
  let p = CWMS_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMS_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMS_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWMS_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMS_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMS_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMS_LT_BY_POS else CWMS_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWMS_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMS_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMS_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMS_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMS_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWMS_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMS_SCALE_LT else CWMS_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMS_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: bottom_support *)
let CWMS_BOTTOM_SUPPORT = prove
 (`forall cO sO uO vO aO l r H.
     cO * cO + sO * sO = &1 /\ &0 < aO /\
     c977cc_normal cO sO /\ &0 <= l /\ &0 <= r /\
     lcont cO sO uO vO aO /\ uO + aO <= H
     ==> aO * (cO * (cO * l + sO * r) + r +
               cO * ((sO * l - cO * r + abs(sO * l - cO * r)) / &2)) - r * H <=
         cO * ABT_upper cO sO uO vO aO (--r) l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcy] THEN
  SUBGOAL_THEN `abs sO = sO` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; DISCH_TAC] THEN
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS; REAL_NEG_NEG] THEN
  NLIN_FACTS_TAC [] [`&0 <= r * sO`; `&0 <= l * cO`; `&0 <= r * sO + l * cO`] THEN
  SUBGOAL_THEN `abs(r * sO + l * cO) = r * sO + l * cO /\
                abs(--r * cO + l * sO) = abs(sO * l - cO * r)` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `ad = abs(sO * l - cO * r)` THEN
  NLIN_FACTS_TAC []
   [`&0 <= sO * uO + cO * vO`; `&0 <= (r * sO + l * cO) * (sO * uO + cO * vO)`;
    `&0 <= r * (H - (uO + aO))`] THEN
  NLIN_TAC ~deg2:false [CWMS_EQ_HINT `--r * uO` (ASSUME `cO pow 2 + sO pow 2 = &1`)]);;

(* Lean: wall_support *)
let CWMS_WALL_SUPPORT = prove
 (`forall cW sW uW vW aW t l r H.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cW t /\ c977cc_normal l r /\ sW = --t /\
     lcont cW sW uW vW aW /\ vW + aW <= H
     ==> cW * ABT_lower cW sW uW vW aW (--r) l <=
         l * H - aW * (cW * (r * cW + l * t) + l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= r * cW + l * t`; `&0 <= cW * (l - r)`; `&0 <= r * (cW - t)`;
                     `&0 <= l * cW - r * t`] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `--r`; `l:real`] C977NCO_LOWER_NEGATIVE_NONPOS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[lcx; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `abs t = t` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cW * (uW + aW) + t * (vW + aW) - aW * (cW + t)`;
    `&0 <= (r * cW + l * t) * (cW * (uW + aW) + t * (vW + aW) - aW * (cW + t))`;
    `&0 <= l * (H - (vW + aW))`] THEN
  NLIN_TAC ~deg2:false [CWMS_EQ_HINT `l * vW` (ASSUME `cW pow 2 + t pow 2 = &1`)]);;

(* Lean: sector *)
let CWMS_SECTOR = prove
 (`forall cO sO uO vO aO cL sL (uL:real) vL aL cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cW t /\
     sW = --t /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cW sW uW vW aW /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     sO <= t /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     ABT_upper cO sO uO vO aO (--sL) cL <= vL /\
     vL + aL <= ABT_lower cW sW uW vW aW (--sL) cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW:real = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  ABBREV_TAC `ex = (sO * cL - cO * sL + abs(sO * cL - cO * sL)) / &2` THEN
  SUBGOAL_THEN `&0 <= ex /\ sO * cL - cO * sL <= ex` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ex" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aW:real`; `cL:real`; `sL:real`;
                `&2 * cO + (&457 / &500) * sO`] CWMS_BOTTOM_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `sL:real`; `(&457 / &500) * t + &3 * cW`] CWMS_WALL_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `sL:real`; `ex:real`]
    CWMSB_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
                  REWRITE_TAC[CWMSB_FIRST_DEF; CWMSB_SECOND_DEF] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `~(cO = &0) /\ ~(cW = &0) /\ &0 < cO * cW` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWMS_CLEAR_ASSUME_TAC [`cO:real`,`iO:real`; `cW:real`,`iW:real`] `cO * cW`
    (ASSUME `&0 <= &1 + cL * (cO + t - &3 + (&1 - (&457 / &500) * t) / cW) +
                  sL * (sO + cW - &2 + (&1 - (&457 / &500) * sO) / cO) + ex`) THEN
  let qc = `cO * cW * (cO * cL + sL * sO + &1 + sL * cW + cL * t + ex) + cW * sL + cO * cL`
  and rc = `cO * cW * (sL * &2 + &3 * cL) + (&457 / &500) * cW * sL * sO +
            (&457 / &500) * cO * cL * t` in
  let sub tm = subst [qc,`QC:real`; rc,`RC:real`] tm in
  NLIN_FACTS_TAC []
   (map sub
   [`&0 <= cW * (cO * ABT_upper cO sO uO vO aW (--sL) cL -
                 (aW * (cO * (cO * cL + sO * sL) + sL + cO * ex) -
                  sL * (&2 * cO + (&457 / &500) * sO)))`;
    `&0 <= cO * ((cL * ((&457 / &500) * t + &3 * cW) - aW * (cW * (sL * cW + cL * t) + cL)) -
                 cW * ABT_lower cW (--t) uW vW aW (--sL) cL)`;
    `&0 <= (cO * cW) * (ABT_lower cW (--t) uW vW aW (--sL) cL -
                        (ABT_upper cO sO uO vO aW (--sL) cL + aW))`;
    `aW * QC <= RC`;
    `&0 <= cO * cL`; `&0 <= sL * sO`; `&0 <= sL * cW`; `&0 <= cL * t`;
    `&0 < QC`; `&0 < (aW - &1) * QC`]) THEN
  NLIN_TAC ~deg2:false []);;
