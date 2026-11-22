(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightCornerLongitudinal.lean (Jatloe).       *)
(* The E-owned longitudinal selector is excluded using the complete top-wall *)
(* support and the top container wall of E.                                   *)
(* K = e*cT + f*sT and H = f*cT - e*sT are written out.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightCornerLongitudinalBounds.ml";;
needs "n12/geometry/UpperRightCornerReachAxes.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let URCL_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: support_growth *)
let URCL_SUPPORT_GROWTH = prove
 (`forall cT sT uT vT aT e f.
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     c977cc_normal e f /\ c977cc_normal cT sT /\ &1 < aT /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20)
     ==> (&7 / &2) * e + &3 * f + (&3 / &5) * f < ABT_upper cT sT uT vT aT e f + aT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `&13 / &20`; `&61 / &100`] URCLB_DISK_MARGIN) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `&13 / &20`; `&61 / &100`] URCLB_DISK_MARGIN) THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `&1 / &2`; `&3 / &5`] URCLB_DISK_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `sT:real`] URCLB_MARKER_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal e f`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cT sT`)) THEN
  URCL_UNFOLD_TAC `linside cT sT uT vT aT (&2) (&1543 / &500)` THEN
  URCL_UNFOLD_TAC `linside cT sT uT vT aT (&12 / &5) (&3)` THEN
  SUBGOAL_THEN `&0 < e * cT + f * sT` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&87 / &50) * cT + &3 * sT <= uT \/
                vT + aT <= &3 * cT - (&87 / &50) * sT` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cT sT uT vT aT (&87 / &50) (&3)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&47 / &20) * (cT + sT) <= uT \/
                (&47 / &20) * (cT - sT) <= vT` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cT sT uT vT aT (&47 / &20) (&47 / &20)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `--e * sT + f * cT = f * cT - e * sT`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  ASM_CASES_TAC `&0 <= f * cT - e * sT` THENL
  [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
     is_disj(concl th) && can (find_term ((=) `&47 / &20`)) (concl th))) THENL
   [SUBGOAL_THEN
     `&0 <= (e * cT + f * sT) * (uT - (&47 / &20) * (cT + sT)) /\
      &0 <= (f * cT - e * sT) * ((vT + aT) - (&3 * cT - (&12 / &5) * sT)) /\
      &0 < (e * cT + f * sT) * (aT - (&13 / &20) * (cT + sT)) /\
      &0 <= (f * cT - e * sT) * ((&3 / &5) * sT)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
      MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(e * cT + f * sT) * ((&47 / &20) * (cT + sT) + aT) +
      (f * cT - e * sT) * (&3 * cT - (&12 / &5) * sT) =
      &3 * (e + f) + (e * cT + f * sT) * (aT - (&13 / &20) * (cT + sT)) +
      (&3 / &5) * sT * (f * cT - e * sT)` MP_TAC THENL
    [UNDISCH_TAC `cT * cT + sT * sT = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `(&87 / &50) * cT + &3 * sT <= uT` ASSUME_TAC THENL
    [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
     ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `sT:real`] URCLB_LOWER_PAIR_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= (e * cT + f * sT) * (uT - ((&87 / &50) * cT + &3 * sT)) /\
      &0 <= (f * cT - e * sT) * (vT - (&47 / &20) * (cT - sT)) /\
      &0 < ((e * cT + f * sT) + (f * cT - e * sT) + &1) * (aT - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(e * cT + f * sT) * ((&87 / &50) * cT + &3 * sT) +
      (f * cT - e * sT) * ((&47 / &20) * (cT - sT)) +
      (e * cT + f * sT) + (f * cT - e * sT) + &1 -
      ((&7 / &2) * e + &3 * f + (&3 / &5) * f) =
      &1 + e * (cT - sT - &44 / &25 + (&61 / &100) * sT pow 2 + (&13 / &20) * cT * sT) +
      f * (cT + sT - &5 / &4 + (&13 / &20) * sT pow 2 - (&61 / &100) * cT * sT)`
    MP_TAC THENL
    [UNDISCH_TAC `cT * cT + sT * sT = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `abs(f * cT - e * sT) = --(f * cT - e * sT)` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
     is_disj(concl th) && can (find_term ((=) `&87 / &50`)) (concl th))) THENL
   [SUBGOAL_THEN
     `&0 <= (e * cT + f * sT) * (uT - ((&87 / &50) * cT + &3 * sT)) /\
      &0 <= --(f * cT - e * sT) * (((&1543 / &500) * cT - &2 * sT) - vT) /\
      &0 < ((e * cT + f * sT) + &1) * (aT - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(e * cT + f * sT) * ((&87 / &50) * cT + &3 * sT) +
      (f * cT - e * sT) * ((&1543 / &500) * cT - &2 * sT) +
      (e * cT + f * sT) + &1 - ((&7 / &2) * e + &3 * f + (&3 / &5) * f) =
      &1 + e * (cT - &44 / &25 + (&13 / &50) * sT pow 2 - (&43 / &500) * cT * sT) +
      f * ((&43 / &500) * cT pow 2 + sT - (&13 / &50) * cT * sT - &3 / &5)`
    MP_TAC THENL
    [UNDISCH_TAC `cT * cT + sT * sT = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN `(&47 / &20) * (cT + sT) <= uT` ASSUME_TAC THENL
    [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
     ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&3 / &10) * cT <= sT` ASSUME_TAC THENL
    [RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `sT:real`] URCLB_UPPER_PAIR_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (e * cT + f * sT) * (uT - (&47 / &20) * (cT + sT)) /\
      &0 <= --(f * cT - e * sT) * ((&3 * cT - (&87 / &50) * sT) - (vT + aT)) /\
      &0 < ((e * cT + f * sT) - (f * cT - e * sT) + &1) * (aT - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(e * cT + f * sT) * ((&47 / &20) * (cT + sT)) +
      (f * cT - e * sT) * (&3 * cT - (&87 / &50) * sT) +
      (e * cT + f * sT) - (f * cT - e * sT) + &1 -
      ((&7 / &2) * e + &3 * f + (&3 / &5) * f) =
      &1 + e * (cT + sT - &23 / &20 - (&61 / &100) * sT pow 2 - (&13 / &20) * cT * sT) +
      f * (sT - cT + (&61 / &100) * cT * sT - (&13 / &20) * sT pow 2 - &3 / &5)`
    MP_TAC THENL
    [UNDISCH_TAC `cT * cT + sT * sT = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]]);;

(* Lean: top_wall *)
let URCL_TOP_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ lcont c s u v a
     ==> s * (u + a) + c * (v + a) <= &4`,
  REWRITE_TAC[lcont] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &4 - s * (u + a) - c * (v + a)
                           ==> s * (u + a) + c * (v + a) <= &4`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + a - e) - s * (v + a - e)`;
                                `s * (u + a - e) + c * (v + a - e)`]) THEN
  ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
  [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: corner_axis_impossible *)
let URCL_CORNER_AXIS_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cT sT uT vT aT.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     c977cc_normal cE sE /\ c977cc_normal cT sT /\
     aE = aT /\ &1 < aE /\ lcont cE sE uE vE aE /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     ~linside cE sE uE vE aE (&7 / &2) (&3) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     ABT_upper cT sT uT vT aT cE sE <= uE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `cE:real`; `sE:real`]
    URCL_SUPPORT_GROWTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  URCL_UNFOLD_TAC `linside cE sE uE vE aE (&3) (&3)` THEN
  URCL_UNFOLD_TAC `linside cE sE uE vE aE (&16 / &5) (&3)` THEN
  SUBGOAL_THEN `uE + aE <= (&7 / &2) * cE + &3 * sE \/
                &3 * cE - (&7 / &2) * sE <= vE` MP_TAC THENL
  [UNDISCH_TAC `~linside cE sE uE vE aE (&7 / &2) (&3)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URCL_TOP_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sE * (uE - ABT_upper cT sT uT vT aE cE sE) /\
    &0 <= cE * (vE - (&3 * cE - (&7 / &2) * sE)) /\
    &0 <= sE * ((ABT_upper cT sT uT vT aE cE sE + aE) -
                ((&7 / &2) * cE + &3 * sE + (&3 / &5) * sE)) /\
    &0 < cE * (aE - &1) /\
    &0 <= (&1 - cE) * ((&3 / &5) * cE - &2 / &5)` MP_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
    MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;
