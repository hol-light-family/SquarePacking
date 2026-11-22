(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightCornerTopLongitudinal.lean (Jatloe).    *)
(* The remaining top-owned longitudinal axis, and the complete               *)
(* positive/positive corner reach.                                           *)
(* K = cE*cT + sE*sT and H = cE*sT - sE*cT are written out.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightCornerLongitudinal.ml";;
needs "n12/geometry/UpperRightCornerTopTransverse.ml";;
needs "n12/geometry/C977CornerHalfAngle.ml";;

let URCTL_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: corner_radial (private) *)
let URCTL_CORNER_RADIAL = prove
 (`forall c s. c977cc_normal c s ==> &1 - c <= (&3 / &5) * s pow 2`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * ((&3 / &5) * (&1 + c) - &1)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: parallel_lower_margin (private) *)
let URCTL_PARALLEL_LOWER_MARGIN = prove
 (`forall c s. c977cc_normal c s ==> &0 <= c + &2 * s - &1 - (&9 / &5) * c * s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&9 / &10`; `&3 / &10`] URCLB_DISK_MARGIN) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URCTL_CORNER_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= s * (&2 - (&9 / &5) * c - (&3 / &5) * s)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&1 - c <= (&3 / &5) * s pow 2` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: positive_lower_margin (private) *)
let URCTL_POSITIVE_LOWER_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 <= c * t - s * d
     ==> &0 <= s + (c * d + s * t) * (c + s - &1) - (&9 / &5) * d * s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CHA_ORDERED_NORMALS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URCTL_PARALLEL_LOWER_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `c * (c + s - &1) - (&9 / &5) * s <= &0` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 - c) * (c + s - &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= --(c * (c + s - &1) - (&9 / &5) * s) * (c - d) /\
    &0 <= (s * (c + s - &1)) * (t - s)` MP_TAC THENL
  [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `s + (c * d + s * t) * (c + s - &1) - (&9 / &5) * d * s =
    (c + &2 * s - &1 - (&9 / &5) * c * s) -
    (c * (c + s - &1) - (&9 / &5) * s) * (c - d) + s * (c + s - &1) * (t - s)`
  MP_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_lower_margin (private) *)
let URCTL_NEGATIVE_LOWER_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ c * t - s * d <= &0
     ==> &0 <= s + s * (c * d + s * t) + d - (c * d + s * t) - (&9 / &5) * d * s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CSB_DOT_LE_ONE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URCTL_PARALLEL_LOWER_MARGIN) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URCTL_CORNER_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  ASM_CASES_TAC `s <= &5 / &9` THENL
  [MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CSB_SINE_ORDER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= c - &1 + s * (&9 / &5 - c)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= s * (&9 / &5 - c - (&3 / &5) * s)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&1 - c <= (&3 / &5) * s pow 2` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`;
                 `c - &1 + s * (&9 / &5 - c)`; `s * (&1 - s)`] C977CSB_LINEAR_ARC_MAX) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= s * (&5 / &9 - s)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(c - &1 + s * (&9 / &5 - c)) * c + (s * (&1 - s)) * s =
                 s - (c + &2 * s - &1 - (&9 / &5) * c * s)` SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   SUBGOAL_THEN `&0 <= (&1 - (c * d + s * t)) * (&1 - s) /\
                 &0 <= (&1 - d) * ((&9 / &5) * s - &1)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

(* Lean: top_lower *)
let URCTL_TOP_LOWER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\ &1 < a /\
     linside c s u v a (&2) (&1543 / &500) /\
     linside c s u v a (&12 / &5) (&3) /\
     ~linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&47 / &20) (&47 / &20)
     ==> (&17 / &10) * c + &3 * s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &20`; `&61 / &100`] URCLB_DISK_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  URCTL_UNFOLD_TAC `linside c s u v a (&2) (&1543 / &500)` THEN
  URCTL_UNFOLD_TAC `linside c s u v a (&12 / &5) (&3)` THEN
  ASM_CASES_TAC `(&87 / &50) * c + &3 * s <= u` THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= &3 * c - (&87 / &50) * s` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&87 / &50) (&3)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&47 / &20) * (c + s) <= u` MP_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(&47 / &20) * (c - s) <= v` MP_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&47 / &20) (&47 / &20)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: impossible *)
let URCTL_IMPOSSIBLE = prove
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
     uT + aT <= ABT_lower cE sE uE vE aE cT sT
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`] URCTL_TOP_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URCL_TOP_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  URCTL_UNFOLD_TAC `linside cE sE uE vE aE (&3) (&3)` THEN
  URCTL_UNFOLD_TAC `linside cE sE uE vE aE (&16 / &5) (&3)` THEN
  SUBGOAL_THEN `&0 < cE * cT + sE * sT` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (cE * cT + sE * sT) + (cE * sT - sE * cT) /\
                &0 <= (cE * cT + sE * sT) - (cE * sT - sE * cT)` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= cT * (cE - sE) /\ &0 <= sT * (cE + sE) /\
                 &0 <= cE * (cT - sT) /\ &0 <= sE * (cT + sT)` MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &10 <= cE * cT + sE * sT` ASSUME_TAC THENL
  [SUBGOAL_THEN `(cE * cT + sE * sT) pow 2 + (cE * sT - sE * cT) pow 2 = &1` MP_TAC THENL
   [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN UNDISCH_TAC `cT * cT + sT * sT = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= ((cE * cT + sE * sT) + (cE * sT - sE * cT)) *
                       ((cE * cT + sE * sT) - (cE * sT - sE * cT))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   UNDISCH_TAC `&0 < cE * cT + sE * sT` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
   SPEC_TAC(`cE * cT + sE * sT`,`K:real`) THEN SPEC_TAC(`cE * sT - sE * cT`,`H:real`) THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
   NLIN_TAC [SQ_NONNEG `K - &7 / &10`]; ALL_TAC] THEN
  SUBGOAL_THEN `uE + aE <= (&7 / &2) * cE + &3 * sE \/
                &3 * cE - (&7 / &2) * sE <= vE` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cE sE uE vE aE (&7 / &2) (&3)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= cE * sT - sE * cT` THENL
  [SUBGOAL_THEN `ABT_lower cE sE uE vE aE cT sT =
                 (cE * cT + sE * sT) * uE + (cE * sT - sE * cT) * vE` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cT * cE + sT * sE) = cE * cT + sE * sT /\
                  abs(--cT * sE + sT * cE) = cE * sT - sE * cT`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN `cT <= cE * cT + sE * sT` ASSUME_TAC THENL
    [MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
     MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `cE:real` THEN
     CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `cE * (((cE * cT + sE * sT) - cT) - &0) =
                   sE * (cE * sT - sE * cT) + cT * (&1 - cE)` SUBST1_TAC THENL
     [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (cE * cT + sE * sT) * (((&7 / &2) * cE + &3 * sE) - (uE + aE)) /\
      &0 <= (cE * sT - sE * cT) * ((&3 * cE - (&16 / &5) * sE) - vE) /\
      &0 <= ((cE * cT + sE * sT) - cT) * (&1 - (&3 / &10) * cE) /\
      &0 <= cT * ((&1 - (&3 / &10) * cE) - &7 / &10) /\
      &0 < (&1 + (cE * cT + sE * sT)) * (aE - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
      MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(cE * cT + sE * sT) * ((&7 / &2) * cE + &3 * sE) +
      (cE * sT - sE * cT) * (&3 * cE - (&16 / &5) * sE) =
      (&16 / &5) * cT + &3 * sT + (&3 / &10) * cE * (cE * cT + sE * sT)` MP_TAC THENL
    [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cE:real`; `sE:real`; `cT:real`; `sT:real`] URCTL_POSITIVE_LOWER_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= sE * (((cE * cT + sE * sT) * uE + (cE * sT - sE * cT) * vE) - (uT + aE)) /\
      &0 <= sE * (uT - ((&17 / &10) * cT + &3 * sT)) /\
      &0 <= (cE * cT + sE * sT) * (&4 - (sE * (uE + aE) + cE * (vE + aE))) /\
      &0 <= cT * (vE - (&3 * cE - (&7 / &2) * sE)) /\
      &0 < (sE + (cE * cT + sE * sT) * (cE + sE)) * (aE - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LET_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(cE * cT + sE * sT) * (&4 - sE * (uE + aE) - cE * (vE + aE)) +
      cT * (vE - (&3 * cE - (&7 / &2) * sE)) +
      sE * ((cE * cT + sE * sT) * uE + (cE * sT - sE * cT) * vE -
            ((&17 / &10) * cT + &3 * sT + aE)) =
      (cE * cT + sE * sT) + (&9 / &5) * cT * sE -
      aE * (sE + (cE * cT + sE * sT) * (cE + sE))` MP_TAC THENL
    [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `ABT_lower cE sE uE vE aE cT sT =
                 (cE * cT + sE * sT) * uE + (cE * sT - sE * cT) * (vE + aE)` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cT * cE + sT * sE) = cE * cT + sE * sT /\
                  abs(--cT * sE + sT * cE) = --(cE * sT - sE * cT)`
    (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN
     `&0 <= (cE * cT + sE * sT) * (((&7 / &2) * cE + &3 * sE) - (uE + aE)) /\
      &0 <= --(cE * sT - sE * cT) * ((vE + aE) - (&3 * cE - &3 * sE)) /\
      &0 <= (cE * cT + sE * sT) * ((&1 - cE / &2) - &1 / &2) /\
      &0 < (&1 + (cE * cT + sE * sT)) * (aE - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
      MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(cE * cT + sE * sT) * ((&7 / &2) * cE + &3 * sE) +
      (cE * sT - sE * cT) * (&3 * cE - &3 * sE) =
      &3 * cT + &3 * sT + (&1 / &2) * cE * (cE * cT + sE * sT)` MP_TAC THENL
    [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cE:real`; `sE:real`; `cT:real`; `sT:real`] URCTL_NEGATIVE_LOWER_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&0 <= sE * (((cE * cT + sE * sT) * uE + (cE * sT - sE * cT) * (vE + aE)) - (uT + aE)) /\
      &0 <= sE * (uT - ((&17 / &10) * cT + &3 * sT)) /\
      &0 <= (cE * cT + sE * sT) * (&4 - (sE * (uE + aE) + cE * (vE + aE))) /\
      &0 <= cT * (vE - (&3 * cE - (&7 / &2) * sE)) /\
      &0 <= sE * (cE * cT + sE * sT) /\
      &0 < (sE + sE * (cE * cT + sE * sT) + cT) * (aE - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&0 <= sE * (cE * cT + sE * sT)` MP_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
     ALL_TAC] THEN
    SUBGOAL_THEN
     `(cE * cT + sE * sT) * (&4 - sE * (uE + aE) - cE * (vE + aE)) +
      cT * (vE - (&3 * cE - (&7 / &2) * sE)) +
      sE * ((cE * cT + sE * sT) * uE + (cE * sT - sE * cT) * (vE + aE) -
            ((&17 / &10) * cT + &3 * sT + aE)) =
      (cE * cT + sE * sT) + (&9 / &5) * cT * sE -
      aE * (sE + sE * (cE * cT + sE * sT) + cT)` MP_TAC THENL
    [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]]);;

(* Lean: point *)
let URCTL_POINT = prove
 (`forall cE sE uE vE aE cT sT uT vT aT.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     c977cc_normal cE sE /\ c977cc_normal cT sT /\
     aE = aT /\ &1 < aE /\ lcont cE sE uE vE aE /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     ~linside cE sE uE vE aE (&3) (&12 / &5) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     ldisj cE sE uE vE aE cT sT uT vT aT
     ==> linside cE sE uE vE aE (&7 / &2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cT sT`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`] URCRA_ALTERNATIVES) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `c977cc_normal cE sE` THEN UNDISCH_TAC `c977cc_normal cT sT` THEN
   REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                 `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`]
     URCL_CORNER_AXIS_IMPOSSIBLE);
   MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                 `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`]
     URCTL_IMPOSSIBLE);
   MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                 `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`]
     URCTT_IMPOSSIBLE)] THEN
  ASM_REWRITE_TAC[]);;
