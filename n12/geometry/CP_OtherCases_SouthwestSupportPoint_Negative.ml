(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SouthwestSupportPoint/Negative.lean *)
(* (namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint).      *)
(* Section 6 of C974-C976-SW-SUPPORT-POINT (negative sign, s = --t).        *)
(* Input: ocswsp_input; LowerFaces.negative: OCSWSPLF_NEGATIVE; Scalars.*:  *)
(* OCSWSPS_*; upper: ABT_upper; WallProfile.upper_in_bands:                 *)
(* OCWPSG_UPPER_IN_BANDS; CanonicalScalars.bounds: CCCS_BOUNDS.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_LowerFaces.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Scalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let OCSWSPNEG_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: negative *)
let OCSWSPNEG_NEGATIVE = prove
 (`forall c s u v a t.
      c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a /\
      s = --t /\ &0 < c /\ &0 <= t /\ t <= c /\
      (u + a <= &13 / &50 * c \/ ABT_upper c s u v a (&35) (&9) <= &91 / &10)
      ==> linside c s u v a (--(&73 / &100)) (--(&1 / &25))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC_ALL OCSWSPLF_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ocswsp_input c s u v a` THEN REWRITE_TAC[ocswsp_input] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ABT_upper c s u v a (&35) (&9) =
                ABT_upper c (--t) u v a (&35) (&9)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [OCSWSPNEG_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper c (--t) u v a (&35) (&9) =
                (&35 * c - &9 * t) * (u + a) + (&35 * t + &9 * c) * (v + a)`
    ASSUME_TAC THENL
   [REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `&35 * c + &9 * --t = &35 * c - &9 * t /\
                  -- &35 * --t + &9 * c = &35 * t + &9 * c` (fun th -> REWRITE_TAC[th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c /\ t <= c ==> abs(&35 * c - &9 * t) = &35 * c - &9 * t`;
                 REAL_ARITH `&0 < c /\ &0 <= t ==> abs(&35 * t + &9 * c) = &35 * t + &9 * c`] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a - &1) * ((&35 * c - &9 * t) + (&35 * t + &9 * c))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* lowerV *)
  SUBGOAL_THEN `v < --(&73 / &100) * t - &1 / &25 * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `t <= &3 / &4 * c` THENL [OCSWSPNEG_KEEP_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `&3 / &5 <= t` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (&4 / &5 - c) * (&4 / &5 + c) /\
                    &0 <= (&3 / &5 - t) * (&3 / &5 + t)` MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (&35 * c - &9 * t) * (u - (--c + &13 / &50 * t)) /\
      &0 <= (&35 * t + &9 * c) * (v - (--(&73 / &100) * t - &1 / &25 * c)) /\
      &0 <= c * t /\ &0 <= t * (t - &3 / &5)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    OCSWSPNEG_KEEP_TAC [];
    ALL_TAC] THEN
  (* lowerU *)
  SUBGOAL_THEN `u < --(&73 / &100) * c + &1 / &25 * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&35 * c - &9 * t) * (u - (--(&73 / &100) * c + &1 / &25 * t))`
      ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `--c <= v` THENL
     [SUBGOAL_THEN `&0 <= (&35 * t + &9 * c) * (v - --c)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`c:real`; `t:real`] OCSWSPS_NEGATIVE_LOWER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ocswsps_f4] THEN DISCH_TAC THEN OCSWSPNEG_KEEP_TAC [];
      ALL_TAC] THEN
    SUBGOAL_THEN `u + a <= t` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      OCSWSPNEG_KEEP_TAC [`~linside c (--t) u v a (&0) (--(&1))`]; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `t:real`] OCSWSPS_HALF_LOWER_OF_SPAN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= (&35 * t + &9 * c) * (v - (--(&13 / &50) * t - c))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `t:real`] OCSWSPS_NEGATIVE_UPPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ocswsps_f5] THEN DISCH_TAC THEN OCSWSPNEG_KEEP_TAC [];
    ALL_TAC] THEN
  OCSWSPNEG_KEEP_TAC []);;
