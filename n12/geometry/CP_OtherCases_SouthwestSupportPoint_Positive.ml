(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SouthwestSupportPoint/Positive.lean *)
(* (namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint).      *)
(* Sections 4 and 5 of C974-C976-SW-SUPPORT-POINT (nonnegative sign).       *)
(* Input: ocswsp_input; LowerFaces.positive: OCSWSPLF_POSITIVE; Scalars.*:  *)
(* OCSWSPS_*; upper: ABT_upper; WallProfile.upper_in_bands:                 *)
(* OCWPSG_UPPER_IN_BANDS; short_projections: WFP_SP; CanonicalProjection:   *)
(* CCCP_BEFORE / CCCP_AFTER; increasing_projection:                         *)
(* CCOS_INCREASING_PROJECTION; LowerCornerSupport.horizontal:               *)
(* OCLCS_HORIZONTAL.                                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_LowerFaces.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Scalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;
needs "n12/geometry/CP_OtherCases_LowerCornerSupport.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;

let OCSWSPPOS_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let OCSWSPPOS_STEP t keep =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCSWSPPOS_KEEP_TAC keep; ALL_TAC];;

(* the upper support in face form, for either sign of the second component *)
let OCSWSPPOS_UPPER_FORMS = prove
 (`forall c s u v a p q.
     &0 < a /\ &0 <= p * c + q * s
     ==> (&0 <= --p * s + q * c
          ==> ABT_upper c s u v a p q = (p * c + q * s) * (u + a) + (--p * s + q * c) * (v + a)) /\
         (--p * s + q * c <= &0
          ==> ABT_upper c s u v a p q = (p * c + q * s) * (u + a) + (--p * s + q * c) * v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
  CONJ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REAL_ARITH_TAC);;

(* Lean: positive_lowerU (private) *)
let OCSWSPPOS_POSITIVE_LOWERU = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a /\
      &0 < c /\ &0 <= s /\ s <= c /\
      (u + a <= &13 / &50 * c \/ ABT_upper c s u v a (&35) (&9) <= &91 / &10)
      ==> u < --(&73 / &100) * c - &1 / &25 * s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC_ALL OCSWSPLF_POSITIVE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ocswsp_input c s u v a` THEN REWRITE_TAC[ocswsp_input] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(WFP_SP `&99 / &100` `&1 / &25`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    OCSWSPPOS_KEEP_TAC [];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&35`; `&9`]
    OCSWSPPOS_UPPER_FORMS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= (&35 * c + &9 * s) * (u - (--(&73 / &100) * c - &1 / &25 * s))`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= &9 * c - &35 * s` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      lhand(lhand(concl th)) = `&0`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= (&9 * c - &35 * s) * (v - (&2 / &5 * s - c)) /\
                  &0 < (a - &1) * ((&35 * c + &9 * s) + (&9 * c - &35 * s))`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OCSWSPS_POSITIVE_LOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
    REWRITE_TAC[ocswsps_f1] THEN DISCH_TAC THEN OCSWSPPOS_KEEP_TAC [];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
      rand(lhand(concl th)) = `&0`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= (&35 * s - &9 * c) * --(v + &13 / &50 * c) /\
                  &0 < (a - &1) * (&35 * c + &9 * s)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
      OCSWSPPOS_KEEP_TAC [`linside c s u v a (&0) (--(&13 / &50))`]; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OCSWSPS_POSITIVE_HIGH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ocswsps_f2] THEN DISCH_TAC THEN OCSWSPPOS_KEEP_TAC []]);;

(* Lean: positive_upperV (private) *)
let OCSWSPPOS_POSITIVE_UPPERV = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a /\
      &0 < c /\ &0 <= s /\ s <= c
      ==> &73 / &100 * s - &1 / &25 * c < v + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCSWSPLF_POSITIVE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ocswsp_input c s u v a` THEN REWRITE_TAC[ocswsp_input] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&3 / &4 * c <= s` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `&4 / &5`; `&3 / &5`; `&24 / &25`; `&33 / &100`]
      CCCP_AFTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
    OCSWSPPOS_KEEP_TAC [];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  let mN = `~linside c s u v a (--(&7 / &20)) (&7 / &20)`
  and mE = `~linside c s u v a (&7 / &20) (--(&7 / &20))`
  and mB0 = `~linside c s u v a (-- &1 / &2) (-- &1)`
  and mB1 = `~linside c s u v a (-- &13 / &50) (-- &1)` in
  MAP_EVERY (fun x -> FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[] o
      CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) o SPEC x o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `--(&1 / &2)`)) (concl th))))
    [`--(&1 / &2)`; `--(&13 / &50)`] THEN
  MP_TAC(WFP_SP `--(&23 / &100)` `&24 / &25`) THEN
  MP_TAC(WFP_SP `&61 / &100` `&13 / &20`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&4 / &5`; `&3 / &5`; `&3 / &20`; `&27 / &20`]
    CCCP_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&7 / &10`; `&7 / &10`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  OCSWSPPOS_STEP `--(&1 / &2) * c - s <= u` [mB0; `linside c s u v a (--(&7 / &20)) (--(&7 / &20))`] THEN
  OCSWSPPOS_STEP `v + a <= &7 / &20 * (c + s)` [mN; `linside c s u v a (--(&7 / &20)) (--(&7 / &20))`] THEN
  OCSWSPPOS_STEP `u + a <= &7 / &20 * (c - s)` [mE; `linside c s u v a (--(&7 / &20)) (--(&7 / &20))`; `linside c s u v a (--(&13 / &50)) (&0)`] THEN
  OCSWSPPOS_STEP `&13 / &50 * s - c <= v` [mB1; `linside c s u v a (--(&7 / &20)) (--(&7 / &20))`; `linside c s u v a (--(&13 / &50)) (&0)`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `--(&1 / &2)`; `--(&13 / &50)`] OCLCS_HORIZONTAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN (FIRST_ASSUM MATCH_ACCEPT_TAC ORELSE OCSWSPPOS_KEEP_TAC [`linside c s u v a (--(&7 / &20)) (--(&7 / &20))`; `linside c s u v a (--(&13 / &50)) (&0)`]);
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= s * (&7 / &20 * (c - s) - (u + a)) /\
    &0 <= c * ((&73 / &100 * s - &1 / &25 * c) - (v + a)) /\
    &0 < (a - &1) * (c + s)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    OCSWSPPOS_KEEP_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSWSPS_POSITIVE_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ocswsps_f3] THEN DISCH_TAC THEN OCSWSPPOS_KEEP_TAC []);;

(* Lean: positive *)
let OCSWSPPOS_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a /\
      &0 < c /\ &0 <= s /\ s <= c /\
      (u + a <= &13 / &50 * c \/ ABT_upper c s u v a (&35) (&9) <= &91 / &10)
      ==> linside c s u v a (--(&73 / &100)) (--(&1 / &25))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC_ALL OCSWSPPOS_POSITIVE_LOWERU) THEN
  MP_TAC(SPEC_ALL OCSWSPPOS_POSITIVE_UPPERV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  UNDISCH_TAC `ocswsp_input c s u v a` THEN REWRITE_TAC[ocswsp_input] THEN STRIP_TAC THEN
  OCSWSPPOS_KEEP_TAC [`linside c s u v a (--(&7 / &20)) (--(&7 / &20))`; `linside c s u v a (--(&1 / &2)) (&0)`]);;
