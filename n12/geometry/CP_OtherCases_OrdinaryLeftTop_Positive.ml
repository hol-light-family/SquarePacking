(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/Positive.lean       *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop).            *)
(* Input: ocolti_input (fields side, marker, anchor, left, middle, far,     *)
(* corner, lower, topNear, topFar in that order); ScalarMargins: OLTSM_*;   *)
(* CanonicalScalars.bounds: CCCS_BOUNDS.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_Inputs.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ScalarMargins.ml";;

(* Lean: Profile (structure) *)
let oltp_profile = new_definition
 `oltp_profile (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    &0 < c /\ &0 < s /\ s <= c /\ (&2 / &3) * c < s /\ s < (&8 / &11) * c /\
    --(&43 / &500) * c <= u /\ --(&27 / &100) * s - (&1 / &25) * c <= v /\
    u + a <= (&11 / &25) * c + s /\ v + a <= c`;;

let OLTP_NEG_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;;

let OLTP_FACE_TAC t =
  (REWRITE_TAC[GSYM REAL_NOT_LT] ORELSE REWRITE_TAC[GSYM REAL_NOT_LE]) THEN
  DISCH_TAC THEN OLTP_NEG_TAC t;;

(* Lean: positive_profile *)
let OLTP_POSITIVE_PROFILE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocolti_input c s u v a /\
               &0 < c /\ &0 <= s /\ s <= c
     ==> oltp_profile c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ocolti_input c s u v a` THEN REWRITE_TAC[ocolti_input] THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`linside c s u v a (&13 / &20) (&7 / &20)`;
                         `linside c s u v a (&0) (&13 / &50)`] THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--(&1 / &2) * s <= v` ASSUME_TAC THENL
   [OLTP_FACE_TAC `~linside c s u v a (&1 / &2) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c` ASSUME_TAC THENL
   [OLTP_FACE_TAC `~linside c s u v a (&0) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&37 / &50) * c + s` ASSUME_TAC THENL
   [OLTP_FACE_TAC `~linside c s u v a (&37 / &50) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&43 / &500) * c <= u` ASSUME_TAC THENL
   [OLTP_FACE_TAC `~linside c s u v a (--(&43 / &500)) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &6) * c < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_LOWSIXTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_SIXTHSLOPESINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `u + a <= (&11 / &25) * c + s` ASSUME_TAC THENL
   [OLTP_FACE_TAC `~linside c s u v a (&11 / &25) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 / &3) * c < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_LOWTWOTHIRDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_SEVENTEENONEOHFOUR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `--(&27 / &100) * s - (&1 / &25) * c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u < (&27 / &100) * c - (&1 / &25) * s` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    OLTP_NEG_TAC `~linside c s u v a (&27 / &100) (--(&1 / &25))`; ALL_TAC] THEN
  SUBGOAL_THEN `s < (&8 / &11) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_HIGHEIGHTELEVENTHS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[oltp_profile] THEN RASM_ARITH_TAC);;

(* Lean: upper_point *)
let OLTP_UPPER_POINT = prove
 (`forall c s u v a x. c * c + s * s = &1 /\ &0 < a /\ ocolti_input c s u v a /\
                 oltp_profile c s u v a /\ &7 / &25 <= x /\ x <= &2 / &5
     ==> linside c s u v a x (&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oltp_profile; ocolti_input] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_POINTUPPERU) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OLTSM_POINTUPPERV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= c * (x - &7 / &25) /\ &0 <= s * (&2 / &5 - x) /\
                &0 <= c * (&2 / &5 - x) /\ &0 <= s * (x - &7 / &25)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `linside c s u v a (&0) (&13 / &50)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN RASM_ARITH_TAC);;

(* Lean: upper_points *)
let OLTP_UPPER_POINTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ ocolti_input c s u v a /\
               oltp_profile c s u v a
     ==> linside c s u v a (&7 / &25) (&1) /\ linside c s u v a (&2 / &5) (&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OLTP_UPPER_POINT THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
