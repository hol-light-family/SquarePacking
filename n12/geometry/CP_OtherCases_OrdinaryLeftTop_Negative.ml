(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/Negative.lean       *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop).            *)
(* The nonpositive canonical sign (s = --t) is impossible.  Input:          *)
(* ocolti_input; ScalarMargins: OLTSM_*; CanonicalScalars.bounds: CCCS_BOUNDS*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_Inputs.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ScalarMargins.ml";;

let OLTN_NEG_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;;

let OLTN_FACE_TAC t =
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OLTN_NEG_TAC t;;

let OLTN_SM_TAC th =
  MP_TAC(SPECL [`c:real`; `t:real`] th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: nonpositive_impossible *)
let OLTN_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ &0 < a /\ ocolti_input c s u v a /\
                 s = --t /\ &0 < c /\ &0 <= t /\ t <= c
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ocolti_input c (--t) u v a` THEN REWRITE_TAC[ocolti_input] THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`linside c (--t) u v a (&13 / &20) (&7 / &20)`;
                         `linside c (--t) u v a (&0) (&13 / &50)`] THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  (* farUpperU *)
  SUBGOAL_THEN `u + a <= (&37 / &50) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&37 / &50) * t <= v` ASSUME_TAC THENL
     [OLTN_FACE_TAC `~linside c (--t) u v a (&37 / &50) (&0)`; ALL_TAC] THEN
    SUBGOAL_THEN `u + a <= (&37 / &50) * c - t` ASSUME_TAC THENL
     [OLTN_FACE_TAC `~linside c (--t) u v a (&37 / &50) (&1)`; ALL_TAC] THEN
    SUBGOAL_THEN `--t <= u` ASSUME_TAC THENL
     [OLTN_FACE_TAC `~linside c (--t) u v a (&0) (&1)`; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  (* middleUpperU *)
  SUBGOAL_THEN `u + a <= (&1 / &2) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&1 / &2) * t <= v` ASSUME_TAC THENL
     [OLTN_FACE_TAC `~linside c (--t) u v a (&1 / &2) (&0)`; ALL_TAC] THEN
    SUBGOAL_THEN `(&11 / &25) * c - t <= u` ASSUME_TAC THENL
     [OLTN_FACE_TAC `~linside c (--t) u v a (&11 / &25) (&1)`; ALL_TAC] THEN
    OLTN_SM_TAC OLTSM_THREETENTHS THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &7) * c < t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  (* leftLowerV *)
  SUBGOAL_THEN `--(&43 / &500) * t <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u < --(&43 / &500) * c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    OLTN_NEG_TAC `~linside c (--t) u v a (--(&43 / &500)) (&0)`; ALL_TAC] THEN
  (* cornerLowerU *)
  OLTN_SM_TAC OLTSM_SMALLSINE THEN
  SUBGOAL_THEN `--t <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c < v + a` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    OLTN_NEG_TAC `~linside c (--t) u v a (&0) (&1)`; ALL_TAC] THEN
  (* angleLarge *)
  SUBGOAL_THEN `(&2 / &3) * c < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OLTN_SM_TAC OLTSM_HALFBEFORETWOTHIRDS THEN RASM_ARITH_TAC; ALL_TAC] THEN
  (* topUpperV *)
  OLTN_SM_TAC OLTSM_SIXHUNDREDTHS THEN
  SUBGOAL_THEN `v + a <= c + (&11 / &25) * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u < (&11 / &25) * c - t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    OLTN_NEG_TAC `~linside c (--t) u v a (&11 / &25) (&1)`; ALL_TAC] THEN
  OLTN_SM_TAC OLTSM_TWENTYSEVENONEOHFOUR THEN
  OLTN_SM_TAC OLTSM_ONEOHFOURSEVENTEEN THEN
  OLTN_NEG_TAC `~linside c (--t) u v a (&27 / &100) (--(&1 / &25))`);;
