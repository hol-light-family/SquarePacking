(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryBarCrosspoint/Positive.lean *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint).      *)
(* Input: obci_input; positive_segment: OBCI_POSITIVE_SEGMENT;              *)
(* CanonicalScalars.bounds: CCCS_BOUNDS; OutwardScalars.increasing_         *)
(* projection: CCOS_INCREASING_PROJECTION.                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryBarCrosspoint_Inputs.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;

let OBCP_NEG_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;;

(* Lean: positive *)
let OBCP_POSITIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ obci_input c s u v a /\
               &0 < c /\ &0 <= s /\ s <= c
     ==> linside c s u v a (&1 / &2) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&103 / &500`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(SPEC_ALL OBCI_POSITIVE_SEGMENT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `obci_input c s u v a` THEN REWRITE_TAC[obci_input] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside c s u v a (&13 / &50) (--(&1)) /\
                ~linside c s u v a (&22 / &25) (--(&1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
      check (is_forall o concl)) THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`linside c s u v a (&7 / &20) (--(&7 / &20))`;
                         `linside c s u v a (&1) (--(&13 / &50))`] THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v + a <= --(&1 / &2) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OBCP_NEG_TAC `~linside c s u v a (&1 / &2) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&543 / &500) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v + a <= --(&543 / &500) * s` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      OBCP_NEG_TAC `~linside c s u v a (&543 / &500) (&0)`; ALL_TAC] THEN
    SUBGOAL_THEN `(&22 / &25) * c - s <= u` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      OBCP_NEG_TAC `~linside c s u v a (&22 / &25) (--(&1))`; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&13 / &50) * c - s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OBCP_NEG_TAC `~linside c s u v a (&13 / &50) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&22 / &25) * s - c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OBCP_NEG_TAC `~linside c s u v a (&22 / &25) (--(&1))`; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    can (find_term ((=) `s * u + c * v`)) (concl th))) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= s * ((&543 / &500) * c - (u + a)) /\
                &0 <= c * (--(&1 / &2) * s - (v + a)) /\
                &0 < (a - &1) * (c + s) /\ &0 <= c * s` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  RASM_ARITH_TAC);;
