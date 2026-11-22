(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveProfile.lean           *)
(* (N12Compact.C1092MPPMInwardPositive).  POSITIVE-MISSING-INWARD-SUCCESSOR *)
(* section 1.  C = c s u v a; Input is c1092ipp_input, Profile is            *)
(* c1092ipp_profile (fields in Lean order); Normal: c977cc_normal; half:     *)
(* C1092WPS_half (quarter_data C1092WPS_QUARTER_DATA, half_identity          *)
(* C1092IFBS_HALF_IDENTITY); normal_sum: C1092MANS_NORMAL_SUM.               *)
(* Tag C1092IPP_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinaryScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomData.ml";;

(* Lean: Input (structure) *)
let c1092ipp_input = new_definition
 `c1092ipp_input (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    &1 < a /\ c977cc_normal c s /\
    linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
    linside c s u v a (&0) (--(&13 / &50)) /\
    linside c s u v a (--(&13 / &50)) (&0) /\
    linside c s u v a (--(&1 / &2)) (&0) /\
    linside c s u v a (--(&1 / &100)) (--(&27 / &50)) /\
    ~linside c s u v a (&0) (&0) /\
    ~linside c s u v a (--(&1)) (--(&2 / &5)) /\
    ~linside c s u v a (--(&2 / &5)) (--(&1)) /\
    ~linside c s u v a (--(&7 / &20)) (&7 / &20)`;;

(* Lean: Profile (structure) *)
let c1092ipp_profile = new_definition
 `c1092ipp_profile (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    &0 < s /\ --c - (&2 / &5) * s <= u /\ u + a <= &0 /\
    (&2 / &5) * s - c <= v /\ v + a <= (&7 / &20) * (c + s) /\
    linside c s u v a (&0) (--(&1 / &2)) /\ C1092WPS_half c s < &2 / &5 /\ s < c`;;

(* Lean: short_projections *)
let C1092IPP_SHORT_PROJECTIONS = prove
 (`forall c s. c977cc_normal c s ==> (&2 / &5) * c + s < &1 /\ (&13 / &20) * c + (&3 / &4) * s < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (c - s) * (&41 * c + s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [NLIN_TAC [SQ_NONNEG `(&2 / &5) * c + s - &1`];
    NLIN_TAC [SQ_NONNEG `(&3 / &4) * c - (&13 / &20) * s`;
              SQ_NONNEG `(&13 / &20) * c + (&3 / &4) * s - &1`]]);;

(* Lean: half_of_width *)
let C1092IPP_HALF_OF_WIDTH = prove
 (`forall c s alpha. c977cc_normal c s /\ &1 < c + alpha * s ==> C1092WPS_half c s < alpha`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFBS_HALF_IDENTITY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= s * (C1092WPS_half c s - alpha)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN
    UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: sine_le_twice_half *)
let C1092IPP_SINE_LE_TWICE_HALF = prove
 (`forall c s. c977cc_normal c s ==> s <= &2 * C1092WPS_half c s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 <= s * C1092WPS_half c s pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: profile *)
let C1092IPP_PROFILE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1092ipp_input c s u v a
     ==> c1092ipp_profile c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input]) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IPP_SHORT_PROJECTIONS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MANS_NORMAL_SUM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092PRS_NORMAL_TAC THEN
  C1092IFBD_PT_TAC [`linside c s u v a (--(&7 / &20)) (--(&7 / &20))`;
                    `linside c s u v a (&0) (--(&13 / &50))`;
                    `linside c s u v a (--(&13 / &50)) (&0)`;
                    `linside c s u v a (--(&1 / &2)) (&0)`;
                    `linside c s u v a (--(&1 / &100)) (--(&27 / &50))`] THEN
  let miss t = UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC in
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~linside c (&0) u v a (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; REAL_ADD_LID;
                                REAL_NEG_0]) THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; REAL_NEG_0] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN miss `~linside c s u v a (&0) (&0)`;
    ALL_TAC] THEN
  SUBGOAL_THEN `linside c s u v a (&0) (--(&1 / &2))` ASSUME_TAC THENL
   [REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 / &5) * s - c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    miss `~linside c s u v a (--(&2 / &5)) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `--c - (&2 / &5) * s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    miss `~linside c s u v a (--(&1)) (--(&2 / &5))`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&7 / &20) * (c + s)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    miss `~linside c s u v a (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c + (&2 / &5) * s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092ipp_profile] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C1092IPP_HALF_OF_WIDTH THEN ASM_REWRITE_TAC[]; RASM_ARITH_TAC]);;
