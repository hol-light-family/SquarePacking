(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveCrosspointAngleDichotomy.lean*)
(* (N12Compact.C1092MPPMPositiveCrosspointAngleDichotomy), Theorem 1.       *)
(* The square C is c s u v a; Normal is c977cc_normal; CrosspointSeeds:      *)
(* C1092PCS_* / c1092pcs_*; half / quarter_data: C1092WPS_*.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveCrosspointSeeds.ml";;

(* Lean: Shallow (structure) *)
let c1092pad_shallow = new_definition
 `c1092pad_shallow c s u v a <=>
    u + a <= --s / &2 /\ &25 * s < &13 * c /\ s / c < &13 / &25 /\
    C1092WPS_half c s < &1 / &4 /\ ~linside c s u v a (&0) (--(&13 / &50)) /\
    linside c s u v a (--(&1)) (--(&1 / &2))`;;

(* Lean: Steep (structure) *)
let c1092pad_steep = new_definition
 `c1092pad_steep c s (u:real) v (a:real) <=>
    --c / &2 <= v /\ &1 / &3 < C1092WPS_half c s /\ &1 + c < &3 * s`;;

let C1092PAD_HALF_TAC =
  C1092PCS_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c s`,`q:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN DISCH_TAC;;

(* Lean: quarter_lt_of_slope (private) *)
let C1092PAD_QUARTER_LT_OF_SLOPE = prove
 (`forall c s. c977cc_normal c s /\ &25 * s < &13 * c ==> C1092WPS_half c s < &1 / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PAD_HALF_TAC THEN
  SUBGOAL_THEN `(&1 + q pow 2) * (&8 * c - &15 * s) = -- &2 * (&4 * q - &1) * (q + &4)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + q pow 2) * c = &1 - q pow 2` THEN
   UNDISCH_TAC `(&1 + q pow 2) * s = &2 * q` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + q pow 2) * (&8 * c - &15 * s)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&4 * q - &1) * (q + &4)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  C1092PCS_LIN_TAC);;

(* Lean: third_lt_of_width (private) *)
let C1092PAD_THIRD_LT_OF_WIDTH = prove
 (`forall c s. c977cc_normal c s /\ &1 < s + c / &2 ==> &1 / &3 < C1092WPS_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `C1092WPS_half c s < &1` MP_TAC THENL
  [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
     check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
   REWRITE_TAC[C1092WPS_half] THEN
   SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092PAD_HALF_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + q pow 2) * (s + c / &2 - &1) = (&1 - q) * (&3 * q - &1) / &2`
  ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + q pow 2) * c = &1 - q pow 2` THEN
   UNDISCH_TAC `(&1 + q pow 2) * s = &2 * q` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + q pow 2) * (s + c / &2 - &1)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - q) * (&1 - &3 * q)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN C1092PCS_LP_TAC; ALL_TAC] THEN
  C1092PCS_LIN_TAC);;

(* Lean: classify *)
let C1092PAD_CLASSIFY = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
               &0 < s /\ c1092pcs_forwardCore c s u v a /\
               ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
               ~linside c s u v a (&0) (--(&1 / &2))
               ==> c1092pad_shallow c s u v a \/ c1092pad_steep c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `u + a <= --s / &2` THENL
  [DISJ1_TAC THEN
   SUBGOAL_THEN `&25 * s < &13 * c` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092pcs_forwardCore c s u v a` THEN
    REWRITE_TAC[c1092pcs_forwardCore; linside] THEN STRIP_TAC THEN C1092PCS_LP_TAC;
    ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`] C1092PAD_QUARTER_LT_OF_SLOPE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
     C1092PCS_HALFPOINT_OF_NEXT_CROSSPOINT) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
   ASM_REWRITE_TAC[c1092pad_shallow] THEN
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
   DISJ2_TAC THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
     C1092PCS_FORWARD_PROFILE) THEN
   ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN
   SUBGOAL_THEN `--c / &2 <= v` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092pcs_forwardCore c s u v a` THEN
    REWRITE_TAC[c1092pcs_forwardCore] THEN STRIP_TAC THEN C1092PCS_SETUP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092PCS_MISS_TAC `&0` `--(&1 / &2)`; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`] C1092PAD_THIRD_LT_OF_WIDTH) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   ASM_REWRITE_TAC[c1092pad_steep] THEN
   UNDISCH_TAC `&1 / &3 < C1092WPS_half c s` THEN REWRITE_TAC[C1092WPS_half] THEN
   SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC]);;

(* Lean: exclusive *)
let C1092PAD_EXCLUSIVE = prove
 (`forall c s u v a. ~(c1092pad_shallow c s u v a /\ c1092pad_steep c s u v a)`,
  REWRITE_TAC[c1092pad_shallow; c1092pad_steep] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;

(* Lean: exactly_one *)
let C1092PAD_EXACTLY_ONE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
               &0 < s /\ c1092pcs_forwardCore c s u v a /\
               ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
               ~linside c s u v a (&0) (--(&1 / &2))
               ==> (c1092pad_shallow c s u v a \/ c1092pad_steep c s u v a) /\
                   ~(c1092pad_shallow c s u v a /\ c1092pad_steep c s u v a)`,
  MESON_TAC[C1092PAD_CLASSIFY; C1092PAD_EXCLUSIVE]);;
