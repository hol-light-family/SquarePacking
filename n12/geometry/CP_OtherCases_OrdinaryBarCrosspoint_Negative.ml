(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryBarCrosspoint/Negative.lean *)
(* (namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint).      *)
(* Input: obci_input; negative_segment: OBCI_NEGATIVE_SEGMENT; Scalars:     *)
(* OCOBCS_*; CanonicalScalars.bounds: CCCS_BOUNDS; OutwardScalars.          *)
(* increasing_projection: CCOS_INCREASING_PROJECTION.  The square has       *)
(* q.s = --t (hypothesis s = --t).                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryBarCrosspoint_Inputs.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryBarCrosspoint_Scalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;

let OBCN_NEG_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;;

let OBCN_FACE_TAC t =
  (REWRITE_TAC[GSYM REAL_NOT_LT] ORELSE REWRITE_TAC[GSYM REAL_NOT_LE]) THEN
  DISCH_TAC THEN OBCN_NEG_TAC t;;

let OBCN_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[obci_input] o
    check (fun th -> concl th = `obci_input c (--t) u v a`)) THEN
  SUBGOAL_THEN `~linside c (--t) u v a (&13 / &50) (--(&1)) /\
                ~linside c (--t) u v a (&22 / &25) (--(&1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o
      check (is_forall o concl)) THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`linside c (--t) u v a (&7 / &20) (--(&7 / &20))`;
                         `linside c (--t) u v a (&1) (--(&13 / &50))`;
                         `linside c (--t) u v a (&1) (--(&2 / &5))`] THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

(* Lean: negative_bands (private): linside c (--t) u v a x y unfolds by linside *)
let OBCN_NEGATIVE_BANDS = prove
 (`forall c s u v a t x y. s = --t
     ==> (linside c s u v a x y <=>
          u < c * x - t * y /\ c * x - t * y < u + a /\
          v < t * x + c * y /\ t * x + c * y < v + a)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[linside] THEN
  REAL_ARITH_TAC);;

(* Lean: negative_lower_impossible *)
let OBCN_NEGATIVE_LOWER_IMPOSSIBLE = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ &0 < a /\ obci_input c s u v a /\
                 s = --t /\ &0 < c /\ &0 <= t /\ t <= c /\ c / &2 <= u
     ==> false`,
  OBCN_SETUP_TAC THEN
  SUBGOAL_THEN `v + a <= (&543 / &500) * t` ASSUME_TAC THENL
   [OBCN_FACE_TAC `~linside c (--t) u v a (&543 / &500) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&543 / &500) * c + t` ASSUME_TAC THENL
   [OBCN_FACE_TAC `~linside c (--t) u v a (&543 / &500) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `c < &2 * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `t:real`] OCOBCS_BEFORE_HALF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `&19 / &50`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN `(&22 / &25) * t - c <= v` ASSUME_TAC THENL
   [OBCN_FACE_TAC `~linside c (--t) u v a (&22 / &25) (--(&1))`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] OCOBCS_AFTER_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_upper_impossible *)
let OBCN_NEGATIVE_UPPER_IMPOSSIBLE = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ &0 < a /\ obci_input c s u v a /\
                 s = --t /\ &0 < c /\ &0 <= t /\ t <= c /\ v + a <= t / &2
     ==> false`,
  OBCN_SETUP_TAC THEN
  SUBGOAL_THEN `u + a <= (&22 / &25) * c + t` ASSUME_TAC THENL
   [OBCN_FACE_TAC `~linside c (--t) u v a (&22 / &25) (--(&1))`; ALL_TAC] THEN
  SUBGOAL_THEN `(&13 / &50) * t - c <= v` ASSUME_TAC THENL
   [OBCN_FACE_TAC `~linside c (--t) u v a (&13 / &50) (--(&1))`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `t:real`]
    OBCI_NEGATIVE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] OCOBCS_LOWER_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= t * ((u + a) - (c + (&13 / &50) * t)) /\
                &0 <= c * (t / &2 - (v + a)) /\ &0 < c * (a - &1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&1 <= c + &1 / &2 * c * t + &13 / &50 * t pow 2` THEN
  REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN RASM_ARITH_TAC);;

(* Lean: negative *)
let OBCN_NEGATIVE = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ &0 < a /\ obci_input c s u v a /\
                 s = --t /\ &0 < c /\ &0 <= t /\ t <= c
     ==> linside c s u v a (&1 / &2) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `c / &2 <= u` THENL
   [MP_TAC(SPEC_ALL OBCN_NEGATIVE_LOWER_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= t / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&1 / &2) (&0)` THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[obci_input] o
      check (fun th -> concl th = `obci_input c s u v a`)) THEN
    MAP_EVERY UNDISCH_TAC [`linside c s u v a (&7 / &20) (--(&7 / &20))`;
                           `linside c s u v a (&1) (--(&13 / &50))`] THEN
    REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL OBCN_NEGATIVE_UPPER_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;
