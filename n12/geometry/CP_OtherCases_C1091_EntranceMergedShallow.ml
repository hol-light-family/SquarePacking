(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/EntranceMergedShallow.lean    *)
(* (namespace N12Compact.Completion.OtherCases.C1091.EntranceMergedShallow).*)
(* Normal: c977cc_normal; normal_bounds: C977CC_NORMAL_BOUNDS;              *)
(* canonical_frame: CLF_CANONICAL_FRAME; inside_translated_iff:             *)
(* C1091MMS_TRANSLATED.  OpenSquare invariants are explicit hypotheses.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1091_MergedMarkerSeed.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: Input (structure) *)
let c1091ems_input = new_definition
 `c1091ems_input c s u v a <=>
    &1 < a /\
    linside c s u v a (--(&43 / &500)) (&0) /\
    linside c s u v a (&13 / &20) (&13 / &20) /\
    ~linside c s u v a (&0) (&0) /\
    ~linside c s u v a (--(&43 / &500)) (&1)`;;

(* Lean: Input.reframe *)
let C1091EMS_INPUT_REFRAME = prove
 (`forall c s u v a c' s' u' v' a'.
     c1091ems_input c s u v a /\ a' = a /\
     (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)
     ==> c1091ems_input c' s' u' v' a'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1091ems_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let C1091EMS_UNFOLD_TAC =
  REWRITE_TAC[c1091ems_input] THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`linside c s u v a (--(&43 / &500)) (&0)`;
                         `linside c s u v a (&13 / &20) (&13 / &20)`] THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

let C1091EMS_NEG_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;;

(* Lean: nonpositive_impossible (private) *)
let C1091EMS_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091ems_input c s u v a /\
               &0 < c /\ s <= &0 /\ --s <= c
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `c1091ems_input c s u v a` THEN C1091EMS_UNFOLD_TAC THEN
  C1091EMS_NEG_TAC `~linside c s u v a (&0) (&0)`);;

(* Lean: profile *)
let C1091EMS_PROFILE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091ems_input c s u v a /\
               c977cc_normal c s
     ==> &0 <= v /\ &0 < s /\ &5 * s < c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  UNDISCH_TAC `c1091ems_input c s u v a` THEN C1091EMS_UNFOLD_TAC THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1091EMS_NEG_TAC `~linside c s u v a (&0) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c + (&43 / &500) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1091EMS_NEG_TAC `~linside c s u v a (--(&43 / &500)) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c + (&43 / &500) * s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c + (&43 / &500) * s - &1) * (c + (&43 / &500) * s + &1)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s * ((&43 / &250) * c - (&1 - (&43 / &500) pow 2) * s)` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < (c + (&43 / &500) * s - &1) * (c + (&43 / &500) * s + &1)` THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (&43 / &250) * c - (&1 - (&43 / &500) pow 2) * s` MP_TAC THENL
   [NLIN_TAC []; CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN RASM_ARITH_TAC]);;

(* Lean: positive_points *)
let C1091EMS_POSITIVE_POINTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091ems_input c s u v a /\
               c977cc_normal c s
     ==> linside c s u v a (&23 / &50) (&99 / &100) /\
         linside c s u v a (&1 / &2) (&1) /\
         linside c s u v a (&29 / &50) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1091EMS_PROFILE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  UNDISCH_TAC `c1091ems_input c s u v a` THEN C1091EMS_UNFOLD_TAC THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: points *)
let C1091EMS_POINTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091ems_input c s u v a
     ==> linside c s u v a (&23 / &50) (&99 / &100) /\
         linside c s u v a (&1 / &2) (&1) /\
         linside c s u v a (&29 / &50) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] C1091EMS_INPUT_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC C1091EMS_POSITIVE_POINTS THEN ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`]
      C1091EMS_NONPOSITIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: original_points *)
let C1091EMS_ORIGINAL_POINTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&457 / &500) (&1) /\ linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&1) (&1) /\ ~linside c s u v a (&457 / &500) (&2)
     ==> linside c s u v a (&73 / &50) (&199 / &100) /\
         linside c s u v a (&3 / &2) (&2) /\
         linside c s u v a (&79 / &50) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &1 + s * &1)`; `v - (--s * &1 + c * &1)`;
                `a:real`] C1091EMS_POINTS) THEN
  ASM_REWRITE_TAC[c1091ems_input; C1091MMS_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;
