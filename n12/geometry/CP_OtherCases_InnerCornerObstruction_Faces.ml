(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InnerCornerObstruction/Faces.lean   *)
(* (namespace N12Compact.Completion.OtherCases.InnerCornerObstruction).     *)
(* Common literal input and forced faces of the inner-corner obstruction.   *)
(* CanonicalScalars.bounds: CCCS_BOUNDS;                                    *)
(* OutwardScalars.increasing_projection: CCOS_INCREASING_PROJECTION.        *)
(* A square q is c s u v a with c * c + s * s = &1 and &0 < a.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryBarCrosspoint_Scalars.ml";;

(* linear arithmetic; of the negated linside assumptions only those in keep *)
let OCICOF_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: Input (structure) *)
let ocico_input = new_definition
 `ocico_input (c:real) s u v a <=>
    &1 < a /\
    linside c s u v a (&0) (&0) /\
    linside c s u v a (&13 / &20) (&13 / &20) /\
    ~linside c s u v a (--(&43 / &500)) (&0) /\
    ~linside c s u v a (&3 / &25) (&0) /\
    ~linside c s u v a (--(&43 / &500)) (&1)`;;

(* Lean: Input.reframe *)
let OCICOF_INPUT_REFRAME = prove
 (`forall c s u v a c' s' u' v' a'.
      ocico_input c s u v a /\ a' = a /\
      (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)
      ==> ocico_input c' s' u' v' a'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `ocico_input c s u v a` THEN ASM_REWRITE_TAC[ocico_input]);;

(* Lean: positive_faces *)
let OCICOF_POSITIVE_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ ocico_input c s u v a /\
      &0 < c /\ &0 <= s /\ s <= c
      ==> --(&43 / &500) * c <= u /\ --(&3 / &25) * s <= v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocico_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--(&3 / &25) * s <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCICOF_KEEP_TAC [`~linside c s u v a (&3 / &25) (&0)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  OCICOF_KEEP_TAC [`~linside c s u v a (--(&43 / &500)) (&0)`]);;

(* Lean: negative_impossible *)
let OCICOF_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a t.
      c * c + s * s = &1 /\ &0 < a /\ ocico_input c s u v a /\
      s = --t /\ &0 < c /\ &0 <= t /\ t <= c
      ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocico_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `u + a <= &3 / &25 * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCICOF_KEEP_TAC [`~linside c (--t) u v a (&3 / &25) (&0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&53 / &100 * c < &13 / &20 * t` ASSUME_TAC THENL
   [OCICOF_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `--(&43 / &500) * c - t <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCICOF_KEEP_TAC [`~linside c (--t) u v a (--(&43 / &500)) (&1)`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `&103 / &500`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  OCICOF_KEEP_TAC []);;
