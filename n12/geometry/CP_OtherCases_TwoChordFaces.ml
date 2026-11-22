(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/TwoChordFaces.lean                  *)
(* (namespace N12Compact.Completion.OtherCases.TwoChordFaces).  Two strict  *)
(* vertical markers and four omitted chord endpoints force four faces.      *)
(* CanonicalScalars.bounds: CCCS_BOUNDS; CanonicalProjection.before:        *)
(* CCCP_BEFORE.  A square q is c s u v a.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCTCF_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: Faces (structure) *)
let octcf_faces = new_definition
 `octcf_faces (c:real) s u v a <=>
    --(&13 / &50) * s <= u /\
    --(&13 / &50) * c - s <= v /\
    u + a <= c + &13 / &50 * s /\
    v + a <= &13 / &50 * c /\
    &0 < s /\
    &1 < &13 / &25 * c + s /\
    &228 / &397 * c < &325 / &397 * s`;;

(* Lean: positive *)
let OCTCF_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      linside c s u v a (&7 / &20) (&7 / &20) /\
      ~linside c s u v a (&0) (--(&13 / &50)) /\
      ~linside c s u v a (&0) (&13 / &50) /\
      ~linside c s u v a (&1) (--(&13 / &50)) /\
      ~linside c s u v a (&1) (&13 / &50)
      ==> octcf_faces c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  let mF = `~linside c s u v a (&0) (--(&13 / &50))`
  and mH = `~linside c s u v a (&0) (&13 / &50)`
  and mJ = `~linside c s u v a (&1) (--(&13 / &50))`
  and mG = `~linside c s u v a (&1) (&13 / &50)` in
  let step t keep =
    SUBGOAL_THEN t ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCTCF_KEEP_TAC keep;
      ALL_TAC] in
  step `s * --(&13 / &50) <= u` [mF] THEN
  step `--s + c * --(&13 / &50) <= v` [mJ] THEN
  SUBGOAL_THEN `v + a <= c * &13 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s * &13 / &50 <= u` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCTCF_KEEP_TAC [mH];
      ALL_TAC] THEN
    SUBGOAL_THEN `--s + c * &13 / &50 <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCTCF_KEEP_TAC [mG];
      ALL_TAC] THEN
    OCTCF_KEEP_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c + s * &13 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCTCF_KEEP_TAC [mG];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < &13 / &25 * c + s` ASSUME_TAC THENL
   [OCTCF_KEEP_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&228 / &397 * c < &325 / &397 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `&325 / &397`; `&228 / &397`;
                  `&13 / &25`; `&1`] CCCP_BEFORE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN
      OCTCF_KEEP_TAC []];
    ALL_TAC] THEN
  REWRITE_TAC[octcf_faces] THEN OCTCF_KEEP_TAC []);;
