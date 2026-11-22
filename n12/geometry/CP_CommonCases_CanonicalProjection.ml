(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/CanonicalProjection.lean           *)
(* (N12Compact.CommonCases.CanonicalProjection).  Projection monotonicity on *)
(* the unit circle from two orthogonal dot products.  Scalar.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: dot_bound (private) *)
let CCCP_DOT_BOUND = prove
 (`forall c s c0 s0. c pow 2 + s pow 2 = &1 /\ c0 pow 2 + s0 pow 2 = &1
               ==> c0 * c + s0 * s <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c0 * c + s0 * s) * (c0 * c + s0 * s) +
                (c0 * s - s0 * c) * (c0 * s - s0 * c) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `c0 pow 2 + s0 pow 2 = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  NLIN_TAC [SQ_NONNEG `c0 * s - s0 * c`; SQ_NONNEG `c0 * c + s0 * s - &1`]);;

let CCCP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `c0:real`; `s0:real`] CCCP_DOT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a * c + b * s =
      (a * c0 + b * s0) * (c0 * c + s0 * s) + (b * c0 - a * s0) * (c0 * s - s0 * c)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c0 pow 2 + s0 pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`(b * c0 - a * s0) * (c0 * s - s0 * c) <= &0`;
    `(a * c0 + b * s0) * (c0 * c + s0 * s) <= (a * c0 + b * s0) * &1`] THEN
  NLIN_TAC ~deg2:false [];;

(* Lean: before *)
let CCCP_BEFORE = prove
 (`forall c s c0 s0 a b.
      c pow 2 + s pow 2 = &1 /\ c0 pow 2 + s0 pow 2 = &1 /\ c0 * s <= s0 * c /\
      a * s0 <= b * c0 /\ &0 <= a * c0 + b * s0
      ==> a * c + b * s <= a * c0 + b * s0`,
  CCCP_TAC);;

(* Lean: after *)
let CCCP_AFTER = prove
 (`forall c s c0 s0 a b.
      c pow 2 + s pow 2 = &1 /\ c0 pow 2 + s0 pow 2 = &1 /\ s0 * c <= c0 * s /\
      b * c0 <= a * s0 /\ &0 <= a * c0 + b * s0
      ==> a * c + b * s <= a * c0 + b * s0`,
  CCCP_TAC);;
