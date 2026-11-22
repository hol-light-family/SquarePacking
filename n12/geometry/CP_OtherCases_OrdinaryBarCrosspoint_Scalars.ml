(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryBarCrosspoint/Scalars.lean  *)
(* (N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Scalars).         *)
(* The two arctan(1/2) projection comparisons and the lower-vertex bound.   *)
(* CanonicalScalars.bounds: CCCS_BOUNDS.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: before_half *)
let OCOBCS_BEFORE_HALF = prove
 (`forall c t. &0 < c /\ &0 <= t /\ c pow 2 + t pow 2 = &1 /\ &2 * t <= c
         ==> &293 / &500 * c + t < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - &2 * t) * (&750151 / &250000 * c + &17651 / &125000 * t)`] THEN
  NLIN_TAC [SQ_NONNEG `&293 / &500 * c + t - &1`]);;

(* Lean: after_half *)
let OCOBCS_AFTER_HALF = prove
 (`forall c t. &0 < c /\ &0 <= t /\ c pow 2 + t pow 2 = &1 /\ c <= &2 * t
         ==> c + &103 / &500 * t < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&2 * t - c) * (&33391 / &250000 * c + &290891 / &125000 * t)`] THEN
  NLIN_TAC [SQ_NONNEG `c + &103 / &500 * t - &1`]);;

(* Lean: lower_vertex *)
let OCOBCS_LOWER_VERTEX = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1
         ==> &1 <= c + &1 / &2 * c * t + &13 / &50 * t pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  NLIN_FACTS_TAC []
   [`&0 <= t * (c - t)`; `&0 <= (&1 - c) * (&19 / &25 * c - &6 / &25)`] THEN
  NLIN_TAC ~deg2:false []);;
