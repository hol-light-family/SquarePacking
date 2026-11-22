(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InnerCornerObstruction/Scalars.lean *)
(* (namespace N12Compact.Completion.OtherCases.InnerCornerObstruction.      *)
(* Scalars).  CanonicalQuadratic.before_one / after_one: CCCQ_BEFORE_ONE /  *)
(* CCCQ_AFTER_ONE.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalQuadratic.ml";;

let OCICS_TAC th a b n m =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; a; b; n; m] th) THEN
  REWRITE_TAC[cccq_firstCoeff; cccq_secondCoeff] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;;

(* Lean: before_sixth *)
let OCICS_BEFORE_SIXTH = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &6 * s <= c
         ==> (&413 / &500) * c + s < &1`,
  OCICS_TAC CCCQ_BEFORE_ONE `&413 / &500` `&1` `&6` `&1`);;

(* Lean: after_four_ninth *)
let OCICS_AFTER_FOUR_NINTH = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &4 * c <= &9 * s
         ==> c + (&103 / &500) * s < &1`,
  OCICS_TAC CCCQ_AFTER_ONE `&1` `&103 / &500` `&9` `&4`);;

(* Lean: upper_v *)
let OCICS_UPPER_V = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ c <= &6 * s
         ==> (&26 / &25) * c - (&19 / &50) * s < &1`,
  OCICS_TAC CCCQ_AFTER_ONE `&26 / &25` `--(&19 / &50)` `&6` `&1`);;

(* Lean: upper_u *)
let OCICS_UPPER_U = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &9 * s <= &4 * c
         ==> (&313 / &500) * c + (&26 / &25) * s < &1`,
  OCICS_TAC CCCQ_BEFORE_ONE `&313 / &500` `&26 / &25` `&9` `&4`);;
