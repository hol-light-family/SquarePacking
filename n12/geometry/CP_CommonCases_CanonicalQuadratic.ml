(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/CanonicalQuadratic.lean            *)
(* (N12Compact.CommonCases.CanonicalQuadratic).  Rational endpoint           *)
(* comparisons on the unit circle without square roots.  Scalar.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: firstCoeff *)
let cccq_firstCoeff = new_definition
 `cccq_firstCoeff (a:real) (b:real) (n:real) (m:real) =
    &2 * n * a * b + m * (b pow 2 - a pow 2)`;;

(* Lean: secondCoeff *)
let cccq_secondCoeff = new_definition
 `cccq_secondCoeff (a:real) (b:real) (n:real) (m:real) =
    n * (b pow 2 - a pow 2) - &2 * m * a * b`;;

(* Lean: factor_identity (private) *)
let CCCQ_FACTOR_IDENTITY = prove
 (`forall c s a b n m. c pow 2 + s pow 2 = &1
     ==> (n * a + m * b) pow 2 - (n pow 2 + m pow 2) * (a * c + b * s) pow 2 =
         (m * c - n * s) * (cccq_firstCoeff a b n m * c + cccq_secondCoeff a b n m * s)`,
  REWRITE_TAC[cccq_firstCoeff; cccq_secondCoeff] THEN REPEAT GEN_TAC THEN
  CONV_TAC REAL_RING);;

(* Lean: strict_projection (private) *)
let CCCQ_STRICT_PROJECTION = prove
 (`forall L N K. &0 < N /\ K < N /\ N * L pow 2 <= K ==> L < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&1 <= L * L`; `&0 <= N * (L * L - &1)`] THEN
  NLIN_TAC ~deg2:false []);;

let CCCQ_TAC sgn =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CCCQ_STRICT_PROJECTION THEN
  MAP_EVERY EXISTS_TAC [`n pow 2 + m pow 2`; `(n * a + m * b) pow 2`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `a:real`; `b:real`; `n:real`; `m:real`]
    CCCQ_FACTOR_IDENTITY) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC [`F1 = cccq_firstCoeff a b n m`; `F2 = cccq_secondCoeff a b n m`;
    `P = (n * a + m * b) pow 2`; `Q = n pow 2 + m pow 2`; `R = (a * c + b * s) pow 2`] THEN
  DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [if sgn then `&0 <= F1 * c + F2 * s` else `F1 * c + F2 * s <= &0`;
    `&0 <= (m * c - n * s) * (F1 * c + F2 * s)`] THEN
  NLIN_TAC ~deg2:false [];;

(* Lean: before_one *)
let CCCQ_BEFORE_ONE = prove
 (`forall c s a b n m.
      &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &0 < n pow 2 + m pow 2 /\
      (n * a + m * b) pow 2 < n pow 2 + m pow 2 /\ n * s <= m * c /\
      &0 <= cccq_firstCoeff a b n m /\ &0 <= cccq_secondCoeff a b n m
      ==> a * c + b * s < &1`,
  CCCQ_TAC true);;

(* Lean: after_one *)
let CCCQ_AFTER_ONE = prove
 (`forall c s a b n m.
      &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &0 < n pow 2 + m pow 2 /\
      (n * a + m * b) pow 2 < n pow 2 + m pow 2 /\ m * c <= n * s /\
      cccq_firstCoeff a b n m <= &0 /\ cccq_secondCoeff a b n m <= &0
      ==> a * c + b * s < &1`,
  CCCQ_TAC false);;
