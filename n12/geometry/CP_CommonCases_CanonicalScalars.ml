(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/CanonicalScalars.lean              *)
(* (N12Compact.CommonCases.CanonicalScalars).  Purely scalar.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: bounds *)
let CCCS_BOUNDS = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1
         ==> &7 / &10 < c /\ c <= &1 /\ &1 <= c + t /\ c + t <= &10 / &7 /\
             &1 + &4 / &5 * c * t <= c + t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`; SQ_NONNEG `c - t:real`]
   [`&0 <= c * t`; `&0 <= (c - t) * (c + t)`; `&7 / &10 < c`; `c <= &1`;
    `&1 <= c + t`; `c + t <= &10 / &7`;
    `&0 <= (&3 / &2 - (c + t)) * (c + t - &1)`] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: c_small_sine *)
let CCCS_C_SMALL_SINE = prove
 (`forall c t. &0 < c /\ &0 <= t /\ c pow 2 + t pow 2 = &1 /\ c <= &5 * t
         ==> c + &43 / &500 * t < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 < t`; `&0 < &248151 / &250000 * t - &43 / &250 * c`;
    `&0 < t * (&248151 / &250000 * t - &43 / &250 * c)`] THEN
  NLIN_TAC []);;

(* Lean: positive_margin *)
let CCCS_POSITIVE_MARGIN = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1
         ==> &244959 / &250000 - &3 / &10 * t pow 2 + &463 / &500 * c * t <
             &613 / &500 * c + &313 / &500 * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - t) * (&2 - (c + t))`;
    `&0 <= (&3 / &7 - ((c + t) - &1)) * (&3 / &7 + ((c + t) - &1))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_margin *)
let CCCS_NEGATIVE_MARGIN = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1
         ==> &3001 / &5000 + &94909 / &250000 * t pow 2 + &4501 / &5000 * c * t <
             &313 / &500 * c + &613 / &500 * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  NLIN_FACTS_TAC []
   [`&0 <= &3 / &5 - &1997 / &5000 * c - &94909 / &250000 * t`;
    `&0 <= t * (&3 / &5 - &1997 / &5000 * c - &94909 / &250000 * t)`] THEN
  NLIN_TAC ~deg2:false []);;
