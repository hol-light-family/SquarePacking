(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralCrossMargin.lean (Jatloe).         *)
(* The two-angle support comparison for the missing-west entrance.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* Lean: F (definition) *)
let pccm_f = new_definition
 `pccm_f (p:real) q l r =
    &1 - &2 * r - (&457 / &500) * q * r / p + r / p + (p * l + q * r) +
    max (q * l - p * r) (&0)`;;

(* Lean: scaled_difference (private) *)
let PCCM_SCALED_DIFFERENCE = prove
 (`forall p q l r. c977cc_normal p q /\ c977cc_normal l r
     ==> p * l * (p + l) *
           (pccm_f p q l r - (&2 - &2 * r + r * (&1 - (&457 / &500) * r) / l)) =
         (p * r - l * q) * (r * (&457 / &500 - r) * (p + l) - l * (r - q) * (p - r)) +
         p * l * (p + l) * max (q * l - p * r) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[pccm_f] THEN
  SPEC_TAC(`max (q * l - p * r) (&0)`,`m:real`) THEN GEN_TAC THEN
  UNDISCH_TAC `&7 / &10 <= p` THEN UNDISCH_TAC `&7 / &10 <= l` THEN
  UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN
  CONV_TAC REAL_FIELD);;

(* Lean: diagonal_minimum *)
let PCCM_DIAGONAL_MINIMUM = prove
 (`forall p q l r. c977cc_normal p q /\ c977cc_normal l r
     ==> &2 - &2 * r + r * (&1 - (&457 / &500) * r) / l <= pccm_f p q l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`; `l:real`; `r:real`] PCCM_SCALED_DIFFERENCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `p * l * (p + l)` THEN
  CONJ_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[REWRITE_RULE[GSYM REAL_MUL_ASSOC] th]) THEN
  DISJ_CASES_TAC(REAL_ARITH `q <= r \/ r <= q`) THENL
  [MP_TAC(SPECL [`l:real`; `r:real`; `p:real`; `q:real`] C977CSB_COSINE_ORDER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= p * r - l * q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= p * (r - q) /\ &0 <= q * (p - l)` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `max (q * l - p * r) (&0) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `&0 <= p * (&5 / &7 - r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `&0 <= (l * (r - q)) * (&1 - p) /\ &0 <= (l * q) * (&1 - r) /\
     &0 <= r * (p * (&457 / &500 - r) - (&43 / &500) * l)` MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC;
   MP_TAC(SPECL [`p:real`; `q:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= q * l - p * r` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= l * (q - r) /\ &0 <= r * (l - p)` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `max (q * l - p * r) (&0) = q * l - p * r` SUBST1_TAC THENL
   [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `&0 <= (p + l) * (p * (l - q) + r * (p + q - &457 / &500)) /\
     &0 <= (p * (q - r)) * (p - r)` MP_TAC THENL
   [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN
    `&0 <= (q * l - p * r) *
           ((p + l) * (p * l - (&457 / &500) * r + r * r) -
            l * (q - r) * (p - r))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   REAL_ARITH_TAC]);;

(* Lean: margin *)
let PCCM_MARGIN = prove
 (`forall p q l r. c977cc_normal p q /\ c977cc_normal l r
     ==> &2 * l * (l + r - &1) <= r * pccm_f p q l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`; `l:real`; `r:real`] PCCM_DIAGONAL_MINIMUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN
   `l * (&1 + l) * (r * (&2 - &2 * r + r * (&1 - (&457 / &500) * r) / l) -
                    &2 * l * (l + r - &1)) =
    (&1 - l) * r pow 2 * (&1 - r) + (&43 / &500) * r pow 3 * (&1 + l)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `&7 / &10 <= l` THEN UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * l * (l + r - &1) <=
                r * (&2 - &2 * r + r * (&1 - (&457 / &500) * r) / l)` MP_TAC THENL
  [MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `l * (&1 + l)` THEN
   CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
   ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
   REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
   TRY(MATCH_MP_TAC REAL_POW_LE) THEN REWRITE_TAC[REAL_LE_POW_2] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r * (pccm_f p q l r -
                (&2 - &2 * r + r * (&1 - (&457 / &500) * r) / l))` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;
