(* ========================================================================= *)
(* Port of Compact/Geometry/C849ShallowMargins.lean                          *)
(* (namespace N12Compact.C849ShallowMargins).                                *)
(* Exact all-angle shallow-A/B margins.  Purely scalar statements.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: coordinate_bounds (private) *)
let C849SHM_COORDINATE_BOUNDS = prove
 (`forall p q. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 ==> p <= &1 /\ q <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  NLIN_TAC [SQ_NONNEG `p:real`; SQ_NONNEG `q:real`; SQ_NONNEG `p - &1`; SQ_NONNEG `q - &1`]);;

(* Lean: quartic (private) *)
let C849SHM_QUARTIC = prove
 (`forall t. &0 <= t /\ t <= &2 / &5
       ==> &0 < &1 / &50 - (&19 / &250) * t - (&16 / &25) * t pow 2 +
                (&819 / &250) * t pow 3 - (&99 / &50) * t pow 4`,
  GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= ((t - &1 / &5) + &1 / &5) * (&1 / &5 - (t - &1 / &5))`;
    `&0 <= &21260 + &42300 * (t - &1 / &5) - &49500 * (t - &1 / &5) pow 2`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t - &1 / &5`]
   [`&0 <= (t - &1 / &5) pow 2 *
           (&21260 + &42300 * (t - &1 / &5) - &49500 * (t - &1 / &5) pow 2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* 0 < e from 0 < e * d and 0 < d *)
let C849SHM_POS_CANCEL = prove
 (`forall e d. &0 < d /\ &0 < e * d ==> &0 < e`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&0`; `e:real`; `d:real`] REAL_LT_RMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO]);;

(* Lean: half_angle_margin (private) *)
let C849SHM_HALF_ANGLE_MARGIN = prove
 (`forall p q. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\ q <= (&4 / &5) * p
         ==> &0 < p + (&4 / &5) * q - (&49 / &50) * p pow 2 - (&419 / &500) * p * q -
                  (&13 / &20) * q pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] C849SHM_COORDINATE_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = q / (&1 + p)` THEN
  SUBGOAL_THEN `t * (&1 + p) = q` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN UNDISCH_TAC `&0 < &1 + p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t /\ t <= &2 / &5` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPEC `t:real` C849SHM_QUARTIC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p * (&1 + t pow 2) = &1 - t pow 2 /\ q * (&1 + t pow 2) = &2 * t`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `t * (&1 + p) = q` THEN
    UNDISCH_TAC `&0 < &1 + p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `(p + (&4 / &5) * q - (&49 / &50) * p pow 2 - (&419 / &500) * p * q -
     (&13 / &20) * q pow 2) * (&1 + t pow 2) pow 2 =
    &1 / &50 - (&19 / &250) * t - (&16 / &25) * t pow 2 +
    (&819 / &250) * t pow 3 - (&99 / &50) * t pow 4`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p * (&1 + t pow 2) = &1 - t pow 2` THEN
    UNDISCH_TAC `q * (&1 + t pow 2) = &2 * t` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC C849SHM_POS_CANCEL THEN EXISTS_TAC `(&1 + t pow 2) pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LT THEN NLIN_TAC [SQ_NONNEG `t:real`]);;

(* Lean: lowerV_b_neg *)
let C849SHM_LOWERV_B_NEG = prove
 (`forall p q c s. &0 < p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\
             &0 < c /\ &0 <= s /\ s <= (&4 / &5) * c /\ c * q - s * p <= &0
             ==> &0 < (c * p + s * q) * (&1 - (&7 / &10) * (p + q)) +
                      (c * q - s * p) * ((&7 / &20) * p - (&9 / &100) * q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= p * ((&4 / &5) * c - s)`] THEN
  SUBGOAL_THEN `q <= (&4 / &5) * p` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    NLIN_FACTS_TAC [] [`&0 < c * (q - (&4 / &5) * p)`] THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:real`; `q:real`] C849SHM_HALF_ANGLE_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `p - &7 / &10`; SQ_NONNEG `&7 * q - &6`]
   [`q <= p`; `&0 <= (p - q) * (p + q)`; `&7 / &10 <= p`;
    `&0 <= q * (p - &7 / &10)`;
    `q - (&7 / &20) * p pow 2 - (&61 / &100) * p * q - (&7 / &10) * q pow 2 <= &0`;
    `&0 < (p - (&7 / &10) * p pow 2 - (&7 / &20) * p * q - (&9 / &100) * q pow 2) +
          (&4 / &5) * (q - (&7 / &20) * p pow 2 - (&61 / &100) * p * q -
                       (&7 / &10) * q pow 2)`;
    `&0 < c * ((p - (&7 / &10) * p pow 2 - (&7 / &20) * p * q - (&9 / &100) * q pow 2) +
          (&4 / &5) * (q - (&7 / &20) * p pow 2 - (&61 / &100) * p * q -
                       (&7 / &10) * q pow 2))`;
    `&0 <= ((&4 / &5) * c - s) *
           --(q - (&7 / &20) * p pow 2 - (&61 / &100) * p * q - (&7 / &10) * q pow 2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lowerU_b_pos *)
let C849SHM_LOWERU_B_POS = prove
 (`forall p q c s. &0 <= p /\ &3 / &7 <= q /\ p pow 2 + q pow 2 = &1 /\
             &0 < c /\ s <= (&4 / &5) * c
             ==> &0 < (c * p + s * q) + (c * q - s * p) +
                      (&7 / &10) * (c * q - s * p) * (p - q) +
                      (c * p + s * q) * ((&1 / &20) * p - (&27 / &20) * q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] C849SHM_COORDINATE_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&13 * q - &10`]
   [`&0 <= p * (&1 - q)`;
    `q - p - (&7 / &10) * p pow 2 + (&3 / &4) * p * q - (&27 / &20) * q pow 2 <= &0`;
    `&0 <= (q - &53 / &127) * (&1 - q)`; `&0 <= p * (&1 / &5 - q / &20)`;
    `&0 < (p + q + (&1 / &20) * p pow 2 - (&13 / &20) * p * q - (&7 / &10) * q pow 2) +
          (&4 / &5) * (q - p - (&7 / &10) * p pow 2 + (&3 / &4) * p * q -
                       (&27 / &20) * q pow 2)`;
    `&0 < c * ((p + q + (&1 / &20) * p pow 2 - (&13 / &20) * p * q - (&7 / &10) * q pow 2) +
          (&4 / &5) * (q - p - (&7 / &10) * p pow 2 + (&3 / &4) * p * q -
                       (&27 / &20) * q pow 2))`;
    `&0 <= ((&4 / &5) * c - s) *
        --(q - p - (&7 / &10) * p pow 2 + (&3 / &4) * p * q - (&27 / &20) * q pow 2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lowerU_a_pos *)
let C849SHM_LOWERU_A_POS = prove
 (`forall p q c s. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\
             &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
             &3 * c <= &7 * s /\ s <= (&4 / &5) * c
             ==> &0 < &1 + (&1 / &20) * p - (&27 / &20) * q +
                      (c * q - s * p) * ((&7 / &20) * c + (&92 / &125) * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &23 / &25`; SQ_NONNEG `c - s`;
                  SQ_NONNEG `(&22 / &25) * p - (&21 / &50) * q`;
                  SQ_NONNEG `(&21 / &50) * p + (&22 / &25) * q - &1`]
   [`&0 <= (&7 * s - &3 * c) * (&7 * s + &3 * c)`;
    `&0 <= ((&4 / &5) * c - s) * ((&4 / &5) * c + s)`;
    `c <= &23 / &25`; `&3 / &5 <= c pow 2`; `s pow 2 <= &2 / &5`;
    `c - s <= &92 / &175`; `s <= c`;
    `&0 <= (&92 / &175 - (c - s)) * (&92 / &175 + (c - s))`;
    `&9 / &25 <= c * s`; `c * s <= &1 / &2`;
    `s * ((&7 / &20) * c + (&92 / &125) * s) - &1 / &20 <= &21 / &50`;
    `&27 / &20 - c * ((&7 / &20) * c + (&92 / &125) * s) <= &22 / &25`;
    `p * (s * ((&7 / &20) * c + (&92 / &125) * s) - &1 / &20) <= p * (&21 / &50)`;
    `q * (&27 / &20 - c * ((&7 / &20) * c + (&92 / &125) * s)) <= q * (&22 / &25)`;
    `(&21 / &50) * p + (&22 / &25) * q < &1`] THEN
  NLIN_TAC ~deg2:false []);;
