(* ========================================================================= *)
(* Port of Compact/Geometry/C849SteepMargins.lean                            *)
(* (namespace N12Compact.C849SteepMargins).                                  *)
(* Uniform scalar margins for A/B in the transverse upper-left-marker sector *)
(* of 849/851.  Purely scalar statements.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* p * (l - r) = 0 from |- l = r : a hint for linear combinations.          *)
let C849SM_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: structure Bounds *)
let C849SM_BOUNDS_DEF = new_definition
 `c849sm_bounds (c:real) (s:real) <=>
    &7 / &10 <= c /\ c <= &4 / &5 /\ &3 / &5 <= s /\ s <= &71 / &100 /\ s <= c /\
    &7 / &5 <= c + s /\ c + s <= &10 / &7 /\ c - s <= &1 / &5`;;

(* Lean: bounds *)
let C849SM_BOUNDS = prove
 (`forall c s a. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
           &1 < a /\ a <= s + c / &2 ==> c849sm_bounds c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C849SM_BOUNDS_DEF] THEN
  SUBGOAL_THEN `&3 * c / &4 < s` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    NLIN_FACTS_TAC [] [`&0 <= c * (&3 * c / &4 - s)`; `&1 < s + c / &2`] THEN
    NLIN_TAC [SQ_NONNEG `s + c / &2 - &1`];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - s) * (c + s)`; `&0 < (s - &3 * c / &4) * (s + &3 * c / &4)`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &7 / &10`; SQ_NONNEG `c - &4 / &5`]
   [`&7 / &10 <= c`; `c <= &4 / &5`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s - &3 / &5`; SQ_NONNEG `s - &71 / &100`]
   [`&3 / &5 <= s`; `s <= &71 / &100`; `c - s <= &1 / &5`;
    `&0 <= (&1 / &5 - (c - s)) * (&1 / &5 + (c - s))`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c + s - &7 / &5`; SQ_NONNEG `c - s`;
                  SQ_NONNEG `c + s - &10 / &7`]
   [`&7 / &5 <= c + s`; `c + s <= &10 / &7`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: frame (private) *)
let C849SM_FRAME = prove
 (`forall p q. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1
         ==> p <= &1 /\ q <= &1 /\ &1 <= p + q /\ p + q <= &10 / &7 /\ p * q <= &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
  NLIN_TAC [SQ_NONNEG `p:real`; SQ_NONNEG `q:real`; SQ_NONNEG `p - &1`;
            SQ_NONNEG `q - &1`; SQ_NONNEG `p + q - &1`; SQ_NONNEG `p - q`;
            SQ_NONNEG `p + q - &10 / &7`]);;

(* Lean: weighted (private) *)
let C849SM_WEIGHTED = prove
 (`forall c s f g. &0 <= c /\ &0 <= s /\ s <= c /\ c + s <= &10 / &7 /\
             f <= g /\ f + g <= &11 / &8 ==> c * f + s * g < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= (c - s) * (g - f)`; `&0 <= (c + s) * (&11 / &8 - (f + g))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lowerV_b_pos *)
let C849SM_LOWERV_B_POS = prove
 (`forall p q c s. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\ c pow 2 + s pow 2 = &1 /\
             &0 <= c /\ &0 <= s /\ q <= p /\ &0 <= c * q - s * p
             ==> &0 < &1 + (c * p + s * q) + (c * q - s * p) +
                      (&13 / &20) * (c * q - s * p) * (p - q) -
                      (&27 / &20) * (c * p + s * q) * (p + q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] C849SM_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `p - c`; SQ_NONNEG `q - s`]
   [`&0 <= c * p`; `&0 <= s * q`; `&0 <= c * p + s * q`; `c * p + s * q <= &1`;
    `&0 <= (c * p + s * q) * (&10 / &7 - (p + q))`;
    `&0 <= (c * q - s * p) * (p - q)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lowerV_b_neg *)
let C849SM_LOWERV_B_NEG = prove
 (`forall p q c s. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\
             &0 <= c /\ &0 <= s /\ q <= p /\ s <= c /\ c + s <= &10 / &7
             ==> &0 < &1 + (c * p + s * q) + (c * q - s * p) * (p - (&37 / &50) * q) -
                      (&27 / &20) * (c * p + s * q) * (p + q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] C849SM_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&13 * q - &4`]
   [`&0 <= (p - q) * (&1 - (&7 / &20) * (p + q))`; `&0 <= q * (p + q)`;
    `(&27 / &20) * p pow 2 + (&7 / &20) * p * q + (&37 / &50) * q pow 2 - p <=
     p pow 2 + (&61 / &100) * p * q + (&27 / &20) * q pow 2 - q`;
    `&0 <= (p + q - &1) * (&3 / &2 - (p + q))`; `&0 <= q * (&1 - p)`;
    `((&27 / &20) * p pow 2 + (&7 / &20) * p * q + (&37 / &50) * q pow 2 - p) +
     (p pow 2 + (&61 / &100) * p * q + (&27 / &20) * q pow 2 - q) <= &11 / &8`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`;
    `(&27 / &20) * p pow 2 + (&7 / &20) * p * q + (&37 / &50) * q pow 2 - p`;
    `p pow 2 + (&61 / &100) * p * q + (&27 / &20) * q pow 2 - q`] C849SM_WEIGHTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  NLIN_TAC ~deg2:false
   [C849SM_EQ_HINT `c:real` (ASSUME `p pow 2 + q pow 2 = &1`);
    C849SM_EQ_HINT `s:real` (ASSUME `p pow 2 + q pow 2 = &1`)]);;

(* Lean: lowerU_b_pos *)
let C849SM_LOWERU_B_POS = prove
 (`forall p q c s. &0 <= p /\ &3 / &7 <= q /\ p pow 2 + q pow 2 = &1 /\
             &0 <= c /\ &0 <= s /\ s <= c /\ c + s <= &10 / &7
             ==> &0 < &1 + (c * p + s * q) + (c * q - s * p) +
                      (&27 / &20) * (c * q - s * p) * (p - q) -
                      (c * p + s * q) * (&2 * q + (&3 / &5) * p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] C849SM_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `p:real`; SQ_NONNEG `q:real`]
   [`&0 <= p * (&1 - q)`;
    `(&3 / &5) * p pow 2 + (&13 / &20) * p * q + (&27 / &20) * q pow 2 - p - q <=
     (&27 / &20) * p pow 2 - (&3 / &4) * p * q + &2 * q pow 2 + p - q`;
    `&0 <= (q - &3 / &7) * (&1 - q)`; `&0 <= p * q`;
    `((&3 / &5) * p pow 2 + (&13 / &20) * p * q + (&27 / &20) * q pow 2 - p - q) +
     ((&27 / &20) * p pow 2 - (&3 / &4) * p * q + &2 * q pow 2 + p - q) <= &11 / &8`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`;
    `(&3 / &5) * p pow 2 + (&13 / &20) * p * q + (&27 / &20) * q pow 2 - p - q`;
    `(&27 / &20) * p pow 2 - (&3 / &4) * p * q + &2 * q pow 2 + p - q`] C849SM_WEIGHTED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  NLIN_TAC ~deg2:false
   [C849SM_EQ_HINT `c:real` (ASSUME `p pow 2 + q pow 2 = &1`);
    C849SM_EQ_HINT `s:real` (ASSUME `p pow 2 + q pow 2 = &1`)]);;

(* Lean: lowerV_a_pos *)
let C849SM_LOWERV_A_POS = prove
 (`forall p q c s. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\ c849sm_bounds c s /\
             &0 <= c * q - s * p
             ==> &0 < &1 + (c * p + s * q) - (&27 / &20) * (p + q) + (c * q - s * p) * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C849SM_BOUNDS_DEF] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&3 / &4) * p - (&13 / &20) * q`;
                  SQ_NONNEG `(&13 / &20) * p + (&3 / &4) * q - &1`]
   [`&0 <= p * (c - &7 / &10)`; `&0 <= q * (s - &3 / &5)`;
    `&0 <= (c * q - s * p) * c`; `(&13 / &20) * p + (&3 / &4) * q < &1`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lowerV_a_neg *)
let C849SM_LOWERV_A_NEG = prove
 (`forall p q c s. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\ c849sm_bounds c s
             ==> &0 < &1 + (c * p + s * q) - (&27 / &20) * (p + q) +
                      (&13 / &20) * (c * q - s * p) * (c - s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C849SM_BOUNDS_DEF] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] C849SM_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - s) * (&71 / &100 - s)`; `&0 <= (c - s) * (c - &7 / &10)`;
    `&27 / &20 - c + (&13 / &20) * s * (c - s) <= &33 / &50`;
    `&27 / &20 - s - (&13 / &20) * c * (c - s) <= &33 / &50`;
    `p * (&27 / &20 - c + (&13 / &20) * s * (c - s)) <= p * (&33 / &50)`;
    `q * (&27 / &20 - s - (&13 / &20) * c * (c - s)) <= q * (&33 / &50)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lowerU_a_pos *)
let C849SM_LOWERU_A_POS = prove
 (`forall p q c s. &0 <= p /\ &0 <= q /\ p pow 2 + q pow 2 = &1 /\ c pow 2 + s pow 2 = &1 /\
             c849sm_bounds c s
             ==> &0 < &1 + (c * p + s * q) - (&2 * q + (&3 / &5) * p) + (c * q - s * p) * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C849SM_BOUNDS_DEF] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&4 / &5) * p - (&2 / &5) * q`;
                  SQ_NONNEG `(&2 / &5) * p + (&4 / &5) * q - &1`]
   [`&0 <= (c - &7 / &10) * (&1 - s)`; `&3 / &5 - c + c * s <= &2 / &5`;
    `&0 <= (s - &3 / &5) * (&71 / &100 - s)`; `&1 - s + s pow 2 <= &4 / &5`;
    `p * (&3 / &5 - c + c * s) <= p * (&2 / &5)`;
    `q * (&1 - s + s pow 2) <= q * (&4 / &5)`;
    `(&2 / &5) * p + (&4 / &5) * q < &1`] THEN
  NLIN_TAC ~deg2:false [C849SM_EQ_HINT `q:real` (ASSUME `c pow 2 + s pow 2 = &1`)]);;
