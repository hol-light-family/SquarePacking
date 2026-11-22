(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralEscapeOrder.lean (Jatloe,         *)
(* N12-jatloe; namespace N12Compact.PositiveCentralEscapeOrder).             *)
(* Continuous support comparisons for the missing-(1,2) branch.              *)
(* Lean upper/lower are ABT_upper/ABT_lower; CornerOuterOrderMonotone's      *)
(* cross/denominator/F/G are coom_cross/coom_denominator/coom_f/coom_g.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C696CornerMargins.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/PositiveCentralLeftBand.ml";;
needs "n12/geometry/PositiveCentralPositiveBottom.ml";;
needs "n12/geometry/NegativeWallTopSeed.ml";;
needs "n12/geometry/CornerOuterOrderEndpoint.ml";;
needs "n12/geometry/CornerOuterOrderMonotone.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;

let PCEO_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCEO_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PCEO_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCEO_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PCEO_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let PCEO_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: B (definition) *)
let pceo_b = new_definition
 `pceo_b (p:real) q = &1 - &2 * q + q * (&1 - q) / p`;;

(* p * B p q, for p > 0 (helper) *)
let PCEO_P_B = prove
 (`forall p q. &0 < p ==> p * pceo_b p q = p - &2 * p * q + q * (&1 - q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pceo_b] THEN
  (SUBGOAL_THEN `~(p = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: B_alt (private) *)
let PCEO_B_ALT = prove
 (`forall p q. c977cc_normal p q ==> pceo_b p q = &1 - &2 * q + p * q / (&1 + q)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCEO_NORMAL_TAC THEN REWRITE_TAC[pceo_b] THEN
  UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN
  (SUBGOAL_THEN `~(p = &0) /\ ~(&1 + q = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: half_order (private) *)
let PCEO_HALF_ORDER = prove
 (`forall p q C S. c977cc_normal p q /\ c977cc_normal C S /\ q <= S
     ==> p * (&1 - S) <= C * (&1 - q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCEO_NORMAL_TAC THEN
  PCEO_PROD_TAC `&1 - S` `&1 - q` THEN PCEO_PROD_TAC `p:real` `C:real` THEN
  PCEO_PROD_TAC `S - q` `(&1 - S) * (&1 - q) + p * C` THEN
  SUBGOAL_THEN `(p + C) * (C * (&1 - q) - p * (&1 - S)) =
                (S - q) * ((&1 - S) * (&1 - q) + p * C)` ASSUME_TAC THENL
  [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * (&1 - q) - p * (&1 - S)` MP_TAC THENL
  [MATCH_MP_TAC PCEO_NONNEG_OF_MUL THEN EXISTS_TAC `p + C` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: strong_base_bound *)
let PCEO_STRONG_BASE_BOUND = prove
 (`forall p q C S v. c977cc_normal p q /\ c977cc_normal C S /\ q <= S /\
     pceo_b p q < (p * S - q * C) * (&2 * (C + S) - &1) + (p * C + q * S) * (v - &1)
     ==> &1 + (C + S) * (&1 - &2 * S) + C * (&1 - p) < C * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCEO_USE PCEO_HALF_ORDER [`p:real`; `q:real`; `C:real`; `S:real`] THEN
  PCEO_NORMAL_TAC THEN
  PCEO_USE PCEO_P_B [`p:real`; `q:real`] THEN
  PCEO_PROD_TAC `q:real` `C * (&1 - q) - p * (&1 - S)` THEN
  PCEO_PROD_TAC `p:real` `&1 - p` THEN
  PCEO_PROD_TAC `C:real` `p * (&1 - p)` THEN
  PCEO_PRODLT_TAC `p:real` `C:real` THEN
  PCEO_PROD_TAC `q:real` `S:real` THEN
  PCEO_PRODLT_TAC `p * C`
    `((p * S - q * C) * (&2 * (C + S) - &1) + (p * C + q * S) * (v - &1)) - pceo_b p q` THEN
  SUBGOAL_THEN
   `(p * C) * (((p * S - q * C) * (&2 * (C + S) - &1) + (p * C + q * S) * (v - &1)) -
               pceo_b p q) =
    p * (p * C + q * S) * (C * v - (&1 + (C + S) * (&1 - &2 * S))) -
    p * C * (&1 - p) - q * (C * (&1 - q) - p * (&1 - S))` ASSUME_TAC THENL
  [UNDISCH_TAC `p * pceo_b p q = p - &2 * p * q + q * (&1 - q)` THEN
   UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `p * C * (&1 - p) <
                p * (p * C + q * S) * (C * v - (&1 + (C + S) * (&1 - &2 * S)))`
  ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C * v - (&1 + (C + S) * (&1 - &2 * S))` ASSUME_TAC THENL
  [MATCH_MP_TAC PCEO_POS_OF_MUL THEN EXISTS_TAC `p * (p * C + q * S)` THEN
   CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; RASM_ARITH_TAC];
   ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `p - C:real`; SQ_NONNEG `q - S:real`]
    [`p * C + q * S <= &1`] THEN
  SUBGOAL_THEN `&0 <= p * (&1 - (p * C + q * S))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCEO_PROD_TAC `p * (&1 - (p * C + q * S))` `C * v - (&1 + (C + S) * (&1 - &2 * S))` THEN
  SUBGOAL_THEN `&0 < p * ((C * v - (&1 + (C + S) * (&1 - &2 * S))) - C * (&1 - p))`
  ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (C * v - (&1 + (C + S) * (&1 - &2 * S))) - C * (&1 - p)` MP_TAC THENL
  [MATCH_MP_TAC PCEO_POS_OF_MUL THEN EXISTS_TAC `p:real` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: base_bound *)
let PCEO_BASE_BOUND = prove
 (`forall p q C S v. c977cc_normal p q /\ c977cc_normal C S /\ q <= S /\
     pceo_b p q < (p * S - q * C) * (&2 * (C + S) - &1) + (p * C + q * S) * (v - &1)
     ==> &1 + (C + S) * (&1 - &2 * S) < C * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCEO_USE PCEO_STRONG_BASE_BOUND [`p:real`; `q:real`; `C:real`; `S:real`; `v:real`] THEN
  PCEO_NORMAL_TAC THEN PCEO_PROD_TAC `C:real` `&1 - p` THEN RASM_ARITH_TAC);;

(* Lean: northwest_threshold *)
let PCEO_NORTHWEST_THRESHOLD = prove
 (`forall C S v. c977cc_normal C S /\ &1 + (C + S) * (&1 - &2 * S) < C * v /\
           v <= (&47 / &20) * C - (&33 / &20) * S
     ==> &81 / &100 < C /\ C * ((&47 / &25) * C - S) <= &1 + (C + S) * (&1 - &2 * S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCEO_NORMAL_TAC THEN
  PCEO_PROD_TAC `C:real` `((&47 / &20) * C - (&33 / &20) * S) - v` THEN
  NLIN_FACTS_TAC [] [`&0 < &1 + (&7 / &20) * C * (C + S) - (C + S)`] THEN
  SUBGOAL_THEN `&81 / &100 < C` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PCEO_PROD_TAC `&81 / &100 - C` `&81 / &100 + C` THEN
   SUBGOAL_THEN `&293 / &500 <= S` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    PCEO_PROD_TAC `S:real` `&293 / &500 - S` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PCEO_PROD_TAC `C - S` `&28 / &125 - (C - S)` THEN
   SUBGOAL_THEN `&349 / &250 <= C + S` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    PCEO_PROD_TAC `C + S` `&349 / &250 - (C + S)` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PCEO_PROD_TAC `(C + S) - &349 / &250` `&1 - (&7 / &20) * C` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&22 / &25 < C + (&3 / &25) * S` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PCEO_PROD_TAC `C - &81 / &100` `&22 / &25 - C` THEN
   PCEO_PROD_TAC `&22 - &25 * C - &3 * S` `&22 - &25 * C + &3 * S` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  PCEO_PROD_TAC `&1 - S` `(C + (&3 / &25) * S) - &22 / &25` THEN
  NLIN_TAC ~deg2:false []);;

(* (1 + q) * B p q = (1 + q) * (1 - 2 q) + p q  (helper) *)
let PCEO_B_REL = prove
 (`forall p q. c977cc_normal p q ==> (&1 + q) * pceo_b p q = (&1 + q) * (&1 - &2 * q) + p * q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PCEO_B_ALT th]) THEN
  PCEO_NORMAL_TAC THEN
  (SUBGOAL_THEN `~(&1 + q = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: lower_transfer *)
let PCEO_LOWER_TRANSFER = prove
 (`forall p q d t C S v.
     c977cc_normal p q /\ c977cc_normal d t /\ c977cc_normal C S /\ t <= q /\ q <= S /\
     pceo_b p q < (p * S - q * C) * (&2 * (C + S) - &1) + (p * C + q * S) * (v - &1)
     ==> pceo_b d t < (d * S - t * C) * (&2 * (C + S) - &1) + (d * C + t * S) * (v - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCEO_USE PCEO_B_REL [`p:real`; `q:real`] THEN PCEO_USE PCEO_B_REL [`d:real`; `t:real`] THEN
  PCEO_USE C977CSB_COSINE_ORDER [`p:real`; `q:real`; `d:real`; `t:real`] THEN
  PCEO_USE COOM_DIFFERENCES [`p:real`; `q:real`; `d:real`; `t:real`] THEN
  PCEO_NORMAL_TAC THEN
  PCEO_PRODLT_TAC `p:real` `C:real` THEN PCEO_PROD_TAC `q:real` `S:real` THEN
  PCEO_PRODLT_TAC `d:real` `C:real` THEN PCEO_PROD_TAC `t:real` `S:real` THEN
  SUBGOAL_THEN `coom_denominator q t = (&1 + q) * (&1 + t)` ASSUME_TAC THENL
  [REWRITE_TAC[coom_denominator]; ALL_TAC] THEN
  PCEO_PRODLT_TAC `&1 + q` `&1 + t` THEN
  SUBGOAL_THEN `&0 <= coom_f p q d t` ASSUME_TAC THENL
  [REWRITE_TAC[coom_f; coom_denominator] THEN
   PCEO_PROD_TAC `(&1 + q) * (&1 + t)` `d - p` THEN
   PCEO_PROD_TAC `p:real` `d:real` THEN
   PCEO_PROD_TAC `p * d` `q - t` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCEO_PROD_TAC `S - q` `p + C - S - q` THEN
  SUBGOAL_THEN `(p + C) * (C + S - p - q) = (S - q) * (p + C - S - q)` ASSUME_TAC THENL
  [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `p + q <= C + S` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= C + S - p - q` MP_TAC THENL
   [MATCH_MP_TAC PCEO_NONNEG_OF_MUL THEN EXISTS_TAC `p + C` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  PCEO_PROD_TAC `coom_f p q d t` `(C + S) - (p + q)` THEN
  PCEO_PROD_TAC `coom_g p q d t - coom_f p q d t` `S - q` THEN
  SUBGOAL_THEN `&0 <= coom_f p q d t * C + coom_g p q d t * S - coom_denominator q t * coom_cross p q d t` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `coom_denominator q t * ((d * C + t * S) * pceo_b p q - (p * C + q * S) * pceo_b d t + (&2 * (C + S) - &1) * coom_cross p q d t) =
                coom_f p q d t * C + coom_g p q d t * S - coom_denominator q t * coom_cross p q d t` ASSUME_TAC THENL
  [REWRITE_TAC[coom_f; coom_g; coom_denominator; coom_cross] THEN
   UNDISCH_TAC `(&1 + q) * pceo_b p q = (&1 + q) * (&1 - &2 * q) + p * q` THEN
   UNDISCH_TAC `(&1 + t) * pceo_b d t = (&1 + t) * (&1 - &2 * t) + d * t` THEN
   UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (d * C + t * S) * pceo_b p q - (p * C + q * S) * pceo_b d t + (&2 * (C + S) - &1) * coom_cross p q d t` ASSUME_TAC THENL
  [MATCH_MP_TAC PCEO_NONNEG_OF_MUL THEN EXISTS_TAC `coom_denominator q t` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * (C + S) - &1) * ((d * S - t * C) * (p * C + q * S) - (p * S - q * C) * (d * C + t * S)) = (&2 * (C + S) - &1) * coom_cross p q d t` ASSUME_TAC THENL
  [REWRITE_TAC[coom_cross] THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(d * C + t * S) * pceo_b p q < (d * C + t * S) * ((p * S - q * C) * (&2 * (C + S) - &1) + (p * C + q * S) * (v - &1))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p * C + q * S) * ((d * S - t * C) * (&2 * (C + S) - &1) + (d * C + t * S) * (v - &1)) <= (p * C + q * S) * pceo_b d t` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: endpoint_obstruction *)
let PCEO_ENDPOINT_OBSTRUCTION = prove
 (`forall d t C S v.
     c977cc_normal d t /\ c977cc_normal C S /\ t <= S /\
     pceo_b d t < (d * S - t * C) * (&2 * (C + S) - &1) + (d * C + t * S) * (v - &1) /\
     v <= (&47 / &20) * C - (&33 / &20) * S /\
     (d * v <= C * (t + (&72 / &25) * d) - (C + S * d pow 2 + C * d * t) \/
      d + t - t pow 2 - (&72 / &25) * d * t < d * ((C * d - S * t) * (&2 * (C + S) - &1) - (S * d + C * t) * v))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
  [PCEO_USE PCEO_STRONG_BASE_BOUND [`d:real`; `t:real`; `C:real`; `S:real`; `v:real`] THEN
   PCEO_USE PCEO_BASE_BOUND [`d:real`; `t:real`; `C:real`; `S:real`; `v:real`] THEN
   PCEO_USE PCEO_NORTHWEST_THRESHOLD [`C:real`; `S:real`; `v:real`] THEN
   PCEO_NORMAL_TAC THEN
   PCEO_PROD_TAC `C:real` `&1 - t` THEN PCEO_PROD_TAC `&1 - d` `C * (&1 - t)` THEN
   PCEO_PROD_TAC `d:real` `&1 - S` THEN PCEO_PROD_TAC `&1 - d` `d * (&1 - S)` THEN
   SUBGOAL_THEN `d * v <= d * ((&47 / &25) * C - S + &1 - d)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `C * (d * v) <= C * (d * ((&47 / &25) * C - S + &1 - d)) /\
                 d * (C * ((&47 / &25) * C - S)) <= d * (&1 + (C + S) * (&1 - &2 * S)) /\
                 d * (&1 + (C + S) * (&1 - &2 * S) + C * (&1 - d)) < d * (C * v)`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LT_LMUL] THEN
    CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PCEO_NORMAL_TAC THEN
  PCEO_PRODLT_TAC `d:real` `C:real` THEN PCEO_PROD_TAC `t:real` `S:real` THEN
  PCEO_PROD_TAC `S:real` `d:real` THEN PCEO_PROD_TAC `C:real` `t:real` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d - C:real`; SQ_NONNEG `t - S:real`] [`(d * C + t * S) <= &1`] THEN
  SUBGOAL_THEN `(d * C + t * S) * (C * d - S * t) + (S * d + C * t) * (d * S - t * C) = (d pow 2 - t pow 2) /\ (S * d + C * t) * (d * C + t * S) = d * t + C * S`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCEO_PROD_TAC `S - t` `d + C - S - t` THEN
  SUBGOAL_THEN `(d + C) * (C + S - d - t) = (S - t) * (d + C - S - t)` ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `d + t <= C + S` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= C + S - d - t` MP_TAC THENL
   [MATCH_MP_TAC PCEO_NONNEG_OF_MUL THEN EXISTS_TAC `d + C` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  PCEO_USE PCEO_P_B [`d:real`; `t:real`] THEN
  SUBGOAL_THEN `&0 <= t * (&1 - t) / d` ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_DIV) THEN CONJ_TAC) THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (d - t) <= pceo_b d t + &1` ASSUME_TAC THENL
  [REWRITE_TAC[pceo_b] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCEO_PROD_TAC `d + t` `(pceo_b d t + &1) - &2 * (d - t)` THEN
  SUBGOAL_THEN `(&2 * (d pow 2 - t pow 2) - (d + t) * pceo_b d t) <= d + t` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCEO_PROD_TAC `(C + S) - (d + t)` `(C + S + d + t) / &2 - (&2 * (d pow 2 - t pow 2) - (d + t) * pceo_b d t)` THEN
  SUBGOAL_THEN `(&2 * (d pow 2 - t pow 2) - (d + t) * pceo_b d t) * (C + S) - C * S <= (&2 * (d pow 2 - t pow 2) - (d + t) * pceo_b d t) * (d + t) - d * t` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCEO_PROD_TAC `t:real` `&1 - (&22 / &25) * (d * C + t * S)` THEN
  MP_TAC(SPECL [`d:real`; `t:real`] COOE_ENDPOINT) THEN
  ASM_REWRITE_TAC[GSYM pceo_b] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&2 * (d pow 2 - t pow 2) - (d + t) * pceo_b d t) * (C + S) + (&22 / &25) * t * (d * C + t * S) - (d pow 2 - t pow 2) - d * t - C * S <= &0`
  ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN
   `d * ((d pow 2 - t pow 2) * (&2 * (C + S) - &1) - (S * d + C * t) * (pceo_b d t + (d * C + t * S))) - (d * C + t * S) * (d + t - t pow 2 - (&72 / &25) * d * t) =
    d * ((&2 * (d pow 2 - t pow 2) - (d + t) * pceo_b d t) * (C + S) + (&22 / &25) * t * (d * C + t * S) - (d pow 2 - t pow 2) - d * t - C * S)` ASSUME_TAC THENL
  [UNDISCH_TAC `d * pceo_b d t = d - &2 * d * t + t * (&1 - t)` THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCEO_PROD_TAC `d:real` `--((&2 * (d pow 2 - t pow 2) - (d + t) * pceo_b d t) * (C + S) + (&22 / &25) * t * (d * C + t * S) - (d pow 2 - t pow 2) - d * t - C * S)` THEN
  SUBGOAL_THEN `&0 <= d * (S * d + C * t)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCEO_PROD_TAC `d * (S * d + C * t)` `((d * S - t * C) * (&2 * (C + S) - &1) + (d * C + t * S) * (v - &1)) - pceo_b d t` THEN
  SUBGOAL_THEN `(d * C + t * S) * (d + t - t pow 2 - (&72 / &25) * d * t) <
                (d * C + t * S) * (d * ((C * d - S * t) * (&2 * (C + S) - &1) - (S * d + C * t) * v))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * (&2 * (C + S) - &1) * ((d * C + t * S) * (C * d - S * t) + (S * d + C * t) * (d * S - t * C)) = d * (&2 * (C + S) - &1) * (d pow 2 - t pow 2)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

let PCEO_LOWER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny = (nx * c + ny * s) * u + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

let PCEO_LOWER_PN = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ --nx * s + ny * c <= &0
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * u + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

(* Lean: support_order *)
let PCEO_SUPPORT_ORDER = prove
 (`forall cO sO (uO:real) vO aO cA sA uA vA aA cW sW uW vW aW t.
     c977cc_normal cO sO /\ c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\
     aO = aA /\ aA = aW /\ &1 < aA /\ lcont cW sW uW vW aW /\
     uA + aA <= &2 * (cA + sA) /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     sO <= sA /\ pceo_b cO sO < vO + aO /\
     vO + aO <= ABT_lower cA sA uA vA aA (--sO) cO /\
     (vA + aA <= ABT_lower cW sW uW vW aW (--sA) cA \/
      uW + aW <= ABT_lower cA sA uA vA aA cW sW) /\
     vW + aW <= t + (&72 / &25) * cW
     ==> sO < t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --t`)) THEN
  PCEO_USE C977CSB_COSINE_ORDER [`cA:real`; `sA:real`; `cO:real`; `sO:real`] THEN
  PCEO_NORMAL_TAC THEN
  PCEO_PROD_TAC `sO:real` `cO - cA` THEN PCEO_PROD_TAC `cO:real` `sA - sO` THEN
  SUBGOAL_THEN `&0 <= (cO * sA - sO * cA)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCEO_PRODLT_TAC `cO:real` `cA:real` THEN PCEO_PROD_TAC `sO:real` `sA:real` THEN
  PCEO_PROD_TAC `cW:real` `cA - sA` THEN PCEO_PROD_TAC `sA:real` `cW - t` THEN
  SUBGOAL_THEN `&0 <= (cA * cW - sA * t)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCEO_PROD_TAC `sA:real` `cW:real` THEN PCEO_PROD_TAC `cA:real` `t:real` THEN
  PCEO_PROD_TAC `sA:real` `cW pow 2` THEN PCEO_PROD_TAC `cA * cW` `t:real` THEN
  PCEO_PROD_TAC `cA:real` `cW:real` THEN
  PCEO_USE PCEO_LOWER_PP
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aW:real`; `--sO`; `cO:real`] THEN
  SUBGOAL_THEN `uA <= &2 * (cA + sA) - &1` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCEO_PROD_TAC `(cO * sA - sO * cA)` `(&2 * (cA + sA) - &1) - uA` THEN
  PCEO_PROD_TAC `(cO * cA + sO * sA)` `aW - &1` THEN
  SUBGOAL_THEN `pceo_b cO sO < (cO * sA - sO * cA) * (&2 * (cA + sA) - &1) + (cO * cA + sO * sA) * ((vA + aW) - &1)`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cW * cW + --t * --t = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cW pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcx; REAL_ABS_NEG]) THEN
  SUBGOAL_THEN `abs t = t` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `aW * (cW + t) <= cW * (uW + aW) + t * (vW + aW)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `cW * (vA + aW) <= cA * (t + (&72 / &25) * cW) - (cA + sA * cW pow 2 + cA * cW * t) \/
    cW + t - t pow 2 - (&72 / &25) * cW * t <
      cW * ((cA * cW - sA * t) * (&2 * (cA + sA) - &1) - (sA * cW + cA * t) * (vA + aW))`
  ASSUME_TAC THENL
  [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [DISJ1_TAC THEN
    PCEO_USE C977NCO_LOWER_NEGATIVE_NONPOS
      [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`; `t:real`; `--sA`; `cA:real`] THEN
    SUBGOAL_THEN `cW * (vA + aW) <= cW * ABT_lower cW (--t) uW vW aW (--sA) cA`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `ABT_lower c s u v a nx ny = e`) (concl th)
      then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN
    PCEO_PROD_TAC `(sA * cW + cA * t)` `(cW * (uW + aW) + t * (vW + aW)) - aW * (cW + t)` THEN
    PCEO_PROD_TAC `cA:real` `(t + (&72 / &25) * cW) - (vW + aW)` THEN
    SUBGOAL_THEN `&0 < (cA + sA * cW pow 2 + cA * cW * t)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    PCEO_PROD_TAC `(cA + sA * cW pow 2 + cA * cW * t)` `aW - &1` THEN
    SUBGOAL_THEN
     `cW * ((--sA * cW - cA * t) * (uW + aW) + (--sA * t + cA * cW) * vW) +
      (sA * cW + cA * t) * (cW * (uW + aW) + t * (vW + aW) - aW * (cW + t)) =
      cA * (vW + aW) - aW * (cA + sA * cW pow 2 + cA * cW * t)` ASSUME_TAC THENL
    [UNDISCH_TAC `cW pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    DISJ2_TAC THEN
    PCEO_USE PCEO_LOWER_PN
      [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aW:real`; `cW:real`; `--t`] THEN
    SUBGOAL_THEN `cW * (uW + aW) <= cW * ABT_lower cA sA uA vA aW cW (--t)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `ABT_lower c s u v a nx ny = e`) (concl th)
      then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN
    SUBGOAL_THEN `&0 <= cW * (cA * cW - sA * t)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    PCEO_PROD_TAC `cW * (cA * cW - sA * t)` `(&2 * (cA + sA) - &1) - uA` THEN
    PCEO_PROD_TAC `t:real` `(t + (&72 / &25) * cW) - (vW + aW)` THEN
    PCEO_PRODLT_TAC `aW - &1` `cW + t` THEN
    NLIN_TAC ~deg2:false []];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cA:real`; `sA:real`; `vA + aW`]
    PCEO_LOWER_TRANSFER) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `t:real`; `cA:real`; `sA:real`; `vA + aW`]
    PCEO_ENDPOINT_OBSTRUCTION) THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC));;

(* Lean: angle_order *)
let PCEO_ANGLE_ORDER = prove
 (`forall cO sO uO vO aO cA sA uA vA aA cW sW uW vW aW t.
     c977cc_normal cO sO /\ c977cc_normal cA sA /\ c977cc_normal cW t /\ sW = --t /\
     aO = aA /\ aA = aW /\ &1 < aA /\ lcont cO sO uO vO aO /\ lcont cW sW uW vW aW /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\ ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     uA + aA <= &2 * (cA + sA) /\ ~linside cA sA uA vA aA (&1) (&2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     linside cW sW uW vW aW (&1) (&12 / &5) /\
     ~linside cW sW uW vW aW (&1) (&72 / &25) /\
     ldisj cO sO uO vO aO cA sA uA vA aA /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> sO < t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCEO_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + sO * sO = &1 /\ cA * cA + sA * sA = &1 /\
                cW * cW + sW * sW = &1 /\ &0 < aA /\ &0 < aW /\ &0 < aO /\
                abs sO <= cO`
  STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `cW pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]]; ALL_TAC] THEN
  PCEO_USE PCPB_ONLY_BOTTOM_AXIS
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
     `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCEO_USE PCLB_UPPER_FACE [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCEO_USE PCPB_OWN_AXIS_ANGLE
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
     `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCEO_USE PCLB_NORTHWEST_CAP [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCEO_USE C696PC_CORNER_FACES [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] THEN
  SUBGOAL_THEN `pceo_b cO sO <= c696cm_boundary cO sO` ASSUME_TAC THENL
  [PCEO_USE PCEO_P_B [`cO:real`; `sO:real`] THEN
   SUBGOAL_THEN `cO * c696cm_boundary cO sO =
                 cO + sO - &2 * cO * sO - (&457 / &500) * sO pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[c696cm_boundary] THEN
    (SUBGOAL_THEN `~(cO = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= c696cm_boundary cO sO - pceo_b cO sO` MP_TAC THENL
   [MATCH_MP_TAC PCEO_NONNEG_OF_MUL THEN EXISTS_TAC `cO:real` THEN
    CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `sO:real`]; REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    NWTS_ALTERNATIVES) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); DISCH_TAC] THEN
  PCEO_USE NWTS_UPPER_FACE
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
     `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    PCEO_SUPPORT_ORDER) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC));;
