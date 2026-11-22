(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralWallAngleOrder.lean (Jatloe).      *)
(* Continuous angle-order obstruction for the bottom square O, the central   *)
(* square A and the negative left wall W: O.s < t.                           *)
(* Normal: c977cc_normal; upper/lower: ABT_*; W.s = -t written sW = --t;     *)
(* PositiveCentralTransverse.alternatives: PCT_ALTERNATIVES;                 *)
(* C696PositiveCorner.corner_faces: C696PC_CORNER_FACES;                     *)
(* NegativeWallAngleOrder.angle_order: NWAO_ANGLE_ORDER;                     *)
(* CentralLeftWallNegative.wall_axis: CLWN_WALL_AXIS;                        *)
(* LeftWallNegativeFaces: LWNF_FACES, LWNF_LOWER_FACE_AND_TILT.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/NegativeWallAngleOrder.ml";;
needs "n12/geometry/CentralPositiveTransverse.ml";;

let PCWAO_PROD = PCT_PROD_TAC;;
let PCWAO_PRODLT = PCT_PRODLT_TAC;;

let PCWAO_NONNEG_OF_MUL = prove
 (`forall k p. &0 < k /\ &0 <= k * p ==> &0 <= p`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: margin *)
let PCWAO_MARGIN = prove
 (`forall C S d t. c977cc_normal C S /\ c977cc_normal d t /\
             &4 / &5 <= d /\ t <= &3 / &5 /\ d <= C /\ S <= t
     ==> (d pow 2 - (d + t - &1)) * (&1 + C * S) + d * t * (&2 - S pow 2 - (d + t - &1)) -
         d * ((d + t) * C + (d - t) * S) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (d pow 2 - (d + t - &1))` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `d - &1 / &2`]; ALL_TAC] THEN
  PCWAO_PROD `t:real` `d - &4 / &5` THEN
  MP_TAC(SPEC `t - &1 / &2` REAL_LE_POW_2) THEN DISCH_TAC THEN
  PCWAO_PROD `(t - &1 / &2) pow 2` `t + &1` THEN
  PCWAO_PROD `&3 / &5 - t` `&5 / &4 - t` THEN
  SUBGOAL_THEN `&2 * (d pow 2 * (&1 - t)) - &3 * (d pow 2 - (d + t - &1)) * t =
    &3 * t * (d - &4 / &5) + &5 * (t - &1 / &2) pow 2 * (t + &1) +
    (&3 / &5 - t) * (&5 / &4 - t)` ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * (d pow 2 * (&1 - t)) - &3 * (d pow 2 - (d + t - &1)) * t` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `(d pow 2 - (d + t - &1))` `t:real` THEN PCWAO_PROD `(d pow 2 - (d + t - &1))` `t - S:real` THEN
  SUBGOAL_THEN `&0 <= (d pow 2 * (&1 - t)) - (d pow 2 - (d + t - &1)) * S` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `d:real` `t:real` THEN
  PCWAO_PROD `&1 - C` `d * t` THEN
  PCWAO_PROD `(&1 - C) * (d * t)` `C - d:real` THEN
  PCWAO_PROD `&1 - C` `C - d:real` THEN
  SUBGOAL_THEN `(&1 + d) * (&1 - C) <= S pow 2` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `&1 + d` `((&1 - C) * (d * t)) * (C - d)` THEN
  PCWAO_PROD `(d pow 2 * (&1 - t)) - (d pow 2 - (d + t - &1)) * S` `S pow 2 - (&1 + d) * (&1 - C)` THEN
  SUBGOAL_THEN `(&1 + d) * ((&1 - C) * (d pow 2 - d * t * C - (d pow 2 - (d + t - &1)) * S) + S * (d + t - &1) pow 2 / &2) <= (S pow 2 * (d pow 2 * (&1 - t) - (d pow 2 - (d + t - &1)) * S) + (&1 + d) * S * (d + t - &1) pow 2 / &2)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `t + S:real` `&2 * (d pow 2 * (&1 - t)) - &3 * (d pow 2 - (d + t - &1)) * t` THEN
  PCWAO_PROD `t - S:real` `t + &2 * S` THEN
  PCWAO_PROD `(d pow 2 - (d + t - &1))` `(t - S) * (t + &2 * S)` THEN
  SUBGOAL_THEN `&0 <= (d pow 2 * (&1 - t)) * (t + S) - (d pow 2 - (d + t - &1)) * (t pow 2 + t * S + S pow 2)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `t - S:real` `(d pow 2 * (&1 - t)) * (t + S) - (d pow 2 - (d + t - &1)) * (t pow 2 + t * S + S pow 2)` THEN
  MP_TAC(SPEC `(d + t - &1)` REAL_LE_POW_2) THEN DISCH_TAC THEN
  PCWAO_PROD `&1 + d` `(d + t - &1) pow 2` THEN
  PCWAO_PROD `t - S:real` `(&1 + d) * (d + t - &1) pow 2` THEN
  SUBGOAL_THEN `(S pow 2 * (d pow 2 * (&1 - t) - (d pow 2 - (d + t - &1)) * S) + (&1 + d) * S * (d + t - &1) pow 2 / &2) <= (t pow 2 * (d pow 2 * (&1 - t) - (d pow 2 - (d + t - &1)) * t) + (&1 + d) * t * (d + t - &1) pow 2 / &2)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - d <= t / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCWAO_PRODLT `&1 - (d + t / &2)` `&1 + (d + t / &2)` THEN
   PCWAO_PROD `t:real` `d - (&3 / &4) * t` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `d - &1 / &2` REAL_LE_POW_2) THEN DISCH_TAC THEN
  PCWAO_PROD `t:real` `(d - &1 / &2) pow 2` THEN
  SUBGOAL_THEN `&1 - d - t * (&2 * d pow 2 - &2 * d + &1) <= &0` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `&1 - d` `--(&1 - d - t * (&2 * d pow 2 - &2 * d + &1))` THEN
  PCWAO_PROD `&1 + d` `(&1 - d) * --(&1 - d - t * (&2 * d pow 2 - &2 * d + &1))` THEN
  SUBGOAL_THEN `(&1 + d) * ((d pow 2 - (d + t - &1)) * (&1 + C * S) + d * t * (&2 - S pow 2 - (d + t - &1)) - d * ((d + t) * C + (d - t) * S)) = (&1 + d) * (--((d + t - &1) pow 2 * (&1 + (d + t - &1))) / &2) + (&1 + d) * ((&1 - C) * (d pow 2 - d * t * C - (d pow 2 - (d + t - &1)) * S) + S * (d + t - &1) pow 2 / &2)` ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + d) * (--((d + t - &1) pow 2 * (&1 + (d + t - &1))) / &2) + (t pow 2 * (d pow 2 * (&1 - t) - (d pow 2 - (d + t - &1)) * t) + (&1 + d) * t * (d + t - &1) pow 2 / &2) =
                (&1 + d) * (&1 - d) * (&1 - d - t * (&2 * d pow 2 - &2 * d + &1))`
  ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + d) * ((d pow 2 - (d + t - &1)) * (&1 + C * S) + d * t * (&2 - S pow 2 - (d + t - &1)) - d * ((d + t) * C + (d - t) * S)) <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  PCWAO_PRODLT `&1 + d` `((d pow 2 - (d + t - &1)) * (&1 + C * S) + d * t * (&2 - S pow 2 - (d + t - &1)) - d * ((d + t) * C + (d - t) * S))` THEN RASM_ARITH_TAC);;

(* Lean: ordered (private) *)
let PCWAO_ORDERED = prove
 (`forall p q d t. c977cc_normal p q /\ c977cc_normal d t /\ t <= q
             ==> p <= d /\ d + t <= p + q /\ p * t <= d * q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCT_NORMAL_TAC THEN
  PCWAO_PROD `q - t:real` `q + t:real` THEN
  SUBGOAL_THEN `p <= d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCWAO_PRODLT `p - d:real` `p + d:real` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `q - t:real` `p + d - q - t` THEN
  SUBGOAL_THEN `(p + d) * (p + q - d - t) = (q - t) * (p + d - q - t)` ASSUME_TAC THENL
  [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `d + t <= p + q` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCWAO_PRODLT `p + d:real` `d + t - (p + q)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `q:real` `d - p:real` THEN PCWAO_PROD `p:real` `q - t:real` THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: support_obstruction *)
let PCWAO_SUPPORT_OBSTRUCTION = prove
 (`forall p q C S d t a ou ov au av wu wv.
     c977cc_normal p q /\ c977cc_normal C S /\ c977cc_normal d t /\
     &1 < a /\ t <= &3 / &5 /\ S <= t /\ t <= q /\
     &0 <= q * ou + p * ov /\ ou + a <= &2 * p + q /\
     au + a <= &2 * (C + S) /\ wv + a <= t + &3 * d /\
     a * (d + t) <= d * (wu + a) + t * (wv + a) /\
     (ov + a <= --(q * C - p * S) * (au + a) + (p * C + q * S) * av \/
      (q * C - p * S) * (ou + a) + (p * C + q * S) * (ov + a) <= av) /\
     wu + a <= (C * d - S * t) * au - (S * d + C * t) * (av + a)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`; `d:real`; `t:real`] PCWAO_ORDERED) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `C:real`; `S:real`] PCWAO_ORDERED) THEN
  MP_TAC(SPECL [`p:real`; `q:real`; `C:real`; `S:real`] PCWAO_ORDERED) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < p /\ &0 < C /\ &0 < d` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 / &5 <= d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCWAO_PRODLT `&4 / &5 - d` `&4 / &5 + d` THEN
   PCWAO_PROD `&3 / &5 - t` `&3 / &5 + t` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PRODLT `p:real` `C:real` THEN PCWAO_PROD `q:real` `S:real` THEN
  PCWAO_PROD `S:real` `d:real` THEN PCWAO_PROD `C:real` `t:real` THEN
  PCWAO_PRODLT `C:real` `d - t:real` THEN PCWAO_PROD `t:real` `C - S:real` THEN
  PCWAO_PRODLT `p:real` `d - t:real` THEN PCWAO_PROD `t:real` `p - q:real` THEN
  SUBGOAL_THEN `&0 < (p * C + q * S) /\ &0 <= (q * C - p * S) /\ &0 <= (S * d + C * t) /\ &0 < (C * d - S * t) /\ &0 < (p * d - q * t)`
  STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Bv = (p + q - q * (&2 * p + q)) / p` THEN
  SUBGOAL_THEN `p * Bv = p + q - q * (&2 * p + q)` ASSUME_TAC THENL
  [EXPAND_TAC "Bv" THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `(p * C + q * S) pow 2 + (q * C - p * S) pow 2 = &1 /\ (p * C + q * S) * (C * d - S * t) - (q * C - p * S) * (S * d + C * t) = (p * d - q * t) /\
                p * (q * C - p * S) - q * (p * C + q * S) = --S` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN
   UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  (* strictBottom *)
  PCWAO_PROD `q:real` `(&2 * p + q) - (ou + a)` THEN
  PCWAO_PRODLT `a - &1` `p + q:real` THEN
  MP_TAC(SPECL [`p:real`; `ov + a - Bv`] PCT_POS_BY_POS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  (* virtualX, virtualY, virtualProjection *)
  PCWAO_PROD `p:real` `q:real` THEN PCWAO_PROD `p * q:real` `&1 - p` THEN
  MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  PCWAO_PROD `q pow 2` `&1 - q` THEN
  SUBGOAL_THEN `p * (&2 - (p * (&2 * p + q) - q * Bv)) = p * q * (&1 - p) + q pow 2 * (&1 - q)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `p * Bv = p + q - q * (&2 * p + q)` THEN UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`p:real`; `&2 - (p * (&2 * p + q) - q * Bv)`] PCWAO_NONNEG_OF_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `q * (&2 * p + q) + p * Bv <= &2` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCWAO_PROD `C:real` `&2 - (p * (&2 * p + q) - q * Bv)` THEN
  PCWAO_PROD `S:real` `&2 - (q * (&2 * p + q) + p * Bv)` THEN
  SUBGOAL_THEN `(p * C + q * S) * (&2 * p + q) - (q * C - p * S) * Bv <= &2 * (C + S)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  (* reduced *)
  SUBGOAL_THEN `wu + a < (C * d - S * t) * (&2 * (C + S) - &1) - (S * d + C * t) * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv)` ASSUME_TAC THENL
  [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN `Bv + (q * C - p * S) * (au + a) + (p * C + q * S) * a < (p * C + q * S) * (av + a)` ASSUME_TAC THENL
    [RASM_ARITH_TAC; ALL_TAC] THEN
    PCWAO_PROD `(p * C + q * S)` `((C * d - S * t) * au - (S * d + C * t) * (av + a)) - (wu + a)` THEN
    PCWAO_PROD `(S * d + C * t)` `(p * C + q * S) * (av + a) - (Bv + (q * C - p * S) * (au + a) + (p * C + q * S) * a)` THEN
    PCWAO_PROD `(p * d - q * t)` `&2 * (C + S) - (au + a)` THEN
    PCWAO_PROD `(S * d + C * t)` `(q * C - p * S) + (p * C + q * S)` THEN
    PCWAO_PRODLT `a - &1` `(p * d - q * t) + (S * d + C * t) * ((q * C - p * S) + (p * C + q * S))` THEN
    SUBGOAL_THEN `au * ((p * C + q * S) * (C * d - S * t) - (q * C - p * S) * (S * d + C * t)) = au * (p * d - q * t)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(p * C + q * S) * (wu + a) < (p * d - q * t) * (&2 * (C + S) - &1) - (S * d + C * t) * (Bv + (q * C - p * S) + (p * C + q * S))` ASSUME_TAC THENL
    [RASM_ARITH_TAC; ALL_TAC] THEN
    PCWAO_PROD `(S * d + C * t)` `(q * C - p * S)` THEN
    PCWAO_PROD `(S * d + C * t) * (q * C - p * S)` `&2 * (C + S) - ((p * C + q * S) * (&2 * p + q) - (q * C - p * S) * Bv)` THEN
    SUBGOAL_THEN `(p * C + q * S) * ((C * d - S * t) * (&2 * (C + S) - &1) - (S * d + C * t) * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv)) - ((p * d - q * t) * (&2 * (C + S) - &1) - (S * d + C * t) * (Bv + (q * C - p * S) + (p * C + q * S))) =
                  (S * d + C * t) * (q * C - p * S) * (&2 * (C + S) - ((p * C + q * S) * (&2 * p + q) - (q * C - p * S) * Bv))` ASSUME_TAC THENL
    [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
     CONV_TAC REAL_RING; ALL_TAC] THEN
    MP_TAC(SPECL [`(p * C + q * S)`; `((C * d - S * t) * (&2 * (C + S) - &1) - (S * d + C * t) * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv)) - (wu + a)`] PCT_POS_BY_POS) THEN
    ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; RASM_ARITH_TAC];
    PCWAO_PROD `S:real` `(&2 * p + q) - (ou + a)` THEN
    PCWAO_PROD `(p * C + q * S)` `q * ou + p * ov` THEN
    PCWAO_PRODLT `(p * C + q * S)` `p + q:real` THEN
    PCWAO_PRODLT `a - &1` `(p * C + q * S) * (p + q)` THEN
    SUBGOAL_THEN `p * ((q * C - p * S) * (ou + a) + (p * C + q * S) * (ov + a)) <= p * av` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `p * ((q * C - p * S) * (ou + a) + (p * C + q * S) * (ov + a) - ((q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv)) =
                  (p * C + q * S) * (q * ou + p * ov) + a * p * ((q * C - p * S) + (p * C + q * S)) - S * ou -
                  p * ((q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv) /\
                  p * ((q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv) = (p * C + q * S) * (p + q) - S * (&2 * p + q) /\
                  a * (p * ((q * C - p * S) + (p * C + q * S)) + S) = a * ((p * C + q * S) * (p + q))` STRIP_ASSUME_TAC THENL
    [REPEAT CONJ_TAC THEN
     UNDISCH_TAC `p * Bv = p + q - q * (&2 * p + q)` THEN
     UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MP_TAC(SPECL [`p:real`; `av - ((q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv)`] PCT_POS_BY_POS) THEN
    ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `(&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv) < av + a` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    PCWAO_PROD `(S * d + C * t)` `(av + a) - (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv)` THEN
    PCWAO_PROD `(C * d - S * t)` `&2 * (C + S) - (au + a)` THEN
    PCWAO_PRODLT `(C * d - S * t)` `a - &1` THEN
    RASM_ARITH_TAC]; ALL_TAC] THEN
  (* monotone *)
  SUBGOAL_THEN `p * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv) = p * (&1 + C * (p + q) - &2 * S) + S * q * (p + q - &1)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `p * Bv = p + q - q * (&2 * p + q)` THEN UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  PCWAO_PROD `p:real` `d:real` THEN PCWAO_PROD `p * d:real` `C:real` THEN
  PCWAO_PROD `(p * d) * C` `(p + q) - (d + t)` THEN
  PCWAO_PROD `S * d:real` `q:real` THEN
  PCWAO_PROD `(S * d) * q` `(p + q) - (d + t)` THEN
  PCWAO_PROD `d * q - p * t` `d + t - &1` THEN
  PCWAO_PROD `S:real` `(d * q - p * t) * (d + t - &1)` THEN
  SUBGOAL_THEN `p * (d * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv) - (d * (&1 + C * (d + t) - &2 * S) + S * t * (d + t - &1))) =
                p * d * C * ((p + q) - (d + t)) + S * d * q * ((p + q) - (d + t)) +
                S * (d * q - p * t) * (d + t - &1)` ASSUME_TAC THENL
  [UNDISCH_TAC `p * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv) = p * (&1 + C * (p + q) - &2 * S) + S * q * (p + q - &1)` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`p:real`; `d * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv) - (d * (&1 + C * (d + t) - &2 * S) + S * t * (d + t - &1))`] PCWAO_NONNEG_OF_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  (* final *)
  PCWAO_PRODLT `d:real` `((C * d - S * t) * (&2 * (C + S) - &1) - (S * d + C * t) * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv)) - (wu + a)` THEN
  PCWAO_PROD `(S * d + C * t)` `d * (&1 + (q * C - p * S) * (&2 * p + q) + (p * C + q * S) * Bv) - (d * (&1 + C * (d + t) - &2 * S) + S * t * (d + t - &1))` THEN
  PCWAO_PROD `t:real` `(t + &3 * d) - (wv + a)` THEN
  PCWAO_PRODLT `a - &1` `d + t:real` THEN
  SUBGOAL_THEN `&0 < d * (C * d - S * t) * (&2 * (C + S) - &1) - (S * d + C * t) * (d * (&1 + C * (d + t) - &2 * S) + S * t * (d + t - &1)) - (d + t - t pow 2 - &3 * d * t)`
  ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * (C * d - S * t) * (&2 * (C + S) - &1) - (S * d + C * t) * (d * (&1 + C * (d + t) - &2 * S) + S * t * (d + t - &1)) - (d + t - t pow 2 - &3 * d * t) = ((d pow 2 - (d + t - &1)) * (&1 + C * S) + d * t * (&2 - S pow 2 - (d + t - &1)) - d * ((d + t) * C + (d - t) * S))`
  ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `d:real`; `t:real`] PCWAO_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* upper support value with both coefficients >= 0 (helper) *)
let PCWAO_UPPER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

(* Lean: angle_order *)
let PCWAO_ANGLE_ORDER = prove
 (`forall cO sO uO vO aO cA sA uA vA aA cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cA sA /\ c977cc_normal cW t /\
     sW = --t /\ aO = aA /\ aA = aW /\ &1 < aA /\ aA <= &1001 / &1000 /\
     lcont cO sO uO vO aO /\ lcont cW sW uW vW aW /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&1) (&2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     uA + aA <= &2 * (cA + sA) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     ~linside cW sW uW vW aW (&457 / &500) (&3) /\
     ~linside cW sW uW vW aW (&19 / &25) (&187 / &100) /\
     ldisj cO sO uO vO aO cA sA uA vA aA /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> sO < t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aW`)) THEN
  let use th tms = MP_TAC(SPECL tms th) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                    DISCH_THEN STRIP_ASSUME_TAC] in
  let sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aW:real`]
  and sqW = [`cW:real`; `--t`; `uW:real`; `vW:real`; `aW:real`]
  and sqO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aW:real`] in
  PCT_NORMAL_TAC THEN
  use NWAO_ANGLE_ORDER (sqA @ sqW @ [`t:real`]) THEN
  SUBGOAL_THEN `~linside cW (--t) uW vW aW (&1) (&2)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cA sA uA vA aW cW (--t) uW vW aW` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&1`; `&2`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  use LWNF_FACES (sqW @ [`t:real`]) THEN
  use LWNF_LOWER_FACE_AND_TILT (sqW @ [`t:real`]) THEN
  use C696PC_CORNER_FACES sqO THEN
  MP_TAC(SPECL (sqO @ sqA) PCT_ALTERNATIVES) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_TAC] THEN
  use CLWN_WALL_AXIS (sqA @ sqW @ [`t:real`]) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cA:real`; `sA:real`] PCWAO_ORDERED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  PCWAO_PROD `cO:real` `cA:real` THEN PCWAO_PROD `sO:real` `sA:real` THEN
  PCWAO_PROD `cW:real` `cA - sA:real` THEN PCWAO_PROD `sA:real` `cW - t:real` THEN
  PCWAO_PROD `sA:real` `cW:real` THEN PCWAO_PROD `cA:real` `t:real` THEN
  SUBGOAL_THEN `&0 <= cO * cA + sO * sA /\ &0 <= sO * cA - cO * sA /\
                &0 <= cA * cW - sA * t /\ &0 <= sA * cW + cA * t` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  let rw th tms = MP_TAC(SPECL tms th) THEN
    ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC;
                    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] in
  rw CPTR_LOWER_NP (sqA @ [`--sO`; `cO:real`]) THEN
  rw PCWAO_UPPER_PP (sqO @ [`--sA`; `cA:real`]) THEN
  rw PCT_LOWER_PN (sqA @ [`cW:real`; `--t`]) THEN
  MATCH_MP_TAC PCWAO_SUPPORT_OBSTRUCTION THEN
  MAP_EVERY EXISTS_TAC [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `cW:real`; `t:real`;
    `aW:real`; `uO:real`; `vO:real`; `uA:real`; `vA:real`; `uW:real`; `vW:real`] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN REAL_ARITH_TAC]);;
