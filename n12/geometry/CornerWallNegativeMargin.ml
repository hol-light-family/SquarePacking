(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallNegativeMargin.lean (Jatloe).           *)
(* Continuous scalar margin for the negative left singleton.                 *)
(* Divisions are replaced in the proofs by auxiliary reals e with d*e = 1-t  *)
(* etc.; the statements are verbatim.                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* Lean: half_order *)
let CWNM_HALF_ORDER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t
             ==> c * (&1 - t) <= d * (&1 - s)`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c + d` THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c + d) * (d * (&1 - s) - c * (&1 - t)) =
                (t - s) * ((&1 - t) * (&1 - s) + c * d)` SUBST1_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: coefficient_bound (private) *)
let CWNM_COEFFICIENT_BOUND = prove
 (`forall d t l r. c977cc_normal d t /\ c977cc_normal l r /\ r <= t /\ t <= &51 / &100
     ==> &0 <= &1 - l * (&189 / &100 - t - (&1 - t) / d) - r * (d pow 2 / (&1 + d))`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `exists a b. &189 / &100 - t - (&1 - t) / d = a /\ d pow 2 / (&1 + d) = b /\
                      d * (&89 / &100 - a) = (&1 - d) * (&1 - t) /\
                      d * (&871 / &1000 - a) = (&1 - d) * (&1 - t) - (&19 / &1000) * d /\
                      (&1 + d) * b = d pow 2`
  STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXISTS_TAC [`&189 / &100 - t - (&1 - t) / d`; `d pow 2 / (&1 + d)`] THEN
   REWRITE_TAC[] THEN UNDISCH_TAC `&7 / &10 <= d` THEN CONV_TAC REAL_FIELD;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `a <= &89 / &100 /\ b <= &1 / &2` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THENL
   [MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `d:real` THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `&1 + d` THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - d) * (d + &1 / &2)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= l * (&89 / &100 - a) /\ &0 <= r * (&1 / &2 - b)`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t <= &11 / &50` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d <= &49 / &50` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < (d - &49 / &50) * (d + &49 / &50) /\
                 &0 <= (t - &11 / &50) * (t + &11 / &50)` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4719 / &125000 <= t * t * (&1 - t)` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (t - &11 / &50) * ((t + &11 / &50) * (&1 - t) - (&11 / &50) * (&11 / &50))`
   MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (t - &11 / &50) * (&1 - t) /\
                  &0 <= (&11 / &25) * (&51 / &100 - t)` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - d) * (&1 - t) - (&19 / &1000) * d` ASSUME_TAC THENL
  [MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `&1 + d` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 + d) * (((&1 - d) * (&1 - t) - (&19 / &1000) * d) - &0) =
                 t * t * (&1 - t) - (&19 / &1000) * d * (&1 + d)` SUBST1_TAC THENL
   [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (&49 / &50 - d) * (&99 / &50 + d)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a <= &871 / &1000 /\ b <= &49 / &100` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THENL
   [MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `d:real` THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `&1 + d` THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&49 / &50 - d) * (d + &49 / &100)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(&871 / &1000) * l + (&49 / &100) * r <= &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `((&871 / &1000) * l + (&49 / &100) * r) * ((&871 / &1000) * l + (&49 / &100) * r)
                 <= &998741 / &1000000` MP_TAC THENL
   [MP_TAC(SPEC `(&871 / &1000) * r - (&49 / &100) * l` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `l * l + r * r = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SPEC_TAC(`(&871 / &1000) * l + (&49 / &100) * r`,`w:real`) THEN
   GEN_TAC THEN DISCH_TAC THEN NLIN_TAC [SQ_NONNEG `w - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= l * (&871 / &1000 - a) /\ &0 <= r * (&49 / &100 - b)`
  MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: margin *)
let CWNM_MARGIN = prove
 (`forall c s d t l r.
     c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ r <= t /\ t <= &51 / &100 /\ &43 / &50 <= d
     ==> &0 <= l + r - d + l * r * (c + t - &72 / &25 + (&1 - t) / d) +
               l pow 2 * (s + d - &2 + (&1 - s) / c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`] CWNM_COEFFICIENT_BOUND) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWNM_HALF_ORDER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN
   `exists e1 e2 g h. (&1 - t) / d = e1 /\ (&1 - s) / c = e2 /\
                d pow 2 / (&1 + d) = d pow 2 * g /\
                d * e1 = &1 - t /\ c * e2 = &1 - s /\
                (&1 + d) * g = &1 /\ (&1 + l) * h = &1`
  STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXISTS_TAC [`(&1 - t) / d`; `(&1 - s) / c`; `&1 / (&1 + d)`;
                         `&1 / (&1 + l)`] THEN
   UNDISCH_TAC `&7 / &10 <= d` THEN UNDISCH_TAC `&7 / &10 <= c` THEN
   UNDISCH_TAC `&7 / &10 <= l` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(&1 - t) / d = e1`;
                              ASSUME `d pow 2 / (&1 + d) = d pow 2 * g`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `&0 < g /\ &0 < h` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `d * r <= l * t` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= d * (t - r) /\ &0 <= t * (l - d)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&24 / &25) * c * r <= l * (&1 - s)` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
   MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `d:real` THEN
   REWRITE_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `&0 <= l * (d * (&1 - s) - c * (&1 - t)) /\
     &0 <= (c * l) * ((&1 - t) - (&24 / &25) * t) /\
     &0 <= ((&24 / &25) * c) * (l * t - d * r)` MP_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `H = &1 + t - &289 / &100 + e1` THEN
  ABBREV_TAC `F0 = l + r - d + l * r * H + l * l * (d - &1)` THEN
  SUBGOAL_THEN `F0 <= l + r - d + l * r * (c + t - &72 / &25 + e1) +
                     l * l * (s + d - &2 + e2)` ASSUME_TAC THENL
  [MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `c * ((l + r - d + l * r * (c + t - &72 / &25 + e1) +
           l * l * (s + d - &2 + e2)) - F0) =
     l * (&1 - c) * (l * (&1 - s) - (&24 / &25) * c * r) +
     l * r * c * (&1 / &100 - (&1 - c) / &25)` SUBST1_TAC THENL
   [EXPAND_TAC "F0" THEN EXPAND_TAC "H" THEN
    UNDISCH_TAC `c * e2 = &1 - s` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
   REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + l * H - d * r + l * r * h` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= r * (l * h - d * g)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `l * h - d * g = g * h * (l - d)` SUBST1_TAC THENL
    [UNDISCH_TAC `(&1 + d) * g = &1` THEN UNDISCH_TAC `(&1 + l) * h = &1` THEN
     CONV_TAC REAL_RING; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN
    `&1 + l * H - d * r + l * r * h =
     (&1 - l * (&189 / &100 - t - e1) - r * (d * d * g)) + r * (l * h - d * g)`
   SUBST1_TAC THENL
   [EXPAND_TAC "H" THEN UNDISCH_TAC `(&1 + d) * g = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `F0 = r * (&1 + l * H - d * r + l * r * h)` ASSUME_TAC THENL
  [EXPAND_TAC "F0" THEN UNDISCH_TAC `(&1 + l) * h = &1` THEN
   UNDISCH_TAC `l * l + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= F0` MP_TAC THENL
  [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
