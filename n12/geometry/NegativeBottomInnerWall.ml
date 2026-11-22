(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeBottomInnerWall.lean                     *)
(*                                                                           *)
(* Bottom singleton O = (cO, sO, uO, vO, aO) with sO = --t, next wall        *)
(* D = (cD, sD, uD, vD, aD) with sD = --r.  Normal is c977cc_normal;         *)
(* lower/upper are ABT_lower/ABT_upper.                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/NegativeBottomNextWall.ml";;

let NBIW_STEP = NBNW_STEP;;

(* Lean: negative_projection *)
let NBIW_NEGATIVE_PROJECTION = prove
 (`forall c s u v a t d r.
     s = --t /\ c977cc_normal c t /\ c977cc_normal d r /\ &1 < a /\
     c - t <= u /\ t * (u + a) <= c * v /\
     linside c s u v a (&1) (&457 / &500)
     ==> &2 * d - r < ABT_upper c s u v a d (--r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  NBIW_STEP(SPECL [`c:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  NBIW_STEP(SPECL [`d:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_CASES_TAC `r <= t` THENL
   [NBIW_STEP(SPECL [`c:real`; `t:real`; `d:real`; `r:real`] C977CSB_COSINE_ORDER);
    NBIW_STEP(SPECL [`d:real`; `r:real`; `c:real`; `t:real`] C977CSB_COSINE_ORDER)] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal; linside]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `d * c + --r * --t = c * d + t * r /\ --d * --t + --r * c = t * d - c * r`] THEN
  NLIN_FACTS_TAC [] [`&0 < c * d + t * r`] THEN
  REWRITE_TAC[MATCH_MP (REAL_ARITH `&0 < x ==> abs x = x`) (ASSUME `&0 < c * d + t * r`)] THENL
   [(* r <= t *)
    NLIN_FACTS_TAC [] [`&0 <= t * d - c * r`] THEN
    SUBGOAL_THEN `abs(t * d - c * r) = t * d - c * r` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c * ((c * d + t * r) * (u + a) + (t * d - c * r) * (v + a) - (&2 * d - r)) =
                  d * (u - (c - t)) + (t * d - c * r) * (c * v - t * (u + a)) +
                  (a - &1) * (d + c * (t * d - c * r)) + (&1 - c) * (d * (&1 - t) + c * r)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= d * (u - (c - t))`; `&0 <= (t * d - c * r) * (c * v - t * (u + a))`;
      `&0 < d + c * (t * d - c * r)`; `&0 < (a - &1) * (d + c * (t * d - c * r))`;
      `&0 <= d * (&1 - t) + c * r`; `&0 <= (&1 - c) * (d * (&1 - t) + c * r)`;
      `&0 < c * ((c * d + t * r) * (u + a) + (t * d - c * r) * (v + a) - (&2 * d - r))`;
      `&0 < (c * d + t * r) * (u + a) + (t * d - c * r) * (v + a) - (&2 * d - r)`] THEN
    RASM_ARITH_TAC;
    (* t <= r *)
    NLIN_FACTS_TAC [] [`t * d - c * r <= &0`] THEN
    SUBGOAL_THEN `abs(t * d - c * r) = --(t * d - c * r)` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c * d + t * r) * (u + a) + (t * d - c * r) * v - (&2 * d - r) =
                  (c * d + t * r) * (u - (c - t)) +
                  (t * d - c * r) * (v - (t + (&457 / &500) * c)) +
                  (a - &1) * (c * d + t * r) +
                  d * (c - &1 - (&43 / &500) * c * t) + r * (t + (&43 / &500) * c pow 2)`
      ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `c * (c - &1 - (&43 / &500) * c * t) + t * (t + (&43 / &500) * c pow 2) = &1 - c`
      ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`v < t + (&457 / &500) * c`; `c - &1 - (&43 / &500) * c * t <= &0`;
      `&0 <= t + (&43 / &500) * c pow 2`;
      `&0 <= (c - d) * --(c - &1 - (&43 / &500) * c * t)`;
      `&0 <= (r - t) * (t + (&43 / &500) * c pow 2)`;
      `&0 <= d * (c - &1 - (&43 / &500) * c * t) + r * (t + (&43 / &500) * c pow 2)`;
      `&0 <= (c * d + t * r) * (u - (c - t))`;
      `&0 <= --(t * d - c * r) * ((t + (&457 / &500) * c) - v)`;
      `&0 < (a - &1) * (c * d + t * r)`] THEN
    RASM_ARITH_TAC]);;

(* the vertex (u + a, v + a) in face coordinates *)
let NBIW_CORNER = prove
 (`forall c s u v a p q. c * c + s * s = &1 /\ u <= p /\ p <= u + a /\ v <= q /\ q <= v + a
     ==> lclosed c s u v a (c * p - s * q) (s * p + c * q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lclosed] THEN
  SUBGOAL_THEN `c * (c * p - s * q) + s * (s * p + c * q) = p /\
                --s * (c * p - s * q) + c * (s * p + c * q) = q`
    (fun th -> REWRITE_TAC[th] THEN ASM_REAL_ARITH_TAC) THEN
  CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

(* Lean: positive_projection *)
let NBIW_POSITIVE_PROJECTION = prove
 (`forall c s u v a t x y.
     &0 < a /\ s = --t /\ c977cc_normal c t /\ &1 < a /\ &457 / &500 < c /\
     c - t <= u /\ t * (u + a) <= c * v /\ &0 <= x /\ &0 < y
     ==> &2 * x + (&457 / &500) * y < ABT_upper c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  NBIW_STEP(SPECL [`c:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  NBIW_STEP(SPECL [`c:real`; `--t:real`; `u:real`; `v:real`; `a:real`; `u + a:real`; `v + a:real`]
    NBIW_CORNER) THEN
  NBIW_STEP(SPECL [`c:real`; `--t:real`; `u:real`; `v:real`; `a:real`;
     `c * (u + a) - --t * (v + a)`; `--t * (u + a) + c * (v + a)`; `x:real`; `y:real`]
     ABT_CLOSED_BOUNDS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  SUBGOAL_THEN `c * ((c * (u + a) - --t * (v + a)) - &2) =
                (u - (c - t)) + t * (c * v - t * (u + a)) + (a - &1) * (&1 + c * t) +
                (&1 - c) * (&1 - t)` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= t * (c * v - t * (u + a))`; `&0 <= c * t`; `&0 < &1 + c * t`;
    `&0 < (a - &1) * (&1 + c * t)`;
    `&0 <= (&1 - c) * (&1 - t)`;
    `&0 < c * ((c * (u + a) - --t * (v + a)) - &2)`;
    `&2 < c * (u + a) - --t * (v + a)`;
    `&0 < c * (a - &1)`;
    `&457 / &500 < --t * (u + a) + c * (v + a)`;
    `&0 <= x * ((c * (u + a) - --t * (v + a)) - &2)`;
    `&0 < y * ((--t * (u + a) + c * (v + a)) - &457 / &500)`] THEN
  RASM_ARITH_TAC);;

(* the two directed alternatives of one axis (the local rule of the Lean proof) *)
let NBIW_RULE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD t d r.
     cO * cO + sO * sO = &1 /\ cD * cD + sD * sD = &1 /\ &0 < aO /\ &0 < aD /\
     sO = --t /\ c977cc_normal cO t /\ &457 / &500 < cO /\ &1 < aO /\
     cO - t <= uO /\ t * (uO + aO) <= cO * vO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&2) (&1) /\
     c977cc_normal d r /\
     (ABT_upper cO sO uO vO aO d (--r) <= ABT_lower cD sD uD vD aD d (--r) \/
      ((&43 / &130) * d < r /\ ABT_upper cO sO uO vO aO r d <= ABT_lower cD sD uD vD aD r d))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NBIW_STEP(SPECL [`d:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  ALL_TAC THENL
   [NBIW_STEP(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                     `t:real`; `d:real`; `r:real`] NBIW_NEGATIVE_PROJECTION) THEN
    NBIW_STEP(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                     `&2`; `&1`; `d:real`; `--r:real`] ABT_STRICT_BOUNDS);
    NBIW_STEP(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                     `t:real`; `r:real`; `d:real`] NBIW_POSITIVE_PROJECTION) THEN
    NBIW_STEP(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                     `&2`; `&457 / &500`; `r:real`; `d:real`] ABT_STRICT_BOUNDS)] THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN RASM_ARITH_TAC);;

(* Lean: impossible_of_cosine *)
let NBIW_IMPOSSIBLE_OF_COSINE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD t r.
     cO * cO + sO * sO = &1 /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sO = --t /\ sD = --r /\
     c977cc_normal cO t /\ c977cc_normal cD r /\ &457 / &500 < cO /\
     aO = aD /\ &1 < aO /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&2) (&1) /\
     ldisj cO sO uO vO aO cD sD uD vD aD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aO:real = aD` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sO = --t` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `sD = --r` o concl)) THEN
  NBIW_STEP(SPECL [`cO:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  NBIW_STEP(SPECL [`cD:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  NBIW_STEP(SPECL [`cO:real`; `--t:real`; `uO:real`; `vO:real`; `aO:real`; `t:real`]
    C977NCO_CORNER_FACE) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  NBIW_STEP(SPECL [`cO:real`; `--t:real`; `uO:real`; `vO:real`; `aO:real`;
                   `cD:real`; `--r:real`; `uD:real`; `vD:real`; `aO:real`] C696BCS_SINGLETON_WALL) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C696BCS_singletonStep; REAL_NEG_NEG]) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> can (find_term ((=) `ABT_upper`)) (concl th))) THENL
   [MATCH_MP_TAC NBIW_RULE THEN
    MAP_EVERY EXISTS_TAC [`cO:real`; `--t:real`; `uO:real`; `vO:real`; `aO:real`;
                          `cD:real`; `--r:real`; `uD:real`; `vD:real`; `aO:real`;
                          `t:real`; `cO:real`; `t:real`];
    MATCH_MP_TAC NBIW_RULE THEN
    MAP_EVERY EXISTS_TAC [`cO:real`; `--t:real`; `uO:real`; `vO:real`; `aO:real`;
                          `cD:real`; `--r:real`; `uD:real`; `vD:real`; `aO:real`;
                          `t:real`; `cD:real`; `r:real`]] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: impossible *)
let NBIW_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD t r.
     cO * cO + sO * sO = &1 /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     sO = --t /\ sD = --r /\
     c977cc_normal cO t /\ c977cc_normal cD r /\ t <= &1 / &5 /\
     aO = aD /\ &1 < aO /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&2) (&1) /\
     ldisj cO sO uO vO aO cD sD uD vD aD
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC NBIW_IMPOSSIBLE_OF_COSINE THEN
  MAP_EVERY EXISTS_TAC [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                        `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                        `t:real`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN
  NBIW_STEP(SPECL [`cO:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  NLIN_TAC []);;
