(* ========================================================================= *)
(* Port of Compact/Geometry/C977CornerSupportBounds.lean (Jatloe, N12-jatloe)*)
(* (namespace N12Compact.C977CornerSupportBounds).                           *)
(* Support-line comparisons for the C977 corner coupling.                   *)
(* Note: Lean variable T is renamed TT (T is truth in HOL).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/C977CornerHalfAngle.ml";;

let C977CSUP_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C977CSUP_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let C977CSUP_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Instantiate a lemma, discharge its hypotheses from the assumptions. *)
let C977CSUP_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let C977CSUP_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ k * x < k * y ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: positive_dot *)
let C977CSUP_POSITIVE_DOT = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT ==> &0 < c * C + t * TT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSUP_NORMAL_TAC THEN
  C977CSUP_PRODLT_TAC `c:real` `C:real` THEN
  C977CSUP_PROD_TAC `t:real` `TT:real` THEN RASM_ARITH_TAC);;

(* Lean: own_axis_above *)
let C977CSUP_OWN_AXIS_ABOVE = prove
 (`forall c t C TT u v a.
     c977cc_normal c t /\ c977cc_normal C TT /\ &1 < a /\
     c - t <= u /\ t * (u + a) <= c * v /\ &0 <= c * TT - t * C
     ==> &2 * (C + TT) < (c * TT - t * C) * (u + a) + (c * C + t * TT) * (v + a) + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C977CSUP_USE C977CSUP_POSITIVE_DOT [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_USE C977CHA_ORDERED_NORMALS [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_USE C977CSB_A_AXIS_ABOVE [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_NORMAL_TAC THEN
  SUBGOAL_THEN `c * (&2 * (C + TT)) <= TT * (c - t + &1) + c * (c * C + t * TT) + c`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `TT * (c - t + &1) + c * (c * C + t * TT) + c =
                 c * ((TT / c) * (c - t + &1) + (c * C + t * TT) + &1)` SUBST1_TAC THENL
   [(SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `c * ((c * TT - t * C) * (u + a) + (c * C + t * TT) * (v + a) + a) =
    (c * C + t * TT) * (c * v - t * (u + a)) + TT * (u + a) +
    c * (c * C + t * TT) * a + c * a` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C977CSUP_PROD_TAC `c * C + t * TT` `c * v - t * (u + a)` THEN
  C977CSUP_PROD_TAC `TT:real` `u - (c - t)` THEN
  C977CSUP_PRODLT_TAC `c:real` `c * C + t * TT` THEN
  C977CSUP_PRODLT_TAC `a - &1` `TT + c * (c * C + t * TT) + c` THEN
  MATCH_MP_TAC C977CSUP_LT_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []);;

(* Lean: own_axis_below *)
let C977CSUP_OWN_AXIS_BELOW = prove
 (`forall c t C TT u v a.
     c977cc_normal c t /\ c977cc_normal C TT /\ &1 < a /\
     c - t <= u /\ t * (u + a) <= c * v /\ c * TT - t * C <= &0
     ==> &2 * (C + TT) < (c * TT - t * C) * u + (c * C + t * TT) * (v + a) + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C977CSUP_USE C977CSUP_POSITIVE_DOT [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_USE C977CSB_SINE_ORDER [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_USE C977CSB_A_AXIS_BELOW [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_NORMAL_TAC THEN
  SUBGOAL_THEN `c * (&2 * (C + TT)) <= TT * (c - t) + (c * C + t * TT) * (c + t) + c`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `TT * (c - t) + (c * C + t * TT) * (c + t) + c =
                 c * ((TT / c) * (c - t) + (c * C + t * TT) * (&1 + t / c) + &1)`
   SUBST1_TAC THENL
   [(SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `c * ((c * TT - t * C) * u + (c * C + t * TT) * (v + a) + a) =
    (c * C + t * TT) * (c * v - t * (u + a)) + TT * u +
    (c * C + t * TT) * a * (c + t) + c * a` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C977CSUP_PROD_TAC `c * C + t * TT` `c * v - t * (u + a)` THEN
  C977CSUP_PROD_TAC `TT:real` `u - (c - t)` THEN
  C977CSUP_PRODLT_TAC `c * C + t * TT` `c + t` THEN
  C977CSUP_PRODLT_TAC `a - &1` `(c * C + t * TT) * (c + t) + c` THEN
  MATCH_MP_TAC C977CSUP_LT_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []);;

(* Lean: corner_axis_below *)
let C977CSUP_CORNER_AXIS_BELOW = prove
 (`forall c t C TT U V a.
     c977cc_normal c t /\ c977cc_normal C TT /\ &1 < a /\
     U <= (&87 / &50) * C - &2 * TT /\ V + a <= &2 * (C + TT) /\
     c * TT - t * C <= &0
     ==> --(c * TT - t * C) * U + (c * C + t * TT) * V < c977cc_boundary c t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C977CSUP_USE C977CSUP_POSITIVE_DOT [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_USE C977CSB_SINE_ORDER [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_USE C977CSB_O_AXIS_BELOW [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_NORMAL_TAC THEN
  SUBGOAL_THEN
   `--(c * TT - t * C) * ((&87 / &50) * C - &2 * TT) +
    (c * C + t * TT) * (&2 * (C + TT) - &1) =
    c * (&2 + (&13 / &50) * C * TT - C) +
    t * (&87 / &50 + (&13 / &50) * TT pow 2 - TT)` ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C977CSUP_PROD_TAC `--(c * TT - t * C)` `((&87 / &50) * C - &2 * TT) - U` THEN
  C977CSUP_PROD_TAC `c * C + t * TT` `&2 * (C + TT) - (V + a)` THEN
  C977CSUP_PRODLT_TAC `c * C + t * TT` `a - &1` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: remaining_section_bounds *)
let C977CSUP_REMAINING_SECTION_BOUNDS = prove
 (`forall c t C TT U V a.
     c977cc_normal c t /\ c977cc_normal C TT /\ &1 < a /\ &0 < TT /\
     V + a <= &2 * (C + TT) /\ &0 < c * TT - t * C /\
     c977cc_boundary c t < --(c * TT - t * C) * (U + a) + (c * C + t * TT) * V
     ==> C * U + TT * V < &1 /\ U < C - (&28 / &25) * TT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C977CSUP_USE C977CSUP_POSITIVE_DOT [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_USE C977CHA_LEFT_PROJECTION [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_USE C977CHA_NEAR_PROJECTION [`c:real`; `t:real`; `C:real`; `TT:real`] THEN
  C977CSUP_NORMAL_TAC THEN
  C977CSUP_PROD_TAC `c * C + t * TT` `&2 * (C + TT) - (V + a)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C977CSUP_PROD_TAC `c * TT - t * C` `(C * U + TT * V) - &1` THEN
   C977CSUP_PROD_TAC `c:real` `&2 * (C + TT) - (V + a)` THEN
   C977CSUP_PRODLT_TAC `C:real` `c * TT - t * C` THEN
   C977CSUP_PRODLT_TAC `a - &1` `c + C * (c * TT - t * C)` THEN
   SUBGOAL_THEN
    `c * (&2 * (C + TT) - &1) - (c * TT - t * C) - C * (c * TT - t * C) <=
     C * c977cc_boundary c t` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `c * (&2 * (C + TT) - &1) - (c * TT - t * C) - C * (c * TT - t * C) =
      C * (c * (&2 + (TT - &1) / C - TT) + t * (&1 + C))` SUBST1_TAC THENL
    [(SUBGOAL_THEN `~(C = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
     CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `C * c977cc_boundary c t <
     C * (--(c * TT - t * C) * (U + a) + (c * C + t * TT) * V)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `C * (--(c * TT - t * C) * (U + a) + (c * C + t * TT) * V) =
     c * V - (c * TT - t * C) - C * (c * TT - t * C) * a -
     (c * TT - t * C) * (C * U + TT * V - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `C pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C977CSUP_PROD_TAC `c * TT - t * C` `U - (C - (&28 / &25) * TT)` THEN
  C977CSUP_PRODLT_TAC `a - &1` `(c * TT - t * C) + (c * C + t * TT)` THEN
  SUBGOAL_THEN
   `--(c * TT - t * C) * (C - (&28 / &25) * TT + &1) +
    (c * C + t * TT) * (&2 * (C + TT) - &1) =
    c * (&2 - (&22 / &25) * TT pow 2 + C * TT - C - TT) +
    t * (&1 + TT pow 2 + (&22 / &25) * C * TT + C - TT)` ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;
