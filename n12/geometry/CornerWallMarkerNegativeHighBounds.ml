(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerNegativeHighBounds.lean          *)
(* (namespace N12Compact.CornerWallMarkerNegativeHighBounds).                *)
(* The final negative-L high-angle scalar with the genuine marker caps.      *)
(* X, Y are cwml_x, cwml_y; G, boundary are cwmmb_g, cwmmb_boundary;         *)
(* g_order, g_upper, linear_margin are the CWMMB_ theorems.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/CornerWallMarkerLongitudinal.ml";;
needs "n12/geometry/CornerWallMarkerMixedBounds.ml";;

let CWMNHB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let CWMNHB_LE_CANCEL = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: seven_three (private) *)
let CWMNHB_SEVEN_THREE = prove
 (`forall l r. c977cc_normal l r ==> &7 <= &7 * l + &3 * r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= &21 * l - &20 * r`; `&0 <= r * (&21 * l - &20 * r)`] THEN
  REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
  NLIN_FACTS_TAC [] [`&0 < (&7 - (&7 * l + &3 * r)) * (&7 + (&7 * l + &3 * r))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: coefficients (private) *)
let CWMNHB_COEFFICIENTS = prove
 (`forall d t. c977cc_normal d t /\ t <= &3 / &5 ==> &2 <= cwml_x d t /\ cwml_y d t <= &13 / &20`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWML_X_DEF; CWML_Y_DEF] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&1 - d`]
   [`t pow 2 / &2 <= &1 - d`; `&0 <= d * (&1 - d)`; `&1 - d <= t pow 2`;
    `&0 <= t * (&1 - d)`; `&0 <= t * (&33 / &125 - (&3 / &20) * t)`;
    `&0 <= t * (&7 / &20 - (&33 / &125) * t)`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: chord_margin (private) *)
let CWMNHB_CHORD_MARGIN = prove
 (`forall d t l r. c977cc_normal d t /\ c977cc_normal l r
     ==> &0 <= ((l + d) pow 2 - (r + t) pow 2) / &2 - (&3 / &4) * (l + d) * (r + t) +
              (&7 / &4) * (r + t) - (&13 / &20) * (l + d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `r:real`] CWMNHB_SEVEN_THREE) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] CWMNHB_SEVEN_THREE) THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `d:real`; `t:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(l + d) - (r + t)`]
   [`&0 <= (l + d) - (r + t)`; `(l + d) - (r + t) <= &2`;
    `&0 <= &4 - (l + d) pow 2 - (r + t) pow 2`;
    `&0 <= (r + t) - &7 / &5 + (&7 / &10) * ((l + d) - (r + t))`;
    `&0 <= (((l + d) - (r + t)) + &11 / &10) *
           ((r + t) - &7 / &5 + (&7 / &10) * ((l + d) - (r + t)))`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `(l + d) - (r + t)`]);;

(* Lean: response (private def) *)
let CWMNHB_RESPONSE_DEF = new_definition
 `cwmnhb_response (d:real) (t:real) (l:real) (r:real) =
    &1 + l * (cwmmb_g d t - t / d - cwml_x d t) + (t / d) * l pow 2 + l * r - r * cwml_y d t`;;

(* Lean: response_order (private) *)
let CWMNHB_RESPONSE_ORDER = prove
 (`forall d t l r. c977cc_normal d t /\ c977cc_normal l r /\ t <= r /\
     t <= &3 / &5 /\ &4 / &5 <= d
     ==> cwmnhb_response d t d t <= cwmnhb_response d t l r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] CWMNHB_COEFFICIENTS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] CWMMB_G_UPPER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`] CWMNHB_CHORD_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(d = &0) /\ t / d <= &3 / &4 /\ &0 <= t / d` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`t:real`; `&3 / &4`; `d:real`] REAL_LE_LDIV_EQ) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  let J = `((l + d) pow 2 - (r + t) pow 2) / &2 +
           (r + t) * (cwml_x d t - cwmmb_g d t + t / d) -
           (t / d) * (l + d) * (r + t) - cwml_y d t * (l + d)` in
  let sub tm = subst [J,`JJ:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= (r + t) * (cwml_x d t - cwmmb_g d t - &1)`;
    `&0 <= (&3 / &4 - t / d) * (r + t)`;
    `&0 <= ((&3 / &4 - t / d) * (r + t)) * ((l + d) - &1)`;
    `&0 <= (&13 / &20 - cwml_y d t) * (l + d)`;
    `&0 <= JJ`; `&0 <= (r - t) * JJ`]) THEN
  SUBGOAL_THEN (sub `(l + d) * (cwmnhb_response d t l r - cwmnhb_response d t d t) =
                     (r - t) * JJ`) ASSUME_TAC THENL
   [REWRITE_TAC[CWMNHB_RESPONSE_DEF] THEN
    MAP_EVERY UNDISCH_TAC [`l pow 2 + r pow 2 = &1`; `d pow 2 + t pow 2 = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC CWMNHB_LE_CANCEL THEN EXISTS_TAC `l + d` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* Lean: endpoint (private) *)
let CWMNHB_ENDPOINT = prove
 (`forall d t. c977cc_normal d t /\ t <= &3 / &5 /\ &4 / &5 <= d
         ==> &0 <= cwmnhb_response d t d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `d:real`; `t:real`; `d:real`; `t:real`]
    CWMMB_LINEAR_MARGIN) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * cwml_x d t + t * cwml_y d t = &3 * d + (&457 / &500) * t - &1`
    ASSUME_TAC THENL
   [REWRITE_TAC[CWML_X_DEF; CWML_Y_DEF] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `cwmnhb_response d t d t -
                (&1 + d * (cwmmb_g d t + t + (&1 - t) / d - &3) - t * (&1 - d)) =
                --(&1) + t + &3 * d - d * cwml_x d t - t * cwml_y d t` ASSUME_TAC THENL
   [REWRITE_TAC[CWMNHB_RESPONSE_DEF] THEN UNDISCH_TAC `~(d = &0)` THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: margin *)
let CWMNHB_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= r /\ t <= &3 / &5 /\ &4 / &5 <= d
     ==> &0 <= &1 + (l / c) * cwmmb_boundary c s + (l / c) * (s * l + c * r) -
              r * cwml_y d t - l * cwml_x d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWMMB_G_ORDER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] CWMNHB_ENDPOINT) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`] CWMNHB_RESPONSE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(d = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s / c <= t / d` ASSUME_TAC THENL
   [MATCH_MP_TAC CWMNHB_LE_CANCEL THEN EXISTS_TAC `c * d` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c * d) * (t / d - s / c) = c * t - d * s` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(c = &0)`; `~(d = &0)`] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= c * (t - s)`; `&0 <= s * (c - d)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + (l / c) * cwmmb_boundary c s + (l / c) * (s * l + c * r) -
     r * cwml_y d t - l * cwml_x d t) - cwmnhb_response d t l r =
    l * (cwmmb_g c s - cwmmb_g d t) + (t / d - s / c) * l * (&1 - l)` ASSUME_TAC THENL
   [REWRITE_TAC[CWMNHB_RESPONSE_DEF; CWMMB_G_DEF] THEN
    MAP_EVERY UNDISCH_TAC [`~(c = &0)`; `~(d = &0)`] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= l * (cwmmb_g c s - cwmmb_g d t)`;
    `&0 <= (t / d - s / c) * l`; `&0 <= ((t / d - s / c) * l) * (&1 - l)`] THEN
  NLIN_TAC ~deg2:false []);;
