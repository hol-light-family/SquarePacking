(* ========================================================================= *)
(* Port of Compact/Geometry/C977CornerCubic.lean (Jatloe, N12-jatloe).        *)
(* Exact scalar comparisons for the negative corner coupling.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: Normal (definition) *)
let c977cc_normal = new_definition
 `c977cc_normal (c:real) t <=> &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1`;;

(* Lean: normal_bounds *)
let C977CC_NORMAL_BOUNDS = prove
 (`forall c t. c977cc_normal c t
     ==> &7 / &10 <= c /\ c <= &1 /\ &0 <= t /\ t <= &1 /\
         &1 <= c + t /\ c + t <= &10 / &7`,
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &10 <= c` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `t:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c + t` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c + t <= &10 / &7` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - t:real`; SQ_NONNEG `c + t - &10 / &7`]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: boundary (definition) *)
let c977cc_boundary = new_definition
 `c977cc_boundary (c:real) t = &1 + t + t * (&1 - t) / c`;;

(* Lean: H (definition) *)
let c977cc_h = new_definition
 `c977cc_h (f:real) g r = (&2 - g) + (&1 - &2 * f) * r + g * r pow 2 - r pow 3`;;

(* Lean: cubic_chord *)
let C977CC_CUBIC_CHORD = prove
 (`forall f g rho r. rho < &1 /\ rho <= r /\ r <= &1 /\
               &0 <= c977cc_h f g rho /\ &0 <= c977cc_h f g (&1) /\
               &0 <= r + &1 + rho - g
     ==> &0 <= c977cc_h f g r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(&1 - rho) * c977cc_h f g r =
    (&1 - r) * c977cc_h f g rho + (r - rho) * c977cc_h f g (&1) +
    (&1 - rho) * ((r - rho) * (&1 - r)) * (r + &1 + rho - g)`
  ASSUME_TAC THENL [REWRITE_TAC[c977cc_h] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - rho) * c977cc_h f g r` MP_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
   REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `rho < &1` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`c977cc_h f g r`,`X:real`) THEN REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: wing_coefficient *)
let C977CC_WING_COEFFICIENT = prove
 (`forall c t. c977cc_normal c t ==> &1 + t pow 2 + (&22 / &25) * c * t + c - t <= &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &625 - &475 * c - &1241 * c * c + &1109 * c * c * c`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (c - &7 / &10) * ((c - &9 / &10) * (c - &9 / &10))`
   MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `c - &9 / &10` REAL_LE_SQUARE) THEN
   MP_TAC(SPEC `&100 * (c - &9 / &10) - &1` REAL_LE_SQUARE) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * (&625 - &475 * c - &1241 * c * c + &1109 * c * c * c)`
  ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&625 * ((t * (&1 - &22 / &25 * c)) * (t * (&1 - &22 / &25 * c)) -
            (c * (&1 - c)) * (c * (&1 - c))) =
    (&1 - c) * (&625 - &475 * c - &1241 * c * c + &1109 * c * c * c)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c * (&1 - c) <= t * (&1 - &22 / &25 * c)` MP_TAC THENL
  [SUBGOAL_THEN `&0 <= t * (&1 - &22 / &25 * c) /\ &0 <= c * (&1 - c)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC
    `&625 * ((t * (&1 - &22 / &25 * c)) * (t * (&1 - &22 / &25 * c)) -
             (c * (&1 - c)) * (c * (&1 - c))) =
     (&1 - c) * (&625 - &475 * c - &1241 * c * c + &1109 * c * c * c)` THEN
   UNDISCH_TAC
    `&0 <= (&1 - c) * (&625 - &475 * c - &1241 * c * c + &1109 * c * c * c)` THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN
   SPEC_TAC(`(&1 - c) * (&625 - &475 * c - &1241 * c * c + &1109 * c * c * c)`,
            `R:real`) THEN
   SPEC_TAC(`t * (&1 - &22 / &25 * c)`,`P:real`) THEN
   SPEC_TAC(`c * (&1 - c)`,`Q:real`) THEN
   REPEAT STRIP_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  UNDISCH_TAC `c * c + t * t = &1` THEN REAL_ARITH_TAC);;

(* Lean: low_coefficient *)
let C977CC_LOW_COEFFICIENT = prove
 (`forall c t. c977cc_normal c t ==> &2 - (&22 / &25) * t pow 2 + c * t - c - t <= &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 - c <= &3 / &5 * t * t` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&3 / &5 * t * t - (&1 - c)) * (&1 - t) /\
                &0 <= (t * t) * t` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: high_tilt_coefficient *)
let C977CC_HIGH_TILT_COEFFICIENT = prove
 (`forall c t. c977cc_normal c t /\ &3 / &5 <= t
         ==> &2 - (&22 / &25) * t pow 2 + c * t - c - t <= &4 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal c t` THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 - c <= &3 / &5 * t * t` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&3 / &5 * t * t - (&1 - c)) * (&1 - t) /\
                &0 <= (t * t) * (t - &3 / &5) /\ &9 / &25 <= t * t`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
    ASM_REAL_ARITH_TAC;
    NLIN_TAC []]; ALL_TAC] THEN
  NLIN_TAC []);;
