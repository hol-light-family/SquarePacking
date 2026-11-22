(* ========================================================================= *)
(* Port of Completion/Cases/C977/WallChains.lean                             *)
(* (with the needed parts of source/S12/WallGeometry.lean).                  *)
(*                                                                           *)
(* NearAxis q  :=  &0 <= c /\ abs s <= &1 / &10                              *)
(* normalDot q r := cq * cr + sq * sr,  normalCross q r := cq * sr - sq * cr *)
(* (both inlined).  turnFrame (c,s,u,v,a) = (--s, c, v, --u - a, a).         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* ------------------------------------------------------------------------- *)
(* Local ports from source/S12/WallGeometry.lean.                            *)
(* ------------------------------------------------------------------------- *)

(* Lean: S12.turnFrame_inside *)
let C977WC_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: S12.turnFrame_centerX *)
let C977WC_TURN_CX = prove
 (`forall c s u v a. lcx (--s) c v (--u - a) a = lcx c s u v a`,
  REWRITE_TAC[lcx] THEN REAL_ARITH_TAC);;

(* Lean: S12.turnFrame_centerY *)
let C977WC_TURN_CY = prove
 (`forall c s u v a. lcy (--s) c v (--u - a) a = lcy c s u v a`,
  REWRITE_TAC[lcy] THEN REAL_ARITH_TAC);;

(* Lean: S12.affine_endpoint_nonnegative *)
let C977WC_AFFINE_ENDPOINT = prove
 (`forall a d v. &0 < a /\ (forall t. &0 < t /\ t < a ==> &0 <= v + d * t) ==> &0 <= v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `k = abs d + &1` THEN
  SUBGOAL_THEN `&0 < k /\ d <= k - &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `t = min (a / &2) (--v / (&2 * k))` THEN
  SUBGOAL_THEN `&0 < --v / (&2 * k) /\ (--v / (&2 * k)) * (&2 * k) = --v`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t < a /\ t <= --v / (&2 * k)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT; REAL_MIN_LE] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `w = --v / (&2 * k)` THEN
  NLIN_TAC []);;

(* points given by face coordinates *)
let C977WC_ROT_INSIDE = prove
 (`forall c s u v a p r. c * c + s * s = &1 /\ u < p /\ p < u + a /\ v < r /\ r < v + a
     ==> linside c s u v a (c * p - s * r) (s * p + c * r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[linside] THEN
  SUBGOAL_THEN `c * (c * p - s * r) + s * (s * p + c * r) = p /\
                --s * (c * p - s * r) + c * (s * p + c * r) = r`
    (fun th -> REWRITE_TAC[th] THEN ASM_REAL_ARITH_TAC) THEN
  CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

(* Lean: S12.positive_frame_wall_bounds *)
let C977WC_POSITIVE_FRAME_WALL_BOUNDS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y)
     ==> a * (c + s) / &2 <= lcx c s u v a /\ a * (c + s) / &2 <= lcy c s u v a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lcx; lcy] THENL
   [SUBGOAL_THEN `&0 <= c * u - s * (v + a)` MP_TAC THENL
     [MATCH_MP_TAC C977WC_AFFINE_ENDPOINT THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + t) - s * (v + a - t)`;
                                    `s * (u + t) + c * (v + a - t)`]) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC C977WC_ROT_INSIDE THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN REAL_ARITH_TAC];
      DISCH_TAC THEN NLIN_TAC []];
    SUBGOAL_THEN `&0 <= s * u + c * v` MP_TAC THENL
     [MATCH_MP_TAC C977WC_AFFINE_ENDPOINT THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + t) - s * (v + t)`;
                                    `s * (u + t) + c * (v + t)`]) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC C977WC_ROT_INSIDE THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN REAL_ARITH_TAC];
      DISCH_TAC THEN NLIN_TAC []]]);;

(* ------------------------------------------------------------------------- *)
(* WallChains.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Lean: near_axis_cos *)
let C977WC_NEAR_AXIS_COS = prove
 (`forall c s. c * c + s * s = &1 /\ &0 <= c /\ abs s <= &1 / &10
         ==> &99 / &100 <= c /\ c <= &1`,
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN REPEAT STRIP_TAC THEN
  NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]);;

(* Lean: near_axis_wall_gain *)
let C977WC_NEAR_AXIS_WALL_GAIN = prove
 (`forall c s. c * c + s * s = &1 /\ &0 <= c /\ abs s <= &1 / &10
         ==> &1 + (&43 / &50) * abs s <= c + abs s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977WC_NEAR_AXIS_COS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs s * abs s = s * s /\ &0 <= abs s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS; GSYM REAL_ABS_MUL] THEN
    REWRITE_TAC[REAL_ABS_REFL; REAL_LE_SQUARE]; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: normal_pair_unit *)
let C977WC_NORMAL_PAIR_UNIT = prove
 (`forall cq sq cr sr. cq * cq + sq * sq = &1 /\ cr * cr + sr * sr = &1
     ==> (cq * cr + sq * sr) pow 2 + (cq * sr - sq * cr) pow 2 = &1`,
  REPEAT STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

(* Lean: near_axis_relative_bounds *)
let C977WC_NEAR_AXIS_RELATIVE_BOUNDS = prove
 (`forall cq sq cr sr.
     cq * cq + sq * sq = &1 /\ cr * cr + sr * sr = &1 /\
     (&0 <= cq /\ abs sq <= &1 / &10) /\ (&0 <= cr /\ abs sr <= &1 / &10)
     ==> &97 / &100 <= cq * cr + sq * sr /\ cq * cr + sq * sr <= &1 /\
         abs (cq * sr - sq * cr) <= &1 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`] C977WC_NEAR_AXIS_COS) THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`] C977WC_NEAR_AXIS_COS) THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `cr:real`; `sr:real`] C977WC_NORMAL_PAIR_UNIT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN
  NLIN_FACTS_TAC [] [`--(&1 / &100) <= sq * sr`; `&97 / &100 <= cq * cr + sq * sr`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `cq * sr - sq * cr`]);;

(* Lean: near_axis_pair_gain *)
let C977WC_NEAR_AXIS_PAIR_GAIN = prove
 (`forall cq sq cr sr.
     cq * cq + sq * sq = &1 /\ cr * cr + sr * sr = &1 /\
     (&0 <= cq /\ abs sq <= &1 / &10) /\ (&0 <= cr /\ abs sr <= &1 / &10)
     ==> &1 + (&43 / &50) * abs (sr - sq) <=
         (cq * cr + sq * sr) + abs (cq * sr - sq * cr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `cr:real`; `sr:real`] C977WC_NEAR_AXIS_RELATIVE_BOUNDS) THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`] C977WC_NEAR_AXIS_COS) THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`] C977WC_NEAR_AXIS_COS) THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `cr:real`; `sr:real`] C977WC_NORMAL_PAIR_UNIT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = cq * cr + sq * sr` THEN
  ABBREV_TAC `X = cq * sr - sq * cr` THEN
  SUBGOAL_THEN `X * (cq + cr) = (sr - sq) * (&1 + D)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "D"] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      not (is_var(rand(concl th)))))) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `abs X * (cq + cr) = abs (sr - sq) * (&1 + D)` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs (X * (cq + cr)) = abs ((sr - sq) * (&1 + D))` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs (cq + cr) = cq + cr /\ abs (&1 + D) = &1 + D`
      (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[REAL_ABS_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs X * abs X = X pow 2 /\ &0 <= abs X /\ &0 <= abs (sr - sq)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_POS; GSYM REAL_ABS_MUL; REAL_POW_2] THEN
    REWRITE_TAC[REAL_ABS_REFL; REAL_LE_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (&89 / &100) * abs X <= D + abs X` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: near_axis_left_wall *)
let C977WC_NEAR_AXIS_LEFT_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     (&0 <= c /\ abs s <= &1 / &10) /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y)
     ==> a / &2 + a * (&43 / &100) * abs s <= lcx c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a * (c + abs s) / &2 <= lcx c s u v a` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= s` THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`] THEN
      MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
        C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[REAL_ARITH `~(&0 <= s) ==> abs s = --s`] THEN
      MP_TAC(SPECL [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`]
        C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
      ASM_REWRITE_TAC[C977WC_TURN_INSIDE; C977WC_TURN_CX] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977WC_NEAR_AXIS_WALL_GAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  NLIN_TAC []);;

(* Lean: near_axis_right_wall *)
let C977WC_NEAR_AXIS_RIGHT_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     (&0 <= c /\ abs s <= &1 / &10) /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ x <= &4 /\ &0 <= y /\ y <= &4)
     ==> a / &2 + a * (&43 / &100) * abs s <= &4 - lcx c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s:real`; `&4 * c - u - a:real`; `v + &4 * s:real`; `a:real`]
    C977WC_NEAR_AXIS_LEFT_WALL) THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&4 - x:real`; `y:real`]) THEN
    ANTS_TAC THENL [POP_ASSUM MP_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
                    REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH `x = y ==> l <= x ==> l <= y`) THEN
    REWRITE_TAC[lcx] THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING]);;
