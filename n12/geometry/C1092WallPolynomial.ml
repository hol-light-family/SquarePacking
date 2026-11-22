(* ========================================================================= *)
(* Port of Compact/Geometry/C1092WallPolynomial.lean (Jatloe, N12-jatloe).    *)
(* Uniform exclusion of the 72 wall systems.                                  *)
(* Fin n indices are represented by numerals i with i < n; the vectors       *)
(* targetX, targetY, upperX, upperH, expansionPoint by conditional chains.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: C, S, D (definitions) *)
let c1092wp_C = new_definition `c1092wp_C (t:real) = &1 - t pow 2`;;
let c1092wp_S = new_definition `c1092wp_S (t:real) = &2 * t`;;
let c1092wp_D = new_definition `c1092wp_D (t:real) = &1 + t pow 2`;;

(* Lean: residual (definition) *)
let c1092wp_residual = new_definition
 `c1092wp_residual (x:real) (y:real) (t:real) (z0:real) (z1:real) (z2:real)
                   (bface:num) (pface:num) (i:num) =
    if i = 0 then &1 / &2 - z0 else
    if i = 1 then &1 / &2 + z0 else
    if i = 2 then &1 / &2 - z1 else
    if i = 3 then &1 / &2 + z1 else
    if i = 4 then z2 else
    if i = 5 then &1 - z2 else
    if i = 6 then --(c1092wp_C t + c1092wp_S t) / &2 - c1092wp_C t * z0 +
                  c1092wp_S t * z1 + (&457 / &500) * c1092wp_D t * z2 else
    if i = 7 then c1092wp_C t * z0 - c1092wp_S t * z1 +
                  (&43 / &500) * c1092wp_D t * z2 else
    if i = 8 then c1092wp_S t * z0 + c1092wp_C t * z1 else
    if i = 9 then
      (if bface = 0 then --(c1092wp_D t) / &2 - c1092wp_D t * z0 + c1092wp_S t * z2
       else --(c1092wp_D t) / &2 - c1092wp_D t * z1 + c1092wp_C t * z2) else
    if pface = 0 then
      --(c1092wp_D t) / &2 + c1092wp_D t * z0 +
      ((x - &457 / &500) * c1092wp_C t - (&2 - y) * c1092wp_S t) * z2 else
    if pface = 1 then
      --(c1092wp_D t) / &2 - c1092wp_D t * z0 +
      (--(x - &457 / &500) * c1092wp_C t + (&2 - y) * c1092wp_S t) * z2 else
    --(c1092wp_D t) / &2 - c1092wp_D t * z1 +
    ((x - &457 / &500) * c1092wp_S t + (&2 - y) * c1092wp_C t) * z2`;;

(* Lean: WallSystem (definition) *)
let c1092wp_wallsystem = new_definition
 `c1092wp_wallsystem x y t z0 z1 z2 bface pface <=>
    forall i. i < 11 ==>
        (if i < 6 then &0 < c1092wp_residual x y t z0 z1 z2 bface pface i
         else &0 <= c1092wp_residual x y t z0 z1 z2 bface pface i)`;;

(* Lean: residual_nonneg *)
let C1092WP_RESIDUAL_NONNEG = prove
 (`forall x y t z0 z1 z2 bface pface i.
     c1092wp_wallsystem x y t z0 z1 z2 bface pface /\ i < 11
     ==> &0 <= c1092wp_residual x y t z0 z1 z2 bface pface i`,
  REWRITE_TAC[c1092wp_wallsystem] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN SIMP_TAC[REAL_LT_IMP_LE]);;

(* the residual i of a system with literal faces, written out *)
let C1092WP_RES k =
  let th = SPECL [`x:real`; `y:real`; `t:real`; `z0:real`; `z1:real`; `z2:real`;
                  `bface:num`; `pface:num`; mk_small_numeral k] C1092WP_RESIDUAL_NONNEG in
  GEN_ALL(REWRITE_RULE[c1092wp_residual; ARITH] th);;

let C1092WP_RES_TAC ks =
  MAP_EVERY (fun k -> FIRST_ASSUM(fun sys ->
     MP_TAC(REWRITE_RULE[ARITH] (MATCH_MP (C1092WP_RES k) sys)))) ks;;

(* Lean: reciprocal_band *)
let C1092WP_RECIPROCAL_BAND = prove
 (`forall x y t z0 z1 z2 bface pface.
     c1092wp_wallsystem x y t z0 z1 z2 bface pface ==> &0 < z2 /\ z2 < &1`,
  REWRITE_TAC[c1092wp_wallsystem] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `4`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `5`) THEN
  REWRITE_TAC[c1092wp_residual; ARITH] THEN REAL_ARITH_TAC);;

(* Lean: targetX, targetY (definitions; Fin 12 vectors) *)
let c1092wp_targetX = new_definition
 `c1092wp_targetX (i:num) =
    if i = 0 then &457 / &500 else if i = 1 then &457 / &500 else
    if i = 2 then &23 / &25 else if i = 3 then &23 / &25 else
    if i = 4 then &47 / &50 else if i = 5 then &47 / &50 else
    if i = 6 then &24 / &25 else if i = 7 then &24 / &25 else
    if i = 8 then &49 / &50 else if i = 9 then &49 / &50 else
    if i = 10 then &1 else &1`;;
let c1092wp_targetY = new_definition
 `c1092wp_targetY (i:num) =
    if i = 0 then &837 / &500 else if i = 1 then &1999 / &1000 else
    if i = 2 then &1667 / &1000 else if i = 3 then &997 / &500 else
    if i = 4 then &823 / &500 else if i = 5 then &1973 / &1000 else
    if i = 6 then &1627 / &1000 else if i = 7 then &39 / &20 else
    if i = 8 then &1611 / &1000 else if i = 9 then &481 / &250 else
    if i = 10 then &803 / &500 else &947 / &500`;;

(* case split on a bounded index *)
let C1092WP_ENUM_TAC v n =
  let tm = list_mk_disj (map (fun k -> mk_eq(v, mk_small_numeral k)) (0--(n-1))) in
  SUBGOAL_THEN tm MP_TAC THENL
  [UNDISCH_TAC (mk_binop `(<):num->num->bool` v (mk_small_numeral n)) THEN ARITH_TAC;
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)];;

(* D t > 0 and the two nonnegative frame factors on [0,1] *)
let C1092WP_D_POS = prove
 (`forall t. &0 < c1092wp_D t`,
  GEN_TAC THEN REWRITE_TAC[c1092wp_D] THEN
  MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let C1092WP_CS_NONNEG = prove
 (`forall t. &0 <= t /\ t <= &1 ==> &0 <= c1092wp_C t /\ &0 <= c1092wp_S t`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092wp_C; c1092wp_S] THEN
  CONJ_TAC THENL [NLIN_TAC []; ASM_REAL_ARITH_TAC]);;

(* Lean: excludes_opposite_faces *)
let C1092WP_EXCLUDES_OPPOSITE_FACES = prove
 (`forall x y t z0 z1 z2.
     (x - &457 / &500) pow 2 + (y - &1) pow 2 <= &1 /\
     c1092wp_wallsystem x y t z0 z1 z2 0 0 ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092WP_RECIPROCAL_BAND) THEN
  MP_TAC(SPEC `t:real` C1092WP_D_POS) THEN DISCH_TAC THEN
  ABBREV_TAC `L = (x - &457 / &500) * c1092wp_C t + (y - &1) * c1092wp_S t` THEN
  SUBGOAL_THEN `L pow 2 + ((x - &457 / &500) * c1092wp_S t - (y - &1) * c1092wp_C t) pow 2 =
                ((x - &457 / &500) pow 2 + (y - &1) pow 2) * c1092wp_D t pow 2`
  ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN REWRITE_TAC[c1092wp_C; c1092wp_S; c1092wp_D] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L pow 2 <= c1092wp_D t pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `(x - &457 / &500) * c1092wp_S t - (y - &1) * c1092wp_C t`
     REAL_LE_POW_2) THEN
   MP_TAC(SPEC `c1092wp_D t` REAL_LE_POW_2) THEN
   UNDISCH_TAC `(x - &457 / &500) pow 2 + (y - &1) pow 2 <= &1` THEN
   UNDISCH_TAC `L pow 2 + ((x - &457 / &500) * c1092wp_S t - (y - &1) * c1092wp_C t) pow 2 =
                ((x - &457 / &500) pow 2 + (y - &1) pow 2) * c1092wp_D t pow 2` THEN
   SPEC_TAC(`(x - &457 / &500) pow 2 + (y - &1) pow 2`,`P:real`) THEN
   SPEC_TAC(`((x - &457 / &500) * c1092wp_S t - (y - &1) * c1092wp_C t) pow 2`,`M:real`) THEN
   SPEC_TAC(`c1092wp_D t pow 2`,`Q:real`) THEN
   REPEAT STRIP_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `L <= c1092wp_D t` ASSUME_TAC THENL
  [UNDISCH_TAC `L pow 2 <= c1092wp_D t pow 2` THEN
   UNDISCH_TAC `&0 < c1092wp_D t` THEN
   SPEC_TAC(`c1092wp_D t`,`Q:real`) THEN REPEAT STRIP_TAC THEN
   NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z2 * (c1092wp_D t - L) /\ &0 < c1092wp_D t * (&1 - z2)`
  MP_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092WP_RES_TAC [9; 10] THEN
  EXPAND_TAC "L" THEN REAL_ARITH_TAC);;

(* Lean: target_distance *)
let C1092WP_TARGET_DISTANCE = prove
 (`forall i. i < 12
       ==> (c1092wp_targetX i - &457 / &500) pow 2 + (c1092wp_targetY i - &1) pow 2 <= &1`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `i:num` 12 THEN
  REWRITE_TAC[c1092wp_targetX; c1092wp_targetY; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: excludes_target_bface0 *)
let C1092WP_EXCLUDES_TARGET_BFACE0 = prove
 (`forall i t z0 z1 z2. i < 12 /\
     c1092wp_wallsystem (c1092wp_targetX i) (c1092wp_targetY i) t z0 z1 z2 0 0 ==> false`,
  MESON_TAC[C1092WP_EXCLUDES_OPPOSITE_FACES; C1092WP_TARGET_DISTANCE]);;

(* Lean: margin (definition) *)
let c1092wp_margin = new_definition
 `c1092wp_margin (x:real) (h:real) (t:real) =
    &1 - x + &2 * h * t + (&2 * x - &457 / &125) * t pow 2 +
    (&4 - &2 * h) * t pow 3 - (&1 + x) * t pow 4`;;

let C1092WP_NONNEG_OF_MUL = prove
 (`forall k p. &0 < k /\ &0 <= k * p ==> &0 <= p`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: quartic_taylor_nonneg *)
let C1092WP_QUARTIC_TAYLOR_NONNEG = prove
 (`forall a0 a1 a2 a3 a4 r t.
     &0 <= t /\ t <= &1 /\ a4 <= &0 /\
     &0 < a2 + &2 * a3 * r + &3 * a4 * r pow 2 /\
     &0 <= a3 + a4 * (&1 + &2 * r) /\
     (a1 + &2 * a2 * r + &3 * a3 * r pow 2 + &4 * a4 * r pow 3) pow 2 <=
       &4 * (a2 + &2 * a3 * r + &3 * a4 * r pow 2) *
       (a0 + a1 * r + a2 * r pow 2 + a3 * r pow 3 + a4 * r pow 4)
     ==> &0 <= a0 + a1 * t + a2 * t pow 2 + a3 * t pow 3 + a4 * t pow 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092WP_NONNEG_OF_MUL THEN
  EXISTS_TAC `&4 * (a2 + &2 * a3 * r + &3 * a4 * r pow 2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&4 * (a2 + &2 * a3 * r + &3 * a4 * r pow 2)) *
      (a0 + a1 * t + a2 * t pow 2 + a3 * t pow 3 + a4 * t pow 4) =
    (&2 * (a2 + &2 * a3 * r + &3 * a4 * r pow 2) * (t - r) +
     (a1 + &2 * a2 * r + &3 * a3 * r pow 2 + &4 * a4 * r pow 3)) pow 2 +
    (&4 * (a2 + &2 * a3 * r + &3 * a4 * r pow 2) *
       (a0 + a1 * r + a2 * r pow 2 + a3 * r pow 3 + a4 * r pow 4) -
     (a1 + &2 * a2 * r + &3 * a3 * r pow 2 + &4 * a4 * r pow 3) pow 2) +
    &4 * (a2 + &2 * a3 * r + &3 * a4 * r pow 2) * t *
      ((a3 + a4 * (&1 + &2 * r)) + --a4 * (&1 - t)) * (t - r) pow 2`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN TRY(ASM_REAL_ARITH_TAC) THEN
  MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

(* Lean: cubic_taylor_nonneg *)
let C1092WP_CUBIC_TAYLOR_NONNEG = prove
 (`forall a0 a1 a2 a3 r t.
     t <= &1 /\ a3 <= &0 /\
     &0 < a2 + a3 * (&1 + &2 * r) /\
     (a1 + &2 * a2 * r + &3 * a3 * r pow 2) pow 2 <=
       &4 * (a2 + a3 * (&1 + &2 * r)) * (a0 + a1 * r + a2 * r pow 2 + a3 * r pow 3)
     ==> &0 <= a0 + a1 * t + a2 * t pow 2 + a3 * t pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092WP_NONNEG_OF_MUL THEN
  EXISTS_TAC `&4 * (a2 + a3 * (&1 + &2 * r))` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&4 * (a2 + a3 * (&1 + &2 * r))) * (a0 + a1 * t + a2 * t pow 2 + a3 * t pow 3) =
    (&2 * (a2 + a3 * (&1 + &2 * r)) * (t - r) +
     (a1 + &2 * a2 * r + &3 * a3 * r pow 2)) pow 2 +
    (&4 * (a2 + a3 * (&1 + &2 * r)) * (a0 + a1 * r + a2 * r pow 2 + a3 * r pow 3) -
     (a1 + &2 * a2 * r + &3 * a3 * r pow 2) pow 2) +
    &4 * (a2 + a3 * (&1 + &2 * r)) * --a3 * (&1 - t) * (t - r) pow 2`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* Lean: upperX, upperH, expansionPoint (definitions; Fin 5 vectors) *)
let c1092wp_upperX = new_definition
 `c1092wp_upperX (i:num) =
    if i = 0 then &457 / &500 else if i = 1 then &23 / &25 else
    if i = 2 then &47 / &50 else if i = 3 then &24 / &25 else &49 / &50`;;
let c1092wp_upperH = new_definition
 `c1092wp_upperH (i:num) =
    if i = 0 then &1 / &1000 else if i = 1 then &3 / &500 else
    if i = 2 then &27 / &1000 else if i = 3 then &1 / &20 else &19 / &250`;;
let c1092wp_expansionPoint = new_definition
 `c1092wp_expansionPoint (i:num) =
    if i = 0 then &83 / &200 else if i = 1 then &41 / &100 else
    if i = 2 then &39 / &100 else if i = 3 then &9 / &25 else &13 / &40`;;

(* Lean: upper_five_margin *)
let C1092WP_UPPER_FIVE_MARGIN = prove
 (`forall i t. i < 5 /\ &0 <= t /\ t <= &1
         ==> &0 <= c1092wp_margin (c1092wp_upperX i) (c1092wp_upperH i) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1 - c1092wp_upperX i`; `&2 * c1092wp_upperH i`;
                `&2 * c1092wp_upperX i - &457 / &125`; `&4 - &2 * c1092wp_upperH i`;
                `--(&1 + c1092wp_upperX i)`; `c1092wp_expansionPoint i`; `t:real`]
    C1092WP_QUARTIC_TAYLOR_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
  [C1092WP_ENUM_TAC `i:num` 5 THEN
   REWRITE_TAC[c1092wp_upperX; c1092wp_upperH; c1092wp_expansionPoint; ARITH] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV;
   REWRITE_TAC[c1092wp_margin] THEN REAL_ARITH_TAC]);;

(* Lean: upper_endpoint_margin *)
let C1092WP_UPPER_ENDPOINT_MARGIN = prove
 (`forall t. &0 <= t /\ t <= &1 ==> &0 <= c1092wp_margin (&1) (&53 / &500) t`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&53 / &250`; `--(&207 / &125)`; `&947 / &250`; `--(&2)`;
                `&7 / &25`; `t:real`] C1092WP_CUBIC_TAYLOR_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= t * (&53 / &250 - &207 / &125 * t + &947 / &250 * t pow 2 -
                           &2 * t pow 3)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   REWRITE_TAC[c1092wp_margin] THEN REAL_ARITH_TAC]);;

(* Lean: margin_mono_height *)
let C1092WP_MARGIN_MONO_HEIGHT = prove
 (`forall x h H t. h <= H /\ &0 <= t /\ t <= &1 /\ &0 <= c1092wp_margin x h t
             ==> &0 <= c1092wp_margin x H t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&2 * (H - h) * t) * (&1 - t pow 2)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    NLIN_TAC []];
   ALL_TAC] THEN
  UNDISCH_TAC `&0 <= c1092wp_margin x h t` THEN
  REWRITE_TAC[c1092wp_margin] THEN REAL_ARITH_TAC);;

(* Lean: UpperTargetRegion (definition) *)
let c1092wp_upper_region = new_definition
 `c1092wp_upper_region x h <=>
    (exists i. i < 5 /\ x = c1092wp_upperX i /\ c1092wp_upperH i <= h) \/
    (x = &1 /\ &53 / &500 <= h)`;;

(* Lean: region_margin *)
let C1092WP_REGION_MARGIN = prove
 (`forall x h t. c1092wp_upper_region x h /\ &0 <= t /\ t <= &1
           ==> &0 <= c1092wp_margin x h t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092wp_upper_region] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092WP_MARGIN_MONO_HEIGHT THENL
  [EXISTS_TAC `c1092wp_upperH i` THEN ASM_SIMP_TAC[C1092WP_UPPER_FIVE_MARGIN];
   EXISTS_TAC `&53 / &500` THEN ASM_SIMP_TAC[C1092WP_UPPER_ENDPOINT_MARGIN]]);;

(* Lean: target_region *)
let C1092WP_TARGET_REGION = prove
 (`forall i. i < 12 ==> c1092wp_upper_region (c1092wp_targetX i) (&2 - c1092wp_targetY i)`,
  let up k = DISJ1_TAC THEN EXISTS_TAC (mk_small_numeral k) THEN
    REWRITE_TAC[c1092wp_upperX; c1092wp_upperH; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV in
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `i:num` 12 THEN
  REWRITE_TAC[c1092wp_upper_region; c1092wp_targetX; c1092wp_targetY; ARITH] THENL
  [up 0; up 0; up 1; up 1; up 2; up 2; up 3; up 3; up 4; up 4;
   DISJ2_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
   DISJ2_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* Lean: excludes_adjacent_faces *)
let C1092WP_EXCLUDES_ADJACENT_FACES = prove
 (`forall x y t z0 z1 z2.
     &0 <= t /\ t <= &1 /\ &0 <= c1092wp_margin x (&2 - y) t /\
     c1092wp_wallsystem x y t z0 z1 z2 1 0 ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092WP_RECIPROCAL_BAND) THEN
  MP_TAC(SPEC `t:real` C1092WP_D_POS) THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:real` C1092WP_CS_NONNEG) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c1092wp_C t + c1092wp_S t` ASSUME_TAC THENL
  [REWRITE_TAC[c1092wp_C; c1092wp_S] THEN NLIN_TAC []; ALL_TAC] THEN
  ABBREV_TAC `L = c1092wp_D t * (c1092wp_C t + c1092wp_S t)` THEN
  ABBREV_TAC `E = (&457 / &500) * c1092wp_D t pow 2 +
                  (x - &457 / &500) * c1092wp_C t pow 2 +
                  (y - &1) * c1092wp_C t * c1092wp_S t` THEN
  SUBGOAL_THEN `L - E = c1092wp_margin x (&2 - y) t` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["L"; "E"] THEN
   REWRITE_TAC[c1092wp_C; c1092wp_S; c1092wp_D; c1092wp_margin] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L * (&1 - z2) /\ &0 <= z2 * (L - E)` MP_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092WP_RES_TAC [6; 9; 10] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= c1092wp_D t * (--(c1092wp_C t + c1092wp_S t) / &2 -
                  c1092wp_C t * z0 + c1092wp_S t * z1 + (&457 / &500) * c1092wp_D t * z2) /\
                &0 <= c1092wp_S t * (--(c1092wp_D t) / &2 - c1092wp_D t * z1 +
                  c1092wp_C t * z2) /\
                &0 <= c1092wp_C t * (--(c1092wp_D t) / &2 + c1092wp_D t * z0 +
                  ((x - &457 / &500) * c1092wp_C t - (&2 - y) * c1092wp_S t) * z2)`
  MP_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  UNDISCH_TAC `&0 < L * (&1 - z2) /\ &0 <= z2 * (L - E)` THEN
  MAP_EVERY EXPAND_TAC ["L"; "E"] THEN REAL_ARITH_TAC);;

(* Lean: excludes_target_pface0 *)
let C1092WP_EXCLUDES_TARGET_PFACE0 = prove
 (`forall i bface t z0 z1 z2.
     i < 12 /\ bface < 2 /\ &0 <= t /\ t <= &1 /\
     c1092wp_wallsystem (c1092wp_targetX i) (c1092wp_targetY i) t z0 z1 z2 bface 0
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092WP_ENUM_TAC `bface:num` 2 THENL
  [ASM_MESON_TAC[C1092WP_EXCLUDES_TARGET_BFACE0];
   MATCH_MP_TAC C1092WP_EXCLUDES_ADJACENT_FACES THEN
   MAP_EVERY EXISTS_TAC [`c1092wp_targetX i`; `c1092wp_targetY i`; `t:real`;
                         `z0:real`; `z1:real`; `z2:real`] THEN
   ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092WP_REGION_MARGIN THEN
   ASM_SIMP_TAC[C1092WP_TARGET_REGION]]);;

(* Lean: excludes_pface1 *)
let C1092WP_EXCLUDES_PFACE1 = prove
 (`forall x y t z0 z1 z2 bface.
     &0 <= t /\ t <= &1 /\ (&1 - x) pow 2 + (&2 - y) pow 2 <= &1 / &4 /\
     c1092wp_wallsystem x y t z0 z1 z2 bface 1 ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092WP_RECIPROCAL_BAND) THEN
  MP_TAC(SPEC `t:real` C1092WP_D_POS) THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:real` C1092WP_CS_NONNEG) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = (&1 - x) * c1092wp_C t + (&2 - y) * c1092wp_S t` THEN
  SUBGOAL_THEN `L pow 2 + ((&1 - x) * c1092wp_S t - (&2 - y) * c1092wp_C t) pow 2 =
                ((&1 - x) pow 2 + (&2 - y) pow 2) * c1092wp_D t pow 2`
  ASSUME_TAC THENL
  [EXPAND_TAC "L" THEN REWRITE_TAC[c1092wp_C; c1092wp_S; c1092wp_D] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * L) pow 2 <= c1092wp_D t pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `(&1 - x) * c1092wp_S t - (&2 - y) * c1092wp_C t` REAL_LE_POW_2) THEN
   MP_TAC(SPEC `c1092wp_D t` REAL_LE_POW_2) THEN
   UNDISCH_TAC `(&1 - x) pow 2 + (&2 - y) pow 2 <= &1 / &4` THEN
   UNDISCH_TAC `L pow 2 + ((&1 - x) * c1092wp_S t - (&2 - y) * c1092wp_C t) pow 2 =
                ((&1 - x) pow 2 + (&2 - y) pow 2) * c1092wp_D t pow 2` THEN
   SPEC_TAC(`(&1 - x) pow 2 + (&2 - y) pow 2`,`P:real`) THEN
   SPEC_TAC(`((&1 - x) * c1092wp_S t - (&2 - y) * c1092wp_C t) pow 2`,`M:real`) THEN
   SPEC_TAC(`c1092wp_D t pow 2`,`Q:real`) THEN
   REPEAT STRIP_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * L <= c1092wp_D t` ASSUME_TAC THENL
  [UNDISCH_TAC `(&2 * L) pow 2 <= c1092wp_D t pow 2` THEN
   UNDISCH_TAC `&0 < c1092wp_D t` THEN
   SPEC_TAC(`c1092wp_D t`,`Q:real`) THEN SPEC_TAC(`&2 * L`,`L2:real`) THEN
   REPEAT STRIP_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  ABBREV_TAC `R = c1092wp_D t pow 2 / &2` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_LT_DIV THEN
   ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092wp_D t * L <= R` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN
   SUBGOAL_THEN `&0 <= c1092wp_D t * (c1092wp_D t - &2 * L)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z2 * (R - c1092wp_D t * L) /\ &0 < R * (&1 - z2)` MP_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092WP_RES_TAC [7; 8; 10] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= c1092wp_C t * (c1092wp_C t * z0 - c1092wp_S t * z1 +
                  (&43 / &500) * c1092wp_D t * z2) /\
                &0 <= c1092wp_S t * (c1092wp_S t * z0 + c1092wp_C t * z1) /\
                &0 <= c1092wp_D t * (--(c1092wp_D t) / &2 - c1092wp_D t * z0 +
                  (--(x - &457 / &500) * c1092wp_C t + (&2 - y) * c1092wp_S t) * z2)`
  MP_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  UNDISCH_TAC `&0 <= z2 * (R - c1092wp_D t * L) /\ &0 < R * (&1 - z2)` THEN
  MAP_EVERY EXPAND_TAC ["L"; "R"] THEN
  REWRITE_TAC[c1092wp_C; c1092wp_S; c1092wp_D] THEN REAL_ARITH_TAC);;

(* Lean: target_half_distance *)
let C1092WP_TARGET_HALF_DISTANCE = prove
 (`forall i. i < 12
       ==> (&1 - c1092wp_targetX i) pow 2 + (&2 - c1092wp_targetY i) pow 2 <= &1 / &4`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `i:num` 12 THEN
  REWRITE_TAC[c1092wp_targetX; c1092wp_targetY; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: pface2_cubic_nonneg *)
let C1092WP_PFACE2_CUBIC_NONNEG = prove
 (`forall t. t <= &1
       ==> &0 <= &53 / &500 - (&447 / &500) * t + (&1053 / &500) * t pow 2 -
                 (&447 / &500) * t pow 3`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&53 / &500`; `--(&447 / &500)`; `&1053 / &500`; `--(&447 / &500)`;
                `&1 / &4`; `t:real`] C1092WP_CUBIC_TAYLOR_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: excludes_pface2 *)
let C1092WP_EXCLUDES_PFACE2 = prove
 (`forall x y t z0 z1 z2 bface.
     &0 <= t /\ t <= &1 /\ x <= &1 /\ &2 - y <= &197 / &500 /\
     c1092wp_wallsystem x y t z0 z1 z2 bface 2 ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092WP_RECIPROCAL_BAND) THEN
  MP_TAC(SPEC `t:real` C1092WP_D_POS) THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:real` C1092WP_CS_NONNEG) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `W = c1092wp_D t * (x * c1092wp_S t + (&2 - y) * c1092wp_C t)` THEN
  ABBREV_TAC `R = (c1092wp_D t pow 2 + c1092wp_S t * (c1092wp_C t + c1092wp_S t)) / &2` THEN
  SUBGOAL_THEN `&0 < R` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN
   SUBGOAL_THEN `&0 < c1092wp_D t pow 2 /\
                 &0 <= c1092wp_S t * (c1092wp_C t + c1092wp_S t)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `W <= R` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 - t) * (&53 / &500 - (&447 / &500) * t +
                   (&1053 / &500) * t pow 2 - (&447 / &500) * t pow 3)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[C1092WP_PFACE2_CUBIC_NONNEG] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `R - c1092wp_D t * (c1092wp_S t + (&197 / &500) * c1092wp_C t) =
       (&1 - t) * (&53 / &500 - (&447 / &500) * t + (&1053 / &500) * t pow 2 -
                   (&447 / &500) * t pow 3)` (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[c1092wp_C; c1092wp_S; c1092wp_D] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= c1092wp_D t * ((&1 - x) * c1092wp_S t +
                   (&197 / &500 - (&2 - y)) * c1092wp_C t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   EXPAND_TAC "W" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z2 * (R - W) /\ &0 < R * (&1 - z2)` MP_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092WP_RES_TAC [6; 8; 10] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= c1092wp_S t * (--(c1092wp_C t + c1092wp_S t) / &2 -
                  c1092wp_C t * z0 + c1092wp_S t * z1 + (&457 / &500) * c1092wp_D t * z2) /\
                &0 <= c1092wp_C t * (c1092wp_S t * z0 + c1092wp_C t * z1) /\
                &0 <= c1092wp_D t * (--(c1092wp_D t) / &2 - c1092wp_D t * z1 +
                  ((x - &457 / &500) * c1092wp_S t + (&2 - y) * c1092wp_C t) * z2)`
  MP_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  UNDISCH_TAC `&0 <= z2 * (R - W) /\ &0 < R * (&1 - z2)` THEN
  MAP_EVERY EXPAND_TAC ["W"; "R"] THEN
  REWRITE_TAC[c1092wp_C; c1092wp_S; c1092wp_D] THEN REAL_ARITH_TAC);;

(* Lean: target_rectangle *)
let C1092WP_TARGET_RECTANGLE = prove
 (`forall i. i < 12 ==> c1092wp_targetX i <= &1 /\ &2 - c1092wp_targetY i <= &197 / &500`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `i:num` 12 THEN
  REWRITE_TAC[c1092wp_targetX; c1092wp_targetY; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: excludes_all_target_systems *)
let C1092WP_EXCLUDES_ALL_TARGET_SYSTEMS = prove
 (`forall i bface pface t z0 z1 z2.
     i < 12 /\ bface < 2 /\ pface < 3 /\ &0 <= t /\ t <= &1 /\
     c1092wp_wallsystem (c1092wp_targetX i) (c1092wp_targetY i) t z0 z1 z2 bface pface
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092WP_ENUM_TAC `pface:num` 3 THENL
  [MATCH_MP_TAC C1092WP_EXCLUDES_TARGET_PFACE0 THEN
   MAP_EVERY EXISTS_TAC [`i:num`; `bface:num`; `t:real`; `z0:real`; `z1:real`; `z2:real`] THEN
   ASM_REWRITE_TAC[];
   MATCH_MP_TAC C1092WP_EXCLUDES_PFACE1 THEN
   MAP_EVERY EXISTS_TAC [`c1092wp_targetX i`; `c1092wp_targetY i`; `t:real`;
                         `z0:real`; `z1:real`; `z2:real`; `bface:num`] THEN
   ASM_SIMP_TAC[C1092WP_TARGET_HALF_DISTANCE];
   MATCH_MP_TAC C1092WP_EXCLUDES_PFACE2 THEN
   MAP_EVERY EXISTS_TAC [`c1092wp_targetX i`; `c1092wp_targetY i`; `t:real`;
                         `z0:real`; `z1:real`; `z2:real`; `bface:num`] THEN
   ASM_SIMP_TAC[C1092WP_TARGET_RECTANGLE]]);;
