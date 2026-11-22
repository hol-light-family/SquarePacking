(* ========================================================================= *)
(* Port of Compact/Geometry/C1092WallCenterCover.lean (Jatloe, N12-jatloe).   *)
(* Parametric replacement of the C1092 centre-cover polygons: two radius-1/2 *)
(* disks cover a cap, two short triangles cover the region below it.         *)
(* Also ports S12.triangle_nonavoidance (source/S12/TriangleCover) in the    *)
(* linside representation, from the Phase-1 TRIANGLE_NONAVOID.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C1092WallPolynomial.ml";;
needs "n12/geometry/C1092WallCenterRegion.ml";;

(* Lean: S12.triangle_nonavoidance *)
let C1092WCC_TRIANGLE_NONAVOIDANCE = prove
 (`forall c s u v a x0 y0 x1 y1 x2 y2 w0 w1 w2.
     c * c + s * s = &1 /\ &1 < a /\
     &0 <= w0 /\ &0 <= w1 /\ &0 <= w2 /\ w0 + w1 + w2 = &1 /\
     w0 * x0 + w1 * x1 + w2 * x2 = lcx c s u v a /\
     w0 * y0 + w1 * y1 + w2 * y2 = lcy c s u v a /\
     (x0 - x1) pow 2 + (y0 - y1) pow 2 <= &1 /\
     (x0 - x2) pow 2 + (y0 - y2) pow 2 <= &1 /\
     (x1 - x2) pow 2 + (y1 - y2) pow 2 <= &1
     ==> linside c s u v a x0 y0 \/ linside c s u v a x1 y1 \/
         linside c s u v a x2 y2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lcx c s u v a`; `lcy c s u v a`; `c:real`; `s:real`; `a:real`;
                `x0:real`; `y0:real`; `x1:real`; `y1:real`; `x2:real`; `y2:real`;
                `w0:real`; `w1:real`; `w2:real`] TRIANGLE_NONAVOID) THEN
  ASM_SIMP_TAC[C1092WCR_OSQ_CENTRE] THEN DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REWRITE_TAC[]);;

(* Lean: half_disk_inside *)
let C1092WCC_HALF_DISK_INSIDE = prove
 (`forall c s u v a x y.
     c * c + s * s = &1 /\ &1 < a /\
     (x - lcx c s u v a) pow 2 + (y - lcy c s u v a) pow 2 <= &1 / &4
     ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x - lcx c s u v a) pow 2 + (y - lcy c s u v a) pow 2 <= &1 / &4` THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(c * (x - X) + s * (y - Y)) pow 2 + (--s * (x - X) + c * (y - Y)) pow 2
                <= &1 / &4` MP_TAC THENL
  [SUBGOAL_THEN `(c * (x - X) + s * (y - Y)) pow 2 + (--s * (x - X) + c * (y - Y)) pow 2 =
                 (x - X) pow 2 + (y - Y) pow 2` (fun th -> ASM_REWRITE_TAC[th]) THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c * x + s * y = (u + a / &2) + (c * (x - X) + s * (y - Y)) /\
                --s * x + c * y = (v + a / &2) + (--s * (x - X) + c * (y - Y))`
  (fun th -> REWRITE_TAC[linside; th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`c * (x - X) + s * (y - Y)`,`p:real`) THEN
  SPEC_TAC(`--s * (x - X) + c * (y - Y)`,`q:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs p <= &1 / &2 /\ abs q <= &1 / &2` MP_TAC THENL
  [CONJ_TAC THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THEN
   NLIN_TAC [SQ_NONNEG `p:real`; SQ_NONNEG `q:real`]; ALL_TAC] THEN
  UNDISCH_TAC `&1 < a` THEN REAL_ARITH_TAC);;

(* Lean: cap_two_disks *)
let C1092WCC_CAP_TWO_DISKS = prove
 (`forall d H h v w.
     &0 < d /\ &0 < H /\ h <= H /\ &0 <= v /\ H * v <= d * w /\ w <= h /\
     d pow 2 + H pow 2 <= &1 /\
     (d pow 2 + H pow 2 - &2 * H * h) pow 2 + &4 * d pow 2 * h pow 2 <= d pow 2
     ==> v pow 2 + w pow 2 <= &1 / &4 \/
         (d - v) pow 2 + (H - w) pow 2 <= &1 / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= H * v` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= w` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `v <= d` ASSUME_TAC THENL
  [SUBGOAL_THEN `d * w <= d * H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d pow 2` ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_CASES_TAC `w <= H / &2` THENL
  [DISJ1_TAC THEN
   SUBGOAL_THEN `v <= d / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `d * w <= d * (H / &2)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (d / &2 - v) * (d / &2 + v) /\
                 &0 <= (H / &2 - w) * (H / &2 + w)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `d pow 2 + H pow 2 <= &1` THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `(d pow 2 + H pow 2) * ((&2 * w - H) pow 2 + d pow 2) <= d pow 2`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (d pow 2 + H pow 2) * ((h - w) * (h + w - H))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [SUBGOAL_THEN `&0 <= d pow 2 /\ &0 <= H pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2]; REAL_ARITH_TAC];
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
   UNDISCH_TAC `(d pow 2 + H pow 2 - &2 * H * h) pow 2 + &4 * d pow 2 * h pow 2
                <= d pow 2` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&2 * d * v + &2 * H * w <= d pow 2 + H pow 2` THENL
  [DISJ1_TAC THEN
   SUBGOAL_THEN `&0 <= d * v` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (d pow 2 + H pow 2 - &2 * H * w - &2 * d * v) *
                       (d pow 2 + H pow 2 - &2 * H * w + &2 * d * v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= d pow 2 * (&1 / &4 - (v pow 2 + w pow 2))` MP_TAC THENL
   [UNDISCH_TAC `(d pow 2 + H pow 2) * ((&2 * w - H) pow 2 + d pow 2) <= d pow 2` THEN
    UNDISCH_TAC `&0 <= (d pow 2 + H pow 2 - &2 * H * w - &2 * d * v) *
                       (d pow 2 + H pow 2 - &2 * H * w + &2 * d * v)` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN
   MP_TAC(SPECL [`d pow 2`; `&1 / &4 - (v pow 2 + w pow 2)`] C1092WP_NONNEG_OF_MUL) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   DISJ2_TAC THEN
   SUBGOAL_THEN `&0 <= d * (d - v)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (d pow 2 - H pow 2 + &2 * H * w - &2 * d * (d - v)) *
                       (d pow 2 - H pow 2 + &2 * H * w + &2 * d * (d - v))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= d pow 2 * (&1 / &4 - ((d - v) pow 2 + (H - w) pow 2))` MP_TAC THENL
   [UNDISCH_TAC `(d pow 2 + H pow 2) * ((&2 * w - H) pow 2 + d pow 2) <= d pow 2` THEN
    UNDISCH_TAC `&0 <= (d pow 2 - H pow 2 + &2 * H * w - &2 * d * (d - v)) *
                       (d pow 2 - H pow 2 + &2 * H * w + &2 * d * (d - v))` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN
   MP_TAC(SPECL [`d pow 2`; `&1 / &4 - ((d - v) pow 2 + (H - w) pow 2)`]
     C1092WP_NONNEG_OF_MUL) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Lean: cap_forces_point *)
let C1092WCC_CAP_FORCES_POINT = prove
 (`forall c s u v a x y d H h.
     c * c + s * s = &1 /\ &1 < a /\
     &0 < d /\ &0 < H /\ h <= H /\ x <= lcx c s u v a /\
     H * (lcx c s u v a - x) <= d * (lcy c s u v a - y) /\
     lcy c s u v a - y <= h /\ d pow 2 + H pow 2 <= &1 /\
     (d pow 2 + H pow 2 - &2 * H * h) pow 2 + &4 * d pow 2 * h pow 2 <= d pow 2 /\
     ~linside c s u v a (x + d) (y + H)
     ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `H:real`; `h:real`; `lcx c s u v a - x`;
                `lcy c s u v a - y`] C1092WCC_CAP_TWO_DISKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
  [MATCH_MP_TAC C1092WCC_HALF_DISK_INSIDE THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `(lcx c s u v a - x) pow 2 + (lcy c s u v a - y) pow 2 <= &1 / &4` THEN
   REAL_ARITH_TAC;
   UNDISCH_TAC `~linside c s u v a (x + d) (y + H)` THEN
   MATCH_MP_TAC(TAUT `q ==> ~q ==> p`) THEN
   MATCH_MP_TAC C1092WCC_HALF_DISK_INSIDE THEN ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `(d - (lcx c s u v a - x)) pow 2 + (H - (lcy c s u v a - y)) pow 2
                <= &1 / &4` THEN
   REAL_ARITH_TAC]);;

(* barycentric coordinates with a common positive denominator *)
let C1092WCC_BARY = prove
 (`forall A a b c x0 x1 x2 P. &0 < A /\ a * x0 + b * x1 + c * x2 = A * P
     ==> a / A * x0 + b / A * x1 + c / A * x2 = P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `a / A * x0 + b / A * x1 + c / A * x2 = (a * x0 + b * x1 + c * x2) / A`
  SUBST1_TAC THENL
  [UNDISCH_TAC `&0 < A` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < A` THEN CONV_TAC REAL_FIELD);;

let C1092WCC_TRI_GOALS_TAC names =
  let bary = MATCH_MP_TAC C1092WCC_BARY THEN ASM_REWRITE_TAC[] THEN
             MAP_EVERY EXPAND_TAC names THEN REAL_ARITH_TAC in
  REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
         bary;
         ONCE_REWRITE_TAC[REAL_ARITH `a + b + c = (a * &1 + b * &1 + c * &1)`] THEN bary;
         CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
         ASM_REAL_ARITH_TAC];;

(* Lean: below_triangles_forces_point *)
let C1092WCC_BELOW_TRIANGLES_FORCES_POINT = prove
 (`forall c s u v a x y.
     c * c + s * s = &1 /\ &1 < a /\
     &457 / &500 <= x /\ x < &33 / &20 /\
     &0 < (&92 / &125) * (y - &1) - (&13 / &20) * (x - &457 / &500) /\
     x <= lcx c s u v a /\ lcx c s u v a <= &33 / &20 /\
     (&325 / &368) * lcx c s u v a + &1419 / &7360 <= lcy c s u v a /\
     (&33 / &20 - x) * (lcy c s u v a - y) <= (&47 / &20 - y) * (lcx c s u v a - x) /\
     (x - &457 / &500) pow 2 + (y - &1) pow 2 <= &1 /\
     (x - &33 / &20) pow 2 + (y - &33 / &20) pow 2 <= &1 /\
     (x - &33 / &20) pow 2 + (y - &47 / &20) pow 2 <= &1 /\
     ~linside c s u v a (&457 / &500) (&1) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `X = lcx c s u v a` THEN ABBREV_TAC `Y = lcy c s u v a` THEN
  ABBREV_TAC `area = (&92 / &125) * (y - &1) - (&13 / &20) * (x - &457 / &500)` THEN
  ASM_CASES_TAC `(&33 / &20 - x) * (Y - y) <= (&33 / &20 - y) * (X - x)` THENL
  [ABBREV_TAC `NB = (&33 / &20 - x) * (&33 / &20 - Y) - (&33 / &20 - y) * (&33 / &20 - X)` THEN
   ABBREV_TAC `ND = (y - &1) * (X - &457 / &500) - (x - &457 / &500) * (Y - &1)` THEN
   ABBREV_TAC `NP = (&92 / &125) * (Y - &1) - (&13 / &20) * (X - &457 / &500)` THEN
   SUBGOAL_THEN `&0 <= NB` ASSUME_TAC THENL
   [EXPAND_TAC "NB" THEN
    UNDISCH_TAC `(&33 / &20 - x) * (Y - y) <= (&33 / &20 - y) * (X - x)` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= NP` ASSUME_TAC THENL
   [EXPAND_TAC "NP" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= ND` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092WP_NONNEG_OF_MUL THEN EXISTS_TAC `&33 / &20 - x` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&33 / &20 - x) * ND = (X - x) * area + (x - &457 / &500) * NB` SUBST1_TAC THENL
    [MAP_EVERY EXPAND_TAC ["ND"; "NB"; "area"]  THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                 `&457 / &500`; `&1`; `&33 / &20`; `&33 / &20`; `x:real`; `y:real`;
                 `NB / area`; `ND / area`; `NP / area`] C1092WCC_TRIANGLE_NONAVOIDANCE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092WCC_TRI_GOALS_TAC ["NB"; "ND"; "NP"; "area"]; ASM_REWRITE_TAC[]];
   ABBREV_TAC `NF = (&33 / &20 - x) * (Y - y) - (&33 / &20 - y) * (X - x)` THEN
   ABBREV_TAC `ND = (&47 / &20 - y) * (X - x) - (&33 / &20 - x) * (Y - y)` THEN
   ABBREV_TAC `NQ = (&7 / &10) * (&33 / &20 - X)` THEN
   ABBREV_TAC `den = (&33 / &20 - x) * (&7 / &10)` THEN
   SUBGOAL_THEN `&0 < den` ASSUME_TAC THENL
   [EXPAND_TAC "den" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= NF /\ &0 <= ND /\ &0 <= NQ` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["NF"; "ND"; "NQ"] THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                 `x:real`; `y:real`; `&33 / &20`; `&33 / &20`; `&33 / &20`; `&47 / &20`;
                 `NQ / den`; `ND / den`; `NF / den`] C1092WCC_TRIANGLE_NONAVOIDANCE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092WCC_TRI_GOALS_TAC ["NF"; "ND"; "NQ"; "den"]; ASM_REWRITE_TAC[]]]);;

(* Lean: target_cover_arithmetic *)
let C1092WCC_TARGET_COVER_ARITHMETIC = prove
 (`forall i. i < 12 ==>
     &457 / &500 <= c1092wp_targetX i /\ c1092wp_targetX i <= &1 /\
     c1092wp_targetY i <= &2 /\
     &0 < (&92 / &125) * (c1092wp_targetY i - &1) -
          (&13 / &20) * (c1092wp_targetX i - &457 / &500) /\
     (c1092wp_targetX i - &457 / &500) pow 2 + (c1092wp_targetY i - &1) pow 2 <= &1 /\
     (c1092wp_targetX i - &33 / &20) pow 2 + (c1092wp_targetY i - &33 / &20) pow 2 <= &1 /\
     (c1092wp_targetX i - &33 / &20) pow 2 + (c1092wp_targetY i - &47 / &20) pow 2 <= &1 /\
     ((&33 / &20 - c1092wp_targetX i) pow 2 + (&47 / &20 - c1092wp_targetY i) pow 2 -
      &2 * (&47 / &20 - c1092wp_targetY i) * (&2 - c1092wp_targetY i)) pow 2 +
     &4 * (&33 / &20 - c1092wp_targetX i) pow 2 * (&2 - c1092wp_targetY i) pow 2
     <= (&33 / &20 - c1092wp_targetX i) pow 2`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `i:num` 12 THEN
  REWRITE_TAC[c1092wp_targetX; c1092wp_targetY; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: original_right_branch_point *)
let C1092WCC_ORIGINAL_RIGHT_BRANCH_POINT = prove
 (`forall c s u v a i.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\
     linside c s u v a (&457 / &500) (&2) /\
     ~linside c s u v a (&1) (&457 / &500) /\
     ~linside c s u v a (&457 / &500) (&1) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     &1 <= lcx c s u v a /\ lcy c s u v a <= &2 /\ i < 12
     ==> linside c s u v a (c1092wp_targetX i) (c1092wp_targetY i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092WCR_ORIGINAL_MARKER_ENTRANCE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `i:num` C1092WCC_TARGET_COVER_ARITHMETIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(&33 / &20 - c1092wp_targetX i) * (lcy c s u v a - c1092wp_targetY i) <=
                 (&47 / &20 - c1092wp_targetY i) * (lcx c s u v a - c1092wp_targetX i)`
  THENL
  [MATCH_MP_TAC C1092WCC_BELOW_TRIANGLES_FORCES_POINT THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC C1092WCC_CAP_FORCES_POINT THEN
   MAP_EVERY EXISTS_TAC [`&33 / &20 - c1092wp_targetX i`;
                         `&47 / &20 - c1092wp_targetY i`;
                         `&2 - c1092wp_targetY i`] THEN
   ASM_REWRITE_TAC[REAL_ARITH `x + (a - x) = a`] THEN
   REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
   UNDISCH_TAC `(c1092wp_targetX i - &33 / &20) pow 2 +
                (c1092wp_targetY i - &47 / &20) pow 2 <= &1` THEN
   REAL_ARITH_TAC]);;
