(* ========================================================================= *)
(* Port of Compact/Geometry/ThreeSquareSupport.lean (Jatloe, N12-jatloe).     *)
(* Support and section facts for the original OpenSquare.                    *)
(* Also ports positive_frame_wall_bounds (and the face-coordinate part of    *)
(* inside_iff_rotated_box) from source/S12/WallGeometry.lean.                *)
(* ClosedInside q x y <-> lclosed c s u v a x y.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SectionCapacity.ml";;

(* Lean: supportRadius (definition; depends on the frame c, s and the side) *)
let tss_support_radius = new_definition
 `tss_support_radius (c:real) (s:real) (a:real) nx ny =
    a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`;;

(* Lean: closed_coordinates *)
let TSS_CLOSED_COORDINATES = prove
 (`forall c s u v a x y. c * c + s * s = &1 /\ lclosed c s u v a x y
     ==> abs(c * (x - lcx c s u v a) + s * (y - lcy c s u v a)) <= a / &2 /\
         abs(--s * (x - lcx c s u v a) + c * (y - lcy c s u v a)) <= a / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    LCENTRE_COORDS) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `lclosed c s u v a x y` THEN
  REWRITE_TAC[lclosed; REAL_ABS_BOUNDS] THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REAL_ARITH_TAC);;

(* helper: |A U + B V| <= r (|A| + |B|) *)
let TSS_ABS_COMB = prove
 (`forall A B U V r. abs U <= r /\ abs V <= r ==> abs(A * U + B * V) <= r * (abs A + abs B)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(A * U) + abs(B * V)` THEN
  REWRITE_TAC[REAL_ABS_TRIANGLE; REAL_ABS_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= r * a /\ y <= r * b ==> x + y <= r * (a + b)`) THEN
  CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

(* Lean: closed_support *)
let TSS_CLOSED_SUPPORT = prove
 (`forall c s u v a x y nx ny. c * c + s * s = &1 /\ lclosed c s u v a x y
     ==> abs(nx * (x - lcx c s u v a) + ny * (y - lcy c s u v a))
         <= tss_support_radius c s a nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`]
    TSS_CLOSED_COORDINATES) THEN
  ASM_REWRITE_TAC[tss_support_radius] THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `nx * (x - X) + ny * (y - Y) =
    (nx * c + ny * s) * (c * (x - X) + s * (y - Y)) +
    (--nx * s + ny * c) * (--s * (x - X) + c * (y - Y))` SUBST1_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC TSS_ABS_COMB THEN ASM_REWRITE_TAC[]);;

(* Lean: inside_support *)
let TSS_INSIDE_SUPPORT = prove
 (`forall c s u v a x y nx ny. c * c + s * s = &1 /\ linside c s u v a x y
     ==> abs(nx * (x - lcx c s u v a) + ny * (y - lcy c s u v a))
         <= tss_support_radius c s a nx ny`,
  MESON_TAC[TSS_CLOSED_SUPPORT; LINSIDE_CLOSED]);;

(* Lean: S12.inside_iff_rotated_box (face-coordinate direction, WallGeometry) *)
let TSS_INSIDE_FACE = prove
 (`forall c s u v a U V. c * c + s * s = &1
     ==> (linside c s u v a (c * U - s * V) (s * U + c * V) <=>
          u < U /\ U < u + a /\ v < V /\ V < v + a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c * (c * U - s * V) + s * (s * U + c * V) = U /\
                --s * (c * U - s * V) + c * (s * U + c * V) = V`
  (fun th -> REWRITE_TAC[linside; th]) THEN
  CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

(* Lean: S12.positive_frame_wall_bounds (source/S12/WallGeometry.lean) *)
let TSS_POSITIVE_FRAME_WALL_BOUNDS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\
               (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y)
     ==> a * (c + s) / &2 <= lcx c s u v a /\
         a * (c + s) / &2 <= lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c * u - s * (v + a)` ASSUME_TAC THENL
  [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + t) - s * (v + a - t)`;
                                 `s * (u + t) + c * (v + a - t)`]) THEN
   ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s * u + c * v` ASSUME_TAC THENL
  [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + t) - s * (v + t)`;
                                 `s * (u + t) + c * (v + t)`]) THEN
   ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[lcx; lcy] THEN ASM_REAL_ARITH_TAC);;

(* Lean: bottom_wall *)
let TSS_BOTTOM_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ lcont c s u v a
     ==> a * (c + abs s) / &2 <= lcy c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcont] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= s` THENL
  [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
     TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`];
   MP_TAC(SPECL [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`]
     TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
     REPEAT GEN_TAC THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
     ANTS_TAC THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC]];
    REWRITE_TAC[lcy] THEN ASM_REAL_ARITH_TAC]]);;

(* Lean: half_width_lt_one *)
let TSS_HALF_WIDTH_LT_ONE = prove
 (`forall c s a. c * c + s * s = &1 /\ &0 < a /\ a <= &1001 / &1000
     ==> tss_support_radius c s a (&1) (&0) < &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tss_support_radius; REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_RID;
              REAL_ADD_LID; REAL_MUL_LNEG; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `abs c * abs c + abs s * abs s = &1` MP_TAC THENL
  [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
   SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_SQUARE] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `c:real` REAL_ABS_POS) THEN MP_TAC(SPEC `s:real` REAL_ABS_POS) THEN
  SPEC_TAC(`abs c`,`p:real`) THEN SPEC_TAC(`abs s`,`q:real`) THEN
  REPEAT STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `p - q:real`] [`p + q <= &3 / &2`] THEN
  NLIN_TAC []);;

(* Lean: section_crosses_center *)
let TSS_SECTION_CROSSES_CENTER = prove
 (`forall c s u v a h l r. c * c + s * s = &1 /\ &0 < a /\ a <= &1001 / &1000 /\
                     &1 < r - l /\
                     (forall x. l < x /\ x < r ==> linside c s u v a x h)
     ==> l < lcx c s u v a /\ lcx c s u v a < r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `a:real`] TSS_HALF_WIDTH_LT_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall x. l < x /\ x < r
       ==> lcx c s u v a - tss_support_radius c s a (&1) (&0) <= x /\
           x <= lcx c s u v a + tss_support_radius c s a (&1) (&0)`
  ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`;
                 `h:real`; `&1`; `&0`] TSS_INSIDE_SUPPORT) THEN
   ASM_SIMP_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= l - lcx c s u v a + tss_support_radius c s a (&1) (&0) /\
    &0 <= lcx c s u v a + tss_support_radius c s a (&1) (&0) - r`
  MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`r - l:real`; `&1`] THEN
   (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `l + t:real`);
    FIRST_X_ASSUM(MP_TAC o SPEC `r - t:real`)] THEN
   (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]); ALL_TAC] THEN
  UNDISCH_TAC `tss_support_radius c s a (&1) (&0) < &1` THEN
  UNDISCH_TAC `&1 < r - l` THEN
  SPEC_TAC(`tss_support_radius c s a (&1) (&0)`,`w:real`) THEN
  REAL_ARITH_TAC);;

(* Lean: intervals_ordered *)
let TSS_INTERVALS_ORDERED = prove
 (`forall l u l' u'. l < u /\ l' < u' /\
               (forall x. ~(l < x /\ x < u /\ l' < x /\ x < u'))
     ==> u <= l' \/ u' <= l`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `u <= l'` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `u' <= l` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(max l l' + min u u') / &2`) THEN
  REWRITE_TAC[real_max; real_min] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: ordered_sections *)
let TSS_ORDERED_SECTIONS = prove
 (`forall cA sA uA vA aA cB sB uB vB aB h l u l' u'.
     l < u /\ l' < u' /\
     (forall x. l < x /\ x < u ==> linside cA sA uA vA aA x h) /\
     (forall x. l' < x /\ x < u' ==> linside cB sB uB vB aB x h) /\
     l < u' /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> u <= l'`,
  REWRITE_TAC[ldisj] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `u:real`; `l':real`; `u':real`] TSS_INTERVALS_ORDERED) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `h:real`]) THEN ASM_SIMP_TAC[];
   ASM_REAL_ARITH_TAC]);;

(* Lean: section_right_wall *)
let TSS_SECTION_RIGHT_WALL = prove
 (`forall c s u v a h l r. l < r /\
                     (forall x. l < x /\ x < r ==> linside c s u v a x h) /\
                     lcont c s u v a
     ==> r <= &4`,
  REWRITE_TAC[lcont] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &4 - r ==> r <= &4`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`r - l:real`; `&1`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linside c s u v a (r - t) h` MP_TAC THENL
  [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
  REAL_ARITH_TAC);;
