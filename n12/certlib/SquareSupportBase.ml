(* ========================================================================= *)
(* Port of source/S12/SquareSupportBase.lean (Jatloe, N12-jatloe).           *)
(* squareRadius q nx ny is tss_support_radius c s a nx ny                    *)
(* (geometry/ThreeSquareSupport.ml, the same formula a/2*(|nx c+ny s|+|-nx s+ny c|)).*)
(* The parameter u of the Lean bounds is renamed w (u is the square's loU).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/certlib/ConvexOverlap.ml";;

(* Lean: S12.inside_centered_iff (source/S12/SquareFrame.lean) *)
let SSB_INSIDE_CENTERED = prove
 (`forall c s u v a x y. c * c + s * s = &1
     ==> (linside c s u v a x y <=>
          --a / &2 < c * (x - lcx c s u v a) + s * (y - lcy c s u v a) /\
          c * (x - lcx c s u v a) + s * (y - lcy c s u v a) < --a / &2 + a /\
          --a / &2 < --s * (x - lcx c s u v a) + c * (y - lcy c s u v a) /\
          --s * (x - lcx c s u v a) + c * (y - lcy c s u v a) < --a / &2 + a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: square_center_inside *)
let SSB_SQUARE_CENTER_INSIDE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> linside c s u v a (lcx c s u v a) (lcy c s u v a)`,
  SIMP_TAC[SSB_INSIDE_CENTERED] THEN REAL_ARITH_TAC);;

(* Lean: linear_endpoint_le *)
let SSB_LINEAR_ENDPOINT_LE = prove
 (`forall L d w. L <= w /\ (forall t. &0 <= t /\ t < &1 ==> L + t * d <= w) ==> L + d <= w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists t. &0 <= t /\ t < &1 /\ t * d = (d + w - L) / &2` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(d + w - L) / (&2 * d)` THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < d ==> &0 < &2 * d`;
                 REAL_ARITH `&0 < d /\ L <= w ==> &0 <= d + w - L`;
                 REAL_ARITH `&0 < d ==> &0 <= &2 * d`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: square_displacement_inside *)
let SSB_SQUARE_DISPLACEMENT_INSIDE = prove
 (`forall c s u v a dx dy t.
     c * c + s * s = &1 /\ &0 < a /\
     abs(c * dx + s * dy) <= a / &2 /\ abs(--s * dx + c * dy) <= a / &2 /\
     &0 <= t /\ t < &1
     ==> linside c s u v a (lcx c s u v a + t * dx) (lcy c s u v a + t * dy)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[SSB_INSIDE_CENTERED] THEN
  REWRITE_TAC[REAL_ARITH `(x + t * d) - x = t * d`] THEN
  REWRITE_TAC[REAL_ARITH `c * t * dx + s * t * dy = t * (c * dx + s * dy)`] THEN
  UNDISCH_TAC `abs(c * dx + s * dy) <= a / &2` THEN
  UNDISCH_TAC `abs(--s * dx + c * dy) <= a / &2` THEN
  REWRITE_TAC[REAL_ARITH `c * t * dx + s * t * dy = t * (c * dx + s * dy)`] THEN
  SPEC_TAC(`c * dx + s * dy`,`U:real`) THEN SPEC_TAC(`--s * dx + c * dy`,`V:real`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH `abs x <= h <=> --h <= x /\ x <= h`] THEN
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: square_closed_linear_bound *)
let SSB_SQUARE_CLOSED_LINEAR_BOUND = prove
 (`forall c s u v a nx ny w dx dy.
     c * c + s * s = &1 /\ &0 < a /\
     (forall x y. linside c s u v a x y ==> nx * x + ny * y <= w) /\
     abs(c * dx + s * dy) <= a / &2 /\ abs(--s * dx + c * dy) <= a / &2
     ==> nx * lcx c s u v a + ny * lcy c s u v a + (nx * dx + ny * dy) <= w`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x + y + z = (x + y) + z:real`] THEN
  MATCH_MP_TAC SSB_LINEAR_ENDPOINT_LE THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC SSB_SQUARE_CENTER_INSIDE THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`lcx c s u v a + t * dx`; `lcy c s u v a + t * dy`]) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SSB_SQUARE_DISPLACEMENT_INSIDE THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC]]);;

(* Lean: signedOne *)
let signedOne = new_definition `signedOne a = if &0 <= a then &1 else -- &1`;;

(* Lean: signedOne_abs *)
let SSB_SIGNEDONE_ABS = prove
 (`forall a. abs(signedOne a) = &1`,
  GEN_TAC THEN REWRITE_TAC[signedOne] THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* Lean: signedOne_mul *)
let SSB_SIGNEDONE_MUL = prove
 (`forall a. a * signedOne a = abs a`,
  GEN_TAC THEN REWRITE_TAC[signedOne] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: squareRadius (= tss_support_radius) *)
let SSB_SQUARERADIUS = prove
 (`forall c s a nx ny. tss_support_radius c s a nx ny =
     a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`,
  REWRITE_TAC[tss_support_radius]);;

(* Lean: square_support_bound *)
let SSB_SQUARE_SUPPORT_BOUND = prove
 (`forall c s u v a nx ny w.
     c * c + s * s = &1 /\ &0 < a /\
     (forall x y. linside c s u v a x y ==> nx * x + ny * y <= w)
     ==> nx * lcx c s u v a + ny * lcy c s u v a + tss_support_radius c s a nx ny <= w`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `su = signedOne(nx * c + ny * s)` THEN
  ABBREV_TAC `sv = signedOne(--nx * s + ny * c)` THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `nx:real`; `ny:real`; `w:real`;
                `a / &2 * (c * su - s * sv)`; `a / &2 * (s * su + c * sv)`]
    SSB_SQUARE_CLOSED_LINEAR_BOUND) THEN
  SUBGOAL_THEN `c * a / &2 * (c * su - s * sv) + s * a / &2 * (s * su + c * sv) = a / &2 * su /\
                --s * a / &2 * (c * su - s * sv) + c * a / &2 * (s * su + c * sv) = a / &2 * sv`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  MAP_EVERY EXPAND_TAC ["su"; "sv"] THEN REWRITE_TAC[SSB_SIGNEDONE_ABS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs(a / &2) = a / &2`; REAL_MUL_RID; REAL_LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> L + x <= w ==> L + y <= w`) THEN
  REWRITE_TAC[tss_support_radius; GSYM SSB_SIGNEDONE_MUL] THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Lean: squareRadius_neg *)
let SSB_SQUARERADIUS_NEG = prove
 (`forall c s a nx ny. tss_support_radius c s a (--nx) (--ny) = tss_support_radius c s a nx ny`,
  REWRITE_TAC[tss_support_radius] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  BINOP_TAC THEN REAL_ARITH_TAC);;
