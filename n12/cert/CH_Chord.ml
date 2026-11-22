(* ========================================================================= *)
(* W-CHORD, part 1: semantics and soundness of the chord stages.            *)
(* Lean: Compact/Bridge/AngleSection.lean (Radius, Radius.Check,             *)
(*       Radius.bound, VerticalSection, oriented_vertical,                   *)
(*       four_vertical_impossible, interval_nearby, window_excludes),        *)
(*       Compact/Bridge/AxisSection.lean (center, Section, oriented_section, *)
(*       four_impossible, window_excludes, orient, lower, upper,             *)
(*       holds_lower, holds_upper), Compact/Core/CoordinateBound.lean,       *)
(*       Compact/Bridge/IndexedChord.lean (Neighbor, Neighbor.bounds,        *)
(*       Neighbor.Check, Neighbor.sound, Plan, Plan.Check, Plan.sound,       *)
(*       neighbor_cover, plans_cover), Compact/Bridge/DirectPruningPlan.lean *)
(*       (Branch, Branch.Check, Branch.sound for the chord branches).        *)
(* Design: n12/docs/cert_design.md §4.4.  Tag CH_ / ch_.                         *)
(*                                                                           *)
(* Representation.  Rationals are pairs of integer literals (num, den) with  *)
(* den > 0 checked by the checkers.  The 192 Lean radii radiusK (Radii.lean) *)
(* are the literal table ch_radii; CH_RADII_ALL proves radiusK.Check for     *)
(* angle K once (Lean radiusK_checked).  Coordinate-bound rows (Lean         *)
(* AxisSection.lower/upper on reduced rationals) are data; the checker only *)
(* verifies that a row represents the bound (ch_bound_ok), so any positive  *)
(* multiple would be accepted as well (the semantics are the same).         *)
(* ========================================================================= *)

needs "n12/cert/CR_HistData.ml";;
needs "n12/geometry/LongSection.ml";;
needs "n12/geometry/CentralBarHeight.ml";;

(* ------------------------------------------------------------------------- *)
(* Radius (Lean AngleSection.Radius = <sumUpper, radius>)                    *)
(* ------------------------------------------------------------------------- *)

(* Lean: Radius.Check *)
let ch_radius_check = new_definition
 `ch_radius_check (B:real) (r:real) w <=>
    &0 <= r /\ &2 * r <= &1 + B - B pow 2 /\
    (quad_check_on (support_quad (&1) (&0) B (&1) (&1)) (ae_lower w) (ae_upper w) \/
     (&0 <= B /\ &2 <= B pow 2))`;;

let CH_UNIT_SUM_GE1 = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 ==> &1 <= c + s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN NLIN_TAC []);;

let CH_RADIUS_ALGEBRA = prove
 (`forall c s B r. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ c + s <= B /\
             &2 * r <= &1 + B - B pow 2
             ==> r <= (c + s - &2 * c * s) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CH_UNIT_SUM_GE1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (B - (c + s)) * (B + c + s - &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `&2 * r <= &1 + B - B pow 2` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: Radius.bound *)
let CH_RADIUS_BOUND = prove
 (`forall B r w t. ae_check w /\ ch_radius_check B r w /\ ae_lower w <= t /\ t <= ae_upper w
     ==> r <= (normalC t + normalS t - &2 * normalC t * normalS t) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ch_radius_check] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ae_check] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "ae_check" with Failure _ -> false)) THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_NONNEGATIVE) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_UNIT) THEN DISCH_TAC THEN
  MATCH_MP_TAC CH_RADIUS_ALGEBRA THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`&1`; `&0`; `B:real`; `&1`; `&1`; `ae_lower w`; `ae_upper w`; `t:real`]
      AE_SUPPORT_QUADRATIC_SOUND) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `(normalC t + normalS t) pow 2 <= B pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `normalC t - normalS t` REAL_LE_POW_2) THEN
      UNDISCH_TAC `normalC t pow 2 + normalS t pow 2 = &1` THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Sections                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Lean: AngleSection.VerticalSection *)
let ch_vsection = new_definition
 `ch_vsection c s u v a (x:real) <=>
    exists l w. &1 < w - l /\ forall y. l < y /\ y < w ==> linside c s u v a x y`;;

(* Lean: AxisSection.center *)
let ch_center = new_definition
 `ch_center hz c s u v a = if hz then lcy c s u v a else lcx c s u v a`;;

(* Lean: AxisSection.Section *)
let ch_section = new_definition
 `ch_section hz c s u v a (cut:real) <=>
    if hz then exists l w. &1 < w - l /\ forall x. l < x /\ x < w ==> linside c s u v a x cut
    else ch_vsection c s u v a cut`;;

let CH_SECTION_HZ = prove
 (`forall c s u v a cut. ch_section true c s u v a cut <=> scap_longsec c s u v a cut`,
  REWRITE_TAC[ch_section; scap_longsec]);;

let CH_VSECTION_SWAP = prove
 (`forall c s u v a x. ch_vsection c s u v a x <=> scap_longsec s c u (--v - a) a x`,
  REWRITE_TAC[ch_vsection; scap_longsec; LINSIDE_PULLSW]);;

let CH_LSEC_RADIUS_SWAP = prove
 (`forall c s. lsec_radius s c = lsec_radius c s`,
  REWRITE_TAC[lsec_radius] THEN REWRITE_TAC[REAL_MUL_SYM] THEN REAL_ARITH_TAC);;

let CH_LCY_SWAP = prove
 (`forall c s u v a. lcy s c u (--v - a) a = lcx c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: AxisSection.oriented_section (and AngleSection.oriented_vertical) *)
let CH_ORIENTED_SECTION = prove
 (`forall hz leaf B r c s u v a cut.
     ae_check (pl_angle leaf) /\ ch_radius_check B r (pl_angle leaf) /\ &1 < a /\
     angle_witness leaf c s u v a /\ abs(cut - ch_center hz c s u v a) <= r
     ==> ch_section hz c s u v a cut`,
  REPEAT GEN_TAC THEN REWRITE_TAC[angle_witness] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`; `t:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = v)))
    [`a':real`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ae_check] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "ae_check" with Failure _ -> false)) THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_NONNEGATIVE) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  MP_TAC(SPECL [`B:real`; `r:real`; `pl_angle leaf`; `t:real`] CH_RADIUS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r <= lsec_radius c' s'` ASSUME_TAC THENL
   [REWRITE_TAC[lsec_radius; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[real_abs] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `abs (cut - ch_center hz c s u v a) <= r` THEN
  REWRITE_TAC[ch_center; ch_section] THEN COND_CASES_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`; `cut:real`]
      LSEC_HORIZONTAL_LONG_SECTION) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[scap_longsec] THEN ASM_MESON_TAC[];
    MP_TAC(SPECL [`s':real`; `c':real`; `u':real`; `--v' - a:real`; `a:real`; `cut:real`]
      LSEC_HORIZONTAL_LONG_SECTION) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CH_LSEC_RADIUS_SWAP; CH_LCY_SWAP] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CH_VSECTION_SWAP; ch_vsection] THEN ASM_MESON_TAC[]]);;

(* the square families of SectionCapacity, from four explicit squares *)
let ch_fam = new_definition
 `ch_fam (x0:real) x1 x2 x3 (i:num) =
    if i = 0 then x0 else if i = 1 then x1 else if i = 2 then x2 else x3`;;

let CH_LDISJ_SYM = prove
 (`forall c s u v a c' s' u' v' a'. ldisj c s u v a c' s' u' v' a' <=> ldisj c' s' u' v' a' c s u v a`,
  REWRITE_TAC[ldisj] THEN MESON_TAC[]);;

let CH_FOUR_H = prove
 (`forall c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 h.
     lcont c0 s0 u0 v0 a0 /\ lcont c1 s1 u1 v1 a1 /\ lcont c2 s2 u2 v2 a2 /\ lcont c3 s3 u3 v3 a3 /\
     ldisj c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 /\ ldisj c0 s0 u0 v0 a0 c2 s2 u2 v2 a2 /\
     ldisj c0 s0 u0 v0 a0 c3 s3 u3 v3 a3 /\ ldisj c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 /\
     ldisj c1 s1 u1 v1 a1 c3 s3 u3 v3 a3 /\ ldisj c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 /\
     scap_longsec c0 s0 u0 v0 a0 h /\ scap_longsec c1 s1 u1 v1 a1 h /\
     scap_longsec c2 s2 u2 v2 a2 h /\ scap_longsec c3 s3 u3 v3 a3 h
     ==> false`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ch_fam c0 c1 c2 c3`; `ch_fam s0 s1 s2 s3`; `ch_fam u0 u1 u2 u3`;
                `ch_fam v0 v1 v2 v3`; `ch_fam a0 a1 a2 a3`; `h:real`] SCAP_FOUR_ON_ONE_CUT) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[ch_fam; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[CH_LDISJ_SYM] THEN ASM_REWRITE_TAC[]);;

let CH_LDISJ_SWAP = prove
 (`forall c s u v a c' s' u' v' a'. ldisj c s u v a c' s' u' v' a'
     ==> ldisj s c u (--v - a) a s' c' u' (--v' - a') a'`,
  REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN MESON_TAC[]);;

(* Lean: AxisSection.four_impossible (four_on_one_cut / four_vertical_impossible) *)
let CH_FOUR_IMPOSSIBLE = prove
 (`forall hz c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 cut.
     lcont c0 s0 u0 v0 a0 /\ lcont c1 s1 u1 v1 a1 /\ lcont c2 s2 u2 v2 a2 /\ lcont c3 s3 u3 v3 a3 /\
     ldisj c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 /\ ldisj c0 s0 u0 v0 a0 c2 s2 u2 v2 a2 /\
     ldisj c0 s0 u0 v0 a0 c3 s3 u3 v3 a3 /\ ldisj c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 /\
     ldisj c1 s1 u1 v1 a1 c3 s3 u3 v3 a3 /\ ldisj c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 /\
     ch_section hz c0 s0 u0 v0 a0 cut /\ ch_section hz c1 s1 u1 v1 a1 cut /\
     ch_section hz c2 s2 u2 v2 a2 cut /\ ch_section hz c3 s3 u3 v3 a3 cut
     ==> false`,
  GEN_TAC THEN ASM_CASES_TAC `hz:bool` THEN ASM_REWRITE_TAC[CH_SECTION_HZ] THENL
   [MESON_TAC[CH_FOUR_H]; ALL_TAC] THEN
  REWRITE_TAC[ch_section; CH_VSECTION_SWAP] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CH_FOUR_H THEN
  MAP_EVERY EXISTS_TAC [`s0:real`; `c0:real`; `u0:real`; `--v0 - a0:real`; `a0:real`;
                        `s1:real`; `c1:real`; `u1:real`; `--v1 - a1:real`; `a1:real`;
                        `s2:real`; `c2:real`; `u2:real`; `--v2 - a2:real`; `a2:real`;
                        `s3:real`; `c3:real`; `u3:real`; `--v3 - a3:real`; `a3:real`;
                        `cut:real`] THEN
  ASM_SIMP_TAC[LCONT_PULLSW; CH_LDISJ_SWAP]);;

(* Lean: AxisSection.window_excludes (with AngleSection.interval_nearby) *)
let CH_WINDOW_EXCLUDES = prove
 (`forall hz lo hi leaf B r c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 c3 s3 u3 v3 a3.
     lo <= hi /\ ae_check (pl_angle leaf) /\ ch_radius_check B r (pl_angle leaf) /\
     &1 < a0 /\
     lcont c0 s0 u0 v0 a0 /\ lcont c1 s1 u1 v1 a1 /\ lcont c2 s2 u2 v2 a2 /\ lcont c3 s3 u3 v3 a3 /\
     ldisj c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 /\ ldisj c0 s0 u0 v0 a0 c2 s2 u2 v2 a2 /\
     ldisj c0 s0 u0 v0 a0 c3 s3 u3 v3 a3 /\ ldisj c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 /\
     ldisj c1 s1 u1 v1 a1 c3 s3 u3 v3 a3 /\ ldisj c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 /\
     oriented_realizes leaf c0 s0 u0 v0 a0 /\
     (forall cut. lo <= cut /\ cut <= hi ==>
            ch_section hz c1 s1 u1 v1 a1 cut /\ ch_section hz c2 s2 u2 v2 a2 cut /\
            ch_section hz c3 s3 u3 v3 a3 cut)
     ==> ~(lo - r <= ch_center hz c0 s0 u0 v0 a0 /\ ch_center hz c0 s0 u0 v0 a0 <= hi + r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oriented_realizes] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `y = ch_center hz c0 s0 u0 v0 a0` THEN
  SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL
   [ASM_MESON_TAC[ch_radius_check]; ALL_TAC] THEN
  ABBREV_TAC `cut = max lo (y - r)` THEN
  SUBGOAL_THEN `lo <= cut /\ cut <= hi /\ abs(cut - y) <= r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cut" THEN REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`hz:bool`; `leaf:pose_leaf`; `B:real`; `r:real`;
                `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`; `cut:real`]
    CH_ORIENTED_SECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cut:real`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SPEC_ALL CH_FOUR_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Rationals and coordinate-bound rows                                       *)
(* ------------------------------------------------------------------------- *)

let ch_q = new_definition `ch_q (n:int) (d:int) = real_of_int n / real_of_int d`;;

(* Lean: AxisSection.orient, inverted (orient is an involution) *)
let ch_unorient = new_definition
 `ch_unorient hz r = if hz then CRow (cr_y r) (cr_x r) (cr_c r) (cr_s r) else r`;;

(* row r is Lean's AxisSection.lower hz (n/d) s (lw) or .upper hz (n/d) s (~lw), up to
   a positive factor:  r = orient hz (CRow X 0 C s), X > 0 (lower) / X < 0 (upper),
   C = -X n/d. *)
let ch_bound_ok = new_definition
 `ch_bound_ok hz lw (n:int) (d:int) s r <=>
    let r0 = ch_unorient hz r in
    &0 < d /\ (if lw then &0 < cr_x r0 else cr_x r0 < &0) /\ cr_y r0 = &0 /\
    cr_s r0 = s /\ cr_x r0 * n + cr_c r0 * d = &0`;;

let CH_SIGN_SCALE = prove
 (`forall X C n d p. &0 < d /\ X * n + C * d = &0
     ==> X * p + C = X * (p - n / d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C = --(X * n) / d` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `X * n + C * d = &0` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD]);;

(* Lean: AxisSection.holds_lower / holds_upper (CoordinateBound.holds_lower/upper) *)
let CH_BOUND_HOLDS = prove
 (`forall hz lw n d s r px py. ch_bound_ok hz lw n d s r
     ==> (cr_holds r px py <=>
          let p = if hz then py else px in
          if lw then (if s then ch_q n d < p else ch_q n d <= p)
          else (if s then p < ch_q n d else p <= ch_q n d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ch_bound_ok; LET_DEF; LET_END_DEF] THEN
  ABBREV_TAC `r0 = ch_unorient hz r` THEN
  SUBGOAL_THEN `cr_eval r px py = real_of_int (cr_x r0) * (if hz then py else px) +
                  real_of_int (cr_y r0) * (if hz then px else py) + real_of_int (cr_c r0) /\
                cr_s r = cr_s r0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN REWRITE_TAC[ch_unorient] THEN COND_CASES_TAC THEN
    REWRITE_TAC[cr_x; cr_y; cr_c; cr_s; cr_eval] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[cr_holds; ch_q] THEN
  REWRITE_TAC INT_REAL_RULES THEN
  ABBREV_TAC `X = real_of_int (cr_x r0)` THEN ABBREV_TAC `C = real_of_int (cr_c r0)` THEN
  ABBREV_TAC `N = real_of_int n` THEN ABBREV_TAC `D = real_of_int d` THEN
  ABBREV_TAC `(p:real) = (if hz then py else px)` THEN
  ABBREV_TAC `Y = real_of_int (cr_y r0)` THEN
  BOOL_CASES_TAC `lw:bool` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  MP_TAC(SPECL [`X:real`; `C:real`; `N:real`; `D:real`; `p:real`] CH_SIGN_SCALE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_LE_MUL_EQ] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `X * (p - q) = --X * (q - p)`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_LE_MUL_EQ; REAL_ARITH `X < &0 ==> &0 < --X`] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

let CH_Q_SUB = prove
 (`forall hn hd rn rd. &0 < hd /\ &0 < rd
     ==> ch_q (hn * rd - rn * hd) (hd * rd) = ch_q hn hd - ch_q rn rd`,
  REWRITE_TAC[ch_q; int_lt; int_of_num_th; int_sub_th; int_mul_th] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `&0 < real_of_int hd` THEN
  UNDISCH_TAC `&0 < real_of_int rd` THEN CONV_TAC REAL_FIELD);;

let CH_Q_ADD = prove
 (`forall hn hd rn rd. &0 < hd /\ &0 < rd
     ==> ch_q (hn * rd + rn * hd) (hd * rd) = ch_q hn hd + ch_q rn rd`,
  REWRITE_TAC[ch_q; int_lt; int_of_num_th; int_add_th; int_mul_th] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `&0 < real_of_int hd` THEN
  UNDISCH_TAC `&0 < real_of_int rd` THEN CONV_TAC REAL_FIELD);;

let CH_Q_LE = prove
 (`forall ln ld hn hd. &0 < ld /\ &0 < hd /\ ln * hd <= hn * ld ==> ch_q ln ld <= ch_q hn hd`,
  REWRITE_TAC[ch_q; int_lt; int_le; int_of_num_th; int_mul_th] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_ARITH
    `x / y * z = (x * z) / y`] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The radius table (Lean Preservation/Chords/Radii.lean)                    *)
(* ------------------------------------------------------------------------- *)

(* ChRad Bnum Bden rnum rden  =  Lean radiusK = <Bnum/Bden, rnum/rden> *)
let chrad_INDUCT,chrad_RECURSION = define_type "chrad = ChRad int int int int";;
let chr_rn = define `chr_rn (ChRad bn bd rn rd) = rn`;;
let chr_rd = define `chr_rd (ChRad bn bd rn rd) = rd`;;
let chr_B = define `chr_B (ChRad bn bd rn rd) = ch_q bn bd`;;
let chr_r = define `chr_r (ChRad bn bd rn rd) = ch_q rn rd`;;

let ch_radii_data =
  List.map (fun l -> match cr_split ' ' l with
      [k; bn; bd; rn; rd] -> (int_of_string k, bn, bd, rn, rd)
    | _ -> failwith "chord_radii") (cr_read_lines "n12/data/cert/chord_radii.txt");;

let ch_radii_def =
  let tm = mk_list (List.map (fun (_, bn, bd, rn, rd) ->
      list_mk_comb (`ChRad`, map cr_int_tm [bn; bd; rn; rd])) ch_radii_data, `:chrad`) in
  cr_get_or_define "ch_radii" tm;;

(* Lean: radiusK_checked, and the denominator is positive *)
let ch_rad_ok = new_definition
 `ch_rad_ok k <=>
    &0 < chr_rd (EL k ch_radii) /\
    ch_radius_check (chr_B (EL k ch_radii)) (chr_r (EL k ch_radii)) (s12_angles k)`;;

let CH_RAD_THM =
  let pre = REWRITE_CONV([ae_check; support_quad; wall_quad; quad_check_on; quad_eval;
                          ch_radius_check; chr_B; chr_r; chr_rd; ch_q] @ AE_ACCESSORS) in
  fun k ->
    let elk = mk_comb (mk_comb (`EL:num->chrad list->chrad`, mk_small_numeral k), `ch_radii`) in
    let el_th = (REWRITE_CONV [ch_radii_def] THENC EL_CONV) elk in
    let ang = mk_comb (`s12_angles`, mk_small_numeral k) in
    let ang_th = (REWRITE_CONV [s12_angles] THENC NUM_REDUCE_CONV THENC
                  REWRITE_CONV [AD64_EL; AD128_EL]) ang in
    let tm = mk_comb (`ch_rad_ok`, mk_small_numeral k) in
    let th = (REWRITE_CONV [ch_rad_ok; el_th; ang_th] THENC pre THENC
              REWRITE_CONV [int_lt; int_of_num_th; int_neg_th] THENC
              REAL_RAT_REDUCE_CONV THENC REWRITE_CONV []) tm in
    EQT_ELIM th;;

let CH_RAD_LIST = Array.init 192 CH_RAD_THM;;

let CH_LT_SUC_STEP = prove
 (`forall P n. (forall k. k < n ==> P k) /\ P n ==> (forall k. k < SUC n ==> P k)`,
  REWRITE_TAC[LT] THEN MESON_TAC[]);;

let CH_RADII_ALL = prove
 (`forall k. k < 192 ==> ch_rad_ok k`,
  let base = prove (`forall k. k < 0 ==> ch_rad_ok k`, REWRITE_TAC[LT]) in
  let step th k =
    let th1 = MP (ISPECL [`ch_rad_ok`; mk_small_numeral k] CH_LT_SUC_STEP)
                 (CONJ th CH_RAD_LIST.(k)) in
    CONV_RULE (ONCE_DEPTH_CONV NUM_SUC_CONV) th1 in
  ACCEPT_TAC (rev_itlist (fun k th -> step th k) (0--191) base));;

(* ------------------------------------------------------------------------- *)
(* Records                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Lean: DirectPruningPlan.Outcome / Branch for the chord branches:
   ChKeep target hints (chord_keep) | ChClose inputs terms (chord_close,
   EmptyContext.Witness).  The branch inputs are not stored: they are
   cut :: rows of the source pose (Lean low_inputs / high_inputs). *)
let chbranch_INDUCT,chbranch_RECURSION = define_type
  "chbranch = ChKeep cpose (crhint list) | ChClose (num list) ((int#num) list)";;

(* Lean: IndexedChord.Neighbor  (source, radius index, the two Neighbor.bounds rows, hints) *)
let chnbr_INDUCT,chnbr_RECURSION = define_type "chnbr = ChNbr cpose num crow crow (crhint list)";;
let chn_src = define `chn_src (ChNbr p k rl rh hs) = p`;;

(* Lean: IndexedChord.Plan  (source, radius index, low cut row, high cut row, low, high) *)
let chplan_INDUCT,chplan_RECURSION = define_type
  "chplan = ChPlan cpose num crow crow chbranch chbranch";;
let chp_src = define `chp_src (ChPlan p k cl ch bl bh) = p`;;

(* the window: horizontal, lo = ln/ld, hi = hn/hd *)
let chwin_INDUCT,chwin_RECURSION = define_type "chwin = ChWin bool int int int int";;
let chw_hz = define `chw_hz (ChWin hz ln ld hn hd) = hz`;;
let chw_lo = define `chw_lo (ChWin hz ln ld hn hd) = ch_q ln ld`;;
let chw_hi = define `chw_hi (ChWin hz ln ld hn hd) = ch_q hn hd`;;

(* Lean: Branch.targets *)
let ch_branch_targets = define
 `(ch_branch_targets (ChKeep t hs) = [t]) /\ (ch_branch_targets (ChClose ins terms) = [])`;;

(* Lean: Branch.Check (inputs given) *)
let ch_branch_check = define
 `(ch_branch_check src inputs (ChKeep t hs) <=>
     cp_angle src = cp_angle t /\ cr_hints_check inputs (cp_rows t) hs) /\
  (ch_branch_check src inputs (ChClose ins terms) <=> cr_empty_check inputs ins terms)`;;

(* Lean: Neighbor.Check  (radius check via the table entry k = angle index) *)
let ch_nbr_check = define
 `ch_nbr_check (ChWin hz ln ld hn hd) (ChNbr src k rl rh hs) <=>
    &0 < ld /\ &0 < hd /\ cp_angle src = k /\ k < 192 /\
    (let R = EL k ch_radii in
     ch_bound_ok hz true (hn * chr_rd R - chr_rn R * hd) (hd * chr_rd R) false rl /\
     ch_bound_ok hz false (ln * chr_rd R + chr_rn R * ld) (ld * chr_rd R) false rh) /\
    cr_hints_check (cp_rows src) [rl; rh] hs`;;

(* Lean: Plan.targets *)
let ch_plan_targets = define
 `ch_plan_targets (ChPlan src k cl ch bl bh) = APPEND (ch_branch_targets bl) (ch_branch_targets bh)`;;

(* Lean: Plan.Check, plus Lean's `ordered : lo <= hi` and the structural
   low_inputs / high_inputs fields *)
let ch_plan_check = define
 `ch_plan_check (ChWin hz ln ld hn hd) (ChPlan src k cl ch bl bh) <=>
    &0 < ld /\ &0 < hd /\ ln * hd <= hn * ld /\ cp_angle src = k /\ k < 192 /\
    (let R = EL k ch_radii in
     ch_bound_ok hz false (ln * chr_rd R - chr_rn R * ld) (ld * chr_rd R) true cl /\
     ch_bound_ok hz true (hn * chr_rd R + chr_rn R * hd) (hd * chr_rd R) true ch) /\
    ch_branch_check src (CONS cl (cp_rows src)) bl /\
    ch_branch_check src (CONS ch (cp_rows src)) bh`;;

(* ------------------------------------------------------------------------- *)
(* Soundness                                                                 *)
(* ------------------------------------------------------------------------- *)

let CH_LEAF_ANGLE = prove
 (`forall p. pl_angle (cr_leaf p) = s12_angles (cp_angle p)`,
  REWRITE_TAC[cr_leaf; pl_angle_th]);;

let CH_RAD_FACTS = prove
 (`forall k. k < 192 ==>
     &0 < chr_rd (EL k ch_radii) /\ ae_check (s12_angles k) /\
     ch_radius_check (chr_B (EL k ch_radii)) (chr_r (EL k ch_radii)) (s12_angles k) /\
     &0 <= chr_r (EL k ch_radii)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `k:num` CH_RADII_ALL) THEN MP_TAC(SPEC `k:num` S12_ANGLES_CHECKED) THEN
  ASM_REWRITE_TAC[ch_rad_ok] THEN SIMP_TAC[ch_radius_check]);;

let CHR_R = prove
 (`forall R. chr_r R = ch_q (chr_rn R) (chr_rd R)`,
  MATCH_MP_TAC chrad_INDUCT THEN REWRITE_TAC[chr_r; chr_rn; chr_rd]);;

(* Lean: IndexedChord.Neighbor.sound *)
let CH_NBR_SOUND = prove
 (`forall W nb c s u v a cut.
     ch_nbr_check W nb /\ &1 < a /\ oriented_realizes (cr_leaf (chn_src nb)) c s u v a /\
     chw_lo W <= cut /\ cut <= chw_hi W
     ==> ch_section (chw_hz W) c s u v a cut`,
  MATCH_MP_TAC chwin_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`hz:bool`; `ln:int`; `ld:int`; `hn:int`; `hd:int`] THEN
  MATCH_MP_TAC chnbr_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`src:cpose`; `k:num`; `rl:crow`; `rh:crow`; `hs:crhint list`] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ch_nbr_check; chn_src; chw_lo; chw_hi; chw_hz; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `k:num` CH_RAD_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cp_rows src`; `[rl:crow; rh]`; `hs:crhint list`;
                `lcx c s u v a`; `lcy c s u v a`] CR_HINTS_SOUND) THEN
  ASM_SIMP_TAC[CR_REALIZES_ROWS; MEM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cr_holds rl (lcx c s u v a) (lcy c s u v a) /\
                cr_holds rh (lcx c s u v a) (lcy c s u v a)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP CH_BOUND_HOLDS (ASSUME
    `ch_bound_ok hz true (hn * chr_rd (EL k ch_radii) - chr_rn (EL k ch_radii) * hd)
                      (hd * chr_rd (EL k ch_radii)) false rl`)] THEN
  REWRITE_TAC[MATCH_MP CH_BOUND_HOLDS (ASSUME
    `ch_bound_ok hz false (ln * chr_rd (EL k ch_radii) + chr_rn (EL k ch_radii) * ld)
                      (ld * chr_rd (EL k ch_radii)) false rh`)] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ASM_SIMP_TAC[CH_Q_SUB; CH_Q_ADD; GSYM CHR_R] THEN
  REWRITE_TAC[GSYM ch_center] THEN STRIP_TAC THEN
  MATCH_MP_TAC CH_ORIENTED_SECTION THEN
  MAP_EVERY EXISTS_TAC [`cr_leaf src`; `chr_B (EL k ch_radii)`; `chr_r (EL k ch_radii)`] THEN
  UNDISCH_TAC `oriented_realizes (cr_leaf src) c s u v a` THEN
  REWRITE_TAC[oriented_realizes; CH_LEAF_ANGLE] THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: DirectPruningPlan.Branch.sound (chord branches) *)
let CH_BRANCH_SOUND = prove
 (`forall b src inputs c s u v a.
     ch_branch_check src inputs b /\ oriented_realizes (cr_leaf src) c s u v a /\
     (forall r. MEM r inputs ==> cr_holds r (lcx c s u v a) (lcy c s u v a))
     ==> exists t. MEM t (ch_branch_targets b) /\ oriented_realizes (cr_leaf t) c s u v a`,
  MATCH_MP_TAC chbranch_INDUCT THEN
  REWRITE_TAC[ch_branch_check; ch_branch_targets; MEM; UNWIND_THM1; UNWIND_THM2] THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CR_TRANSFER THEN EXISTS_TAC `src:cpose` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CR_HINTS_SOUND];
    ASM_MESON_TAC[CR_EMPTY_SOUND; CR_ROWAT_HOLDS]]);;

(* Lean: IndexedChord.Plan.sound *)
let CH_PLAN_SOUND = prove
 (`forall W p c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 c3 s3 u3 v3 a3.
     ch_plan_check W p /\ &1 < a0 /\
     lcont c0 s0 u0 v0 a0 /\ lcont c1 s1 u1 v1 a1 /\ lcont c2 s2 u2 v2 a2 /\ lcont c3 s3 u3 v3 a3 /\
     ldisj c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 /\ ldisj c0 s0 u0 v0 a0 c2 s2 u2 v2 a2 /\
     ldisj c0 s0 u0 v0 a0 c3 s3 u3 v3 a3 /\ ldisj c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 /\
     ldisj c1 s1 u1 v1 a1 c3 s3 u3 v3 a3 /\ ldisj c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 /\
     oriented_realizes (cr_leaf (chp_src p)) c0 s0 u0 v0 a0 /\
     (forall cut. chw_lo W <= cut /\ cut <= chw_hi W ==>
            ch_section (chw_hz W) c1 s1 u1 v1 a1 cut /\ ch_section (chw_hz W) c2 s2 u2 v2 a2 cut /\
            ch_section (chw_hz W) c3 s3 u3 v3 a3 cut)
     ==> exists t. MEM t (ch_plan_targets p) /\ oriented_realizes (cr_leaf t) c0 s0 u0 v0 a0`,
  MATCH_MP_TAC chwin_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`hz:bool`; `ln:int`; `ld:int`; `hn:int`; `hd:int`] THEN
  MATCH_MP_TAC chplan_INDUCT THEN MAP_EVERY X_GEN_TAC
   [`src:cpose`; `k:num`; `cl:crow`; `ch:crow`; `bl:chbranch`; `bh:chbranch`] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ch_plan_check; chp_src; chw_lo; chw_hi; chw_hz; ch_plan_targets; MEM_APPEND;
              LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `k:num` CH_RAD_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`hz:bool`; `ch_q ln ld`; `ch_q hn hd`; `cr_leaf src`;
     `chr_B (EL k ch_radii)`; `chr_r (EL k ch_radii)`;
     `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`;
     `c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`;
     `c2:real`; `s2:real`; `u2:real`; `v2:real`; `a2:real`;
     `c3:real`; `s3:real`; `u3:real`; `v3:real`; `a3:real`] CH_WINDOW_EXCLUDES) THEN
  ASM_SIMP_TAC[CH_Q_LE; CH_LEAF_ANGLE] THEN
  MP_TAC(MATCH_MP CH_BOUND_HOLDS (ASSUME
    `ch_bound_ok hz false (ln * chr_rd (EL k ch_radii) - chr_rn (EL k ch_radii) * ld)
                      (ld * chr_rd (EL k ch_radii)) true cl`)) THEN
  MP_TAC(MATCH_MP CH_BOUND_HOLDS (ASSUME
    `ch_bound_ok hz true (hn * chr_rd (EL k ch_radii) + chr_rn (EL k ch_radii) * hd)
                      (hd * chr_rd (EL k ch_radii)) true ch`)) THEN
  ASM_SIMP_TAC[CH_Q_SUB; CH_Q_ADD; GSYM CHR_R; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[GSYM ch_center] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `forall r. MEM r (cp_rows src) ==> cr_holds r (lcx c0 s0 u0 v0 a0) (lcy c0 s0 u0 v0 a0)`
   ASSUME_TAC THENL [ASM_MESON_TAC[CR_REALIZES_ROWS]; ALL_TAC] THEN
  SUBGOAL_THEN `cr_holds cl (lcx c0 s0 u0 v0 a0) (lcy c0 s0 u0 v0 a0) \/
                cr_holds ch (lcx c0 s0 u0 v0 a0) (lcy c0 s0 u0 v0 a0)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(ch_q ln ld - chr_r (EL k ch_radii) <= ch_center hz c0 s0 u0 v0 a0 /\
                   ch_center hz c0 s0 u0 v0 a0 <= ch_q hn hd + chr_r (EL k ch_radii))` THEN
    REWRITE_TAC[ch_center] THEN REAL_ARITH_TAC; ALL_TAC; ALL_TAC] THENL
   [MP_TAC(SPECL [`bl:chbranch`; `src:cpose`; `CONS (cl:crow) (cp_rows src)`;
                  `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`] CH_BRANCH_SOUND);
    MP_TAC(SPECL [`bh:chbranch`; `src:cpose`; `CONS (ch:crow) (cp_rows src)`;
                  `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`] CH_BRANCH_SOUND)] THEN
  ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL
    [REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]; MESON_TAC[]]));;

(* Lean: IndexedChord.neighbor_cover *)
let CH_NBR_COVER = prove
 (`forall W nbs c s u v a cut.
     ALL (ch_nbr_check W) nbs /\ &1 < a /\
     oriented_pose_covered (MAP cr_leaf (MAP chn_src nbs)) c s u v a /\
     chw_lo W <= cut /\ cut <= chw_hi W
     ==> ch_section (chw_hz W) c s u v a cut`,
  REWRITE_TAC[oriented_pose_covered; MEM_MAP; GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC CH_NBR_SOUND THEN EXISTS_TAC `x':chnbr` THEN ASM_SIMP_TAC[]);;

(* Lean: Preservation.Chords.CK_StepNN.sound (Fin 4 -> OpenSquare, invariants explicit) *)
let ch_chord_transition = new_definition
 `ch_chord_transition (Sd:pose_leaf list) (N1:pose_leaf list) (N2:pose_leaf list)
                      (N3:pose_leaf list) (Td:pose_leaf list) <=>
    forall c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 c3 s3 u3 v3 a3.
      c0 * c0 + s0 * s0 = &1 /\ &0 < a0 /\ c1 * c1 + s1 * s1 = &1 /\ &0 < a1 /\
      c2 * c2 + s2 * s2 = &1 /\ &0 < a2 /\ c3 * c3 + s3 * s3 = &1 /\ &0 < a3 /\
      &1 < a0 /\ &1 < a1 /\ &1 < a2 /\ &1 < a3 /\
      lcont c0 s0 u0 v0 a0 /\ lcont c1 s1 u1 v1 a1 /\ lcont c2 s2 u2 v2 a2 /\ lcont c3 s3 u3 v3 a3 /\
      ldisj c0 s0 u0 v0 a0 c1 s1 u1 v1 a1 /\ ldisj c0 s0 u0 v0 a0 c2 s2 u2 v2 a2 /\
      ldisj c0 s0 u0 v0 a0 c3 s3 u3 v3 a3 /\ ldisj c1 s1 u1 v1 a1 c2 s2 u2 v2 a2 /\
      ldisj c1 s1 u1 v1 a1 c3 s3 u3 v3 a3 /\ ldisj c2 s2 u2 v2 a2 c3 s3 u3 v3 a3 /\
      oriented_pose_covered Sd c0 s0 u0 v0 a0 /\
      oriented_pose_covered N1 c1 s1 u1 v1 a1 /\
      oriented_pose_covered N2 c2 s2 u2 v2 a2 /\
      oriented_pose_covered N3 c3 s3 u3 v3 a3
      ==> oriented_pose_covered Td c0 s0 u0 v0 a0`;;

let ch_plan_ok = new_definition
 `ch_plan_ok W (Td:cpose list) p <=> ch_plan_check W p /\ ALL (\t. MEM t Td) (ch_plan_targets p)`;;

(* Lean: IndexedChord.plans_cover + the three neighbor_cover instances of CK_StepNN.sound *)
let CH_STAGE_SOUND = prove
 (`forall W n1 n2 n3 plans Sd Td.
     ALL (ch_nbr_check W) n1 /\ ALL (ch_nbr_check W) n2 /\ ALL (ch_nbr_check W) n3 /\
     ALL (ch_plan_ok W Td) plans /\ MAP chp_src plans = Sd
     ==> ch_chord_transition (MAP cr_leaf Sd) (MAP cr_leaf (MAP chn_src n1))
           (MAP cr_leaf (MAP chn_src n2)) (MAP cr_leaf (MAP chn_src n3)) (MAP cr_leaf Td)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ch_chord_transition] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `oriented_pose_covered (MAP cr_leaf Sd) c0 s0 u0 v0 a0` THEN
  REWRITE_TAC[oriented_pose_covered; MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:pose_leaf` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `src:cpose` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `exists p. MEM p plans /\ chp_src p = src` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `MEM (src:cpose) Sd` THEN EXPAND_TAC "Sd" THEN
    REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `ALL (ch_plan_ok W Td) plans` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  DISCH_THEN(MP_TAC o SPEC `p:chplan`) THEN ASM_REWRITE_TAC[ch_plan_ok; GSYM ALL_MEM] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`W:chwin`; `p:chplan`;
     `c0:real`; `s0:real`; `u0:real`; `v0:real`; `a0:real`;
     `c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`;
     `c2:real`; `s2:real`; `u2:real`; `v2:real`; `a2:real`;
     `c3:real`; `s3:real`; `u3:real`; `v3:real`; `a3:real`] CH_PLAN_SOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC CH_NBR_COVER THENL
     [EXISTS_TAC `n1:chnbr list`; EXISTS_TAC `n2:chnbr list`; EXISTS_TAC `n3:chnbr list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:cpose` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cr_leaf t` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:cpose` THEN
  ASM_MESON_TAC[]);;

(* with the source / neighbour domains abstracted (for the assembly) *)
let CH_STAGE_THM = prove
 (`forall W n1 n2 n3 plans Sd Td N1 N2 N3.
     ALL (ch_nbr_check W) n1 /\ ALL (ch_nbr_check W) n2 /\ ALL (ch_nbr_check W) n3 /\
     ALL (ch_plan_ok W Td) plans /\ MAP chp_src plans = Sd /\
     MAP chn_src n1 = N1 /\ MAP chn_src n2 = N2 /\ MAP chn_src n3 = N3
     ==> ch_chord_transition (MAP cr_leaf Sd) (MAP cr_leaf N1) (MAP cr_leaf N2)
                             (MAP cr_leaf N3) (MAP cr_leaf Td)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try let l, _ = dest_eq (concl th) in
        fst (dest_const (rator (rator l))) = "MAP" &&
        rand (rator l) = `chn_src` with Failure _ -> false))) THEN
  MATCH_MP_TAC CH_STAGE_SOUND THEN
  MAP_EVERY EXISTS_TAC [`W:chwin`; `plans:chplan list`] THEN ASM_REWRITE_TAC[]);;

(* evaluation: checker equations *)
let () =
  cr_extra_thms := !cr_extra_thms @
    [ch_radii_def; chr_rn; chr_rd; ch_unorient; ch_bound_ok; ch_branch_check;
     ch_nbr_check; ch_plan_check; ch_branch_targets; ch_plan_targets; chn_src; chp_src;
     injectivity "chbranch"; distinctness "chbranch"];
  cr_cs_reset ();;
