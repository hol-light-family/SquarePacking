(* ========================================================================= *)
(* Phase 2: Compact/Bridge/AngleSection.lean.                                *)
(* Whole-angle long vertical sections and a shared three-neighbour window.  *)
(* Representation as in n12/certlib/README.md: a Radius <sumUpper, radius>  *)
(* is the pair of reals B r; the subtype proof angle.property of a leaf     *)
(* angle becomes the hypothesis ae_check (pl_angle leaf); a family          *)
(* q : Fin 4 -> OpenSquare is five functions cq sq uq vq aq (indices < 4).  *)
(* sectionRadius is lsec_radius (LongSection.ml), horizontal_long_section   *)
(* LSEC_HORIZONTAL_LONG_SECTION, four_on_one_cut SCAP_FOUR_ON_ONE_CUT.       *)
(* (cert/CH_Chord.ml re-proves the same facts in its own vocabulary.)        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/LongSection.ml";;
needs "n12/certlib/OrientedCoverage.ml";;

(* Lean: Radius.Check *)
let asec_radius_check = new_definition
 `asec_radius_check (B:real) (r:real) w <=>
    &0 <= r /\ &2 * r <= &1 + B - B pow 2 /\
    (quad_check_on (support_quad (&1) (&0) B (&1) (&1)) (ae_lower w) (ae_upper w) \/
     (&0 <= B /\ &2 <= B pow 2))`;;

let ASEC_UNIT_SUM_GE1 = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 ==> &1 <= c + s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN NLIN_TAC []);;

let ASEC_RADIUS_ALGEBRA = prove
 (`forall c s B r. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ c + s <= B /\
             &2 * r <= &1 + B - B pow 2
             ==> r <= (c + s - &2 * c * s) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] ASEC_UNIT_SUM_GE1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (B - (c + s)) * (B + c + s - &1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `&2 * r <= &1 + B - B pow 2` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: Radius.bound *)
let ASEC_RADIUS_BOUND = prove
 (`forall B r w t. ae_check w /\ asec_radius_check B r w /\ ae_lower w <= t /\ t <= ae_upper w
     ==> r <= (normalC t + normalS t - &2 * normalC t * normalS t) / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[asec_radius_check] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ae_check] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "ae_check" with Failure _ -> false)) THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_NONNEGATIVE) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_UNIT) THEN DISCH_TAC THEN
  MATCH_MP_TAC ASEC_RADIUS_ALGEBRA THEN EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`&1`; `&0`; `B:real`; `&1`; `&1`; `ae_lower w`; `ae_upper w`; `t:real`]
      AE_SUPPORT_QUADRATIC_SOUND) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `(normalC t + normalS t) pow 2 <= B pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `normalC t - normalS t` REAL_LE_POW_2) THEN
      UNDISCH_TAC `normalC t pow 2 + normalS t pow 2 = &1` THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: VerticalSection *)
let asec_vsection = new_definition
 `asec_vsection c s u v a (x:real) <=>
    exists l w. &1 < w - l /\ forall y. l < y /\ y < w ==> linside c s u v a x y`;;

let ASEC_VSECTION_SWAP = prove
 (`forall c s u v a x. asec_vsection c s u v a x <=> scap_longsec s c u (--v - a) a x`,
  REWRITE_TAC[asec_vsection; scap_longsec; LINSIDE_PULLSW]);;

(* Lean: sectionRadius_swap  (pullSwap exchanges the frame c, s) *)
let ASEC_SECTION_RADIUS_SWAP = prove
 (`forall c s. lsec_radius s c = lsec_radius c s`,
  REWRITE_TAC[lsec_radius] THEN REWRITE_TAC[REAL_MUL_SYM] THEN REAL_ARITH_TAC);;

let ASEC_LCY_SWAP = prove
 (`forall c s u v a. lcy s c u (--v - a) a = lcx c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: oriented_vertical *)
let ASEC_ORIENTED_VERTICAL = prove
 (`forall leaf B r c s u v a x.
     ae_check (pl_angle leaf) /\ asec_radius_check B r (pl_angle leaf) /\ &1 < a /\
     angle_witness leaf c s u v a /\ abs(x - lcx c s u v a) <= r
     ==> asec_vsection c s u v a x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[angle_witness] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`; `t:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `a':real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ae_check] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "ae_check" with Failure _ -> false)) THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_NONNEGATIVE) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  MP_TAC(SPECL [`B:real`; `r:real`; `pl_angle leaf`; `t:real`] ASEC_RADIUS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r <= lsec_radius c' s'` ASSUME_TAC THENL
   [REWRITE_TAC[lsec_radius; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[real_abs] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`s':real`; `c':real`; `u':real`; `--v' - a:real`; `a:real`; `x:real`]
    LSEC_HORIZONTAL_LONG_SECTION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ASEC_SECTION_RADIUS_SWAP; ASEC_LCY_SWAP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM ASEC_VSECTION_SWAP; asec_vsection] THEN ASM_MESON_TAC[]);;

(* Lean: four_vertical_impossible *)
let ASEC_FOUR_VERTICAL_IMPOSSIBLE = prove
 (`forall (cq:num->real) sq uq vq aq x.
     (forall i. i < 4 ==> lcont (cq i) (sq i) (uq i) (vq i) (aq i)) /\
     (forall i j. i < 4 /\ j < 4 /\ ~(i = j)
            ==> ldisj (cq i) (sq i) (uq i) (vq i) (aq i) (cq j) (sq j) (uq j) (vq j) (aq j)) /\
     (forall i. i < 4 ==> asec_vsection (cq i) (sq i) (uq i) (vq i) (aq i) x)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`sq:num->real`; `cq:num->real`; `uq:num->real`;
                `\i. --(vq:num->real) i - aq i`; `aq:num->real`; `x:real`] SCAP_FOUR_ON_ONE_CUT) THEN
  REWRITE_TAC[GSYM ASEC_VSECTION_SWAP] THEN ASM_SIMP_TAC[LCONT_PULLSW] THEN
  REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN ASM_MESON_TAC[ldisj]);;

(* Lean: interval_nearby *)
let ASEC_INTERVAL_NEARBY = prove
 (`forall lo hi y r. &0 <= r /\ lo <= hi /\ lo - r <= y /\ y <= hi + r
     ==> exists h. lo <= h /\ h <= hi /\ abs(h - y) <= r`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `max lo (y - r)` THEN
  REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: window_excludes *)
let ASEC_WINDOW_EXCLUDES = prove
 (`forall lo hi (cq:num->real) sq uq vq aq source B r.
     lo <= hi /\
     ae_check (pl_angle source) /\ asec_radius_check B r (pl_angle source) /\
     (forall i. i < 4 ==> &1 < aq i) /\
     (forall i. i < 4 ==> lcont (cq i) (sq i) (uq i) (vq i) (aq i)) /\
     (forall i j. i < 4 /\ j < 4 /\ ~(i = j)
            ==> ldisj (cq i) (sq i) (uq i) (vq i) (aq i) (cq j) (sq j) (uq j) (vq j) (aq j)) /\
     oriented_realizes source (cq 0) (sq 0) (uq 0) (vq 0) (aq 0) /\
     (forall x. lo <= x /\ x <= hi ==> forall i. i < 3
            ==> asec_vsection (cq (SUC i)) (sq (SUC i)) (uq (SUC i)) (vq (SUC i)) (aq (SUC i)) x)
     ==> ~(lo - r <= lcx (cq 0) (sq 0) (uq 0) (vq 0) (aq 0) /\
           lcx (cq 0) (sq 0) (uq 0) (vq 0) (aq 0) <= hi + r)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oriented_realizes] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= r` ASSUME_TAC THENL
   [ASM_MESON_TAC[asec_radius_check]; ALL_TAC] THEN
  MP_TAC(SPECL [`lo:real`; `hi:real`; `lcx (cq 0) (sq 0) (uq 0) (vq 0) (aq 0)`; `r:real`]
    ASEC_INTERVAL_NEARBY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`source:pose_leaf`; `B:real`; `r:real`; `(cq:num->real) 0`; `(sq:num->real) 0`;
                `(uq:num->real) 0`; `(vq:num->real) 0`; `(aq:num->real) 0`; `x:real`]
    ASEC_ORIENTED_VERTICAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[ARITH_RULE `0 < 4`]; DISCH_TAC] THEN
  MATCH_MP_TAC ASEC_FOUR_VERTICAL_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cq:num->real`; `sq:num->real`; `uq:num->real`; `vq:num->real`;
                        `aq:num->real`; `x:real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i = 0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
    try fst(dest_var(fst(dest_forall(concl th)))) = "x" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `PRE i`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> SUC(PRE i) = i`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;
