(* ========================================================================= *)
(* Port of source/S12/AxisGap.lean (Jatloe, N12-jatloe).                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/AxisAlgebra.ml";;

(* Lean: quadrant_cover *)
let AXG_QUADRANT_COVER = prove
 (`forall P:real->real->bool.
     (forall x y. &0 <= x /\ &0 <= y ==> P x y) /\ (forall x y. P y (--x) ==> P x y)
     ==> forall x y. P x y`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pos") (LABEL_TAC "turn")) THEN
  REPEAT GEN_TAC THEN
  let turn x y = USE_THEN "turn" (MATCH_MP_TAC o SPECL [x; y]) in
  ASM_CASES_TAC `&0 <= x` THEN ASM_CASES_TAC `&0 <= y` THENL
   [USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    turn `x:real` `y:real` THEN turn `y:real` `--x:real` THEN turn `--x:real` `--y:real` THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN USE_THEN "pos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    turn `x:real` `y:real` THEN USE_THEN "pos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    turn `x:real` `y:real` THEN turn `y:real` `--x:real` THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

(* Lean: planeL1_turn *)
let AXG_PLANEL1_TURN = prove
 (`forall c s x y. planeL1 c s y (--x) = planeL1 c s x y`,
  REWRITE_TAC[planeL1] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* Lean: axisOverlap_turn *)
let AXG_AXISOVERLAP_TURN = prove
 (`forall a b c s dx dy. axis_overlap a b c s dx dy ==> axis_overlap a b c s dy (--dx)`,
  REWRITE_TAC[axis_overlap] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> a') /\ (b ==> b') /\ (c ==> c') /\ (d ==> d')
                     ==> a /\ b /\ c /\ d ==> b' /\ a' /\ d' /\ c'`) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `x = y ==> x < r ==> y < r`) THEN
  REAL_ARITH_TAC);;

(* Lean: NormalGap *)
let normal_gap = new_definition
 `normal_gap a b c s dx dy nx ny <=>
    nx * dx + ny * dy < a * (abs nx + abs ny) + b * planeL1 c s nx ny`;;

(* Lean: normalGap_turn_iff *)
let AXG_NORMALGAP_TURN_IFF = prove
 (`forall a b c s dx dy nx ny.
     normal_gap a b c s dy (--dx) ny (--nx) <=> normal_gap a b c s dx dy nx ny`,
  REWRITE_TAC[normal_gap; AXG_PLANEL1_TURN; REAL_ABS_NEG] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `x = x' /\ y = y' ==> (x < y <=> x' < y')`) THEN CONJ_TAC THEN REAL_ARITH_TAC);;

(* Lean: axis_normal_gap *)
let AXG_AXIS_NORMAL_GAP = prove
 (`forall a b c s dx dy nx ny.
     &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
     axis_overlap a b c s dx dy /\ (~(nx = &0) \/ ~(ny = &0))
     ==> normal_gap a b c s dx dy nx ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `forall nx ny. (~(nx = &0) \/ ~(ny = &0)) ==> forall dx dy.
      axis_overlap a b c s dx dy ==> normal_gap a b c s dx dy nx ny`
    (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC AXG_QUADRANT_COVER THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[normal_gap] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC AXA_POSITIVE_NORMAL_GAP THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT(DISCH_TAC ORELSE GEN_TAC) THEN
    ONCE_REWRITE_TAC[GSYM AXG_NORMALGAP_TURN_IFF] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
    ASM_SIMP_TAC[AXG_AXISOVERLAP_TURN]]);;

(* Lean: AxisOverlapAbs *)
let axis_overlap_abs = new_definition
 `axis_overlap_abs a b c s dx dy <=>
    abs dx < a + b * (abs c + abs s) /\ abs dy < a + b * (abs c + abs s) /\
    abs(c * dx + s * dy) < b + a * (abs c + abs s) /\
    abs(--s * dx + c * dy) < b + a * (abs c + abs s)`;;

(* Lean: planeL1_frame_turn *)
let AXG_PLANEL1_FRAME_TURN = prove
 (`forall c s x y. planeL1 s (--c) x y = planeL1 c s x y`,
  REWRITE_TAC[planeL1] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* Lean: axisOverlapAbs_frame_turn *)
let AXG_AXISOVERLAPABS_FRAME_TURN = prove
 (`forall a b c s dx dy. axis_overlap_abs a b c s dx dy ==> axis_overlap_abs a b s (--c) dx dy`,
  REWRITE_TAC[axis_overlap_abs; REAL_ABS_NEG] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `abs s + abs c = abs c + abs s` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(c ==> d') /\ (d ==> c')
                     ==> a /\ b /\ c /\ d ==> a /\ b /\ c' /\ d'`) THEN
  CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `x = y ==> x < r ==> y < r`) THEN
  REAL_ARITH_TAC);;

(* Lean: four_axes_algebra *)
let AXG_FOUR_AXES_ALGEBRA = prove
 (`forall a b c s dx dy nx ny.
     c pow 2 + s pow 2 = &1 /\ axis_overlap_abs a b c s dx dy /\ (~(nx = &0) \/ ~(ny = &0))
     ==> normal_gap a b c s dx dy nx ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `forall c s. c pow 2 + s pow 2 = &1 ==> axis_overlap_abs a b c s dx dy
      ==> normal_gap a b c s dx dy nx ny` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC AXG_QUADRANT_COVER THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC AXG_AXIS_NORMAL_GAP THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `axis_overlap_abs a b x y dx dy` THEN
    ASM_SIMP_TAC[axis_overlap_abs; axis_overlap; REAL_ARITH `&0 <= x ==> abs x = x`];
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_SIMP_TAC[AXG_AXISOVERLAPABS_FRAME_TURN; REAL_POW_NEG; ARITH] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[normal_gap; AXG_PLANEL1_FRAME_TURN]]);;
