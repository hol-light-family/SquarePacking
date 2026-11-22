(* ========================================================================= *)
(* Port of source/S12/SquareAxes.lean (Jatloe, N12-jatloe).                  *)
(* Squares q, r are the 5-tuples cq sq uq vq aq and cr sr ur vr ar;          *)
(* squareRadius q nx ny is tss_support_radius cq sq aq nx ny.                *)
(* N12Compact.SATGeneral.overlap is SSG_OVERLAP (certlib/ScalarSATGeneral.ml).    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/AxisGap.ml";;
needs "n12/certlib/ScalarSATGeneral.ml";;

(* Lean: relativeC *)
let relC = new_definition `relC (cq:real) sq cr sr = cq * cr + sq * sr`;;
(* Lean: relativeS *)
let relS = new_definition `relS (cq:real) sq cr sr = --sq * cr + cq * sr`;;

(* Lean: relative_unit *)
let SAX_RELATIVE_UNIT = prove
 (`forall cq sq cr sr. cq * cq + sq * sq = &1 /\ cr * cr + sr * sr = &1
     ==> relC cq sq cr sr pow 2 + relS cq sq cr sr pow 2 = &1`,
  REWRITE_TAC[relC; relS] THEN CONV_TAC REAL_RING);;

(* Lean: rotated_dot *)
let SAX_ROTATED_DOT = prove
 (`forall c s x y X Y. c pow 2 + s pow 2 = &1
     ==> (c * x + s * y) * (c * X + s * Y) + (--s * x + c * y) * (--s * X + c * Y) =
         x * X + y * Y`,
  CONV_TAC REAL_RING);;

(* Lean: rotated_coordinate *)
let SAX_ROTATED_COORDINATE = prove
 (`forall c s k l x y. c pow 2 + s pow 2 = &1
     ==> (c * k + s * l) * (c * x + s * y) + (--s * k + c * l) * (--s * x + c * y) =
         k * x + l * y`,
  CONV_TAC REAL_RING);;

(* Lean: rotated_cross_coordinate *)
let SAX_ROTATED_CROSS_COORDINATE = prove
 (`forall c s k l x y. c pow 2 + s pow 2 = &1
     ==> --(--s * k + c * l) * (c * x + s * y) + (c * k + s * l) * (--s * x + c * y) =
         --l * x + k * y`,
  CONV_TAC REAL_RING);;

(* Lean: squareRadius_self *)
let SAX_SQUARERADIUS_SELF = prove
 (`forall c s a. c * c + s * s = &1 ==> tss_support_radius c s a c s = a / &2`,
  REWRITE_TAC[tss_support_radius] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(c * c + s * s) + abs(--c * s + s * c) = &1`
    (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN ASM_REAL_ARITH_TAC);;

(* Lean: squareRadius_turn_axis *)
let SAX_SQUARERADIUS_TURN_AXIS = prove
 (`forall c s a nx ny. tss_support_radius c s a (--ny) nx = tss_support_radius c s a nx ny`,
  REWRITE_TAC[tss_support_radius] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* Lean: squareRadius_cross *)
let SAX_SQUARERADIUS_CROSS = prove
 (`forall cq sq cr sr ar. tss_support_radius cr sr ar cq sq =
     ar / &2 * (abs(relC cq sq cr sr) + abs(relS cq sq cr sr))`,
  REWRITE_TAC[tss_support_radius; relC; relS] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  BINOP_TAC THEN REAL_ARITH_TAC);;

(* Lean: relative_abs_swap *)
let SAX_RELATIVE_ABS_SWAP = prove
 (`forall cq sq cr sr. abs(relC cr sr cq sq) + abs(relS cr sr cq sq) =
                 abs(relC cq sq cr sr) + abs(relS cq sq cr sr)`,
  REWRITE_TAC[relC; relS] THEN REPEAT GEN_TAC THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* Lean: AxisSeparates *)
let axis_separates = new_definition
 `axis_separates cq sq uq vq aq cr sr ur vr ar nx ny <=>
    tss_support_radius cq sq aq nx ny + tss_support_radius cr sr ar nx ny <=
    abs(nx * (lcx cr sr ur vr ar - lcx cq sq uq vq aq) +
        ny * (lcy cr sr ur vr ar - lcy cq sq uq vq aq))`;;

(* Lean: square_separating_axes *)
let SAX_SQUARE_SEPARATING_AXES = prove
 (`forall cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     ldisj cq sq uq vq aq cr sr ur vr ar
     ==> axis_separates cq sq uq vq aq cr sr ur vr ar cq sq \/
         axis_separates cq sq uq vq aq cr sr ur vr ar (--sq) cq \/
         axis_separates cq sq uq vq aq cr sr ur vr ar cr sr \/
         axis_separates cq sq uq vq aq cr sr ur vr ar (--sr) cr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p \/ q \/ r \/ s <=> ~(~p /\ ~q /\ ~r /\ ~s)`] THEN
  REWRITE_TAC[axis_separates; REAL_NOT_LE] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAX_SQUARERADIUS_TURN_AXIS]) THEN
  SUBGOAL_THEN `tss_support_radius cq sq aq cq sq = aq / &2 /\
                tss_support_radius cr sr ar cr sr = ar / &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SAX_SQUARERADIUS_SELF]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `tss_support_radius cq sq aq cq sq = aq / &2`;
                              ASSUME `tss_support_radius cr sr ar cr sr = ar / &2`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAX_SQUARERADIUS_CROSS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAX_RELATIVE_ABS_SWAP]) THEN
  ABBREV_TAC `dx = lcx cr sr ur vr ar - lcx cq sq uq vq aq` THEN
  ABBREV_TAC `dy = lcy cr sr ur vr ar - lcy cq sq uq vq aq` THEN
  ABBREV_TAC `X = cq * dx + sq * dy` THEN
  ABBREV_TAC `Y = --sq * dx + cq * dy` THEN
  ABBREV_TAC `c = relC cq sq cr sr` THEN
  ABBREV_TAC `s = relS cq sq cr sr` THEN
  SUBGOAL_THEN `c * X + s * Y = cr * dx + sr * dy /\ --s * X + c * Y = --sr * dx + cr * dy`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c"; "s"; "X"; "Y"] THEN REWRITE_TAC[relC; relS] THEN
    CONJ_TAC THEN UNDISCH_TAC `cq * cq + sq * sq = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`aq / &2`; `ar / &2`; `c:real`; `s:real`; `X:real`; `Y:real`;
                `c * X + s * Y`; `--s * X + c * Y`] SSG_OVERLAP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MAP_EVERY EXPAND_TAC ["c"; "s"] THEN MATCH_MP_TAC SAX_RELATIVE_UNIT THEN
      ASM_REWRITE_TAC[];
      REFL_TAC; REFL_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ssg_overlap; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  UNDISCH_TAC `ldisj cq sq uq vq aq cr sr ur vr ar` THEN REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`lcx cq sq uq vq aq + cq * x - sq * y`;
                             `lcy cq sq uq vq aq + sq * x + cq * y`]) THEN
  ASM_SIMP_TAC[SSB_INSIDE_CENTERED] THEN
  SUBGOAL_THEN
   `cq * ((lcx cq sq uq vq aq + cq * x - sq * y) - lcx cq sq uq vq aq) +
    sq * ((lcy cq sq uq vq aq + sq * x + cq * y) - lcy cq sq uq vq aq) = x /\
    --sq * ((lcx cq sq uq vq aq + cq * x - sq * y) - lcx cq sq uq vq aq) +
    cq * ((lcy cq sq uq vq aq + sq * x + cq * y) - lcy cq sq uq vq aq) = y /\
    cr * ((lcx cq sq uq vq aq + cq * x - sq * y) - lcx cr sr ur vr ar) +
    sr * ((lcy cq sq uq vq aq + sq * x + cq * y) - lcy cr sr ur vr ar) =
      c * x + s * y - (c * X + s * Y) /\
    --sr * ((lcx cq sq uq vq aq + cq * x - sq * y) - lcx cr sr ur vr ar) +
    cr * ((lcy cq sq uq vq aq + sq * x + cq * y) - lcy cr sr ur vr ar) =
      --s * x + c * y - (--s * X + c * Y)`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["c"; "s"; "dx"; "dy"] THEN REWRITE_TAC[relC; relS] THEN
    REPEAT CONJ_TAC THEN UNDISCH_TAC `cq * cq + sq * sq = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REWRITE_TAC[SSI_ABS_LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SSI_ABS_LT]) THEN ASM_REAL_ARITH_TAC);;
