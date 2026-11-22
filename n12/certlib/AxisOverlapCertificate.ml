(* ========================================================================= *)
(* Port of source/S12/AxisOverlapCertificate.lean (Jatloe, N12-jatloe).      *)
(* r.atCenter hr x y = (r.toSquare hr).translated (-x) (-y) is the 5-tuple   *)
(* (rs_c r, rs_s r, rs_at_u r x y, rs_at_v r x y, rs_side r).                *)
(* The AxisOverlapCertificate structure is AxCert first second inputsA       *)
(* inputsB proofs; the subtype checks of first/second are in axcert_check.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/SquareAxes.ml";;
needs "n12/certlib/AffineOverlap.ml";;

(* Lean: ReferenceSquare.ratRadius *)
let rs_rat_radius = new_definition
 `rs_rat_radius r nx ny =
    rs_side r / &2 * (abs(nx * rs_c r + ny * rs_s r) + abs(--nx * rs_s r + ny * rs_c r))`;;

(* Lean: ReferenceSquare.atCenter (lower face offsets of the translated square) *)
let rs_at_u = new_definition
 `rs_at_u r x y = --(rs_side r) / &2 - (rs_c r * --x + rs_s r * --y)`;;
let rs_at_v = new_definition
 `rs_at_v r x y = --(rs_side r) / &2 - (--(rs_s r) * --x + rs_c r * --y)`;;

(* Lean: ReferenceSquare.atCenter_inside *)
let AOC_ATCENTER_INSIDE = prove
 (`forall r x y px py.
     linside (rs_c r) (rs_s r) (rs_at_u r x y) (rs_at_v r x y) (rs_side r) px py <=>
     linside (rs_c r) (rs_s r) (--(rs_side r) / &2) (--(rs_side r) / &2) (rs_side r)
             (px - x) (py - y)`,
  REWRITE_TAC[linside; rs_at_u; rs_at_v] THEN REAL_ARITH_TAC);;

(* Lean: ReferenceSquare.atCenter_X *)
let AOC_ATCENTER_X = prove
 (`forall r x y. rs_check r
     ==> lcx (rs_c r) (rs_s r) (rs_at_u r x y) (rs_at_v r x y) (rs_side r) = x`,
  REWRITE_TAC[rs_check; lcx; rs_at_u; rs_at_v] THEN CONV_TAC REAL_RING);;

(* Lean: ReferenceSquare.atCenter_Y *)
let AOC_ATCENTER_Y = prove
 (`forall r x y. rs_check r
     ==> lcy (rs_c r) (rs_s r) (rs_at_u r x y) (rs_at_v r x y) (rs_side r) = y`,
  REWRITE_TAC[rs_check; lcy; rs_at_u; rs_at_v] THEN CONV_TAC REAL_RING);;

(* Lean: ReferenceSquare.ratRadius_sound *)
let AOC_RATRADIUS_SOUND = prove
 (`forall r nx ny. tss_support_radius (rs_c r) (rs_s r) (rs_side r) nx ny = rs_rat_radius r nx ny`,
  REWRITE_TAC[tss_support_radius; rs_rat_radius]);;

(* Lean: pairAxes *)
let pair_axes = new_definition
 `pair_axes a b = [(rs_c a, rs_s a); (--(rs_s a), rs_c a); (rs_c b, rs_s b); (--(rs_s b), rs_c b)]`;;

(* Lean: axisGapForm *)
let axis_gap_form = new_definition
 `axis_gap_form a b nx ny =
    LinCon (Affine [nx; ny; --nx; --ny] (rs_rat_radius a nx ny + rs_rat_radius b nx ny)) true`;;

(* Lean: axisGapForm_holds *)
let AOC_AXISGAPFORM_HOLDS = prove
 (`forall a b nx ny x0 x1 x2 x3.
     lc_holds (axis_gap_form a b nx ny) [x0; x1; x2; x3] <=>
     nx * (x2 - x0) + ny * (x3 - x1) < rs_rat_radius a nx ny + rs_rat_radius b nx ny`,
  REWRITE_TAC[axis_gap_form; lc_holds; aff_eval; ldot] THEN REAL_ARITH_TAC);;

(* Lean: axisOverlapForms *)
let axis_overlap_forms = new_definition
 `axis_overlap_forms a b =
    lflat (MAP (\n. [axis_gap_form a b (FST n) (SND n);
                    axis_gap_form a b (--(FST n)) (--(SND n))]) (pair_axes a b))`;;

(* Lean: ratRadius_neg *)
let AOC_RATRADIUS_NEG = prove
 (`forall a nx ny. rs_rat_radius a (--nx) (--ny) = rs_rat_radius a nx ny`,
  REWRITE_TAC[rs_rat_radius] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  BINOP_TAC THEN REAL_ARITH_TAC);;

(* the eight gap rows give strict two-sided bounds on each axis *)
let AOC_NO_AXIS = prove
 (`forall a b x0 x1 x2 x3 nx ny.
     (forall f. MEM f (axis_overlap_forms a b) ==> lc_holds f [x0; x1; x2; x3]) /\
     MEM (nx,ny) (pair_axes a b)
     ==> abs(nx * (x2 - x0) + ny * (x3 - x1)) < rs_rat_radius a nx ny + rs_rat_radius b nx ny`,
  REPEAT GEN_TAC THEN REWRITE_TAC[axis_overlap_forms; MEM_LFLAT; MEM_MAP] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `axis_gap_form a b nx ny`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `axis_gap_form a b (--nx) (--ny)`) THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (c /\ d ==> e) ==> (a ==> c) ==> (b ==> d) ==> e`) THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `[axis_gap_form a b nx ny; axis_gap_form a b (--nx) (--ny)]` THEN
    REWRITE_TAC[MEM] THEN EXISTS_TAC `(nx:real,ny:real)` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `[axis_gap_form a b nx ny; axis_gap_form a b (--nx) (--ny)]` THEN
    REWRITE_TAC[MEM] THEN EXISTS_TAC `(nx:real,ny:real)` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[AOC_AXISGAPFORM_HOLDS; AOC_RATRADIUS_NEG] THEN REAL_ARITH_TAC]);;

(* Lean: axisOverlapForms_sound *)
let AOC_AXISOVERLAPFORMS_SOUND = prove
 (`forall a b x0 x1 x2 x3.
     rs_check a /\ rs_check b /\
     (forall f. MEM f (axis_overlap_forms a b) ==> lc_holds f [x0; x1; x2; x3])
     ==> overlaps_at (rs_sqset a) (rs_sqset b) (x0,x1) (x2,x3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`rs_c a`; `rs_s a`; `rs_at_u a x0 x1`; `rs_at_v a x0 x1`; `rs_side a`;
                `rs_c b`; `rs_s b`; `rs_at_u b x2 x3`; `rs_at_v b x2 x3`; `rs_side b`]
    SAX_SQUARE_SEPARATING_AXES) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `rs_check a` THEN UNDISCH_TAC `rs_check b` THEN
    REWRITE_TAC[rs_check; REAL_POW_2] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ldisj; AOC_ATCENTER_INSIDE] THEN
    MAP_EVERY X_GEN_TAC [`px:real`; `py:real`] THEN STRIP_TAC THEN
    UNDISCH_TAC `~overlaps_at (rs_sqset a) (rs_sqset b) (x0,x1) (x2,x3)` THEN
    REWRITE_TAC[overlaps_at] THEN EXISTS_TAC `(px:real,py:real)` THEN
    ASM_REWRITE_TAC[psub; rs_sqset; IN_SQSET; FST; SND];
    ALL_TAC] THEN
  REWRITE_TAC[axis_separates] THEN
  ASM_SIMP_TAC[AOC_ATCENTER_X; AOC_ATCENTER_Y; AOC_RATRADIUS_SOUND] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC AOC_NO_AXIS THEN ASM_REWRITE_TAC[pair_axes; MEM]);;

(* Lean: structure AxisOverlapCertificate *)
let axcert_INDUCT,axcert_RECURSION = define_type
 "axcert = AxCert refsq refsq (lincon list) (lincon list) (((real#lincon)list)list)";;
let ax_first = define `ax_first (AxCert f s ia ib pr) = f`;;
let ax_second = define `ax_second (AxCert f s ia ib pr) = s`;;
let ax_inputsA = define `ax_inputsA (AxCert f s ia ib pr) = ia`;;
let ax_inputsB = define `ax_inputsB (AxCert f s ia ib pr) = ib`;;
let ax_proofs = define `ax_proofs (AxCert f s ia ib pr) = pr`;;

(* Lean: AxisOverlapCertificate.inputs *)
let ax_inputs = new_definition
 `ax_inputs w = APPEND (MAP lc_liftl (ax_inputsA w)) (MAP lc_liftr (ax_inputsB w))`;;

(* Lean: AxisOverlapCertificate.Check, with the subtype checks of first, second *)
let axcert_check = new_definition
 `axcert_check w <=>
    rs_check (ax_first w) /\ rs_check (ax_second w) /\
    forall target. MEM target (axis_overlap_forms (ax_first w) (ax_second w)) ==>
      exists terms. MEM terms (ax_proofs w) /\ limp_check 4 (ax_inputs w) target terms`;;

(* Lean: AxisOverlapCertificate.sound *)
let AOC_SOUND = prove
 (`forall w x0 x1 x2 x3.
     axcert_check w /\
     (forall f. MEM f (ax_inputsA w) ==> lc_holds f [x0; x1]) /\
     (forall f. MEM f (ax_inputsB w) ==> lc_holds f [x2; x3])
     ==> overlaps_at (rs_sqset (ax_first w)) (rs_sqset (ax_second w)) (x0,x1) (x2,x3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[axcert_check] THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall f. MEM f (ax_inputs w) ==> lc_holds f [x0; x1; x2; x3]` ASSUME_TAC THENL
   [REWRITE_TAC[ax_inputs] THEN MATCH_MP_TAC AO_INPUTS_HOLD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC AOC_AXISOVERLAPFORMS_SOUND THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:lincon` o check (fun th ->
    can (find_term ((=) `ax_proofs:axcert->((real#lincon)list)list`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC LI_LINEAR_IMPLICATION_SOUND THEN
  MAP_EVERY EXISTS_TAC [`4`; `ax_inputs w`; `terms:(real#lincon)list`] THEN
  ASM_REWRITE_TAC[]);;
