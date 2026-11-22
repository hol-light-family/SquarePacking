(* ========================================================================= *)
(* Certificate layer, part 1: integer rows and dictionary poses.             *)
(* Lean: Compact/Core/IntegerSupport.lean (Row, Row.eval, Row.Holds,         *)
(*       Row.normalized, normalized_holds_iff), Compact/Core/RegionDAG.lean  *)
(*       (opposite, opposite_holds), Compact/Bridge/IndexedRelaxation.lean   *)
(*       (Dictionary.pose, Dictionary.transfer).                             *)
(* Design: n12/docs/cert_design.md.  Tag CR_ / cr_.                              *)
(* ========================================================================= *)

needs "n12/certlib/p3_all.ml";;

(* Lean: IntegerSupport.Row  (x y constant : Int, strict : Bool) *)
let crow_INDUCT,crow_RECURSION = define_type "crow = CRow int int int bool";;

let cr_x = define `cr_x (CRow x y c s) = x`;;
let cr_y = define `cr_y (CRow x y c s) = y`;;
let cr_c = define `cr_c (CRow x y c s) = c`;;
let cr_s = define `cr_s (CRow x y c s) = s`;;

let CR_ROW_ETA = prove
 (`forall r. CRow (cr_x r) (cr_y r) (cr_c r) (cr_s r) = r`,
  MATCH_MP_TAC crow_INDUCT THEN REWRITE_TAC[cr_x; cr_y; cr_c; cr_s]);;

(* Lean: Row.eval  (p 0 = px, p 1 = py) *)
let cr_eval = new_definition
 `cr_eval r (px:real) (py:real) =
    real_of_int (cr_x r) * px + real_of_int (cr_y r) * py + real_of_int (cr_c r)`;;

(* Lean: Row.Holds *)
let cr_holds = new_definition
 `cr_holds r (px:real) (py:real) <=>
    if cr_s r then &0 < cr_eval r px py else &0 <= cr_eval r px py`;;

(* Lean: Row.nonneg *)
let CR_HOLDS_NONNEG = prove
 (`forall r px py. cr_holds r px py ==> &0 <= cr_eval r px py`,
  REWRITE_TAC[cr_holds] THEN REPEAT GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* Lean: Row.positive *)
let CR_HOLDS_POS = prove
 (`forall r px py. cr_s r /\ cr_holds r px py ==> &0 < cr_eval r px py`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cr_holds] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* The S12 LinearConstraint 2 of an integer row with denominator one. *)
let cr_lincon = new_definition
 `cr_lincon r = LinCon (Affine [real_of_int (cr_x r); real_of_int (cr_y r)]
                               (real_of_int (cr_c r))) (cr_s r)`;;

let CR_LINCON_HOLDS = prove
 (`forall r px py. lc_holds (cr_lincon r) [px; py] <=> cr_holds r px py`,
  REWRITE_TAC[cr_lincon; lc_holds; aff_eval; ldot; cr_holds; cr_eval] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ADD_RID; REAL_ADD_ASSOC]);;

(* Lean: Row.normalized *)
let cr_normalized = new_definition
 `cr_normalized r (den:num) =
    LinCon (Affine [real_of_int (cr_x r) / &den; real_of_int (cr_y r) / &den]
                   (real_of_int (cr_c r) / &den)) (cr_s r)`;;

(* Lean: Row.normalized_holds_iff *)
let CR_NORMALIZED_HOLDS_IFF = prove
 (`forall r den px py. 0 < den ==>
     (lc_holds (cr_normalized r den) [px; py] <=> cr_holds r px py)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &den` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  REWRITE_TAC[cr_normalized; lc_holds; aff_eval; ldot; cr_holds; cr_eval; REAL_ADD_RID] THEN
  SUBGOAL_THEN
   `(real_of_int (cr_x r) / &den * px + real_of_int (cr_y r) / &den * py) + real_of_int (cr_c r) / &den =
    (real_of_int (cr_x r) * px + real_of_int (cr_y r) * py + real_of_int (cr_c r)) / &den`
   SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &den` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_MUL_LZERO]);;

(* Lean: RegionDAG.opposite *)
let cr_opposite = new_definition
 `cr_opposite r = CRow (--(cr_x r)) (--(cr_y r)) (--(cr_c r)) (~(cr_s r))`;;

(* Lean: RegionDAG.opposite_holds *)
let CR_OPPOSITE_HOLDS = prove
 (`forall r px py. cr_holds (cr_opposite r) px py <=> ~cr_holds r px py`,
  REWRITE_TAC[cr_holds; cr_opposite; cr_eval; cr_x; cr_y; cr_c; cr_s; int_neg_th] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Dictionary poses.                                                         *)
(* A historical dictionary pose is an angle index (into the 192 angles of    *)
(* Lean's C713Shared.angles = HOL s12_angles) and its list of integer rows.  *)
(* ------------------------------------------------------------------------- *)

let cpose_INDUCT,cpose_RECURSION = define_type "cpose = CPose num (crow list)";;

let cp_angle = define `cp_angle (CPose a rs) = a`;;
let cp_rows = define `cp_rows (CPose a rs) = rs`;;

(* Lean: Dictionary.pose, with every denominator cleared (see
   CR_LEAF_NORMALIZED below for the equivalence with the S12 pose). *)
let cr_leaf = new_definition
 `cr_leaf p = PoseLeaf (s12_angles (cp_angle p)) (MAP cr_lincon (cp_rows p))`;;

(* The S12 pose exactly as Lean's Dictionary.pose builds it from rows with
   positive denominators (Lean stores denPred, den = denPred + 1). *)
let cr_dict_leaf = new_definition
 `cr_dict_leaf a (rds:(crow#num)list) =
    PoseLeaf (s12_angles a) (MAP (\rd. cr_normalized (FST rd) (SND rd + 1)) rds)`;;

let pl_angle_th = prove
 (`forall w l. pl_angle (PoseLeaf w l) = w /\ pl_inputs (PoseLeaf w l) = l`,
  REWRITE_TAC[pl_angle; pl_inputs]);;

let CR_CENTRE_HOLDS = prove
 (`forall p c s u v a. (forall f. MEM f (pl_inputs (cr_leaf p)) ==> lc_holds f [lcx c s u v a; lcy c s u v a]) <=>
                 (forall r. MEM r (cp_rows p) ==> cr_holds r (lcx c s u v a) (lcy c s u v a))`,
  REWRITE_TAC[cr_leaf; pl_angle_th; MEM_MAP] THEN MESON_TAC[CR_LINCON_HOLDS]);;

let CR_DICT_CENTRE_HOLDS = prove
 (`forall a rds c s u v a'. (forall f. MEM f (pl_inputs (cr_dict_leaf a rds)) ==> lc_holds f [lcx c s u v a'; lcy c s u v a']) <=>
                 (forall r. MEM r (MAP FST rds) ==> cr_holds r (lcx c s u v a') (lcy c s u v a'))`,
  REWRITE_TAC[cr_dict_leaf; pl_angle_th; MEM_MAP] THEN
  MESON_TAC[CR_NORMALIZED_HOLDS_IFF; ARITH_RULE `0 < n + 1`]);;

(* Dropping the (positive) denominators does not change the pose semantics. *)
let CR_LEAF_NORMALIZED = prove
 (`forall a rds c s u v a'.
     (pose_realizes (cr_dict_leaf a rds) c s u v a' <=>
      pose_realizes (cr_leaf (CPose a (MAP FST rds))) c s u v a') /\
     (oriented_realizes (cr_dict_leaf a rds) c s u v a' <=>
      oriented_realizes (cr_leaf (CPose a (MAP FST rds))) c s u v a')`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `pl_angle (cr_dict_leaf a rds) = pl_angle (cr_leaf (CPose a (MAP FST rds)))`
    ASSUME_TAC THENL [REWRITE_TAC[cr_dict_leaf; cr_leaf; pl_angle_th; cp_angle]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) /\ ((a <=> b) ==> (c <=> d)) ==> (a <=> b) /\ (c <=> d)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pose_realizes; CR_CENTRE_HOLDS; CR_DICT_CENTRE_HOLDS; cp_rows] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN REWRITE_TAC[oriented_realizes] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[angle_witness] THEN ASM_REWRITE_TAC[]]);;

(* Lean: Dictionary.transfer (same angle index, target rows hold at the centre) *)
let CR_TRANSFER = prove
 (`forall src tgt c s u v a.
     cp_angle src = cp_angle tgt /\
     (forall r. MEM r (cp_rows tgt) ==> cr_holds r (lcx c s u v a) (lcy c s u v a)) /\
     oriented_realizes (cr_leaf src) c s u v a
     ==> oriented_realizes (cr_leaf tgt) c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OCV_ORIENTED_TRANSFER THEN
  EXISTS_TAC `cr_leaf src` THEN ASM_REWRITE_TAC[CR_CENTRE_HOLDS] THEN
  REWRITE_TAC[cr_leaf; pl_angle_th] THEN ASM_REWRITE_TAC[]);;

(* Realizing a dictionary pose gives all its rows at the centre. *)
let CR_REALIZES_ROWS = prove
 (`forall p c s u v a. oriented_realizes (cr_leaf p) c s u v a
     ==> forall r. MEM r (cp_rows p) ==> cr_holds r (lcx c s u v a) (lcy c s u v a)`,
  REWRITE_TAC[oriented_realizes; pose_realizes] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM CR_CENTRE_HOLDS]);;
