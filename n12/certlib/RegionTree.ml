(* ========================================================================= *)
(* Port of source/S12/RegionTree.lean (Jatloe, N12-jatloe).                  *)
(* PlaneConstraint = LinearConstraint 2 = lincon (dimension 2);              *)
(* RegionConstraints = lincon list; FarkasTerms = (real#lincon) list.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/LinearImplication.ml";;

(* Lean: inductive RegionTree *)
let rtree_INDUCT,rtree_RECURSION = define_type
 "rtree = RLeaf
        | REmpty ((real#lincon)list)
        | RCut lincon rtree rtree
        | RForbidden (lincon list) (((real#lincon)list)list)";;

(* Lean: RegionTree.Check inputs forbidden tree *)
let rtree_check = define
 `(rtree_check inputs forbidden RLeaf <=> true) /\
  (rtree_check inputs forbidden (REmpty terms) <=> lcert_check 2 inputs terms) /\
  (rtree_check inputs forbidden (RCut test yes no) <=>
     rtree_check (CONS test inputs) forbidden yes /\
     rtree_check (CONS (lc_opposite test) inputs) forbidden no) /\
  (rtree_check inputs forbidden (RForbidden block proofs) <=>
     MEM block forbidden /\
     forall r. MEM r block ==> exists terms. MEM terms proofs /\ limp_check 2 inputs r terms)`;;

(* Lean: RegionTree.leaves inputs tree *)
let rtree_leaves = define
 `(rtree_leaves inputs RLeaf = [inputs]) /\
  (rtree_leaves inputs (REmpty terms) = []) /\
  (rtree_leaves inputs (RCut test yes no) =
     APPEND (rtree_leaves (CONS test inputs) yes)
            (rtree_leaves (CONS (lc_opposite test) inputs) no)) /\
  (rtree_leaves inputs (RForbidden block proofs) = [])`;;

(* Lean: RegionTree.sound *)
let RT_SOUND = prove
 (`forall tree inputs forbidden p.
     rtree_check inputs forbidden tree /\ (forall r. MEM r inputs ==> lc_holds r p) /\
     (forall block. MEM block forbidden ==> ~(forall r. MEM r block ==> lc_holds r p))
     ==> exists leaf. MEM leaf (rtree_leaves inputs tree) /\ forall r. MEM r leaf ==> lc_holds r p`,
  MATCH_MP_TAC rtree_INDUCT THEN REWRITE_TAC[rtree_check; rtree_leaves; MEM] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`2`; `inputs:lincon list`; `a:(real#lincon)list`]
      LC_LINEAR_CERTIFICATE_SOUND) THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`test:lincon`; `yes:rtree`; `no:rtree`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "y") (LABEL_TAC "n")) THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[MEM_APPEND] THEN
    ASM_CASES_TAC `lc_holds test p` THENL
     [REMOVE_THEN "y" (MP_TAC o SPECL [`CONS (test:lincon) inputs`; `forbidden:(lincon list)list`;
        `p:real list`]) THEN ASM_REWRITE_TAC[MEM] THEN
      ANTS_TAC THENL [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `leaf:lincon list`) THEN EXISTS_TAC `leaf:lincon list` THEN
      ASM_REWRITE_TAC[];
      REMOVE_THEN "n" (MP_TAC o SPECL [`CONS (lc_opposite test) (inputs:lincon list)`;
        `forbidden:(lincon list)list`; `p:real list`]) THEN ASM_REWRITE_TAC[MEM] THEN
      ANTS_TAC THENL [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[LI_OPPOSITE_HOLDS]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `leaf:lincon list`) THEN EXISTS_TAC `leaf:lincon list` THEN
      ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `forall block. MEM block (forbidden:(lincon list)list)
                   ==> ~(forall r. MEM r block ==> lc_holds r (p:real list))` THEN
    DISCH_THEN(MP_TAC o SPEC `a0:lincon list`) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:lincon` THEN DISCH_TAC THEN
    UNDISCH_TAC `forall r. MEM r (a0:lincon list) ==> exists terms. MEM terms (a1:((real#lincon)list)list) /\
                   limp_check 2 (inputs:lincon list) r terms` THEN
    DISCH_THEN(MP_TAC o SPEC `r:lincon`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC LI_LINEAR_IMPLICATION_SOUND THEN
    MAP_EVERY EXISTS_TAC [`2`; `inputs:lincon list`; `terms:(real#lincon)list`] THEN
    ASM_REWRITE_TAC[]]);;
