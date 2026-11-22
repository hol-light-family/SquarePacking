(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C1092WallSymmetry.lean.                           *)
(* Four genuine D4 wall-sign sectors of the original C1092 family.           *)
(* Conventions of OwnerTransport.ml / ContextTransport.ml / Actions.ml:      *)
(* (symmetry u).pullPacking p is the packing (d1,d2,e1,e2) (side l) with    *)
(* c1092ot_pk (EL u c1092ws_symmetry) (c1,c2,a,b) = (d1,d2,e1,e2) (u < 8);   *)
(* it is again a normalized packing (C1092OT_NPACK, stated explicitly);      *)
(* canonicalBranch k is c1092ws_canonical_branch k (k < 4).                  *)
(* BranchEnding k is c1092wsy_ending k; the structure FourBranchEndings is   *)
(* c1092wsy_four (conjunction of its four fields).  Tag C1092WSY_.           *)
(* ========================================================================= *)

needs "n12/geometry/ContextTransport.ml";;
needs "n12/geometry/BranchClassification.ml";;

(* WallContext only reads the four wall bits *)
let C1092WSY_CTX_CONG = prove
 (`forall c1 c2 a b l br br'. c1092wc_ctx c1 c2 a b l br /\ (forall j. j < 4 ==> br j = br' j)
     ==> c1092wc_ctx c1 c2 a b l br'`,
  REWRITE_TAC[c1092wc_ctx] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun c -> DISCH_THEN(fun e -> MP_TAC c THEN REWRITE_TAC[e])) THEN SIMP_TAC[]);;

(* Lean: original_four_branches *)
let C1092WSY_ORIGINAL_FOUR_BRANCHES = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family
     ==> exists u k. u < 8 /\ k < 4 /\
           exists d1 d2 e1 e2. c1092ot_pk (EL u c1092ws_symmetry) (c1,c2,a,b) = (d1,d2,e1,e2) /\
                         NPACK d1 d2 e1 e2 l /\
                         IMAGE binarysum (FFP d1 d2 e1 e2 l) = c1092wc_family /\
                         c1092wc_ctx d1 d2 e1 e2 l (c1092ws_canonical_branch k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C1092WC_ORIGINAL_WALL_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `br:num->bool`) THEN
  MP_TAC(SPEC `br:num->bool` C1092WSB_BRANCH_COVERAGE) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:num` (X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:num`; `k:num`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exists d1 d2 e1 e2. c1092ot_pk (EL u c1092ws_symmetry) (c1,c2,a,b) =
                              (d1:num->real,d2:num->real,e1:num->real,e2:num->real)`
    STRIP_ASSUME_TAC THENL [MESON_TAC[PAIR]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN
    MAP_EVERY EXISTS_TAC [`EL u c1092ws_symmetry`; `c1:num->real`; `c2:num->real`;
                          `a:num->real`; `b:num->real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`EL u c1092ws_symmetry`; `c1:num->real`; `c2:num->real`;
                          `a:num->real`; `b:num->real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092WSY_CTX_CONG THEN
    EXISTS_TAC `c1092ws_branch_action (EL u c1092ws_symmetry) br` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC C1092CT_CONTEXT_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: BranchEnding *)
let c1092wsy_ending = new_definition
 `c1092wsy_ending (k:num) <=>
    forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family /\
                  c1092wc_ctx c1 c2 a b l (c1092ws_canonical_branch k) ==> false`;;

(* Lean: FourBranchEndings (fields windmill, oneExceptional, adjacentPair, oppositePair) *)
let c1092wsy_four = new_definition
 `c1092wsy_four <=> c1092wsy_ending 0 /\ c1092wsy_ending 1 /\ c1092wsy_ending 2 /\ c1092wsy_ending 3`;;

(* Lean: excludes_original *)
let C1092WSY_EXCLUDES_ORIGINAL = prove
 (`c1092wsy_four
   ==> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1092wc_family ==> false`,
  REWRITE_TAC[c1092wsy_four; c1092wsy_ending] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP C1092WSY_ORIGINAL_FOUR_BRANCHES) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` MP_TAC THENL
   [UNDISCH_TAC `k < 4` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_MESON_TAC[]);;
