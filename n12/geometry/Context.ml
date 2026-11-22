(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/Context.lean.                              *)
(* Conventions of SwapReduction.ml / WallBranches.ml / MissingCornerBounds:  *)
(* q = p \/ q = transposePacking p is (d1,d2,e1,e2) = (c1,c2,a,b) \/          *)
(* (d1,d2,e1,e2) = (c2,c1,b,a) (side l); a WallOwners q structure is w with  *)
(* c977wb_owners d1 d2 e1 e2 l w, WallHalfSpaces is c977wb_half;             *)
(* StrengthenedMissingCorner is c977mcp_strengthened, CanonicalCornerBounds  *)
(* is c977mcb_ccb; retained rows as in C977SR_RETAINED_*; ExcludesCase 977   *)
(* is excl_case 977.  Tag C977CTX_.                                          *)
(* ========================================================================= *)

needs "n12/geometry/SwapReduction.ml";;
needs "n12/geometry/WallBranches.ml";;
needs "n12/geometry/MissingCornerBounds.ml";;
needs "n12/geometry/InteriorFaces.ml";;
needs "n12/geometry/UnusedMarkerDistance.ml";;
needs "n12/geometry/CC_C977_RowIdentity.ml";;

(* Lean: canonical_wall_context_cover *)
let C977CTX_CANONICAL_WALL_CONTEXT_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists d1 d2 e1 e2.
           ((d1,d2,e1,e2) = (c1,c2,a,b) \/ (d1,d2,e1,e2) = (c2,c1,b,a)) /\
           NPACK d1 d2 e1 e2 l /\ IMAGE binarysum (FFP d1 d2 e1 e2 l) = ccc977ri_family /\
           exists i j. i < 12 /\ j < 12 /\ ownmask (d1 i) (d2 i) (e1 i) (e2 i) l = 1 /\
                 ownmask (d1 j) (d2 j) (e1 j) (e2 j) l = 2 /\ ~(i = j) /\
                 c977mcp_strengthened (e1 i) (e2 i) (e1 i * d1 i + e2 i * d2 i - l / &2)
                                      (--e2 i * d1 i + e1 i * d2 i - l / &2) l /\
                 exists w. c977wb_owners d1 d2 e1 e2 l w /\ exists bb. c977wb_half d1 d2 e1 e2 l w bb`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977SR_CANONICAL_MISSING_CORNER_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]
    C977WB_CASE_WALL_BRANCH_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[]);;

(* Lean: retained_canonical_wall_context_cover *)
let C977CTX_RETAINED_CANONICAL_WALL_CONTEXT_COVER = prove
 (`forall r. r < 577 /\ MEM (EL r COVER_IDS) EXPECTED_IDS /\ EL r COVER_IDS = 977
     ==> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL r ROWS)
     ==> exists d1 d2 e1 e2.
           ((d1,d2,e1,e2) = (c1,c2,a,b) \/ (d1,d2,e1,e2) = (c2,c1,b,a)) /\
           NPACK d1 d2 e1 e2 l /\ IMAGE binarysum (FFP d1 d2 e1 e2 l) = ccc977ri_family /\
           exists i j. i < 12 /\ j < 12 /\ ownmask (d1 i) (d2 i) (e1 i) (e2 i) l = 1 /\
                 ownmask (d1 j) (d2 j) (e1 j) (e2 j) l = 2 /\ ~(i = j) /\
                 c977mcp_strengthened (e1 i) (e2 i) (e1 i * d1 i + e2 i * d2 i - l / &2)
                                      (--e2 i * d1 i + e1 i * d2 i - l / &2) l /\
                 exists w. c977wb_owners d1 d2 e1 e2 l w /\ exists bb. c977wb_half d1 d2 e1 e2 l w bb`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977CTX_CANONICAL_WALL_CONTEXT_COVER THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `set_of_list (EL r ROWS)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CCC977RI_ROW_FAMILY THEN ASM_REWRITE_TAC[]);;

(* Lean: canonical_bounded_wall_context_cover *)
let C977CTX_CANONICAL_BOUNDED_WALL_CONTEXT_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists d1 d2 e1 e2.
           ((d1,d2,e1,e2) = (c1,c2,a,b) \/ (d1,d2,e1,e2) = (c2,c1,b,a)) /\
           NPACK d1 d2 e1 e2 l /\ IMAGE binarysum (FFP d1 d2 e1 e2 l) = ccc977ri_family /\
           exists i j. i < 12 /\ j < 12 /\ ownmask (d1 i) (d2 i) (e1 i) (e2 i) l = 1 /\
                 ownmask (d1 j) (d2 j) (e1 j) (e2 j) l = 2 /\ ~(i = j) /\
                 c977mcp_strengthened (e1 i) (e2 i) (e1 i * d1 i + e2 i * d2 i - l / &2)
                                      (--e2 i * d1 i + e1 i * d2 i - l / &2) l /\
                 c977mcb_ccb (e1 i) (e2 i) (e1 i * d1 i + e2 i * d2 i - l / &2)
                             (--e2 i * d1 i + e1 i * d2 i - l / &2) l /\
                 exists w. c977wb_owners d1 d2 e1 e2 l w /\ exists bb. c977wb_half d1 d2 e1 e2 l w bb`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977CTX_CANONICAL_WALL_CONTEXT_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC C977MCB_CODE_ONE_MISSING_CORNER_BOUNDS THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_MESON_TAC[]);;

(* Lean: excludes_case_of_canonical_wall_contexts *)
let C977CTX_EXCLUDES_CASE_OF_CANONICAL_WALL_CONTEXTS = prove
 (`(forall c1 c2 a b l i j.
      NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
      i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
      ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
      c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                           (--b i * c1 i + a i * c2 i - l / &2) l
      ==> forall w bb. c977wb_owners c1 c2 a b l w /\ c977wb_half c1 c2 a b l w bb ==> false)
   ==> excl_case 977`,
  DISCH_TAC THEN REWRITE_TAC[CCC977RI_EXCLUDES_CASE_IFF; excl_fam] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977CTX_CANONICAL_WALL_CONTEXT_COVER) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
    [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`; `i:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`w:num->num`; `bb:num->bool`]) THEN
  ASM_REWRITE_TAC[]);;
