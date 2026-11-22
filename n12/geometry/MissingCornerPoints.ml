(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/MissingCornerPoints.lean.                  *)
(* Conventions of CornerRoots.ml / Anchors.ml: p.square i is the 5-tuple     *)
(* (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)                            *)
(* (--b i * c1 i + a i * c2 i - l / &2) l;  pullSwap (c,s,u,v,a) is          *)
(* (s,c,u,--v - a,a);  MissingCornerEntrance / SingletonAnchors /            *)
(* MissingCornerPoints are c977cr_mce / c977mcg_anchors / c977mcg_points;    *)
(* ExcludesCase 977 is excl_case 977 (CCC977RI_EXCLUDES_CASE_IFF); retained  *)
(* rows r with originalId 977 as in Anchors.ml.  Tag C977MCP_.               *)
(* ========================================================================= *)

needs "n12/geometry/Anchors.ml";;

(* Lean: missing_corner_points *)
let C977MCP_MISSING_CORNER_POINTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     c977cr_mce c s u v a /\ c977mcg_anchors c s u v a
     ==> c977mcg_points c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977cr_mce] THEN STRIP_TAC THEN
  MATCH_MP_TAC C977MCG_MISSING_CORNER_POINTS_OF_ANCHORS THEN ASM_REWRITE_TAC[]);;

let C977MCP_SQ_TAC =
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: code_one_missing_points *)
let C977MCP_CODE_ONE_MISSING_POINTS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
     ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1)
     ==> c977mcg_points (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                        (--b i * c1 i + a i * c2 i - l / &2) l`,
  REPEAT STRIP_TAC THEN C977MCP_SQ_TAC THEN
  MATCH_MP_TAC C977MCP_MISSING_CORNER_POINTS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C977CR_CODE_ONE_MISSING_ENTRANCE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C977AN_CODE_ONE_ANCHORS THEN ASM_REWRITE_TAC[]]);;

(* Lean: code_two_missing_points *)
let C977MCP_CODE_TWO_MISSING_POINTS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 2 /\
     ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1)
     ==> c977mcg_points (b i) (a i) (a i * c1 i + b i * c2 i - l / &2)
                        (--(--b i * c1 i + a i * c2 i - l / &2) - l) l`,
  REPEAT STRIP_TAC THEN C977MCP_SQ_TAC THEN
  MATCH_MP_TAC C977MCP_MISSING_CORNER_POINTS THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C977CR_CODE_TWO_MISSING_ENTRANCE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C977AN_CODE_TWO_ANCHORS THEN ASM_REWRITE_TAC[]]);;

(* Lean: code_two_original_missing_points *)
let C977MCP_CODE_TWO_ORIGINAL_MISSING_POINTS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 2 /\
     ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1)
     ==> linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                 (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&91 / &50) /\
         linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                 (--b i * c1 i + a i * c2 i - l / &2) l (&19 / &25) (&49 / &25)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP C977MCP_CODE_TWO_MISSING_POINTS) THEN
  REWRITE_TAC[c977mcg_points; LINSIDE_PULLSW]);;

(* Lean: StrengthenedMissingCorner (structure) *)
let c977mcp_strengthened = new_definition
 `c977mcp_strengthened (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    c977cr_mce c s u v a /\ c977mcg_anchors c s u v a /\ c977mcg_points c s u v a`;;

(* Lean: missing_corner_strengthening_cover *)
let C977MCP_MISSING_CORNER_STRENGTHENING_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
               ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               (c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                                     (--b i * c1 i + a i * c2 i - l / &2) l \/
                (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                         (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
                 c977mcp_strengthened (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                                      (--(--b j * c1 j + a j * c2 j - l / &2) - l) l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977AN_ANCHORED_MISSING_CORNER_ENTRANCE_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c977mcp_strengthened] THENL
   [DISJ1_TAC; DISJ2_TAC] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C977MCP_MISSING_CORNER_POINTS THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `i:num`] NPACK_SQ);
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `j:num`] NPACK_SQ)] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: retained_missing_corner_strengthening_cover *)
let C977MCP_RETAINED_MISSING_CORNER_STRENGTHENING_COVER = prove
 (`forall r. r < 577 /\ MEM (EL r COVER_IDS) EXPECTED_IDS /\ EL r COVER_IDS = 977
     ==> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL r ROWS)
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
               ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               (c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                                     (--b i * c1 i + a i * c2 i - l / &2) l \/
                (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                         (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
                 c977mcp_strengthened (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                                      (--(--b j * c1 j + a j * c2 j - l / &2) - l) l))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977MCP_MISSING_CORNER_STRENGTHENING_COVER THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `set_of_list (EL r ROWS)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CCC977RI_ROW_FAMILY THEN ASM_REWRITE_TAC[]);;

(* Lean: excludes_case_of_strengthened_corner_roots *)
let C977MCP_EXCLUDES_CASE_OF_STRENGTHENED_CORNER_ROOTS = prove
 (`(forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
      i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
      ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
      c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                           (--b i * c1 i + a i * c2 i - l / &2) l ==> false) /\
   (forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
      i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
      ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
      linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
              (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
      c977mcp_strengthened (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                           (--(--b j * c1 j + a j * c2 j - l / &2) - l) l ==> false)
   ==> excl_case 977`,
  STRIP_TAC THEN REWRITE_TAC[CCC977RI_EXCLUDES_CASE_IFF; excl_fam] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977MCP_MISSING_CORNER_STRENGTHENING_COVER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]);;
