(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/SwapReduction.lean.                        *)
(* Conventions of MissingCornerPoints.ml / CornerReduction.ml: a Transform   *)
(* is a triple bool#bool#bool, S12.allTransforms is c981cr_all_transforms,   *)
(* Transform.maskAction is c981cr_mask_action.  transposePacking p of the    *)
(* packing (c1,c2,a,b,l) is the packing (c2,c1,b,a,l) (NPACK_SW); its square *)
(* i is the 5-tuple (b i) (a i) (b i * c2 i + a i * c1 i - l / &2)           *)
(* (--a i * c2 i + b i * c1 i - l / &2) l.  StrengthenedMissingCorner is     *)
(* c977mcp_strengthened.  Tag C977SR_.                                       *)
(* ========================================================================= *)

needs "n12/geometry/MissingCornerPoints.ml";;
needs "n12/geometry/CornerReduction.ml";;

(* Lean: transpose *)
let c977sr_transpose = new_definition `c977sr_transpose = (true,false,false)`;;

let C977SR_TRANSPOSE_DIAGONAL = prove
 (`c977sr_transpose = c981cr_diagonal`,
  REWRITE_TAC[c977sr_transpose; c981cr_diagonal]);;

(* Lean: transpose_mem *)
let C977SR_TRANSPOSE_MEM = prove
 (`MEM c977sr_transpose c981cr_all_transforms`,
  REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL; C981CR_DIAGONAL_MEM]);;

let C977SR_FAMILY_LIST = [1; 2; 12; 48; 192; 256; 512; 2048; 4096; 8192; 16384; 32768];;

(* Lean: transpose_family_masks *)
let C977SR_TRANSPOSE_FAMILY_MASKS = prove
 (`IMAGE (c981cr_mask_action c977sr_transpose) ccc977ri_family = ccc977ri_family`,
  REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL; ccc977ri_family; IMAGE_CLAUSES] THEN
  REWRITE_TAC(map c981cr_diag_mask C977SR_FAMILY_LIST) THEN
  CONV_TAC setlit_eq_dconv);;

(* Lean: transpose_mask_involution *)
let C977SR_TRANSPOSE_MASK_INVOLUTION = prove
 (`forall m. m IN ccc977ri_family
       ==> c981cr_mask_action c977sr_transpose (c981cr_mask_action c977sr_transpose m) = m`,
  REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL; ccc977ri_family; IN_INSERT; NOT_IN_EMPTY] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC(map c981cr_diag_mask (C977SR_FAMILY_LIST @ [3; 768; 1536; 128])));;

(* Lean: transpose_square  (transposePacking square = pullSwap of the old square) *)
let C977SR_TRANSPOSE_SQUARE = prove
 (`forall c1 c2 a b l (i:num).
     (b i, a i, b i * c2 i + a i * c1 i - l / &2, --a i * c2 i + b i * c1 i - l / &2, l) =
     (b i, a i, a i * c1 i + b i * c2 i - l / &2, --(--b i * c1 i + a i * c2 i - l / &2) - l, l)`,
  REWRITE_TAC[PAIR_EQ] THEN REAL_ARITH_TAC);;

(* Lean: transpose_inside *)
let C977SR_TRANSPOSE_INSIDE = prove
 (`forall c1 c2 a b l (i:num) x y.
     linside (b i) (a i) (b i * c2 i + a i * c1 i - l / &2) (--a i * c2 i + b i * c1 i - l / &2) l x y <=>
     linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C977SR_CODE_RAW = prove
 (`forall c1 c2 a b l (i:num).
     ownmask (c2 i) (c1 i) (b i) (a i) l =
     c981cr_mask_action c977sr_transpose (ownmask (c1 i) (c2 i) (a i) (b i) l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL; c981cr_mask_action; C981CR_DIAG_PERM; OWNED_BITSET] THEN
  REWRITE_TAC[ownmask] THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC(SPECL [`(c1:num->real) i`; `(c2:num->real) i`; `(a:num->real) i`;
                          `(b:num->real) i`; `l:real`] OWNED_SW));;

(* Lean: transpose_code *)
let C977SR_TRANSPOSE_CODE = prove
 (`forall c1 c2 a b l (i:num). NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12
     ==> ownmask (c2 i) (c1 i) (b i) (a i) l =
         c981cr_mask_action c977sr_transpose (ownmask (c1 i) (c2 i) (a i) (b i) l)`,
  REPEAT STRIP_TAC THEN MATCH_ACCEPT_TAC C977SR_CODE_RAW);;

(* Lean: transpose_family *)
let C977SR_TRANSPOSE_FAMILY = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> NPACK c2 c1 b a l /\ IMAGE binarysum (FFP c2 c1 b a l) = ccc977ri_family`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NPACK_SW) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM C977SR_TRANSPOSE_FAMILY_MASKS] THEN
  REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ_ON THEN
  X_GEN_TAC `G:num->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; c981cr_mask_action; C981CR_DIAG_PERM] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC C981CR_FFP_BITSET THEN ASM_MESON_TAC[]);;

(* Lean: transpose_code_one *)
let C977SR_TRANSPOSE_CODE_ONE = prove
 (`forall c1 c2 a b l (i:num). NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1
     ==> ownmask (c2 i) (c1 i) (b i) (a i) l = 2`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[C977SR_CODE_RAW] THEN
  ASM_REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL] THEN
  REWRITE_TAC[c981cr_diag_mask 1]);;

(* Lean: transpose_code_two *)
let C977SR_TRANSPOSE_CODE_TWO = prove
 (`forall c1 c2 a b l (i:num). NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 2
     ==> ownmask (c2 i) (c1 i) (b i) (a i) l = 1`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[C977SR_CODE_RAW] THEN
  ASM_REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL] THEN
  REWRITE_TAC[c981cr_diag_mask 2]);;

(* Lean: code_one_strengthened *)
let C977SR_CODE_ONE_STRENGTHENED = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
     ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1)
     ==> c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                              (--b i * c1 i + a i * c2 i - l / &2) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c977mcp_strengthened] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC C977CR_CODE_ONE_MISSING_ENTRANCE;
    MATCH_MP_TAC C977AN_CODE_ONE_ANCHORS;
    MATCH_MP_TAC C977MCP_CODE_ONE_MISSING_POINTS] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: canonical_missing_corner_cover *)
let C977SR_CANONICAL_MISSING_CORNER_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists d1 d2 e1 e2.
           ((d1,d2,e1,e2) = (c1,c2,a,b) \/ (d1,d2,e1,e2) = (c2,c1,b,a)) /\
           NPACK d1 d2 e1 e2 l /\ IMAGE binarysum (FFP d1 d2 e1 e2 l) = ccc977ri_family /\
           exists i j. i < 12 /\ j < 12 /\ ownmask (d1 i) (d2 i) (e1 i) (e2 i) l = 1 /\
                 ownmask (d1 j) (d2 j) (e1 j) (e2 j) l = 2 /\ ~(i = j) /\
                 c977mcp_strengthened (e1 i) (e2 i) (e1 i * d1 i + e2 i * d2 i - l / &2)
                                      (--e2 i * d1 i + e1 i * d2 i - l / &2) l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CR_CORNER_ROOTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C977SR_CODE_ONE_STRENGTHENED THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
      C977SR_TRANSPOSE_FAMILY) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `i:num`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC C977SR_TRANSPOSE_CODE_TWO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC C977SR_TRANSPOSE_CODE_ONE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC C977SR_CODE_ONE_STRENGTHENED THEN
      ASM_REWRITE_TAC[C977SR_TRANSPOSE_INSIDE] THEN
      MATCH_MP_TAC C977SR_TRANSPOSE_CODE_TWO THEN ASM_REWRITE_TAC[]]]);;

(* Lean: retained_canonical_missing_corner_cover *)
let C977SR_RETAINED_CANONICAL_MISSING_CORNER_COVER = prove
 (`forall r. r < 577 /\ MEM (EL r COVER_IDS) EXPECTED_IDS /\ EL r COVER_IDS = 977
     ==> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL r ROWS)
     ==> exists d1 d2 e1 e2.
           ((d1,d2,e1,e2) = (c1,c2,a,b) \/ (d1,d2,e1,e2) = (c2,c1,b,a)) /\
           NPACK d1 d2 e1 e2 l /\ IMAGE binarysum (FFP d1 d2 e1 e2 l) = ccc977ri_family /\
           exists i j. i < 12 /\ j < 12 /\ ownmask (d1 i) (d2 i) (e1 i) (e2 i) l = 1 /\
                 ownmask (d1 j) (d2 j) (e1 j) (e2 j) l = 2 /\ ~(i = j) /\
                 c977mcp_strengthened (e1 i) (e2 i) (e1 i * d1 i + e2 i * d2 i - l / &2)
                                      (--e2 i * d1 i + e1 i * d2 i - l / &2) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977SR_CANONICAL_MISSING_CORNER_COVER THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `set_of_list (EL r ROWS)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CCC977RI_ROW_FAMILY THEN ASM_REWRITE_TAC[]);;

(* Lean: excludes_case_of_canonical_corner_root *)
let C977SR_EXCLUDES_CASE_OF_CANONICAL_CORNER_ROOT = prove
 (`(forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
      i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
      ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
      c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                           (--b i * c1 i + a i * c2 i - l / &2) l ==> false)
   ==> excl_case 977`,
  DISCH_TAC THEN REWRITE_TAC[CCC977RI_EXCLUDES_CASE_IFF; excl_fam] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977SR_CANONICAL_MISSING_CORNER_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:num->real` (X_CHOOSE_THEN `d2:num->real`
    (X_CHOOSE_THEN `e1:num->real` (X_CHOOSE_THEN `e2:num->real` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`;
                                `l:real`; `i:num`; `j:num`]) THEN
  ASM_REWRITE_TAC[]);;
