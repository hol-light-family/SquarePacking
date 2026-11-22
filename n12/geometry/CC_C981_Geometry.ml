(* ========================================================================= *)
(* Phase 2: Completion/Cases/C981/Geometry.lean.                             *)
(* Packing squares, markerCode and ExactMarkers as in CornerRoots.ml         *)
(* (C977CR_CODED_EXACT etc. are family-independent).  Owns q 8 is           *)
(* linside q (marker 8$1) (marker 8$2).                                      *)
(* ========================================================================= *)

needs "n12/geometry/CC_C981_RowIdentity.ml";;
needs "n12/geometry/CornerRoots.ml";;

let C981G_MEMBER = prove
 (`forall c1 c2 a b l i. i < 12 ==> ownmask (c1 i) (c2 i) (a i) (b i) l IN IMAGE binarysum (FFP c1 c2 a b l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM; ownmask] THEN
  ASM_MESON_TAC[]);;

let C981G_NO8 = prove
 (`forall m. m IN ccc981ri_family ==> ~(8 IN bitset m)`,
  REWRITE_TAC[ccc981ri_family; IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC(map bitset_bits [1;2;12;48;192;512;1024;2048;4096;8192;16384;32768] @ [IN_SET_OF_LIST; MEM]) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Lean: central_marker_unowned *)
let C981G_CENTRAL_MARKER_UNOWNED = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\ i < 12
     ==> ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker 8$1) (marker 8$2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C981G_MEMBER) THEN
  MP_TAC(SPEC `8` (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_CODED_EXACT)) THEN
  ASM_REWRITE_TAC[ARITH] THEN ONCE_REWRITE_TAC[TAUT `p ==> ~q <=> q ==> ~p`] THEN
  MESON_TAC[C981G_NO8]);;

(* Lean: corner_owners *)
let C981G_CORNER_OWNERS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family
     ==> exists i j. i < 12 /\ j < 12 /\ ~(i = j) /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\
               (forall k. k < 16 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN {0})) /\ (forall k. k < 16 ==> (linside (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l (marker k$1) (marker k$2) <=> k IN {1}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `1`]
    C977CR_CODE_OWNER_UNIQUE) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `2`]
    C977CR_CODE_OWNER_UNIQUE) THEN
  ASM_REWRITE_TAC[in_fam 1 `ccc981ri_family`; in_fam 2 `ccc981ri_family`] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num` o CONJUNCT1) THEN
  DISCH_THEN(X_CHOOSE_TAC `i:num` o CONJUNCT1) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[C977CR_CODE_ONE_EXACT; C977CR_CODE_TWO_EXACT] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `1 = 2` MP_TAC THENL [ASM_MESON_TAC[]; ARITH_TAC]);;
