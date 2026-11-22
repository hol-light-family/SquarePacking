(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/Anchors.lean.                              *)
(* The code-1 and code-2 singleton owners carry the three strict singleton  *)
(* anchors.  Conventions of CornerRoots.ml: p.square i is the 5-tuple        *)
(* (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i *)
(* - l / &2) l;  pullSwap (c,s,u,v,a) is (s,c,u,--v - a,a);  SingletonAnchors *)
(* is c977mcg_anchors (MissingCornerGeometry.ml).  S12.corner_singleton_forces *)
(* is SING_EXPL.(0) (hull.ml, kernel-checked); for code 2 its transposed     *)
(* form SING_EXPL.(1) is used.                                               *)
(* ========================================================================= *)

needs "n12/geometry/CornerRoots.ml";;
needs "n12/geometry/MissingCornerGeometry.ml";;

(* a marker membership goal (or its negation) at marker k from the exact-marker fact th *)
let C977AN_MARKER_TAC th (asl, w) =
  let w0 = if is_neg w then rand w else w in
  let x = rand (rator w0) and y = rand w0 in
  let k = find (fun k -> let (mx, my) = marker_xy k in
                 rat_of_term mx =/ rat_of_term x && rat_of_term my =/ rat_of_term y) (0--15) in
  (MP_TAC(SPEC (mk_small_numeral k) th) THEN
   REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2; IN_SING] THEN CONV_TAC NUM_REDUCE_CONV THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]) (asl, w);;

(* marker facts of the singleton square i (code m, marker k0), as osq memberships *)
let C977AN_SINGLETON_TAC exact_th sing_th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] exact_th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(c1:num->real) i`; `(c2:num->real) i`; `(a:num->real) i`; `(b:num->real) i`; `l:real`] sing_th) THEN
  ASM_REWRITE_TAC[PK_OSQ_LINSIDE; VECTOR_2] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           UNDISCH_TAC `(a:num->real) i * a i + (b:num->real) i * b i = &1` THEN REAL_ARITH_TAC;
           FIRST_ASSUM(fun th -> if is_forall (concl th) then C977AN_MARKER_TAC th else failwith "")];
    ALL_TAC] THEN
  REWRITE_TAC[c977mcg_anchors; LINSIDE_PULLSW] THEN SIMP_TAC[];;

(* Lean: code_one_anchors *)
let C977AN_CODE_ONE_ANCHORS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1
     ==> c977mcg_anchors (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l`,
  C977AN_SINGLETON_TAC C977CR_CODE_ONE_EXACT SING_EXPL.(0));;

(* Lean: code_two_original_anchors *)
let C977AN_CODE_TWO_ORIGINAL_ANCHORS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 2
     ==> linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&28 / &25) /\
         linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&87 / &50) /\
         linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&19 / &25) (&187 / &100)`,
  C977AN_SINGLETON_TAC C977CR_CODE_TWO_EXACT SING_EXPL.(1));;

(* Lean: code_two_anchors *)
let C977AN_CODE_TWO_ANCHORS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 2
     ==> c977mcg_anchors (b i) (a i) (a i * c1 i + b i * c2 i - l / &2)
                         (--(--b i * c1 i + a i * c2 i - l / &2) - l) l`,
  REWRITE_TAC[c977mcg_anchors; LINSIDE_PULLSW] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977AN_CODE_TWO_ORIGINAL_ANCHORS) THEN
  SIMP_TAC[]);;

(* Lean: anchored_missing_corner_entrance_cover *)
let C977AN_ANCHORED_MISSING_CORNER_ENTRANCE_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               c977mcg_anchors (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l /\
               c977mcg_anchors (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                               (--(--b j * c1 j + a j * c2 j - l / &2) - l) l /\
               (c977cr_mce (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l \/
                (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
                 c977cr_mce (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                            (--(--b j * c1 j + a j * c2 j - l / &2) - l) l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CR_MISSING_CORNER_ENTRANCE_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C977AN_CODE_ONE_ANCHORS; MATCH_MP_TAC C977AN_CODE_TWO_ANCHORS] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: retained_anchored_missing_corner_entrance_cover *)
let C977AN_RETAINED_ANCHORED_MISSING_CORNER_ENTRANCE_COVER = prove
 (`forall r. r < 577 /\ MEM (EL r COVER_IDS) EXPECTED_IDS /\ EL r COVER_IDS = 977
     ==> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL r ROWS)
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               c977mcg_anchors (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l /\
               c977mcg_anchors (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                               (--(--b j * c1 j + a j * c2 j - l / &2) - l) l /\
               (c977cr_mce (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l \/
                (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
                 c977cr_mce (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                            (--(--b j * c1 j + a j * c2 j - l / &2) - l) l))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977AN_ANCHORED_MISSING_CORNER_ENTRANCE_COVER THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `set_of_list (EL r ROWS)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CCC977RI_ROW_FAMILY THEN ASM_REWRITE_TAC[]);;
