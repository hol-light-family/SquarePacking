(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/CornerRoots.lean.                          *)
(* The two-root missing-corner cover of case 977.  The packing square        *)
(* p.square i is the 5-tuple (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)  *)
(* (--b i * c1 i + a i * c2 i - l / &2) l;  markerCode p i is               *)
(* ownmask (c1 i) (c2 i) (a i) (b i) l;  ExactMarkers q S is                 *)
(* !k. k < 16 ==> (linside q (marker k$1) (marker k$2) <=> k IN S);          *)
(* Fin 12 indices are i < 12;  a retained row r is a row index of ROWS with  *)
(* MEM (EL r COVER_IDS) EXPECTED_IDS (RowIdentity.ml); r.groups is           *)
(* set_of_list (EL r ROWS).  MissingCornerEntrance q is c977cr_mce q.        *)
(* ========================================================================= *)

needs "n12/geometry/CC_C977_RowIdentity.ml";;

(* S12.coded_exact for the packing squares *)
let C977CR_CODED_EXACT = prove
 (`forall c1 c2 a b l (i:num). (forall k. k < 16 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN bitset (ownmask (c1 i) (c2 i) (a i) (b i) l)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OWNED_BITSET; owned; IN_ELIM_THM; GSYM PK_OSQ_LINSIDE] THEN
  SIMP_TAC[VECTOR_2]);;

(* Lean: code_owner_unique *)
let C977CR_CODE_OWNER_UNIQUE = prove
 (`forall c1 c2 a b l m. NPACK c1 c2 a b l /\ m IN IMAGE binarysum (FFP c1 c2 a b l)
     ==> existsunique i. i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FFP; GSYM IMAGE_o; IN_IMAGE; IN_ELIM_THM; o_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `x':num` THEN ASM_REWRITE_TAC[ownmask]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OWNMASK_INJ THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
  ASM_REWRITE_TAC[]);;

let C977CR_SINGLETON_TAC m =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_CODED_EXACT) THEN
  ASM_REWRITE_TAC[bitset_bits m; IN_SET_OF_LIST; MEM; IN_SING];;

(* Lean: code_one_exact *)
let C977CR_CODE_ONE_EXACT = prove
 (`forall c1 c2 a b l (i:num). ownmask (c1 i) (c2 i) (a i) (b i) l = 1 ==> (forall k. k < 16 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN {0}))`,
  C977CR_SINGLETON_TAC 1);;

(* Lean: code_two_exact *)
let C977CR_CODE_TWO_EXACT = prove
 (`forall c1 c2 a b l (i:num). ownmask (c1 i) (c2 i) (a i) (b i) l = 2 ==> (forall k. k < 16 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN {1}))`,
  C977CR_SINGLETON_TAC 2);;

let C977CR_IN_FAMILY = prove
 (`forall c1 c2 a b l m. IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\ m IN ccc977ri_family
     ==> m IN IMAGE binarysum (FFP c1 c2 a b l)`,
  MESON_TAC[]);;

(* Lean: corner_owners *)
let C977CR_CORNER_OWNERS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               (forall k. k < 16 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN {0})) /\ (forall k. k < 16 ==> (linside (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l (marker k$1) (marker k$2) <=> k IN {1}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `1`]
    C977CR_CODE_OWNER_UNIQUE) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `2`]
    C977CR_CODE_OWNER_UNIQUE) THEN
  ASM_REWRITE_TAC[in_fam 1 `ccc977ri_family`; in_fam 2 `ccc977ri_family`] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num` o CONJUNCT1) THEN
  DISCH_THEN(X_CHOOSE_TAC `i:num` o CONJUNCT1) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[C977CR_CODE_ONE_EXACT; C977CR_CODE_TWO_EXACT] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `1 = 2` MP_TAC THENL [ASM_MESON_TAC[]; ARITH_TAC]);;

(* Lean: missing_corner_cover *)
let C977CR_MISSING_CORNER_COVER = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) \/ (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\ ~linside (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l (&1) (&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `i:num`; `j:num`] NPACK_LDISJ) THEN
  ASM_REWRITE_TAC[ldisj] THEN MESON_TAC[]);;

(* Lean: corner_roots *)
let C977CR_CORNER_ROOTS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               (forall k. k < 16 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN {0})) /\ (forall k. k < 16 ==> (linside (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l (marker k$1) (marker k$2) <=> k IN {1})) /\
               (~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) \/ (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\ ~linside (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l (&1) (&1)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CR_CORNER_OWNERS) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C977CR_MISSING_CORNER_COVER THEN ASM_REWRITE_TAC[]);;

(* Lean: retained_corner_roots *)
let C977CR_RETAINED_CORNER_ROOTS = prove
 (`forall r. r < 577 /\ MEM (EL r COVER_IDS) EXPECTED_IDS /\ EL r COVER_IDS = 977
     ==> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL r ROWS)
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               (forall k. k < 16 ==> (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (marker k$1) (marker k$2) <=> k IN {0})) /\ (forall k. k < 16 ==> (linside (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l (marker k$1) (marker k$2) <=> k IN {1})) /\
               (~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) \/ (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\ ~linside (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l (&1) (&1)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977CR_CORNER_ROOTS THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `set_of_list (EL r ROWS)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CCC977RI_ROW_FAMILY THEN ASM_REWRITE_TAC[]);;

(* Lean: MissingCornerEntrance *)
let c977cr_mce = new_definition
 `c977cr_mce c s u v a <=>
    &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
    linside c s u v a (&1) (&457 / &500) /\
    ~linside c s u v a (&457 / &500) (&1) /\
    ~linside c s u v a (&457 / &500) (&2) /\
    ~linside c s u v a (&33 / &20) (&33 / &20) /\
    ~linside c s u v a (&1) (&1)`;;

let C977CR_SQ_FACTS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 ==> &1 < l /\ l <= &1001 / &1000 /\ lcont (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NPACK_SQ) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OWALLS_LCONT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let C977CR_MARKER_TAC i =
  FIRST_X_ASSUM(MP_TAC o SPEC (mk_small_numeral i) o check (is_forall o concl)) THEN
  REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2; IN_SING] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LINSIDE_PULLSW] THEN ASM_REWRITE_TAC[];;

(* Lean: code_one_missing_entrance *)
let C977CR_CODE_ONE_MISSING_ENTRANCE = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1)
     ==> c977cr_mce (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_SQ_FACTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_CODE_ONE_EXACT) THEN
  ASM_REWRITE_TAC[c977cr_mce] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [C977CR_MARKER_TAC 0; C977CR_MARKER_TAC 1; C977CR_MARKER_TAC 12; C977CR_MARKER_TAC 8]);;

(* Lean: code_two_missing_entrance  (pullSwap q = s c u (--v - a) a) *)
let C977CR_CODE_TWO_MISSING_ENTRANCE = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 2 /\ ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1)
     ==> c977cr_mce (b i) (a i) (a i * c1 i + b i * c2 i - l / &2)
                    (--(--b i * c1 i + a i * c2 i - l / &2) - l) l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_SQ_FACTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_CODE_TWO_EXACT) THEN
  ASM_REWRITE_TAC[c977cr_mce; LINSIDE_PULLSW] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LCONT_PULLSW] THENL
   [C977CR_MARKER_TAC 1; C977CR_MARKER_TAC 0; C977CR_MARKER_TAC 13; C977CR_MARKER_TAC 8]);;

(* Lean: missing_corner_entrance_cover *)
let C977CR_MISSING_CORNER_ENTRANCE_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               (c977cr_mce (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l \/
                (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
                 c977cr_mce (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                            (--(--b j * c1 j + a j * c2 j - l / &2) - l) l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CR_CORNER_ROOTS) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC C977CR_CODE_ONE_MISSING_ENTRANCE THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN MATCH_MP_TAC C977CR_CODE_TWO_MISSING_ENTRANCE THEN ASM_REWRITE_TAC[]]);;

(* Lean: excludes_case_of_corner_roots *)
let C977CR_EXCLUDES_CASE_OF_CORNER_ROOTS = prove
 (`(forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\
       IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
       ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\ c977cr_mce (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l ==> false) /\
   (forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\
       IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
       ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\ ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\ linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
       c977cr_mce (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                  (--(--b j * c1 j + a j * c2 j - l / &2) - l) l ==> false)
   ==> excl_case 977`,
  STRIP_TAC THEN REWRITE_TAC[CCC977RI_EXCLUDES_CASE_IFF; excl_fam] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CR_MISSING_CORNER_ENTRANCE_COVER) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
