(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C974/OriginalData.lean             *)
(* (namespace N12Compact.Completion.OtherCases.C974.OriginalData).  The      *)
(* original C974 owners in ascending mask order: Lean owners p i = owner p   *)
(* (masks i) is the owner 5-tuple at EL i c974od_masks; actual p i = ooaux   *)
(* .. (EL i c974od_masks).  family = Domains.family = c974d_family.          *)
(* Lean same: all sides are l; ExactMarkers = OO_MARKERS form.               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C974_Domains.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: family (abbrev Domains.family), masks *)
let c974od_masks = new_definition
 `c974od_masks = [1;2;12;48;192;256;512;1024;4096;8192;16384;32768]`;;
let C974OD_MASKS = [1;2;12;48;192;256;512;1024;4096;8192;16384;32768];;

let C974OD_LIST = oo_list_facts `c974d_family` (rand (concl c974od_masks));;
let C974OD_LENGTH = (REWRITE_CONV[c974od_masks; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c974od_masks`;;

(* Lean: member *)
let C974OD_MEMBER = prove
 (`forall i. i < 12 ==> EL i c974od_masks IN c974d_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C974OD_LENGTH; c974od_masks] THEN ASM_REWRITE_TAC[fst C974OD_LIST]);;

(* Lean: injective *)
let C974OD_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c974od_masks = EL j c974od_masks ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c974od_masks` THEN ASM_REWRITE_TAC[C974OD_LENGTH] THEN
  REWRITE_TAC[c974od_masks; snd C974OD_LIST]);;

(* Lean: side  (Lean same: both sides are l) *)
let C974OD_SIDE = OO_SIDE;;

(* Lean: box *)
let C974OD_BOX = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l
     ==> lcont (ooc c1 c2 a b l (EL i c974od_masks)) (oos c1 c2 a b l (EL i c974od_masks))
               (oou c1 c2 a b l (EL i c974od_masks)) (oov c1 c2 a b l (EL i c974od_masks)) l`,
  SIMP_TAC[OO_BOX]);;

(* Lean: apart *)
let C974OD_APART = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (ooc c1 c2 a b l (EL i c974od_masks)) (oos c1 c2 a b l (EL i c974od_masks))
               (oou c1 c2 a b l (EL i c974od_masks)) (oov c1 c2 a b l (EL i c974od_masks)) l
               (ooc c1 c2 a b l (EL j c974od_masks)) (oos c1 c2 a b l (EL j c974od_masks))
               (oou c1 c2 a b l (EL j c974od_masks)) (oov c1 c2 a b l (EL j c974od_masks)) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN EXISTS_TAC `c974d_family` THEN
  ASM_REWRITE_TAC[C974OD_LENGTH] THEN REWRITE_TAC[c974od_masks] THEN
  REWRITE_TAC[fst C974OD_LIST; snd C974OD_LIST]);;

(* Lean: foreign *)
let C974OD_FOREIGN = prove
 (`forall c1 c2 a b l i j x y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family /\
     i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (ooc c1 c2 a b l (EL j c974od_masks)) (oos c1 c2 a b l (EL j c974od_masks))
             (oou c1 c2 a b l (EL j c974od_masks)) (oov c1 c2 a b l (EL j c974od_masks)) l x y
     ==> ~linside (ooc c1 c2 a b l (EL i c974od_masks)) (oos c1 c2 a b l (EL i c974od_masks))
                  (oou c1 c2 a b l (EL i c974od_masks)) (oov c1 c2 a b l (EL i c974od_masks)) l x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 `i:num`; `j:num`] C974OD_APART) THEN
  ASM_REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]);;

(* Lean: seed — producer at a literal index i and seed point (x, y) *)
let c974od_seed i (x, y) = oo_inst `c974d_family` (oo_seed (el i C974OD_MASKS) (x, y));;

(* Lean: aux *)
let C974OD_AUX = prove
 (`forall c1 c2 a b l i j. j < 20
     ==> (linside (ooc c1 c2 a b l (EL i c974od_masks)) (oos c1 c2 a b l (EL i c974od_masks))
                  (oou c1 c2 a b l (EL i c974od_masks)) (oov c1 c2 a b l (EL i c974od_masks)) l
                  (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=>
          j IN ooaux c1 c2 a b l (EL i c974od_masks))`,
  SIMP_TAC[OO_AUX_EXACT]);;

(* Lean: singleton_horizontal  (owners p 0 = owner 1) *)
let C974OD_SINGLETON_HORIZONTAL = prove
 (`forall c1 c2 a b l x. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family /\
     &28 / &25 <= x /\ x <= &87 / &50
     ==> linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l x (&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_SIMP_TAC[c974od_seed 0 (`&28 / &25`, `&1`); c974od_seed 0 (`&87 / &50`, `&1`)] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: singleton_vertical  (owners p 1 = owner 2) *)
let C974OD_SINGLETON_VERTICAL = prove
 (`forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family /\
     &28 / &25 <= y /\ y <= &87 / &50
     ==> linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l (&1) y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_SIMP_TAC[c974od_seed 1 (`&1`, `&28 / &25`); c974od_seed 1 (`&1`, `&87 / &50`)] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: cap *)
let C974OD_CAP = OO_SIDE_LE;;

(* Lean: markers  (ExactMarkers (owners p i) (maskSupport (masks i))) *)
let C974OD_MARKERS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family /\ i < 12
     ==> forall k. k < 16
         ==> (linside (ooc c1 c2 a b l (EL i c974od_masks)) (oos c1 c2 a b l (EL i c974od_masks))
                      (oou c1 c2 a b l (EL i c974od_masks)) (oov c1 c2 a b l (EL i c974od_masks)) l
                      (marker k$1) (marker k$2) <=> k IN bitset (EL i c974od_masks))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OO_MARKERS THEN
  EXISTS_TAC `c974d_family` THEN ASM_SIMP_TAC[C974OD_MEMBER]);;

(* the twelve literal cases of  i < 12  with EL i c974od_masks evaluated *)
let C974OD_CASES_TAC thms =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `i < 12 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/
                                      i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC))) THEN
  REWRITE_TAC[c974od_masks] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN ASM_SIMP_TAC thms;;

(* Lean: missing_northwest  (marker 11 = (33/20, 47/20) is in no mask) *)
let C974OD_MISSING_NORTHWEST = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family /\ i < 12
     ==> ~linside (ooc c1 c2 a b l (EL i c974od_masks)) (oos c1 c2 a b l (EL i c974od_masks))
                  (oou c1 c2 a b l (EL i c974od_masks)) (oov c1 c2 a b l (EL i c974od_masks)) l
                  (&33 / &20) (&47 / &20)`,
  C974OD_CASES_TAC (map (fun m -> oo_inst `c974d_family` (oo_missing m 11)) C974OD_MASKS));;

(* the SingletonMissing hypotheses for owner m in {1, 2} *)
let C974OD_SINGLETON_TAC m th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_SIMP_TAC[OO_UNIT; OO_BOX] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c974d_family`; mk_small_numeral m] OO_MARKERS) THEN
  ASM_REWRITE_TAC[in_fam m `c974d_family`] THEN
  REWRITE_TAC[bitset_bits m; IN_SET_OF_LIST; MEM];;

(* Lean: missing_zero *)
let C974OD_MISSING_ZERO = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family /\
     ~linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l (&1) (&1)
     ==> linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l
                 (&91 / &50) (&1) /\
         linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l
                 (&49 / &25) (&19 / &25)`,
  C974OD_SINGLETON_TAC 1 CCSM_ZERO_MISSING_POINTS);;

(* Lean: missing_one *)
let C974OD_MISSING_ONE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c974d_family /\
     ~linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l (&1) (&1)
     ==> linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l
                 (&1) (&91 / &50) /\
         linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l
                 (&19 / &25) (&49 / &25)`,
  C974OD_SINGLETON_TAC 2 CCSM_ONE_MISSING_POINTS);;
