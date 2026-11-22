(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C976/OriginalData.lean.            *)
(* The literal C976 family and its ascending-mask owners.  Lean             *)
(* owners p i = owner p (masks i)  is the owner 5-tuple at  EL i c976od_masks *)
(* (literal masks for fixed indices: masks 0 = 1, masks 1 = 2).             *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: family (= S12.case976Family), masks *)
let c976od_family = new_definition
 `c976od_family = {1,2,12,48,192,256,512,1024,6144,8192,16384,32768}`;;
let c976od_masks = new_definition
 `c976od_masks = [1;2;12;48;192;256;512;1024;6144;8192;16384;32768]`;;
let C976OD_MASKS = [1;2;12;48;192;256;512;1024;6144;8192;16384;32768];;

let C976OD_LIST = oo_list_facts `c976od_family` (rand (concl c976od_masks));;
let C976OD_LENGTH = (REWRITE_CONV[c976od_masks; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c976od_masks`;;

(* Lean: member *)
let C976OD_MEMBER = prove
 (`forall i. i < 12 ==> EL i c976od_masks IN c976od_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C976OD_LENGTH; c976od_masks] THEN ASM_REWRITE_TAC[fst C976OD_LIST]);;

(* Lean: injective *)
let C976OD_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c976od_masks = EL j c976od_masks ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c976od_masks` THEN ASM_REWRITE_TAC[C976OD_LENGTH] THEN
  REWRITE_TAC[c976od_masks; snd C976OD_LIST]);;

(* Lean: side  (Lean same: both sides are l) *)
let C976OD_SIDE = OO_SIDE;;

(* Lean: box *)
let C976OD_BOX = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l
     ==> lcont (ooc c1 c2 a b l (EL i c976od_masks)) (oos c1 c2 a b l (EL i c976od_masks))
               (oou c1 c2 a b l (EL i c976od_masks)) (oov c1 c2 a b l (EL i c976od_masks)) l`,
  SIMP_TAC[OO_BOX]);;

(* Lean: apart *)
let C976OD_APART = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (ooc c1 c2 a b l (EL i c976od_masks)) (oos c1 c2 a b l (EL i c976od_masks))
               (oou c1 c2 a b l (EL i c976od_masks)) (oov c1 c2 a b l (EL i c976od_masks)) l
               (ooc c1 c2 a b l (EL j c976od_masks)) (oos c1 c2 a b l (EL j c976od_masks))
               (oou c1 c2 a b l (EL j c976od_masks)) (oov c1 c2 a b l (EL j c976od_masks)) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN EXISTS_TAC `c976od_family` THEN
  ASM_REWRITE_TAC[C976OD_LENGTH] THEN REWRITE_TAC[c976od_masks] THEN
  REWRITE_TAC[fst C976OD_LIST; snd C976OD_LIST]);;

(* Lean: foreign *)
let C976OD_FOREIGN = prove
 (`forall c1 c2 a b l i j x y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family /\
     i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (ooc c1 c2 a b l (EL j c976od_masks)) (oos c1 c2 a b l (EL j c976od_masks))
             (oou c1 c2 a b l (EL j c976od_masks)) (oov c1 c2 a b l (EL j c976od_masks)) l x y
     ==> ~linside (ooc c1 c2 a b l (EL i c976od_masks)) (oos c1 c2 a b l (EL i c976od_masks))
                  (oou c1 c2 a b l (EL i c976od_masks)) (oov c1 c2 a b l (EL i c976od_masks)) l x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 `i:num`; `j:num`] C976OD_APART) THEN
  ASM_REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]);;

(* Lean: seed — producer at a literal index i and seed point (x, y) *)
let c976od_seed i (x, y) = oo_inst `c976od_family` (oo_seed (el i C976OD_MASKS) (x, y));;

(* Lean: aux *)
let C976OD_AUX = prove
 (`forall c1 c2 a b l i j. j < 20
     ==> (linside (ooc c1 c2 a b l (EL i c976od_masks)) (oos c1 c2 a b l (EL i c976od_masks))
                  (oou c1 c2 a b l (EL i c976od_masks)) (oov c1 c2 a b l (EL i c976od_masks)) l
                  (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=>
          j IN ooaux c1 c2 a b l (EL i c976od_masks))`,
  SIMP_TAC[OO_AUX_EXACT]);;

(* Lean: singleton_horizontal  (owners p 0 = owner 1) *)
let C976OD_SINGLETON_HORIZONTAL = prove
 (`forall c1 c2 a b l x. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family /\
     &28 / &25 <= x /\ x <= &87 / &50
     ==> linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l x (&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_SIMP_TAC[c976od_seed 0 (`&28 / &25`, `&1`); c976od_seed 0 (`&87 / &50`, `&1`)] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: singleton_vertical  (owners p 1 = owner 2) *)
let C976OD_SINGLETON_VERTICAL = prove
 (`forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family /\
     &28 / &25 <= y /\ y <= &87 / &50
     ==> linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l (&1) y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_SIMP_TAC[c976od_seed 1 (`&1`, `&28 / &25`); c976od_seed 1 (`&1`, `&87 / &50`)] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
