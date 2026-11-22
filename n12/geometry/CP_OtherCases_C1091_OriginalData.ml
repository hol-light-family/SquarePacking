(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1091/OriginalData.lean.           *)
(* C1091's literal family and owners.  Lean  owners p i = owner p (masks i) *)
(* is the owner 5-tuple at mask  EL i c1091od_masks  (literal masks below   *)
(* for the fixed indices: masks 0 = 1, masks 4 = 258).                       *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: family, masks *)
let c1091od_family = new_definition
 `c1091od_family = {1,12,48,192,258,512,1024,2048,4096,8192,16384,32768}`;;
let c1091od_masks = new_definition
 `c1091od_masks = [1;12;48;192;258;512;1024;2048;4096;8192;16384;32768]`;;

let C1091OD_LIST = oo_list_facts `c1091od_family` (rand (concl c1091od_masks));;
let C1091OD_LENGTH = (REWRITE_CONV[c1091od_masks; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c1091od_masks`;;

(* Lean: member *)
let C1091OD_MEMBER = prove
 (`forall i. i < 12 ==> EL i c1091od_masks IN c1091od_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C1091OD_LENGTH; c1091od_masks] THEN ASM_REWRITE_TAC[fst C1091OD_LIST]);;

(* Lean: injective (private) *)
let C1091OD_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c1091od_masks = EL j c1091od_masks ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c1091od_masks` THEN ASM_REWRITE_TAC[C1091OD_LENGTH] THEN
  REWRITE_TAC[c1091od_masks; snd C1091OD_LIST]);;

(* Lean: side, cap  (the owners' common side is l; Lean "same" is l = l) *)
let C1091OD_SIDE = OO_SIDE;;
let C1091OD_CAP = OO_SIDE_LE;;

(* Lean: box *)
let C1091OD_BOX = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l
     ==> lcont (ooc c1 c2 a b l (EL i c1091od_masks)) (oos c1 c2 a b l (EL i c1091od_masks))
               (oou c1 c2 a b l (EL i c1091od_masks)) (oov c1 c2 a b l (EL i c1091od_masks)) l`,
  SIMP_TAC[OO_BOX]);;

(* Lean: apart *)
let C1091OD_APART = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (ooc c1 c2 a b l (EL i c1091od_masks)) (oos c1 c2 a b l (EL i c1091od_masks))
               (oou c1 c2 a b l (EL i c1091od_masks)) (oov c1 c2 a b l (EL i c1091od_masks)) l
               (ooc c1 c2 a b l (EL j c1091od_masks)) (oos c1 c2 a b l (EL j c1091od_masks))
               (oou c1 c2 a b l (EL j c1091od_masks)) (oov c1 c2 a b l (EL j c1091od_masks)) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN EXISTS_TAC `c1091od_family` THEN
  ASM_REWRITE_TAC[C1091OD_LENGTH] THEN REWRITE_TAC[c1091od_masks] THEN
  REWRITE_TAC[fst C1091OD_LIST; snd C1091OD_LIST]);;

(* Lean: seed — a producer: owner (masks i) contains the seed point (x, y)
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = c1091od_family ==> linside (owner m_i) x y *)
let C1091OD_MASKS = [1;12;48;192;258;512;1024;2048;4096;8192;16384;32768];;
let c1091od_seed i (x, y) = oo_inst `c1091od_family` (oo_seed (el i C1091OD_MASKS) (x, y));;

(* Lean: auxiliary *)
let C1091OD_AUXILIARY = prove
 (`forall c1 c2 a b l i j. j < 20
     ==> (linside (ooc c1 c2 a b l (EL i c1091od_masks)) (oos c1 c2 a b l (EL i c1091od_masks))
                  (oou c1 c2 a b l (EL i c1091od_masks)) (oov c1 c2 a b l (EL i c1091od_masks)) l
                  (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=>
          j IN ooaux c1 c2 a b l (EL i c1091od_masks))`,
  SIMP_TAC[OO_AUX_EXACT]);;

(* Lean: merged_markers  (owners p 4 = owner 258) *)
let C1091OD_MERGED_MARKERS =
  let t1 = c1091od_seed 4 (`&457 / &500`, `&1`) and t2 = c1091od_seed 4 (`&33 / &20`, `&33 / &20`) in
  prove(`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family
           ==> linside (ooc c1 c2 a b l 258) (oos c1 c2 a b l 258) (oou c1 c2 a b l 258)
                       (oov c1 c2 a b l 258) l (&457 / &500) (&1) /\
               linside (ooc c1 c2 a b l 258) (oos c1 c2 a b l 258) (oou c1 c2 a b l 258)
                       (oov c1 c2 a b l 258) l (&33 / &20) (&33 / &20)`,
    MESON_TAC[t1; t2]);;

(* Lean: singleton_missing_marker1  (owners p 0 = owner 1, marker 1 = (457/500, 1)) *)
let C1091OD_SINGLETON_MISSING_MARKER1 = oo_inst `c1091od_family` (oo_missing 1 1);;
