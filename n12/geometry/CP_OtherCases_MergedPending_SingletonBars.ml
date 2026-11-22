(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/SingletonBars.lean   *)
(* (namespace N12Compact.MergedPending).  Singleton segments of the actual   *)
(* owners 1, 2, 16, 32 for an arbitrary family containing the mask.         *)
(* owner p m is the 5-tuple (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l;  *)
(* auxiliaries p m is ooaux c1 c2 a b l m (combined F0..F9, G0..G9).        *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* the segment between two seeds of owner m: Lean  seed .. ; horizontal_segment *)
let MPSB_SEG_TAC seg m p0 p1 =
  let sa = oo_seed m p0 and sb = oo_seed m p1 in
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC seg THEN
  (if seg == OO_HORIZONTAL_SEGMENT then
     MAP_EVERY EXISTS_TAC [fst p0; fst p1] else MAP_EVERY EXISTS_TAC [snd p0; snd p1]) THEN
  ASM_SIMP_TAC[sa; sb] THEN RASM_ARITH_TAC;;

(* Lean: singleton_bottom *)
let MPSB_SINGLETON_BOTTOM = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ 1 IN fam
     ==> forall x. &28 / &25 <= x /\ x <= &87 / &50
             ==> linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1)
                         (oov c1 c2 a b l 1) l x (&1)`,
  MPSB_SEG_TAC OO_HORIZONTAL_SEGMENT 1 (`&28 / &25`, `&1`) (`&87 / &50`, `&1`));;

(* Lean: singleton_left *)
let MPSB_SINGLETON_LEFT = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ 2 IN fam
     ==> forall y. &28 / &25 <= y /\ y <= &87 / &50
             ==> linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2)
                         (oov c1 c2 a b l 2) l (&1) y`,
  MPSB_SEG_TAC OO_VERTICAL_SEGMENT 2 (`&1`, `&28 / &25`) (`&1`, `&87 / &50`));;

(* Lean: singleton_top *)
let MPSB_SINGLETON_TOP = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ 16 IN fam
     ==> forall x. &113 / &50 <= x /\ x <= &72 / &25
             ==> linside (ooc c1 c2 a b l 16) (oos c1 c2 a b l 16) (oou c1 c2 a b l 16)
                         (oov c1 c2 a b l 16) l x (&3)`,
  MPSB_SEG_TAC OO_HORIZONTAL_SEGMENT 16 (`&113 / &50`, `&3`) (`&72 / &25`, `&3`));;

(* Lean: singleton_right *)
let MPSB_SINGLETON_RIGHT = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ 32 IN fam
     ==> forall y. &113 / &50 <= y /\ y <= &72 / &25
             ==> linside (ooc c1 c2 a b l 32) (oos c1 c2 a b l 32) (oou c1 c2 a b l 32)
                         (oov c1 c2 a b l 32) l (&3) y`,
  MPSB_SEG_TAC OO_VERTICAL_SEGMENT 32 (`&3`, `&113 / &50`) (`&3`, `&72 / &25`));;

(* goal  j IN ooaux .. m : the auxiliary point j lies on one of the bars *)
let MPSB_AUX_TAC (asl, w as g) =
  let j = dest_small_numeral (lhand w) in
  (ONCE_REWRITE_TAC[GSYM (oo_aux_point j)] THEN
   FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC)) g;;

(* Lean: singleton_pairs *)
let MPSB_SINGLETON_PAIRS = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     1 IN fam /\ 2 IN fam /\ 16 IN fam /\ 32 IN fam
     ==> {2, 12} SUBSET ooaux c1 c2 a b l 1 /\
         {0, 10} SUBSET ooaux c1 c2 a b l 2 /\
         {7, 17} SUBSET ooaux c1 c2 a b l 16 /\
         {9, 19} SUBSET ooaux c1 c2 a b l 32`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MPSB_SINGLETON_BOTTOM) THEN MP_TAC(SPEC_ALL MPSB_SINGLETON_LEFT) THEN
  MP_TAC(SPEC_ALL MPSB_SINGLETON_TOP) THEN MP_TAC(SPEC_ALL MPSB_SINGLETON_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN REPEAT CONJ_TAC THEN MPSB_AUX_TAC);;
