(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C972Owners.lean                   *)
(* (namespace N12Compact.FiniteCases.C972).  The original C972 owners in     *)
(* ascending mask order: Lean owners p i = owner p (masks i) is the owner    *)
(* 5-tuple at EL i c972o_masks; actual p i = ooaux .. (EL i c972o_masks).    *)
(* family = C972Domains.family = c972d_family.  Lean same: all sides are l.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972Domains.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: family (abbrev C972Domains.family), masks *)
let c972o_masks = new_definition
 `c972o_masks = [1;2;12;48;192;256;512;1024;2048;4096;8192;16384]`;;
let C972O_MASKS = [1;2;12;48;192;256;512;1024;2048;4096;8192;16384];;

let C972O_LIST = oo_list_facts `c972d_family` (rand (concl c972o_masks));;
let C972O_LENGTH = (REWRITE_CONV[c972o_masks; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c972o_masks`;;

(* Lean: member *)
let C972O_MEMBER = prove
 (`forall i. i < 12 ==> EL i c972o_masks IN c972d_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C972O_LENGTH; c972o_masks] THEN ASM_REWRITE_TAC[fst C972O_LIST]);;

(* Lean: injective *)
let C972O_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c972o_masks = EL j c972o_masks ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c972o_masks` THEN ASM_REWRITE_TAC[C972O_LENGTH] THEN
  REWRITE_TAC[c972o_masks; snd C972O_LIST]);;

(* Lean: side  (Lean same: both sides are l) *)
let C972O_SIDE = OO_SIDE;;

(* Lean: box *)
let C972O_BOX = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l
     ==> lcont (ooc c1 c2 a b l (EL i c972o_masks)) (oos c1 c2 a b l (EL i c972o_masks))
               (oou c1 c2 a b l (EL i c972o_masks)) (oov c1 c2 a b l (EL i c972o_masks)) l`,
  SIMP_TAC[OO_BOX]);;

(* Lean: apart *)
let C972O_APART = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (ooc c1 c2 a b l (EL i c972o_masks)) (oos c1 c2 a b l (EL i c972o_masks))
               (oou c1 c2 a b l (EL i c972o_masks)) (oov c1 c2 a b l (EL i c972o_masks)) l
               (ooc c1 c2 a b l (EL j c972o_masks)) (oos c1 c2 a b l (EL j c972o_masks))
               (oou c1 c2 a b l (EL j c972o_masks)) (oov c1 c2 a b l (EL j c972o_masks)) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN EXISTS_TAC `c972d_family` THEN
  ASM_REWRITE_TAC[C972O_LENGTH] THEN REWRITE_TAC[c972o_masks] THEN
  REWRITE_TAC[fst C972O_LIST; snd C972O_LIST]);;

(* Lean: foreign *)
let C972O_FOREIGN = prove
 (`forall c1 c2 a b l i j x y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\
     i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (ooc c1 c2 a b l (EL j c972o_masks)) (oos c1 c2 a b l (EL j c972o_masks))
             (oou c1 c2 a b l (EL j c972o_masks)) (oov c1 c2 a b l (EL j c972o_masks)) l x y
     ==> ~linside (ooc c1 c2 a b l (EL i c972o_masks)) (oos c1 c2 a b l (EL i c972o_masks))
                  (oou c1 c2 a b l (EL i c972o_masks)) (oov c1 c2 a b l (EL i c972o_masks)) l x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 `i:num`; `j:num`] C972O_APART) THEN
  ASM_REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]);;

(* Lean: seed — producer at a literal index i and seed point (x, y) *)
let c972o_seed i (x, y) = oo_inst `c972d_family` (oo_seed (el i C972O_MASKS) (x, y));;

(* Lean: aux *)
let C972O_AUX = prove
 (`forall c1 c2 a b l i j. j < 20
     ==> (linside (ooc c1 c2 a b l (EL i c972o_masks)) (oos c1 c2 a b l (EL i c972o_masks))
                  (oou c1 c2 a b l (EL i c972o_masks)) (oov c1 c2 a b l (EL i c972o_masks)) l
                  (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=>
          j IN ooaux c1 c2 a b l (EL i c972o_masks))`,
  SIMP_TAC[OO_AUX_EXACT]);;

(* Lean: singleton_horizontal  (owners p 0 = owner 1) *)
let C972O_SINGLETON_HORIZONTAL = prove
 (`forall c1 c2 a b l x. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\
     &28 / &25 <= x /\ x <= &87 / &50
     ==> linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l x (&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_SIMP_TAC[c972o_seed 0 (`&28 / &25`, `&1`); c972o_seed 0 (`&87 / &50`, `&1`)] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: singleton_vertical  (owners p 1 = owner 2) *)
let C972O_SINGLETON_VERTICAL = prove
 (`forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\
     &28 / &25 <= y /\ y <= &87 / &50
     ==> linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l (&1) y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_SIMP_TAC[c972o_seed 1 (`&1`, `&28 / &25`); c972o_seed 1 (`&1`, `&87 / &50`)] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* the twelve literal cases of  i < 12  with EL i c972o_masks evaluated *)
let C972O_CASES_TAC thms =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `i < 12 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/
                                      i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC))) THEN
  REWRITE_TAC[c972o_masks] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN ASM_SIMP_TAC thms;;

(* Lean: foreign_aux *)
let C972O_FOREIGN_AUX = prove
 (`forall c1 c2 a b l i j k. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\
     i < 12 /\ j < 12 /\ ~(i = j) /\ k IN ooaux c1 c2 a b l (EL j c972o_masks)
     ==> ~(k IN ooaux c1 c2 a b l (EL i c972o_masks))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 `c972d_family`; `c972o_masks`; `i:num`; `j:num`] OO_LIST_AUX_DISJOINT) THEN
  ASM_REWRITE_TAC[C972O_LENGTH] THEN REWRITE_TAC[c972o_masks] THEN
  REWRITE_TAC[fst C972O_LIST; snd C972O_LIST] THEN REWRITE_TAC[GSYM c972o_masks] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]);;

(* Lean: missing_top  (marker 15 = (2, 1543/500) is in no mask) *)
let C972O_MISSING_TOP = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\ i < 12
     ==> ~linside (ooc c1 c2 a b l (EL i c972o_masks)) (oos c1 c2 a b l (EL i c972o_masks))
                  (oou c1 c2 a b l (EL i c972o_masks)) (oov c1 c2 a b l (EL i c972o_masks)) l
                  (&2) (&1543 / &500)`,
  C972O_CASES_TAC (map (fun m -> oo_inst `c972d_family` (oo_missing m 15)) C972O_MASKS));;

(* Lean: domain *)
let C972O_DOMAIN = prove
 (`forall c1 c2 a b l m al i. cdom c972d_family m al /\ NPACK c1 c2 a b l /\
     IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\ i < 12 /\ m = EL i c972o_masks
     ==> MEM (ooaux c1 c2 a b l (EL i c972o_masks)) al`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl) o
    check (fun th -> lhs (concl th) = `m:num`)) THEN
  MATCH_MP_TAC CDOM_OWNER THEN EXISTS_TAC `c972d_family` THEN ASM_SIMP_TAC[C972O_MEMBER]);;
