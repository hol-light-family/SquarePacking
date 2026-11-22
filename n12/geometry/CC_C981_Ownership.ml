(* ========================================================================= *)
(* Phase 2: Completion/Cases/C981/Ownership.lean.                            *)
(* ownerMasks i is EL i c981ow_masks;  owners p i is the OriginalOwners      *)
(* owner 5-tuple at mask EL i c981ow_masks;  natCombinedOwners p             *)
(* (ownerIndex p m) is ooaux c1 c2 a b l m;  ownershipVector p is            *)
(* c981ow_vector c1 c2 a b l;  List.ofFn v (v : Fin 12 -> Finset) is         *)
(* list_of_seq v 12;  v[i]! is EL i v;  AuxExact q 2 S is                    *)
(* !j. j < 20 ==> (linside q (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=> j IN S). *)
(* owners_query_inside / owners_query_outside quantify over the computed     *)
(* point lists queryInsidePoints / queryOutsidePoints; they are producers    *)
(* c981ow_query_inside i S (x, y) / c981ow_query_outside i S (x, y) that     *)
(* check that (x, y) is in the list for the literal owned set S.             *)
(* ========================================================================= *)

needs "n12/geometry/CC_C981_RowIdentity.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: ownerMasks *)
let c981ow_masks = new_definition
 `c981ow_masks = [1; 2; 12; 48; 192; 512; 1024; 2048; 4096; 8192; 16384; 32768]`;;
let C981OW_MASKS = [1; 2; 12; 48; 192; 512; 1024; 2048; 4096; 8192; 16384; 32768];;

let C981OW_LIST = oo_list_facts `ccc981ri_family` (rand (concl c981ow_masks));;
let C981OW_LENGTH = (REWRITE_CONV[c981ow_masks; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c981ow_masks`;;

(* Lean: ownerMasks_mem *)
let C981OW_OWNERMASKS_MEM = prove
 (`forall i. i < 12 ==> EL i c981ow_masks IN ccc981ri_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C981OW_LENGTH; c981ow_masks] THEN ASM_REWRITE_TAC[fst C981OW_LIST]);;

(* Lean: ownerMasks_injective *)
let C981OW_OWNERMASKS_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c981ow_masks = EL j c981ow_masks ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c981ow_masks` THEN ASM_REWRITE_TAC[C981OW_LENGTH] THEN
  REWRITE_TAC[c981ow_masks; snd C981OW_LIST]);;

(* Lean: ownershipVector *)
let c981ow_vector = new_definition
 `c981ow_vector (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) =
    MAP (\m. ooaux c1 c2 a b l m) c981ow_masks`;;

let C981OW_VECTOR_EL = prove
 (`forall c1 c2 a b l i. i < 12 ==> EL i (c981ow_vector c1 c2 a b l) = ooaux c1 c2 a b l (EL i c981ow_masks)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c981ow_vector] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_MAP o lhand o snd) THEN
  ASM_REWRITE_TAC[C981OW_LENGTH] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN REFL_TAC);;

(* Lean: ownership_entries *)
let C981OW_OWNERSHIP_ENTRIES = prove
 (`forall c1 c2 a b l (v:num->num->bool). c981ow_vector c1 c2 a b l = list_of_seq v 12
     ==> forall i. i < 12 ==> ooaux c1 c2 a b l (EL i c981ow_masks) = v i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM C981OW_VECTOR_EL; EL_LIST_OF_SEQ]);;

(* Lean: ownership_entry_at *)
let C981OW_OWNERSHIP_ENTRY_AT = prove
 (`forall c1 c2 a b l (v:(num->bool)list) i. c981ow_vector c1 c2 a b l = v /\ i < 12
     ==> ooaux c1 c2 a b l (EL i c981ow_masks) = EL i v`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[C981OW_VECTOR_EL]);;

(* Lean: owners_side_gt, owners_side_le  (the owners' side is l) *)
let C981OW_OWNERS_SIDE_GT = OO_SIDE;;
let C981OW_OWNERS_SIDE_LE = OO_SIDE_LE;;

(* Lean: owners_contained *)
let C981OW_OWNERS_CONTAINED = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l ==> lcont (ooc c1 c2 a b l (EL i c981ow_masks)) (oos c1 c2 a b l (EL i c981ow_masks)) (oou c1 c2 a b l (EL i c981ow_masks)) (oov c1 c2 a b l (EL i c981ow_masks)) l`,
  SIMP_TAC[OO_BOX]);;

(* Lean: owners_markers *)
let C981OW_OWNERS_MARKERS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\ i < 12
     ==> forall k. k < 16 ==> (linside (ooc c1 c2 a b l (EL i c981ow_masks)) (oos c1 c2 a b l (EL i c981ow_masks)) (oou c1 c2 a b l (EL i c981ow_masks)) (oov c1 c2 a b l (EL i c981ow_masks)) l (marker k$1) (marker k$2) <=>
                         k IN bitset (EL i c981ow_masks))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OO_MARKERS THEN
  EXISTS_TAC `ccc981ri_family` THEN ASM_SIMP_TAC[C981OW_OWNERMASKS_MEM]);;

(* Lean: owners_disjoint *)
let C981OW_OWNERS_DISJOINT = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (ooc c1 c2 a b l (EL i c981ow_masks)) (oos c1 c2 a b l (EL i c981ow_masks)) (oou c1 c2 a b l (EL i c981ow_masks)) (oov c1 c2 a b l (EL i c981ow_masks)) l (ooc c1 c2 a b l (EL j c981ow_masks)) (oos c1 c2 a b l (EL j c981ow_masks)) (oou c1 c2 a b l (EL j c981ow_masks)) (oov c1 c2 a b l (EL j c981ow_masks)) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_APART THEN EXISTS_TAC `ccc981ri_family` THEN
  ASM_REWRITE_TAC[C981OW_LENGTH] THEN REWRITE_TAC[c981ow_masks] THEN
  REWRITE_TAC[fst C981OW_LIST; snd C981OW_LIST]);;

(* Lean: owners_auxiliary *)
let C981OW_OWNERS_AUXILIARY = prove
 (`forall c1 c2 a b l (v:num->num->bool) i. c981ow_vector c1 c2 a b l = list_of_seq v 12 /\ i < 12
     ==> forall j. j < 20 ==> (linside (ooc c1 c2 a b l (EL i c981ow_masks)) (oos c1 c2 a b l (EL i c981ow_masks)) (oou c1 c2 a b l (EL i c981ow_masks)) (oov c1 c2 a b l (EL i c981ow_masks)) l (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=>
                         j IN v i)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[OO_AUX_EXACT] THEN
  ASM_MESON_TAC[C981OW_OWNERSHIP_ENTRIES]);;

(* Lean: owners_query_inside, as a producer at a literal owner index i, owned set S and point:
   |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = ccc981ri_family /\ ooaux c1 c2 a b l m = S
        ==> linside (owner m) x y   at the literal mask m = EL i c981ow_masks *)
let c981ow_query_inside i s (x, y) =
  let m = el i C981OW_MASKS in
  oo_inst `ccc981ri_family` (oo_known m s (x, y));;

(* Lean: owners_query_outside, the same producer for queryOutsidePoints (missing markers and
   unowned auxiliary points) *)
let c981ow_query_outside i s (x, y) =
  let m = el i C981OW_MASKS in
  let p = (rat_of_term x, rat_of_term y) in
  let mt = mk_small_numeral m in
  let own f = list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; mt]) in
  let eqtm = mk_eq(own `ooaux`, s) in
  let concl0 = mk_neg(list_mk_comb(`linside`, map own [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`; x; y])) in
  let hyp = list_mk_conj [`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family`; eqtm] in
  let goal = list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
                            mk_imp(hyp, concl0)) in
  let th =
    try let k = find (fun k -> not (mem k (bits m)) && qeq (marker_q k) p) (0 -- 15) in
        let mth = oo_inst `ccc981ri_family` (oo_missing m k) in
        prove(goal, REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL mth) THEN ASM_REWRITE_TAC[] THEN
                    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[])
    with Failure _ ->
    let j = try find (fun j -> not (mem j (numset_of s)) && qeq (aux2_point j) p) (0 -- 19)
            with Failure _ -> failwith "c981ow_query_outside: point not in queryOutsidePoints" in
    let ath = SPEC mt (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
                (oo_aux_point j)) in
    prove(goal, REPEAT STRIP_TAC THEN MP_TAC ath THEN ASM_REWRITE_TAC[] THEN
                CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV) in
  th;;

(* checks of the producers *)
let C981OW_QUERY_CHECK_IN = c981ow_query_inside 0 `{3}` (`&1`, `&457 / &500`);;
let C981OW_QUERY_CHECK_OUT1 = c981ow_query_outside 0 `{3}` (`&457 / &500`, `&1`);;
let C981OW_QUERY_CHECK_OUT2 = c981ow_query_outside 0 `{3}` (term_of_rat (fst (aux2_point 4)), term_of_rat (snd (aux2_point 4)));;
