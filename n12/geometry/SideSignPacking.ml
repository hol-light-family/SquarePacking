(* ========================================================================= *)
(* Port of Completion/Cases/C696/SideSignPacking.lean                        *)
(* (namespace S12Completion.C696.SideSignPacking).  The returned C696        *)
(* side-sign lemmas instantiated in the original normalized packing; the     *)
(* exact auxiliary assignment stays an explicit premise.                     *)
(* The packing is NPACK c1 c2 a b l; Lean ownerMasks (Fin 12 -> Nat) and     *)
(* auxiliaryVector (Fin 12 -> Finset Nat) are HOL lists indexed by i < 12;   *)
(* owners p i is the owner of the mask EL i c696ssp_owner_masks, i.e. the    *)
(* 5-tuple (ooc .. m, oos .. m, oou .. m, oov .. m, l);                      *)
(* natCombinedOwners p (ownerIndex p m) is ooaux c1 c2 a b l m.  The retained*)
(* rows with originalId 696 are the rows j < 577 with                        *)
(* MEM (EL j COVER_IDS) EXPECTED_IDS /\ EL j COVER_IDS = 696, r.groups is    *)
(* set_of_list (EL j ROWS) (RowIdentity.ml).  queryInsidePoints /            *)
(* queryOutsidePoints are the producers oo_known / c696ssp_outside.          *)
(* centerX / centerY are lcx / lcy; the side-sign lemmas are C696SS_*.      *)
(* Tag C696SSP_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/SideSign.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: ownerMasks *)
let c696ssp_owner_masks = new_definition
 `c696ssp_owner_masks = [1; 2; 12; 16; 32; 192; 256; 1024; 4096; 8192; 16384; 32768]`;;

(* Lean: family *)
let c696ssp_family = new_definition
 `c696ssp_family = {1, 2, 12, 16, 32, 192, 256, 1024, 4096, 8192, 16384, 32768}`;;
let C696SSP_F = `c696ssp_family`;;

let C696SSP_LT12 = prove
 (`forall P. (forall i. i < 12 ==> P i) <=>
       P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\ P 10 /\ P 11`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN GEN_TAC THEN
    DISCH_THEN(fun th -> MP_TAC(MP (ARITH_RULE (mk_imp(concl th,
      `i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/
       i = 9 \/ i = 10 \/ i = 11`))) th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: ownerMasks_mem *)
let C696SSP_OWNERMASKS_MEM = prove
 (`forall i. i < 12 ==> EL i c696ssp_owner_masks IN c696ssp_family`,
  REWRITE_TAC[C696SSP_LT12; c696ssp_owner_masks] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[c696ssp_family; IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: row_family *)
let C696SSP_ROW = find (fun i -> rand (concl ID_LOOKUP.(i)) = `696`) (0 -- 576);;
let C696SSP_ROW_FAMILY = ri_family_at C696SSP_ROW C696SSP_F;;

(* Lean: auxiliaryVector *)
let c696ssp_auxiliary_vector = new_definition
 `c696ssp_auxiliary_vector =
    [{2, 12}; {0, 10}; {}; {7, 17}; {9, 19}; {};
     {4, 13}; {5, 16}; {1, 11}; {6, 15}; {8, 18}; {3, 14}]:(num->bool)list`;;

(* Lean: ownershipVector *)
let c696ssp_ownership_vector = new_definition
 `c696ssp_ownership_vector c1 c2 a b l = MAP (ooaux c1 c2 a b l) c696ssp_owner_masks`;;

(* Lean: ExactAssignment *)
let c696ssp_exact_assignment = new_definition
 `c696ssp_exact_assignment c1 c2 a b l <=>
    forall i. i < 12 ==> ooaux c1 c2 a b l (EL i c696ssp_owner_masks) = EL i c696ssp_auxiliary_vector`;;

(* Lean: exactAssignment_of_vector *)
let C696SSP_EXACTASSIGNMENT_OF_VECTOR = prove
 (`forall c1 c2 a b l. c696ssp_ownership_vector c1 c2 a b l = c696ssp_auxiliary_vector
     ==> c696ssp_exact_assignment c1 c2 a b l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c696ssp_ownership_vector; c696ssp_exact_assignment] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(AP_TERM `EL (i:num):(num->bool)list->num->bool` th)) THEN
  SUBGOAL_THEN `i < LENGTH c696ssp_owner_masks` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c696ssp_owner_masks; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[EL_MAP]]);;

(* the owner's literal assignment from the exact assignment *)
let C696SSP_LABEL i =
  let th = SPEC (mk_small_numeral i)
    (REWRITE_RULE[c696ssp_exact_assignment] (ASSUME `c696ssp_exact_assignment c1 c2 a b l`)) in
  let th = MP th (EQT_ELIM (NUM_REDUCE_CONV (lhand (concl th)))) in
  CONV_RULE (BINOP_CONV (REWRITE_CONV[c696ssp_owner_masks; c696ssp_auxiliary_vector] THENC
                         ONCE_DEPTH_CONV EL_CONV)) th;;

let C696SSP_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C696SSP_HYP = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c696ssp_family`;;
let C696SSP_HH = ASSUME C696SSP_HYP;;
let C696SSP_NP = CONJUNCT1 C696SSP_HH;;
let c696ssp_q m = map (fun f -> list_mk_comb(f, C696SSP_VARS @ [mk_small_numeral m]))
                    [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

(* Lean: inside_points (private): a point of queryInsidePoints m 2 owned *)
let c696ssp_inside eqth p =
  let m = dest_small_numeral (rand (lhand (concl eqth))) in
  MP (SPECL C696SSP_VARS (oo_inst C696SSP_F (oo_known m (rhs (concl eqth)) p)))
     (CONJ C696SSP_NP (CONJ (CONJUNCT2 C696SSP_HH) eqth));;

(* Lean: outside_points (private): a point of queryOutsidePoints m 2 owned
   (a missing marker of m or an auxiliary point not in owned) *)
let c696ssp_outside eqth (x, y) =
  let m = dest_small_numeral (rand (lhand (concl eqth))) in
  let s = rhs (concl eqth) in
  let p = (rat_of_term x, rat_of_term y) in
  let mt = mk_small_numeral m in
  let concl0 = mk_neg(list_mk_comb(`linside`, c696ssp_q m @ [x; y])) in
  let fin th = let th' = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) th in
    if aconv (concl th') concl0 then th' else failwith "c696ssp_outside: shape" in
  try let k = find (fun k -> not (mem k (bits m)) && qeq (marker_q k) p) (0 -- 15) in
      let mth = MP (SPECL C696SSP_VARS (oo_inst C696SSP_F (oo_missing m k))) C696SSP_HH in
      fin mth
  with Failure _ ->
  let j = try find (fun j -> not (mem j (numset_of s)) && qeq (aux2_point j) p) (0 -- 19)
          with Failure _ -> failwith "c696ssp_outside: point not in queryOutsidePoints" in
  let ath = SPECL (C696SSP_VARS @ [mt]) (oo_aux_point j) in
  let notin = EQF_ELIM ((RAND_CONV (REWR_CONV eqth) THENC REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY] THENC
                         NUM_REDUCE_CONV) (rand (concl ath))) in
  let th = EQ_MP (SYM (AP_TERM `(~)` ath)) notin in
  fin th;;

(* Lean: lower_walls / upper_walls (private) *)
let c696ssp_walls m lower =
  let box = REWRITE_RULE[lcont] (MP (SPECL (C696SSP_VARS @ [mk_small_numeral m]) OO_BOX) C696SSP_NP) in
  let tm = if lower then `forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y`
           else `forall x y. linside c s u v a x y ==> x <= &4 /\ y <= &4` in
  let tm = subst (zip (c696ssp_q m) [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]) tm in
  TAC_PROOF(([], tm), REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box) THEN REAL_ARITH_TAC);;

let c696ssp_is_rrel t =
  (is_eq t && type_of (lhs t) = `:real`) ||
  (try let op = fst (dest_const (rator (rator t))) in
       (op = "real_lt" || op = "real_le") with Failure _ -> false);;
let c696ssp_app th m facts =
  let th' = SPECL (c696ssp_q m) th in
  let ant = lhand (concl th') in
  MP th' (TAC_PROOF((map (fun t -> ("", t)) facts, ant),
    REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY (fun th -> if c696ssp_is_rrel (concl th) then MP_TAC th else ALL_TAC) facts THEN
      REAL_ARITH_TAC]));;

(* Lean: center_signs *)
let C696SSP_CENTER_SIGNS =
  let hv = `c696ssp_exact_assignment c1 c2 a b l` in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP in
  let unit m = MP (SPECL (C696SSP_VARS @ [mk_small_numeral m]) OO_UNIT) C696SSP_NP in
  let one i m lemma lower ptsin ptsout =
    let lab = C696SSP_LABEL i in
    c696ssp_app lemma m ([unit m; side; c696ssp_walls m lower] @
      map (c696ssp_inside lab) ptsin @ map (c696ssp_outside lab) ptsout) in
  let s8 = one 8 4096 C696SS_LEFT_SIDE_CENTER_GT_TWO true
             [(`&457 / &500`, `&2`); (`&1`, `&12 / &5`)] [(`&1`, `&87 / &50`); (`&87 / &50`, `&2`)] in
  let s9 = one 9 8192 C696SS_BOTTOM_SIDE_CENTER_GT_TWO true
             [(`&2`, `&457 / &500`); (`&12 / &5`, `&1`)] [(`&87 / &50`, `&1`); (`&2`, `&87 / &50`)] in
  let s10 = one 10 16384 C696SS_RIGHT_SIDE_CENTER_LT_TWO false
             [(`&1543 / &500`, `&2`); (`&3`, `&8 / &5`)] [(`&3`, `&113 / &50`); (`&113 / &50`, `&2`)] in
  let s11 = one 11 32768 C696SS_TOP_SIDE_CENTER_LT_TWO false
             [(`&2`, `&1543 / &500`); (`&8 / &5`, `&3`)] [(`&113 / &50`, `&3`); (`&2`, `&113 / &50`)] in
  GENL C696SSP_VARS (DISCH (mk_conj(C696SSP_HYP, hv))
    (PROVE_HYP (CONJUNCT1 (ASSUME (mk_conj(C696SSP_HYP, hv))))
      (PROVE_HYP (CONJUNCT2 (ASSUME (mk_conj(C696SSP_HYP, hv))))
        (end_itlist CONJ [s8; s9; s10; s11]))));;

(* Lean: center_signs_of_vector *)
let C696SSP_CENTER_SIGNS_OF_VECTOR = prove
 (mk_forall(`c1:num->real`, list_mk_forall(tl C696SSP_VARS,
    mk_imp(`(NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c696ssp_family) /\
            c696ssp_ownership_vector c1 c2 a b l = c696ssp_auxiliary_vector`,
           rand (snd (strip_forall (concl C696SSP_CENTER_SIGNS)))))),
  MESON_TAC[C696SSP_CENTER_SIGNS; C696SSP_EXACTASSIGNMENT_OF_VECTOR]);;

(* Lean: center_signs_of_row *)
let C696SSP_CENTER_SIGNS_OF_ROW = prove
 (mk_forall(`j:num`, mk_imp(`j < 577 /\ MEM (EL j COVER_IDS) EXPECTED_IDS /\ EL j COVER_IDS = 696`,
    list_mk_forall(C696SSP_VARS,
      mk_imp(`(NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL j ROWS)) /\
              c696ssp_exact_assignment c1 c2 a b l`,
             rand (snd (strip_forall (concl C696SSP_CENTER_SIGNS))))))),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP C696SSP_ROW_FAMILY) THEN
  ACCEPT_TAC C696SSP_CENTER_SIGNS);;
