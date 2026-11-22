(* ========================================================================= *)
(* Port of Completion/Cases/C696/AuxiliaryNecessity.lean                     *)
(* (namespace S12Completion.C696.AuxiliaryNecessity).  The original          *)
(* certified single-family domains (S12 singleSpec n, re-proved by           *)
(* ro_single) imply the unique C696 assignment.  Conventions of              *)
(* SideSignPacking.ml (owner masks c696ssp_owner_masks, family               *)
(* c696ssp_family, ExactAssignment c696ssp_exact_assignment).  Lean          *)
(* nonexempt / candidates / assigned are HOL lists indexed by j < 10 and     *)
(* k < 2; actual p k i = natAuxOwners p k (ownerIndex p (ownerMasks i)) is   *)
(* c696an_actual c1 c2 a b l k i (auxown k at the owner index).  chosen /    *)
(* selection use the Hilbert choice (the proof argument hf of Lean is       *)
(* dropped).  Distinct10 / FDomain / ... are the c696au_ predicates of       *)
(* AuxUnique.ml.  Tag C696AN_.                                               *)
(* ========================================================================= *)

needs "n12/geometry/SideSignPacking.ml";;
needs "n12/geometry/AuxUnique.ml";;
needs "n12/geometry/RelaxedOwnerDomain.ml";;

let C696AN_VARS = C696SSP_VARS;;
let C696AN_HYP = C696SSP_HYP;;
let c696an_stmt concl = list_mk_forall(C696AN_VARS, mk_imp(C696AN_HYP, concl));;

(* Lean: nonexempt *)
let c696an_nonexempt = new_definition
 `c696an_nonexempt = [0; 1; 3; 4; 6; 7; 8; 9; 10; 11]`;;

(* Lean: candidates *)
let c696an_candidates = new_definition
 `c696an_candidates =
   [[[2]; [0]; [7]; [9]; [0; 2; 4]; [5; 7; 9]; [0; 1]; [2; 4; 6]; [8; 9]; [3; 5; 7]];
    [[2]; [0]; [7]; [9]; [0; 2; 3]; [6; 7; 9]; [0; 1; 3]; [2; 5]; [6; 8; 9]; [4; 7]]]:((num list)list)list`;;

(* Lean: assigned *)
let c696an_assigned = new_definition
 `c696an_assigned = [[2; 0; 7; 9; 4; 5; 1; 6; 8; 3]; [2; 0; 7; 9; 3; 6; 1; 5; 8; 4]]:(num list)list`;;

let C696AN_LT10 = prove
 (`forall P. (forall i. i < 10 ==> P i) <=> P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN GEN_TAC THEN
    DISCH_THEN(fun th -> MP_TAC(MP (ARITH_RULE (mk_imp(concl th,
      `i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9`))) th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;
let C696AN_LT2 = prove
 (`forall P. (forall k. k < 2 ==> P k) <=> P 0 /\ P 1`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN GEN_TAC THEN
    DISCH_THEN(fun th -> MP_TAC(MP (ARITH_RULE (mk_imp(concl th, `k = 0 \/ k = 1`))) th)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let C696AN_EL_CONV =
  REWRITE_CONV[c696an_nonexempt; c696an_candidates; c696an_assigned; c696ssp_owner_masks] THENC
  ONCE_DEPTH_CONV EL_CONV THENC ONCE_DEPTH_CONV EL_CONV THENC ONCE_DEPTH_CONV EL_CONV;;

let C696AN_PAIRWISE_TAC =
  REWRITE_TAC[PAIRWISE; ALL] THEN CONV_TAC NUM_REDUCE_CONV;;

(* Lean: nonexempt_injective *)
let C696AN_NONEXEMPT_INJECTIVE = prove
 (`forall i j. i < 10 /\ j < 10 /\ EL i c696an_nonexempt = EL j c696an_nonexempt ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c696an_nonexempt` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c696an_nonexempt; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM c696an_nonexempt] THEN REWRITE_TAC[c696an_nonexempt] THEN C696AN_PAIRWISE_TAC);;

(* Lean: ownerMasks_injective *)
let C696AN_OWNERMASKS_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c696ssp_owner_masks = EL j c696ssp_owner_masks ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c696ssp_owner_masks` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c696ssp_owner_masks; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM c696ssp_owner_masks] THEN REWRITE_TAC[c696ssp_owner_masks] THEN C696AN_PAIRWISE_TAC);;

(* Lean: specifications / specifications_checked: the twenty S12 single specs, re-proved as
   |- hdom c696ssp_family (ownerMasks (nonexempt j)) k [{n} | n in candidates k j] *)
let C696AN_SPEC_IDS = [[0; 4; 14; 17; 20; 34; 55; 66; 75; 88]; [2; 6; 16; 18; 22; 35; 57; 68; 77; 90]];;
let C696AN_NE_L = [0; 1; 3; 4; 6; 7; 8; 9; 10; 11];;
let C696AN_MASKS_L = [1; 2; 12; 16; 32; 192; 256; 1024; 4096; 8192; 16384; 32768];;
let C696AN_CAND_L =
  [[[2]; [0]; [7]; [9]; [0; 2; 4]; [5; 7; 9]; [0; 1]; [2; 4; 6]; [8; 9]; [3; 5; 7]];
   [[2]; [0]; [7]; [9]; [0; 2; 3]; [6; 7; 9]; [0; 1; 3]; [2; 5]; [6; 8; 9]; [4; 7]]];;
let C696AN_SPECIFICATIONS =
  Array.of_list (map (fun k ->
    Array.of_list (map (fun j ->
      let n = el j (el k C696AN_SPEC_IDS) in
      let (_, m, k', _, _, al) = pk_single_row n in
      if m <> el (el j C696AN_NE_L) C696AN_MASKS_L || k' <> k ||
         al <> map (fun x -> [x]) (el j (el k C696AN_CAND_L))
      then failwith ("C696AN_SPECIFICATIONS: spec " ^ string_of_int n) else
      ro_single `c696ssp_family` n) (0 -- 9))) [0; 1]);;

(* Lean: actual *)
let c696an_actual = new_definition
 `c696an_actual (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) k i =
    auxown k (c1 (oidx c1 c2 a b l (EL i c696ssp_owner_masks)))
             (c2 (oidx c1 c2 a b l (EL i c696ssp_owner_masks)))
             (a (oidx c1 c2 a b l (EL i c696ssp_owner_masks)))
             (b (oidx c1 c2 a b l (EL i c696ssp_owner_masks))) l`;;

(* forward helpers: theorems  NPACK .., IMAGE .. |- ...  (hyps = the stripped assumptions) *)
let c696an_ci th = UNDISCH_ALL (REWRITE_RULE[IMP_CONJ] (SPEC_ALL th));;
let c696an_lt i n = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral i) (mk_small_numeral n)));;
let c696an_npack = ASSUME `NPACK c1 c2 a b l` and c696an_image = ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c696ssp_family`;;
(* |- MEM (auxown k (owner m)) al  from  |- hdom c696ssp_family m k al *)
let c696an_owner_mem h =
  let args = snd (strip_comb (concl h)) in
  let m = el 1 args and k = el 2 args and al = el 3 args in
  MP (SPECL ([`c696ssp_family`; m; k; al] @ C696AN_VARS) HDOM_OWNER)
     (end_itlist CONJ [h; c696an_npack; c696an_image; in_fam (dest_small_numeral m) `c696ssp_family`]);;

(* Lean: actual_domains *)
let C696AN_ACTUAL_DOMAINS = prove
 (c696an_stmt `forall k j. k < 2 /\ j < 10 ==>
     MEM (c696an_actual c1 c2 a b l k (EL j c696an_nonexempt))
         (MAP (\n. {n}) (EL j (EL k c696an_candidates)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; C696AN_LT2; C696AN_LT10] THEN
  CONV_TAC C696AN_EL_CONV THEN REWRITE_TAC[MAP; c696an_actual] THEN CONV_TAC C696AN_EL_CONV THEN
  REPEAT CONJ_TAC THEN
  FIRST (map (fun h -> ACCEPT_TAC (c696an_owner_mem h))
    (List.concat (map Array.to_list (Array.to_list C696AN_SPECIFICATIONS)))));;

(* Lean: actual_disjoint *)
let C696AN_ACTUAL_DISJOINT = prove
 (c696an_stmt `forall k i j. i < 12 /\ j < 12 /\ ~(i = j)
     ==> DISJOINT (c696an_actual c1 c2 a b l k i) (c696an_actual c1 c2 a b l k j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[c696an_actual] THEN
  MATCH_MP_TAC OO_AUXK_DISJOINT THEN EXISTS_TAC `c696ssp_family` THEN
  ASM_SIMP_TAC[C696SSP_OWNERMASKS_MEM] THEN ASM_MESON_TAC[C696AN_OWNERMASKS_INJECTIVE]);;

(* Lean: singleton_exists *)
let C696AN_SINGLETON_EXISTS = prove
 (c696an_stmt `forall k j. k < 2 /\ j < 10 ==>
     exists n. MEM n (EL j (EL k c696an_candidates)) /\
         c696an_actual c1 c2 a b l k (EL j c696an_nonexempt) = {n}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `j:num`] (c696an_ci C696AN_ACTUAL_DOMAINS)) THEN
  ASM_REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]);;

(* Lean: chosen *)
let c696an_chosen = new_definition
 `c696an_chosen (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) k j =
    @n. MEM n (EL j (EL k c696an_candidates)) /\
        c696an_actual c1 c2 a b l k (EL j c696an_nonexempt) = {n}`;;

(* Lean: chosen_spec *)
let C696AN_CHOSEN_SPEC = prove
 (c696an_stmt `forall k j. k < 2 /\ j < 10 ==>
     MEM (c696an_chosen c1 c2 a b l k j) (EL j (EL k c696an_candidates)) /\
     c696an_actual c1 c2 a b l k (EL j c696an_nonexempt) = {c696an_chosen c1 c2 a b l k j}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c696an_chosen] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(SPECL [`k:num`; `j:num`] (c696an_ci C696AN_SINGLETON_EXISTS)) THEN ASM_REWRITE_TAC[]);;

(* Lean: selection *)
let c696an_selection = new_definition
 `c696an_selection (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) k j =
    if j < 10 then c696an_chosen c1 c2 a b l k j else 0`;;

(* Lean: selection_spec *)
let C696AN_SELECTION_SPEC = prove
 (c696an_stmt `forall k j. k < 2 /\ j < 10 ==>
     MEM (c696an_selection c1 c2 a b l k j) (EL j (EL k c696an_candidates)) /\
     c696an_actual c1 c2 a b l k (EL j c696an_nonexempt) = {c696an_selection c1 c2 a b l k j}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c696an_selection] THEN
  MP_TAC(SPECL [`k:num`; `j:num`] (c696an_ci C696AN_CHOSEN_SPEC)) THEN ASM_REWRITE_TAC[]);;

let C696AN_NONEXEMPT_LT = prove
 (`forall j. j < 10 ==> EL j c696an_nonexempt < 12`,
  REWRITE_TAC[C696AN_LT10; c696an_nonexempt] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Lean: selection_distinct *)
let C696AN_SELECTION_DISTINCT = prove
 (c696an_stmt `forall k. k < 2 ==> c696au_distinct10 (c696an_selection c1 c2 a b l k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[c696au_distinct10] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `i:num`] (c696an_ci C696AN_SELECTION_SPEC)) THEN
  MP_TAC(SPECL [`k:num`; `j:num`] (c696an_ci C696AN_SELECTION_SPEC)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `EL i c696an_nonexempt`; `EL j c696an_nonexempt`]
    (c696an_ci C696AN_ACTUAL_DISJOINT)) THEN
  ASM_SIMP_TAC[C696AN_NONEXEMPT_LT] THEN
  REWRITE_TAC[SET_RULE `DISJOINT {x:num} {x} <=> false`] THEN
  ASM_MESON_TAC[C696AN_NONEXEMPT_INJECTIVE]);;

(* Lean: f_domain_iff / g_domain_iff / f_assignment_iff / g_assignment_iff (private) are
   replaced by literal evaluation below. *)
let c696an_selfact k j =
  CONV_RULE C696AN_EL_CONV
    (MP (MP (SPECL [mk_small_numeral k; mk_small_numeral j] (c696an_ci C696AN_SELECTION_SPEC))
            (c696an_lt k 2)) (c696an_lt j 10));;

(* Lean: actual_singletons *)
let C696AN_ACTUAL_SINGLETONS = prove
 (c696an_stmt `forall k j. k < 2 /\ j < 10 ==>
     c696an_actual c1 c2 a b l k (EL j c696an_nonexempt) = {EL j (EL k c696an_assigned)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let facts k = map (c696an_selfact k) (0 -- 9) in
  let mems k = map (fun th -> REWRITE_RULE[MEM] (CONJUNCT1 th)) (facts k)
  and eqs k = map CONJUNCT2 (facts k) in
  let dist k = MP (SPEC (mk_small_numeral k) (c696an_ci C696AN_SELECTION_DISTINCT)) (c696an_lt k 2) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; C696AN_LT2; C696AN_LT10] THEN
  SUBGOAL_THEN `c696au_fassignment (c696an_selection c1 c2 a b l 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC C696AU_F_UNIQUE THEN CONJ_TAC THENL
     [REWRITE_TAC[c696au_fdomain] THEN REWRITE_TAC (mems 0); ACCEPT_TAC (dist 0)];
    ALL_TAC] THEN
  SUBGOAL_THEN `c696au_gassignment (c696an_selection c1 c2 a b l 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC C696AU_G_UNIQUE THEN CONJ_TAC THENL
     [REWRITE_TAC[c696au_gdomain] THEN REWRITE_TAC (mems 1); ACCEPT_TAC (dist 1)];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c696au_fassignment; c696au_gassignment]) THEN
  CONV_TAC C696AN_EL_CONV THEN
  REWRITE_TAC (eqs 0 @ eqs 1) THEN ASM_REWRITE_TAC[]);;

(* Lean: actual_empty *)
let C696AN_ACTUAL_EMPTY = prove
 (c696an_stmt `forall k. k < 2 ==> forall i. i = 2 \/ i = 5 ==> c696an_actual c1 c2 a b l k i = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C696AN_LT2] THEN
  CONJ_TAC THEN GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[c696an_actual] THEN CONV_TAC C696AN_EL_CONV THEN
  FIRST (map (fun (m, k) ->
    ACCEPT_TAC (REWRITE_RULE[MEM] (c696an_owner_mem (pk_hdom_empty `c696ssp_family` m k))))
    [12, 0; 12, 1; 192, 0; 192, 1]));;

(* Lean: exact_assignment *)
let C696AN_EXACT_ASSIGNMENT = prove
 (c696an_stmt `c696ssp_exact_assignment c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let norm = CONV_RULE (REWRITE_CONV[c696an_actual] THENC C696AN_EL_CONV) in
  let sing = List.concat (map (fun k -> map (fun j ->
     norm (MP (MP (SPECL [mk_small_numeral k; mk_small_numeral j] (c696an_ci C696AN_ACTUAL_SINGLETONS))
                  (c696an_lt k 2)) (c696an_lt j 10))) (0 -- 9)) [0; 1]) in
  let emp = List.concat (map (fun k -> map (fun i ->
     norm (MP (SPEC (mk_small_numeral i) (MP (SPEC (mk_small_numeral k) (c696an_ci C696AN_ACTUAL_EMPTY))
                                            (c696an_lt k 2)))
              (ARITH_RULE (mk_disj(mk_eq(mk_small_numeral i, `2`), mk_eq(mk_small_numeral i, `5`)))))) [2; 5]) [0; 1]) in
  REWRITE_TAC[c696ssp_exact_assignment; C696SSP_LT12] THEN
  CONV_TAC (REWRITE_CONV[c696ssp_owner_masks; c696ssp_auxiliary_vector] THENC ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[ooaux; AUXOWN2_COMBOWN] THEN REWRITE_TAC (sing @ emp) THEN
  REWRITE_TAC[combown; IMAGE_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN SET_TAC[]);;

(* Lean: ownership_vector *)
let C696AN_OWNERSHIP_VECTOR = prove
 (c696an_stmt `c696ssp_ownership_vector c1 c2 a b l = c696ssp_auxiliary_vector`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC (c696an_ci C696AN_EXACT_ASSIGNMENT) THEN
  REWRITE_TAC[c696ssp_ownership_vector; c696ssp_owner_masks; MAP] THEN
  REWRITE_TAC (map C696SSP_LABEL (0 -- 11)) THEN REWRITE_TAC[c696ssp_auxiliary_vector]);;

(* Lean: center_signs *)
let C696AN_CENTER_SIGNS = prove
 (c696an_stmt (rand (snd (strip_forall (concl C696SSP_CENTER_SIGNS)))),
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC (SPEC_ALL C696SSP_CENTER_SIGNS) THEN
  ASM_SIMP_TAC[C696AN_EXACT_ASSIGNMENT]);;

(* Lean: center_signs_of_row *)
let C696AN_CENTER_SIGNS_OF_ROW = prove
 (mk_forall(`j:num`, mk_imp(`j < 577 /\ MEM (EL j COVER_IDS) EXPECTED_IDS /\ EL j COVER_IDS = 696`,
    list_mk_forall(C696AN_VARS,
      mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL j ROWS)`,
             rand (snd (strip_forall (concl C696SSP_CENTER_SIGNS))))))),
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP C696SSP_ROW_FAMILY) THEN
  ACCEPT_TAC C696AN_CENTER_SIGNS);;
