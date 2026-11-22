(* ========================================================================= *)
(* Port of Completion/Cases/C981/CaseVectors.lean (S12Completion.C981).      *)
(* Lean DomainCasesCheck domains cases (enumerateAssignments of the domains' *)
(* allowed lists, from ∅, all MEM cases) is stated with c981odm_assignments  *)
(* (= pc_enum [allowed lists of C981ODM_DOMAINS] {}, OwnershipDomains.ml);   *)
(* domain_cases_sound for these domains is C981ODM_OWNERSHIP_MEM_ASSIGNMENTS. *)
(* ownershipVector p = c981ow_vector c1 c2 a b l, diagonal.pullPacking p =   *)
(* (c2, c1, b, a, l) (DiagonalAuxiliary.ml), transposeVector /               *)
(* transposeAuxiliary / coveredVectors = c981td_tr_vector / c981td_tr_aux /   *)
(* c981td_covered_vectors, ExcludesVector = c981vd_excludes_vector,          *)
(* ExcludesCase 981 = excl_case 981 (excludes_case_iff:                      *)
(* CCC981RI_EXCLUDES_CASE).  Tag C981CV_.                                    *)
(* ========================================================================= *)

needs "n12/geometry/CC_C981_Coverage_Final.ml";;
needs "n12/geometry/TransposeData.ml";;
needs "n12/geometry/DiagonalAuxiliary.ml";;
needs "n12/geometry/OwnershipDomains.ml";;
needs "n12/geometry/VectorData.ml";;

let C981CV_ALL2_LENGTH = prove
 (`forall (R:A->B->bool) l m. ALL2 R l m ==> LENGTH l = LENGTH m`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; LENGTH; NOT_SUC; SUC_INJ] THEN ASM_MESON_TAC[]);;

let C981CV_LITERAL_CHOICES_LENGTH =
  (REWRITE_CONV[c981cov_literal_choices; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c981cov_literal_choices`;;

(* c981odm_assignments = pc_enum c981cov_literal_choices {} *)
let C981CV_ASSIGNMENTS =
  CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (REWR_CONV C981AD_ALLOWED_EXACT)))) c981odm_assignments;;

(* Lean: complete_vector_coverage *)
let C981CV_COMPLETE_VECTOR_COVERAGE = prove
 (`forall a. MEM a c981odm_assignments ==> MEM a c981td_covered_vectors`,
  REWRITE_TAC[C981CV_ASSIGNMENTS; C981CF_COVERED_EXACT] THEN
  X_GEN_TAC `a:(num->bool)list` THEN DISCH_THEN(MP_TAC o MATCH_MP PC_ENUMERATE_VALID) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[C981AD_REORDERED_EXACT] o MATCH_MP CRO_REORDER_ALLOWED) THEN
  MP_TAC(SPECL [`[]:(num->bool)list`; `cro_reorder (a:(num->bool)list)`]
    (MATCH_MP PC_CHAIN_SOUND C981CF_COMPLETE_CHAIN)) THEN
  ASM_SIMP_TAC[CRO_REORDER_PAIRWISE; MEM; APPEND] THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (a:(num->bool)list) = 12` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP C981CV_ALL2_LENGTH o check (fun th ->
      can (find_term ((=) `c981cov_literal_choices`)) (concl th))) THEN
    REWRITE_TAC[C981CV_LITERAL_CHOICES_LENGTH];
    ALL_TAC] THEN
  MP_TAC(SPEC `cro_reorder (a:(num->bool)list)` C981CF_FINAL_COVERED) THEN
  ASM_SIMP_TAC[CRO_UNORDER_REORDER]);;

(* Lean: ownership_mem_covered *)
let C981CV_OWNERSHIP_MEM_COVERED = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family
     ==> MEM (c981ow_vector c1 c2 a b l) c981td_covered_vectors`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C981CV_COMPLETE_VECTOR_COVERAGE THEN
  MATCH_MP_TAC C981ODM_OWNERSHIP_MEM_ASSIGNMENTS THEN ASM_REWRITE_TAC[]);;

(* Lean: diagonal_auxiliary_actual *)
let C981CV_DIAGONAL_AUXILIARY_ACTUAL = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family /\ i < 12
     ==> ooaux c2 c1 b a l (EL i c981ow_masks) =
         c981td_tr_aux (ooaux c1 c2 a b l (EL (EL i c981da_owner_tr) c981ow_masks))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C981DA_DIAGONAL_AUXILIARY_EQ THEN
  EXISTS_TAC `ooaux c1 c2 a b l (EL (EL i c981da_owner_tr) c981ow_masks)` THEN
  ASM_SIMP_TAC[C981TD_TRANSPOSEAUXILIARY_SUBSET; C981TD_TRANSPOSEAUXILIARY_MEM]);;

(* Lean: diagonal_ownershipVector *)
let C981CV_DIAGONAL_OWNERSHIPVECTOR = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family
     ==> c981ow_vector c2 c1 b a l = c981td_tr_vector (c981ow_vector c1 c2 a b l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; C981TD_TR_VECTOR_LENGTH] THEN CONJ_TAC THENL
   [REWRITE_TAC[c981ow_vector; LENGTH_MAP; C981OW_LENGTH]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[C981OW_VECTOR_EL; C981TD_TR_VECTOR_EL; C981CV_DIAGONAL_AUXILIARY_ACTUAL] THEN
  AP_TERM_TAC THEN REWRITE_TAC[c981td_getd] THEN
  SUBGOAL_THEN `EL i c981da_owner_tr < 12` ASSUME_TAC THENL
   [ASM_SIMP_TAC[C981DA_OWNER_TR_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[c981ow_vector; LENGTH_MAP; C981OW_LENGTH] THEN
  ASM_SIMP_TAC[GSYM c981ow_vector; C981OW_VECTOR_EL]);;

(* Lean: representative_transpose_involution *)
let C981CV_REPRESENTATIVE_TRANSPOSE_INVOLUTION =
  let p = rhs (concl c981vd_representative_vectors) in
  let q = `\v:(num->bool)list. c981td_tr_vector (c981td_tr_vector v) = v` in
  let one v =
    let t1 = c981cf_trv_conv (mk_comb(`c981td_tr_vector`, v)) in
    let t2 = c981cf_trv_conv (mk_comb(`c981td_tr_vector`, rhs (concl t1))) in
    let e = TRANS (TRANS (AP_TERM `c981td_tr_vector` t1) t2) (c981cf_teq (rhs (concl t2)) v) in
    EQ_MP (SYM (BETA_CONV (mk_comb(q, v)))) e in
  let allc = `ALL:((num->bool)list->bool)->((num->bool)list)list->bool` in
  let rec go l =
    let tm = mk_comb(mk_comb(allc, q), l) in
    if is_cons l then
      let h, t = dest_cons l in
      EQ_MP (SYM (REWR_CONV (CONJUNCT2 ALL) tm)) (CONJ (one h) (go t))
    else EQT_ELIM (REWR_CONV (CONJUNCT1 ALL) tm) in
  let th = CONV_RULE (DEPTH_CONV BETA_CONV) (EQ_MP (SYM (ISPECL [q; p] ALL_MEM)) (go p)) in
  let x = `v:(num->bool)list` in
  let mx = mk_comb(mk_comb(`MEM:(num->bool)list->((num->bool)list)list->bool`, x),
                   `c981vd_representative_vectors`) in
  let th' = MP (SPEC x th) (EQ_MP (AP_TERM (rator mx) c981vd_representative_vectors) (ASSUME mx)) in
  GEN x (DISCH mx th');;

(* Lean: excluded_of_representative_proofs *)
let C981CV_EXCLUDED_OF_REPRESENTATIVE_PROOFS = prove
 (`(forall v. MEM v c981vd_representative_vectors ==> c981vd_excludes_vector v) ==> excl_case 981`,
  DISCH_TAC THEN MATCH_MP_TAC CCC981RI_EXCLUDES_CASE THEN REWRITE_TAC[excl_fam] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C981CV_OWNERSHIP_MEM_COVERED) THEN
  REWRITE_TAC[C981TD_MEM_COVERED] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(num->bool)list` (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (ASSUME
      `forall v. MEM v c981vd_representative_vectors ==> c981vd_excludes_vector v`)) THEN
    REWRITE_TAC[c981vd_excludes_vector] THEN
    DISCH_THEN(MP_TAC o SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP (ASSUME
      `forall v. MEM v c981vd_representative_vectors ==> c981vd_excludes_vector v`)) THEN
    REWRITE_TAC[c981vd_excludes_vector] THEN
    DISCH_THEN(MP_TAC o SPECL [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`]) THEN
    ASM_SIMP_TAC[C981CR_DIAGONAL_PACKING_FAMILY; C981CV_DIAGONAL_OWNERSHIPVECTOR;
                 C981CV_REPRESENTATIVE_TRANSPOSE_INVOLUTION]]);;
