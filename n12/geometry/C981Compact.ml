(* ========================================================================= *)
(* Phase 2: Compact/Cases/C981Compact.lean (namespace                        *)
(* N12Compact.C981Compact).  Original C981 classification and symmetry      *)
(* assembly: ExcludesCase 981 (excl_case 981) from the domain coverage       *)
(* (CaseVectors: C981CV_OWNERSHIP_MEM_COVERED, diagonal reflection           *)
(* (c1,c2,a,b,l) -> (c2,c1,b,a,l)) and the 117 representative exclusions     *)
(* of C981Registry.  Case981.Obligations is c981c_obligations (C981.ml).     *)
(* Whole-case closer: C981CMP_EXCLUDED_ROW (retained row 512, id 981).       *)
(* Tag C981CMP_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/C981Registry.ml";;
needs "n12/geometry/CaseVectors.ml";;
needs "n12/geometry/C981.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: excludes_case *)
let C981CMP_EXCLUDES_CASE = prove
 (`c981reg_pending ==> excl_case 981`,
  DISCH_TAC THEN MATCH_MP_TAC C981CV_EXCLUDED_OF_REPRESENTATIVE_PROOFS THEN
  REWRITE_TAC[MEM_EXISTS_EL; CONJUNCT1 C981VD_REPRESENTATIVE_VECTORS_LENGTH] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (UNDISCH C981REG_ALL_REPRESENTATIVES) THEN ASM_REWRITE_TAC[]);;

(* Lean: catalogue_coverage *)
let C981CMP_CATALOGUE_COVERAGE = prove
 (`c981c_catalogue_coverage`,
  let pk = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let rep_idx_tac =
    UNDISCH_TAC `MEM (v:(num->bool)list) c981vd_representative_vectors` THEN
    REWRITE_TAC[MEM_EXISTS_EL; CONJUNCT1 C981VD_REPRESENTATIVE_VECTORS_LENGTH] THEN
    MESON_TAC[] in
  REWRITE_TAC[c981c_catalogue_coverage] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL pk C981CV_OWNERSHIP_MEM_COVERED) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[C981TD_MEM_COVERED] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(num->bool)list` (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THENL
   [MAP_EVERY EXISTS_TAC pk THEN ASM_REWRITE_TAC[] THEN rep_idx_tac;
    MAP_EVERY EXISTS_TAC [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`] THEN
    MP_TAC(SPECL pk C981CR_DIAGONAL_PACKING_FAMILY) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL pk C981CV_DIAGONAL_OWNERSHIPVECTOR) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP C981CV_REPRESENTATIVE_TRANSPOSE_INVOLUTION) THEN
    ASM_REWRITE_TAC[] THEN rep_idx_tac]);;

(* Lean: complete_obligations *)
let C981CMP_COMPLETE_OBLIGATIONS = prove
 (`c981c_obligations`,
  REWRITE_TAC[c981c_obligations; c981c_representative_excluded; C981CMP_CATALOGUE_COVERAGE] THEN
  SIMP_TAC[C981REG_ALL_REPRESENTATIVES_COMPLETE]);;

(* Lean: excludes_case_complete *)
let C981CMP_EXCLUDES_CASE_COMPLETE = MP C981C_EXCLUDED_OF_OBLIGATIONS C981CMP_COMPLETE_OBLIGATIONS;;

(* Lean: family_impossible *)
let C981CMP_FAMILY_IMPOSSIBLE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc981ri_family ==> false`,
  MP_TAC C981CMP_EXCLUDES_CASE_COMPLETE THEN REWRITE_TAC[CCC981RI_EXCLUDES_CASE_IFF; excl_fam]);;

(* the assembly form (retained row 512 has id 981) *)
let C981CMP_EXCLUDED_ROW = ri_excluded_row 512 C981CMP_EXCLUDES_CASE_COMPLETE;;
