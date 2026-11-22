(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMForwardPositiveDLocal.lean            *)
(* (N12Compact.C1092MPPMForwardPositiveD).  Complete positive-recipient      *)
(* two-central theorem of C1092-POSITIVE-D-TRANSFER section 1.  Square C is  *)
(* c s u v a, its successor J is cJ sJ uJ vJ aJ; Predecessor is              *)
(* c1092fpdf_predecessor; predecessor_faces / recipient_u /                  *)
(* recipient_negative_v are C1092FPDF_* / C1092FPDS_*.  All eight separating *)
(* alternatives of ABT_FOUR_AXES are closed by linear arithmetic.  Tag       *)
(* C1092FPDL_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMForwardPositiveDSupport.ml";;

(* Lean: previous_origin_excluded *)
let C1092FPDL_PREVIOUS_ORIGIN_EXCLUDED = prove
 (`forall c s u v a cJ sJ uJ vJ aJ.
     c * c + s * s = &1 /\ &0 < a /\ cJ * cJ + sJ * sJ = &1 /\ &0 < aJ /\
     &1 < a /\ a = aJ /\ &0 < c /\ &0 <= s /\ s <= c /\ &0 < cJ /\ &0 <= sJ /\
     c1092fpdf_predecessor c s u v a /\
     linside cJ sJ uJ vJ aJ (&47 / &20) (&33 / &20) /\
     linside cJ sJ uJ vJ aJ (&2) (&87 / &50) /\
     ldisj c s u v a cJ sJ uJ vJ aJ
     ==> ~linside cJ sJ uJ vJ aJ (&2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aJ`)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092FPDF_PREDECESSOR_FACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `f:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ASSUME `c1092fpd_coefficients c s f`) THEN
  REWRITE_TAC[c1092fpd_coefficients] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092fpdf_predecessor c s u v a`) THEN
  REWRITE_TAC[c1092fpdf_predecessor] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `cJ:real`; `sJ:real`; `f:real`]
    C1092FPDS_RECIPIENT_U) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `cJ:real`; `sJ:real`; `f:real`]
    C1092FPDS_RECIPIENT_NEGATIVE_V) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[REAL_NEG_NEG]
    (SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--sJ:real`; `cJ:real`]
      OCWPVG_UPPER_NEG)) THEN DISCH_TAC THEN
  ABT_OWN_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  ABT_ALL_SB_TAC
   [[`c:real`; `s:real`; `u:real`; `v:real`; `a:real`], (`&33 / &20`, `&33 / &20`);
    [`cJ:real`; `sJ:real`; `uJ:real`; `vJ:real`; `a:real`], (`&47 / &20`, `&33 / &20`);
    [`cJ:real`; `sJ:real`; `uJ:real`; `vJ:real`; `a:real`], (`&2`, `&1`);
    [`cJ:real`; `sJ:real`; `uJ:real`; `vJ:real`; `a:real`], (`&2`, `&87 / &50`)]
   [`c:real`, `s:real`; `--s:real`, `c:real`; `cJ:real`, `sJ:real`; `--sJ:real`, `cJ:real`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cJ:real`; `sJ:real`; `uJ:real`; `vJ:real`; `a:real`] ABT_FOUR_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ABT_ARITH_TAC);;
