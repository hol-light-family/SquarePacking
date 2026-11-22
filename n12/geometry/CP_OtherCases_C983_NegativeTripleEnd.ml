(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeTripleEnd.lean         *)
(* (N12Compact.Completion.OtherCases.C983.NegativeTripleEnd).  The shared   *)
(* physical three-square ending: the north and south separator dichotomies  *)
(* (OCNTNS_SEPARATORS, C983NRS_SEPARATORS) and the four face combinations   *)
(* (C983NFF / C983NMSO / C983NMR / C983NRO _IMPOSSIBLE).  Squares E, N, R   *)
(* are cE sE uE vE aE, cN sN uN vN aN, cR sR uR vR aR; apartEN is           *)
(* `ldisj E N`.  Tag C983NTE_.                                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeForeignFaces.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeMixedRight.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeMixedSouth.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeRightOwned.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeRightSeparation.ml";;
needs "n12/geometry/CP_OtherCases_NegativeTripleNorthSeparation.ml";;

(* Lean: impossible *)
let C983NTE_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     ldisj cE sE uE vE aE cN sN uN vN aN
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocrtd_input] o
    check (fun th -> can (term_match [] `ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR`)
                         (concl th))) THEN
  SUBGOAL_THEN `&1 < aN` ASSUME_TAC THENL
   [UNDISCH_TAC `ccntf_data cE sE uE vE aE (--sE)` THEN REWRITE_TAC[ccntf_data] THEN
    STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] OCNTNS_SEPARATORS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ldisj] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `--sE`] C983NRS_SEPARATORS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ldisj] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  let sq = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
            `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
            `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] in
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [MATCH_MP_TAC(SPECL sq C983NFF_IMPOSSIBLE);
    MATCH_MP_TAC(SPECL sq C983NMSO_IMPOSSIBLE);
    MATCH_MP_TAC(SPECL sq C983NMR_IMPOSSIBLE);
    MATCH_MP_TAC(SPECL sq C983NRO_IMPOSSIBLE)] THEN
  ASM_REWRITE_TAC[]);;
