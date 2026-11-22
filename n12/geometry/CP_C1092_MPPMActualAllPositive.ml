(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualAllPositive.lean               *)
(* (N12Compact.C1092MPPMActualPositiveCycle; Lean header: "Source only").    *)
(* Unconditional scalar assembly and the actual all-positive ordinary MPPM   *)
(* ending.  ScalarProof / PositiveFrames / AllCrosspoints:                   *)
(* c1092mapc_scalarProof / c1092mapc_positiveFrames /                        *)
(* c1092mapc_allCrosspoints (CP_C1092_MPPMActualPositiveCycle.ml).           *)
(* Central.g00_lower / Central.aligned_C: C1092MCAL_G00_LOWER /              *)
(* C1092MCCA_ALIGNED_C; G01/G10/G11_nonnegative: C1092G01_/C1092G10F_/       *)
(* C1092G11_ ..._NONNEGATIVE.  Tag C1092MAAP_.                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualPositiveCycle.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointCentralAll.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointCentralAligned.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG01.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG11.ml";;

(* Lean: scalar_proof *)
let C1092MAAP_SCALAR_PROOF = prove
 (`c1092mapc_scalarProof`,
  REWRITE_TAC[c1092mapc_scalarProof; c1092sptg_modesNonnegative] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MCAL_G00_LOWER) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC C1092G01_G01_NONNEGATIVE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092G10F_G10_NONNEGATIVE THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `d:real`; `t:real`] C1092MCCA_ALIGNED_C) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC C1092G11_G11_NONNEGATIVE THEN ASM_REWRITE_TAC[]]);;

(* Lean: all_crosspoints *)
let C1092MAAP_ALL_CROSSPOINTS =
  REWRITE_RULE[C1092MAAP_SCALAR_PROOF] C1092MAPC_ALL_CROSSPOINTS_OF_SCALARS;;

(* Lean: impossible *)
let C1092MAAP_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ c1092mapc_positiveFrames %s ==> F"
    C1092MAPC_P C1092MPAPO_HYPS C1092MAPC_P),
  MESON_TAC[C1092MAPC_IMPOSSIBLE_OF_SCALARS; C1092MAAP_SCALAR_PROOF]);;
