(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/SectorEndings.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C1089.SectorEndings).  Two    *)
(* complete C1089 sector endings from their literal original owners.         *)
(* Conventions of WallCore.ml / SectorEntrances.ml (owners p i = owner at    *)
(* the literal mask EL i c1089sc_masks).  ContinuousActual.southeast /       *)
(* northwest = C1089CA_SOUTHEAST / C1089CA_NORTHWEST at q = c1089od_owners;  *)
(* OutwardPoint.point_original = CCOP_POINT_ORIGINAL, InwardPoint.           *)
(* point_original = CCIP_POINT_ORIGINAL, ShortDuplicatePoints.outward_of_bar *)
(* / inward_original = OCSDP_OUTWARD_OF_BAR / OCSDP_INWARD_ORIGINAL.         *)
(* (Lean header: "Source only".)  Tag C1089SN_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_SectorEntrances.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousActual.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_OtherCases_ShortDuplicatePoints.ml";;

let C1089SN_V = C1089WC_V;;
let c1089sn_own = c1089wc_own;;
let c1089sn_le = c1089se_le;;
let c1089sn_ldisj m n =
  REWRITE_RULE[ldisj] (MP (SPECL C1089SN_V (oo_apart `c1089sc_family` m n)) (c1089wc_hh ()));;

(* apply a ContinuousActual lemma to the packing's owners c1089od_owners *)
let C1089SN_CONTINUOUS_TAC th =
  MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)
           (REWRITE_RULE[c1089od_frame] (MP (SPEC_ALL C1089OD_FRAME) (c1089wc_hh ())))) THEN
  DISCH_THEN(fun fr ->
    let frs = CONJUNCTS fr in
    MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) (SPECL c1089od_owners th)) THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST (map ACCEPT_TAC frs);
             REWRITE_TAC[] THEN NO_TAC;
             GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OO_UNIT THEN FIRST_ASSUM ACCEPT_TAC;
             ALL_TAC] THEN
      CONV_TAC C1089OD_EL_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC C1089OD_EL_CONV THEN STRIP_TAC]);;

(* Lean: opposed_impossible *)
let C1089SN_OPPOSED_IMPOSSIBLE = prove
 (c1089wc_stmt []
    [c1089sn_le `&2` (c1089wc_lcy 4096); c1089sn_le (c1089wc_lcy 16384) `&2`;
     c1089sn_le (c1089wc_lcx 32768) `&2`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [] THEN
  ASSUME_TAC (MP (SPEC_ALL (c1089od_seed 1 (`&1543 / &500`, `&1`))) (c1089wc_hh ())) THEN
  ASSUME_TAC (MP (SPEC_ALL (c1089od_seed 3 (`&1`, `&1543 / &500`))) (c1089wc_hh ())) THEN
  C1089WC_USE_TAC C1089SN_V C1089WC_SOUTHEAST_INWARD THEN
  C1089WC_USE_TAC C1089SN_V C1089WC_NORTHWEST_INWARD THEN
  C1089SE_AT_TAC C1089WC_SINGLETON_BAR `&8 / &5` THEN
  C1089SE_AT_TAC C1089WC_RIGHT_LOW `&87 / &50` THEN
  C1089SE_AT_TAC C1089WC_TOP_LOW `&87 / &50` THEN
  C1089WC_USE_TAC C1089SN_V C1089DD_BOTTOM_FAR THEN
  C1089SE_HAVE_TAC (c1089sn_own 256 `&1` `&87 / &50`)
    (C1089SE_COVER_TAC C1089AC_SOUTHWEST_F_COVER) THEN
  C1089SE_HAVE_TAC (c1089sn_own 256 `&1` `&8 / &5`)
    (C1089SE_COVER_TAC C1089AC_SOUTHWEST_G_COVER) THEN
  C1089SE_HAVE_TAC (c1089sn_own 4096 `&1` `&12 / &5`)
    (C1089SE_COVER_TAC C1089AC_LEFT_G_COVER) THEN
  C1089SN_CONTINUOUS_TAC C1089CA_SOUTHEAST THEN
  C1089SN_CONTINUOUS_TAC C1089CA_NORTHWEST THEN
  C1089WC_CLASH_TAC);;

(* Lean: southeast_duplicates *)
let C1089SN_SOUTHEAST_DUPLICATES = prove
 (c1089wc_stmt []
    [c1089sn_own 512 `&3` `&87 / &50`; c1089sn_own 512 `&3` `&8 / &5`;
     mk_neg (c1089sn_own 512 `&113 / &50` `&2`)]
    (mk_conj(c1089sn_own 512 `&123 / &50` `&201 / &100`, c1089sn_own 512 `&5 / &2` `&51 / &25`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [512] THEN
  ASSUME_TAC (MP (SPEC_ALL (c1089od_seed 1 (`&1543 / &500`, `&1`))) (c1089wc_hh ())) THEN
  C1089WC_USE_TAC C1089SN_V C1089WC_BOTTOM THEN
  SUBGOAL_THEN (mk_forall(`z:real`, mk_imp(`&113 / &50 <= z`, mk_imp(`z <= &14 / &5`,
                  mk_neg (c1089sn_own 512 `z:real` `&1`))))) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC (SPECL [`z:real`; `&1`] (c1089sn_ldisj 512 8192)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  let tup = c1089wc_py (c1089wc_tuple 512) in
  CONJ_TAC THENL
   [C1089WC_APPLY_TAC (c1089wc_inst CCOP_POINT_ORIGINAL tup);
    C1089WC_APPLY_TAC (c1089wc_inst OCSDP_OUTWARD_OF_BAR tup)]);;

(* Lean: northeast_inward_impossible *)
let C1089SN_NORTHEAST_INWARD_IMPOSSIBLE = prove
 (c1089wc_stmt []
    [c1089sn_le (c1089wc_lcy 4096) `&2`; c1089sn_le `&2` (c1089wc_lcy 16384);
     c1089sn_le `&2` (c1089wc_lcx 32768)] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [1024] THEN
  C1089WC_USE_TAC C1089SN_V C1089WC_SOUTHWEST_INWARD THEN
  C1089WC_USE_TAC C1089SN_V C1089WC_NORTHEAST_INWARD THEN
  C1089WC_USE_TAC C1089SN_V C1089DD_BOTTOM_FAR THEN
  C1089WC_USE_TAC C1089SN_V C1089WC_BOTTOM THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MP_TAC (SPEC `&113 / &50` th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
         REWRITE_TAC[] THEN DISCH_TAC
    else NO_TAC) THEN
  C1089SE_AT_TAC C1089WC_TOP_HIGH `&113 / &50` THEN
  C1089SE_HAVE_TAC (c1089sn_own 512 `&3` `&87 / &50`)
    (C1089SE_COVER_TAC C1089AC_SOUTHEAST_F_COVER) THEN
  C1089SE_HAVE_TAC (c1089sn_own 512 `&3` `&8 / &5`)
    (C1089SE_COVER_TAC C1089AC_SOUTHEAST_G_COVER) THEN
  C1089SE_HAVE_TAC (mk_neg (c1089sn_own 512 `&113 / &50` `&2`)) (DISCH_TAC THEN C1089WC_CLASH_TAC) THEN
  C1089WC_USE_TAC C1089SN_V C1089SN_SOUTHEAST_DUPLICATES THEN
  ASM_CASES_TAC (c1089sn_own 1024 `&12 / &5` `&3`) THENL
   [C1089SE_HAVE_TAC (c1089sn_own 1024 `&5 / &2` `&51 / &25`)
      (C1089WC_APPLY_TAC (SPECL (c1089wc_tuple 1024) OCSDP_INWARD_ORIGINAL)) THEN
    C1089WC_CLASH_TAC;
    C1089SE_HAVE_TAC (c1089sn_own 1024 `&123 / &50` `&201 / &100`)
      (C1089WC_APPLY_TAC (c1089wc_inst CCIP_POINT_ORIGINAL (c1089wc_py (c1089wc_tuple 1024)))) THEN
    C1089WC_CLASH_TAC]);;
