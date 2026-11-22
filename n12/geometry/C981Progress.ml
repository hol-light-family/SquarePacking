(* ========================================================================= *)
(* Phase 2: Compact/Assembly/C981Progress.lean (namespace                    *)
(* N12Compact.C981Progress).  Forty-two whole original representative        *)
(* exclusions of case 981 collected from the bridge / completion files.      *)
(* ExcludesVector (representativeVectors[i]!) is                             *)
(* c981vd_excludes_vector (EL i c981vd_representative_vectors); Lean list    *)
(* ++ is APPEND; List.Nodup is PAIRWISE (\x y. ~(x = y)).  Tag C981P_.       *)
(* ========================================================================= *)

needs "n12/geometry/C981TwoTipRows.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;
needs "n12/geometry/C981InwardWallRows.ml";;
needs "n12/geometry/CP_C981_OutwardRows.ml";;
needs "n12/geometry/CP_C981_ShortRows_CoreRows.ml";;
needs "n12/geometry/CP_C981_ShortWallRows.ml";;
needs "n12/geometry/CP_C981_ShortWall71.ml";;
needs "n12/geometry/CP_C981_Common107.ml";;
needs "n12/geometry/CP_C981_CommonRows.ml";;
needs "n12/geometry/CP_C981_LastRows.ml";;
needs "n12/geometry/CP_C981_Last104.ml";;
needs "n12/geometry/CP_C981_NewSimpleShortRows.ml";;
needs "n12/geometry/CP_C981_OutwardTranspose.ml";;
needs "n12/geometry/CP_C981_ShortCentralRows.ml";;

(* Lean: previousIds *)
let c981p_previous_ids = new_definition
 `c981p_previous_ids =
    APPEND (APPEND (APPEND c981ttr_covered_ids [27]) c981iwr_covered_ids) c981or_coveredIds`;;

(* Lean: earlierIds *)
let c981p_earlier_ids = new_definition
 `c981p_earlier_ids =
    APPEND (APPEND (APPEND c981p_previous_ids [101]) c981swr_covered_ids) [71]`;;

(* Lean: completionIds *)
let c981p_completion_ids = new_definition
 `c981p_completion_ids =
    APPEND (APPEND (APPEND (APPEND c981cr_covered_ids [107; 29; 104]) c981nssr_covered_ids) [55])
      c981scr_coveredIds`;;

(* Lean: newIds *)
let c981p_new_ids = new_definition
 `c981p_new_ids = APPEND c981p_earlier_ids c981p_completion_ids`;;

let C981P_UNFOLD =
  [c981p_new_ids; c981p_earlier_ids; c981p_previous_ids; c981p_completion_ids;
   c981ttr_covered_ids; c981ttr_north_east_ids; c981ttr_north_west_ids; c981ttr_south_east_ids;
   c981iwr_covered_ids; c981or_coveredIds; c981swr_covered_ids; c981cr_covered_ids;
   c981nssr_covered_ids; c981scr_coveredIds; APPEND];;

(* Lean: completionIds_exact *)
let C981P_COMPLETIONIDS_EXACT = prove
 (`c981p_completion_ids =
     [2;28;30;34;37;41;43;69;103;107;29;104;54;56;58;73;109;55;93;98]`,
  REWRITE_TAC C981P_UNFOLD);;

(* Lean: completionIds_count *)
let C981P_COMPLETIONIDS_COUNT = prove
 (`LENGTH c981p_completion_ids = 20`,
  REWRITE_TAC[C981P_COMPLETIONIDS_EXACT; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: newIds_exact *)
let C981P_NEWIDS_EXACT = prove
 (`c981p_new_ids =
     [25;31;40;70;32;33;38;57;99;94;95;27;36;106;24;26;39;101;59;105;108;71;
      2;28;30;34;37;41;43;69;103;107;29;104;54;56;58;73;109;55;93;98]`,
  REWRITE_TAC C981P_UNFOLD);;

(* Lean: newIds_count *)
let C981P_NEWIDS_COUNT = prove
 (`LENGTH c981p_new_ids = 42`,
  REWRITE_TAC[C981P_NEWIDS_EXACT; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: newIds_distinct *)
let C981P_NEWIDS_DISTINCT = prove
 (`PAIRWISE (\x y. ~(x = y)) c981p_new_ids`,
  REWRITE_TAC[C981P_NEWIDS_EXACT; PAIRWISE; ALL] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: newIds_bound *)
let C981P_NEWIDS_BOUND = prove
 (`forall i. MEM i c981p_new_ids ==> i < 117`,
  REWRITE_TAC[C981P_NEWIDS_EXACT; MEM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* goal !i. MEM i L ==> excludes (EL i reps), L unfolded by defs into APPENDs of
   covered-id constants and literal lists; singles: per-row theorems,
   covered: theorems !i. MEM i C ==> ... *)
let C981P_COLLECT_TAC defs singles covered =
  GEN_TAC THEN REWRITE_TAC(defs @ [MEM_APPEND; MEM]) THEN REPEAT STRIP_TAC THEN
  FIRST (map (fun th -> ASM_REWRITE_TAC[th] THEN NO_TAC) singles @
         map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC) covered);;

(* Lean: previous_excluded *)
let C981P_PREVIOUS_EXCLUDED = prove
 (`forall i. MEM i c981p_previous_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
  C981P_COLLECT_TAC [c981p_previous_ids]
    [C981BR27_REPRESENTATIVE27_EXCLUDED]
    [C981TTR_COVERED_EXCLUDED; C981IWR_COVERED_EXCLUDED; C981OR_COVERED_EXCLUDED]);;

(* Lean: earlier_excluded *)
let C981P_EARLIER_EXCLUDED = prove
 (`forall i. MEM i c981p_earlier_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
  C981P_COLLECT_TAC [c981p_earlier_ids]
    [C981SRCR_REPRESENTATIVE101_EXCLUDED; C981SW71_REPRESENTATIVE71_EXCLUDED]
    [C981P_PREVIOUS_EXCLUDED; C981SWR_COVERED_EXCLUDED]);;

(* Lean: completion_excluded *)
let C981P_COMPLETION_EXCLUDED = prove
 (`forall i. MEM i c981p_completion_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
  C981P_COLLECT_TAC [c981p_completion_ids]
    [C981C107_REPRESENTATIVE107_EXCLUDED; C981LR_REPRESENTATIVE29_EXCLUDED;
     C981L104_REPRESENTATIVE104_EXCLUDED; C981OT_REPRESENTATIVE55_EXCLUDED]
    [C981CR_COVERED_EXCLUDED; C981NSSR_COVERED_EXCLUDED; C981SCR_COVERED_EXCLUDED]);;

(* Lean: new_excluded *)
let C981P_NEW_EXCLUDED = prove
 (`forall i. MEM i c981p_new_ids ==> c981vd_excludes_vector (EL i c981vd_representative_vectors)`,
  C981P_COLLECT_TAC [c981p_new_ids] []
    [C981P_EARLIER_EXCLUDED; C981P_COMPLETION_EXCLUDED]);;
