(* ========================================================================= *)
(* Port of source/S12/ContinuousCertificate.lean (Jatloe, N12-jatloe).       *)
(* RelaxationLink <source, target, proofs> -> RLink source target proofs.    *)
(* CertifiedPosePruning <source, neighbors, pruning, targets, links, covered>*)
(*   -> CertPruning source neighbors pruning targets links, with cpp_ok      *)
(*      (pp_ok of pruning, rl_check of every link, and `covered`).           *)
(* Lists of subtypes {w : RelaxationLink // w.Check} / of CertifiedPose-     *)
(* Prunings become plain lists with an explicit "every element checked"      *)
(* hypothesis.                                                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/DomainRelaxation.ml";;

(* Lean: structure RelaxationLink *)
let rlink_INDUCT,rlink_RECURSION =
  define_type "rlink = RLink pose_leaf pose_leaf (((real#lincon)list)list)";;
let rl_source = define `rl_source (RLink s t p) = s`;;
let rl_target = define `rl_target (RLink s t p) = t`;;
let rl_proofs = define `rl_proofs (RLink s t p) = p`;;

(* Lean: RelaxationLink.Check *)
let rl_check = new_definition
 `rl_check w <=>
    ae_reference (pl_angle (rl_source w)) (&1) = ae_reference (pl_angle (rl_target w)) (&1) /\
    forall r. MEM r (pl_inputs (rl_target w)) ==>
      exists terms. MEM terms (rl_proofs w) /\ limp_check 2 (pl_inputs (rl_source w)) r terms`;;

(* Lean: RelaxationLink.sound *)
let CC_RELAXATIONLINK_SOUND = prove
 (`forall w c s u v a. rl_check w /\ pose_realizes (rl_source w) c s u v a
     ==> pose_realizes (rl_target w) c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC DR_LEAFRELAXATION_SOUND THEN
  MAP_EVERY EXISTS_TAC [`rl_source w`; `rl_proofs w`] THEN
  ASM_REWRITE_TAC[lr_ok] THEN ASM_MESON_TAC[rl_check]);;

(* Lean: RelaxationCoverCheck *)
let relaxation_cover_check = new_definition
 `relaxation_cover_check sources targets links <=>
    forall s. MEM s sources ==> exists w. MEM w links /\ rl_source w = s /\ MEM (rl_target w) targets`;;

(* Lean: relaxation_cover_sound *)
let CC_RELAXATION_COVER_SOUND = prove
 (`forall sources targets links c s u v a.
     (forall w. MEM w links ==> rl_check w) /\
     relaxation_cover_check sources targets links /\ pose_covered sources c s u v a
     ==> pose_covered targets c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relaxation_cover_check; pose_covered] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:pose_leaf`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:rlink` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rl_target w` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CC_RELAXATIONLINK_SOUND THEN ASM_MESON_TAC[]);;

(* Lean: structure CertifiedPosePruning *)
let cert_pruning_INDUCT,cert_pruning_RECURSION = define_type
 "cert_pruning = CertPruning pose_leaf (pose_leaf list) pose_pruning (pose_leaf list) (rlink list)";;
let cp_source = define `cp_source (CertPruning s n p t l) = s`;;
let cp_neighbors = define `cp_neighbors (CertPruning s n p t l) = n`;;
let cp_pruning = define `cp_pruning (CertPruning s n p t l) = p`;;
let cp_targets = define `cp_targets (CertPruning s n p t l) = t`;;
let cp_links = define `cp_links (CertPruning s n p t l) = l`;;

(* the proof fields of CertifiedPosePruning (pruning.checked, the link
   subtypes and `covered`) *)
let cpp_ok = new_definition
 `cpp_ok w <=>
    pp_ok (cp_source w) (cp_neighbors w) (cp_pruning w) /\
    (forall l. MEM l (cp_links w) ==> rl_check l) /\
    relaxation_cover_check (pp_result (cp_source w) (cp_pruning w)) (cp_targets w) (cp_links w)`;;

(* Lean: CertifiedPosePruning.sound *)
let CC_CERTIFIEDPOSEPRUNING_SOUND = prove
 (`forall w cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     cpp_ok w /\ pose_realizes (cp_source w) cq sq uq vq aq /\
     pose_covered (cp_neighbors w) cr sr ur vr ar /\ ldisj cq sq uq vq aq cr sr ur vr ar
     ==> pose_covered (cp_targets w) cq sq uq vq aq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpp_ok] THEN STRIP_TAC THEN
  MATCH_MP_TAC CC_RELAXATION_COVER_SOUND THEN
  MAP_EVERY EXISTS_TAC [`pp_result (cp_source w) (cp_pruning w)`; `cp_links w`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CPR_POSEPRUNING_SOUND THEN
  MAP_EVERY EXISTS_TAC [`cp_neighbors w`; `cr:real`; `sr:real`; `ur:real`; `vr:real`;
                        `ar:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: PruningCoverCheck *)
let pruning_cover_check = new_definition
 `pruning_cover_check sources neighbors targets plans <=>
    forall s. MEM s sources ==>
      exists w. MEM w plans /\ cp_source w = s /\ cp_neighbors w = neighbors /\
          forall t. MEM t (cp_targets w) ==> MEM t targets`;;

(* Lean: pruning_cover_sound *)
let CC_PRUNING_COVER_SOUND = prove
 (`forall sources neighbors targets plans cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     (forall w. MEM w plans ==> cpp_ok w) /\
     pruning_cover_check sources neighbors targets plans /\
     pose_covered sources cq sq uq vq aq /\ pose_covered neighbors cr sr ur vr ar /\
     ldisj cq sq uq vq aq cr sr ur vr ar
     ==> pose_covered targets cq sq uq vq aq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pruning_cover_check] THEN STRIP_TAC THEN
  UNDISCH_TAC `pose_covered sources cq sq uq vq aq` THEN
  GEN_REWRITE_TAC LAND_CONV [pose_covered] THEN
  DISCH_THEN(X_CHOOSE_THEN `src:pose_leaf` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `src:pose_leaf` o check (fun th ->
    can (find_term ((=) `cp_targets`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:cert_pruning` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`w:cert_pruning`; `cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
    CC_CERTIFIEDPOSEPRUNING_SOUND) THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[pose_covered] THEN ASM_MESON_TAC[]);;
