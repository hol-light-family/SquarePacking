(* ========================================================================= *)
(* Port of source/S12/OrientedCoverage.lean (Jatloe, N12-jatloe).            *)
(* AngleWitness: the existential OpenSquare r is a 5-tuple c' s' u' v' a'    *)
(* together with its invariants c'*c'+s'*s' = 1 and 0 < a'.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/ContinuousCertificate.ml";;

(* Lean: PoseLeaf.AngleWitness *)
let angle_witness = new_definition
 `angle_witness leaf c s u v a <=>
    exists c' s' u' v' a' t.
      c' * c' + s' * s' = &1 /\ &0 < a' /\
      c' = normalC t /\ s' = normalS t /\
      ae_lower (pl_angle leaf) <= t /\ t <= ae_upper (pl_angle leaf) /\
      a' = a /\ lcx c' s' u' v' a' = lcx c s u v a /\ lcy c' s' u' v' a' = lcy c s u v a /\
      forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y`;;

(* Lean: PoseLeaf.OrientedRealizes *)
let oriented_realizes = new_definition
 `oriented_realizes leaf c s u v a <=>
    pose_realizes leaf c s u v a /\ angle_witness leaf c s u v a`;;

(* Lean: OrientedPoseCovered *)
let oriented_pose_covered = new_definition
 `oriented_pose_covered leaves c s u v a <=>
    exists l. MEM l leaves /\ oriented_realizes l c s u v a`;;

(* Lean: oriented_coverage_forget *)
let OCV_ORIENTED_COVERAGE_FORGET = prove
 (`forall leaves c s u v a. oriented_pose_covered leaves c s u v a
     ==> pose_covered leaves c s u v a`,
  REWRITE_TAC[oriented_pose_covered; pose_covered; oriented_realizes] THEN MESON_TAC[]);;

(* Lean: OwnerEnclosure.oriented_sound *)
let OCV_OWNERENCLOSURE_ORIENTED_SOUND = prove
 (`forall w c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     oe_check w /\ &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     (forall P. MEM P (oe_inside w) ==> linside c s u v a (FST P) (SND P)) /\
     (forall P. MEM P (oe_outside w) ==> ~linside c s u v a (FST P) (SND P))
     ==> oriented_pose_covered (oe_leaves w) c s u v a`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP OE_SOUND_WITNESS) THEN
  REWRITE_TAC[oriented_pose_covered; oriented_realizes; angle_witness]);;

(* Lean: RelaxationLink.AngleCheck *)
let rl_angle_check = new_definition
 `rl_angle_check w <=>
    ae_lower (pl_angle (rl_target w)) <= ae_lower (pl_angle (rl_source w)) /\
    ae_upper (pl_angle (rl_source w)) <= ae_upper (pl_angle (rl_target w))`;;

(* Lean: RelaxationLink.oriented_sound *)
let OCV_RELAXATIONLINK_ORIENTED_SOUND = prove
 (`forall w c s u v a. rl_check w /\ rl_angle_check w /\ oriented_realizes (rl_source w) c s u v a
     ==> oriented_realizes (rl_target w) c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oriented_realizes; rl_angle_check] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CC_RELAXATIONLINK_SOUND]; ALL_TAC] THEN
  UNDISCH_TAC `angle_witness (rl_source w) c s u v a` THEN REWRITE_TAC[angle_witness] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: oriented_relaxation_cover_sound *)
let OCV_ORIENTED_RELAXATION_COVER_SOUND = prove
 (`forall sources targets links c s u v a.
     (forall w. MEM w links ==> rl_check w) /\
     relaxation_cover_check sources targets links /\
     (forall w. MEM w links ==> rl_angle_check w) /\
     oriented_pose_covered sources c s u v a
     ==> oriented_pose_covered targets c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relaxation_cover_check; oriented_pose_covered] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `l:pose_leaf` o check (fun th ->
    can (find_term ((=) `rl_source`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:rlink` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rl_target w` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OCV_RELAXATIONLINK_ORIENTED_SOUND THEN ASM_MESON_TAC[]);;

(* Lean: PosePruning.oriented_sound *)
let OCV_POSEPRUNING_ORIENTED_SOUND = prove
 (`forall source neighbors w cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     pp_ok source neighbors w /\ oriented_realizes source cq sq uq vq aq /\
     pose_covered neighbors cr sr ur vr ar /\ ldisj cq sq uq vq aq cr sr ur vr ar
     ==> oriented_pose_covered (pp_result source w) cq sq uq vq aq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oriented_realizes] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`source:pose_leaf`; `neighbors:pose_leaf list`; `w:pose_pruning`;
                `cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] CPR_POSEPRUNING_SOUND) THEN
  ASM_REWRITE_TAC[pose_covered; oriented_pose_covered; oriented_realizes] THEN
  DISCH_THEN(X_CHOOSE_THEN `leaf:pose_leaf` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `leaf:pose_leaf` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_angle leaf = pl_angle source` ASSUME_TAC THENL
   [UNDISCH_TAC `MEM (leaf:pose_leaf) (pp_result source w)` THEN
    REWRITE_TAC[pp_result; MEM_MAP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[pl_angle];
    UNDISCH_TAC `angle_witness source cq sq uq vq aq` THEN
    ASM_REWRITE_TAC[angle_witness]]);;

(* Lean: CertifiedPosePruning.oriented_sound *)
let OCV_CERTIFIEDPOSEPRUNING_ORIENTED_SOUND = prove
 (`forall w cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     cpp_ok w /\ (forall l. MEM l (cp_links w) ==> rl_angle_check l) /\
     oriented_realizes (cp_source w) cq sq uq vq aq /\
     pose_covered (cp_neighbors w) cr sr ur vr ar /\ ldisj cq sq uq vq aq cr sr ur vr ar
     ==> oriented_pose_covered (cp_targets w) cq sq uq vq aq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpp_ok] THEN STRIP_TAC THEN
  MATCH_MP_TAC OCV_ORIENTED_RELAXATION_COVER_SOUND THEN
  MAP_EVERY EXISTS_TAC [`pp_result (cp_source w) (cp_pruning w)`; `cp_links w`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OCV_POSEPRUNING_ORIENTED_SOUND THEN
  MAP_EVERY EXISTS_TAC [`cp_neighbors w`; `cr:real`; `sr:real`; `ur:real`; `vr:real`;
                        `ar:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: oriented_pruning_cover_sound *)
let OCV_ORIENTED_PRUNING_COVER_SOUND = prove
 (`forall sources neighbors targets plans cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     (forall w. MEM w plans ==> cpp_ok w) /\
     pruning_cover_check sources neighbors targets plans /\
     (forall w. MEM w plans ==> forall l. MEM l (cp_links w) ==> rl_angle_check l) /\
     oriented_pose_covered sources cq sq uq vq aq /\ pose_covered neighbors cr sr ur vr ar /\
     ldisj cq sq uq vq aq cr sr ur vr ar
     ==> oriented_pose_covered targets cq sq uq vq aq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pruning_cover_check] THEN STRIP_TAC THEN
  UNDISCH_TAC `oriented_pose_covered sources cq sq uq vq aq` THEN
  GEN_REWRITE_TAC LAND_CONV [oriented_pose_covered] THEN
  DISCH_THEN(X_CHOOSE_THEN `src:pose_leaf` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `src:pose_leaf` o check (fun th ->
    can (find_term ((=) `cp_targets`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:cert_pruning` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`w:cert_pruning`; `cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
    OCV_CERTIFIEDPOSEPRUNING_ORIENTED_SOUND) THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[oriented_pose_covered] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Dictionary-free form of N12Compact.IndexedRelaxation.Dictionary.transfer  *)
(* (Compact/Bridge/IndexedRelaxation.lean): two leaves with the same angle   *)
(* enclosure; if every row of the target holds at q's centre, the target is  *)
(* realized as soon as the source is.  (The dictionary's row normalization   *)
(* by positive denominators is left to the dictionary layer.)                *)
(* ------------------------------------------------------------------------- *)

(* Lean: Dictionary.transfer (Realizes part) *)
let OCV_POSE_TRANSFER = prove
 (`forall src tgt c s u v a.
     pl_angle src = pl_angle tgt /\
     (forall f. MEM f (pl_inputs tgt) ==> lc_holds f [lcx c s u v a; lcy c s u v a]) /\
     pose_realizes src c s u v a
     ==> pose_realizes tgt c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pose_realizes] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: Dictionary.transfer *)
let OCV_ORIENTED_TRANSFER = prove
 (`forall src tgt c s u v a.
     pl_angle src = pl_angle tgt /\
     (forall f. MEM f (pl_inputs tgt) ==> lc_holds f [lcx c s u v a; lcy c s u v a]) /\
     oriented_realizes src c s u v a
     ==> oriented_realizes tgt c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oriented_realizes] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC OCV_POSE_TRANSFER THEN EXISTS_TAC `src:pose_leaf` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `angle_witness src c s u v a` THEN ASM_REWRITE_TAC[angle_witness]]);;
