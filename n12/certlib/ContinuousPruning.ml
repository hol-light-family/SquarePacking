(* ========================================================================= *)
(* Port of source/S12/ContinuousPruning.lean (Jatloe, N12-jatloe).           *)
(* Structures carrying proofs in Lean are HOL data plus an `_ok` predicate:  *)
(*   PruneBlock <region, overlaps>     -> PruneBlock region overlaps,        *)
(*        Check (plus subtype checks of overlaps) -> pb_check                *)
(*   PosePruning source neighbors      -> PosePruning blocks tree, pp_ok     *)
(*   DomainPruning sources neighbors   -> plans : pose_pruning list, dp_ok   *)
(*        (plans i is EL i plans; ALL2 pairs it with EL i sources)           *)
(*   ContinuousPruneStep (domains : Fin n -> ..) -> cps_ok n domains target  *)
(*        neighbor plans; a family of squares is five functions num->real.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/AxisOverlapCertificate.ml";;
needs "n12/certlib/OwnerEnclosure.ml";;

(* Lean: structure PruneBlock *)
let prune_block_INDUCT,prune_block_RECURSION =
  define_type "prune_block = PruneBlock (lincon list) (axcert list)";;
let pb_region = define `pb_region (PruneBlock r ov) = r`;;
let pb_overlaps = define `pb_overlaps (PruneBlock r ov) = ov`;;

(* Lean: PruneBlock.Check, with the subtype checks of overlaps *)
let pb_check = new_definition
 `pb_check w source neighbors <=>
    (forall c. MEM c (pb_overlaps w) ==> axcert_check c) /\
    forall b. MEM b neighbors ==>
      exists c. MEM c (pb_overlaps w) /\
          ax_first c = ae_reference (pl_angle source) (&1) /\
          ax_second c = ae_reference (pl_angle b) (&1) /\
          ax_inputsA c = APPEND (pb_region w) (pl_inputs source) /\
          ax_inputsB c = pl_inputs b`;;

(* Lean: PoseCovered *)
let pose_covered = new_definition
 `pose_covered domain c s u v a <=> exists l. MEM l domain /\ pose_realizes l c s u v a`;;

(* Lean: PruneBlock.sound *)
let CPR_PRUNEBLOCK_SOUND = prove
 (`forall w source neighbors cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     pb_check w source neighbors /\ pose_realizes source cq sq uq vq aq /\
     pose_covered neighbors cr sr ur vr ar /\ ldisj cq sq uq vq aq cr sr ur vr ar
     ==> ~(forall f. MEM f (pb_region w) ==> lc_holds f [lcx cq sq uq vq aq; lcy cq sq uq vq aq])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pb_check; pose_covered] THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:pose_leaf` o check (fun th ->
    can (find_term ((=) `ax_inputsB`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `cc:axcert` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`cc:axcert`; `lcx cq sq uq vq aq`; `lcy cq sq uq vq aq`;
                `lcx cr sr ur vr ar`; `lcy cr sr ur vr ar`] AOC_SOUND) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pose_realizes]) THEN
  ASM_SIMP_TAC[MEM_APPEND; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM] THEN
  REWRITE_TAC[overlaps_at; NOT_EXISTS_THM] THEN X_GEN_TAC `P:real#real` THEN STRIP_TAC THEN
  UNDISCH_TAC `ldisj cq sq uq vq aq cr sr ur vr ar` THEN REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(P:real#real)`; `SND(P:real#real)`]) THEN
  REWRITE_TAC[GSYM IN_SQSET] THEN ASM_MESON_TAC[]);;

(* Lean: structure PosePruning (the field `checked` is part of pp_ok) *)
let pose_pruning_INDUCT,pose_pruning_RECURSION =
  define_type "pose_pruning = PosePruning (prune_block list) rtree";;
let pp_blocks = define `pp_blocks (PosePruning b t) = b`;;
let pp_tree = define `pp_tree (PosePruning b t) = t`;;

let pp_ok = new_definition
 `pp_ok source neighbors w <=>
    (forall b. MEM b (pp_blocks w) ==> pb_check b source neighbors) /\
    rtree_check (pl_inputs source) (MAP pb_region (pp_blocks w)) (pp_tree w)`;;

(* Lean: PosePruning.result *)
let pp_result = new_definition
 `pp_result source w =
    MAP (\inputs. PoseLeaf (pl_angle source) inputs) (rtree_leaves (pl_inputs source) (pp_tree w))`;;

(* Lean: PosePruning.sound *)
let CPR_POSEPRUNING_SOUND = prove
 (`forall source neighbors w cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     pp_ok source neighbors w /\ pose_realizes source cq sq uq vq aq /\
     pose_covered neighbors cr sr ur vr ar /\ ldisj cq sq uq vq aq cr sr ur vr ar
     ==> pose_covered (pp_result source w) cq sq uq vq aq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pp_ok] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`pp_tree w`; `pl_inputs source`; `MAP pb_region (pp_blocks w)`;
                `[lcx cq sq uq vq aq; lcy cq sq uq vq aq]`] RT_SOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[pose_realizes];
      REWRITE_TAC[MEM_MAP; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `block:lincon list` THEN X_GEN_TAC `b:prune_block` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      MATCH_MP_TAC CPR_PRUNEBLOCK_SOUND THEN
      MAP_EVERY EXISTS_TAC [`source:pose_leaf`; `neighbors:pose_leaf list`;
                            `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `inputs:lincon list` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[pose_covered; pp_result; MEM_MAP] THEN
  EXISTS_TAC `PoseLeaf (pl_angle source) inputs` THEN CONJ_TAC THENL
   [EXISTS_TAC `inputs:lincon list` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `pose_realizes source cq sq uq vq aq` THEN
    REWRITE_TAC[pose_realizes; pl_angle; pl_inputs] THEN ASM_SIMP_TAC[]]);;

(* Lean: structure DomainPruning (plans i = EL i plans) *)
let dp_ok = new_definition
 `dp_ok sources neighbors plans <=> ALL2 (\s p. pp_ok s neighbors p) sources plans`;;

(* Lean: DomainPruning.result *)
let dp_result = new_definition
 `dp_result sources plans = lflat (MAP2 pp_result sources plans)`;;

let CPR_DP_MEM = prove
 (`forall sources plans neighbors s.
     ALL2 (\s p. pp_ok s neighbors p) sources plans /\ MEM s sources
     ==> exists p. pp_ok s neighbors p /\
             forall l. MEM l (pp_result s p) ==> MEM l (lflat (MAP2 pp_result sources plans))`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; MEM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `h':pose_pruning` THEN ASM_REWRITE_TAC[MAP2; lflat; MEM_APPEND] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC) THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t':pose_pruning list`; `neighbors:pose_leaf list`;
                                  `s:pose_leaf`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC[MAP2; lflat; MEM_APPEND] THEN MESON_TAC[]]);;

(* Lean: DomainPruning.sound *)
let CPR_DOMAINPRUNING_SOUND = prove
 (`forall sources neighbors plans cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     dp_ok sources neighbors plans /\ pose_covered sources cq sq uq vq aq /\
     pose_covered neighbors cr sr ur vr ar /\ ldisj cq sq uq vq aq cr sr ur vr ar
     ==> pose_covered (dp_result sources plans) cq sq uq vq aq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dp_ok; dp_result] THEN STRIP_TAC THEN
  UNDISCH_TAC `pose_covered sources cq sq uq vq aq` THEN
  GEN_REWRITE_TAC LAND_CONV [pose_covered] THEN
  DISCH_THEN(X_CHOOSE_THEN `src:pose_leaf` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`sources:pose_leaf list`; `plans:pose_pruning list`;
                `neighbors:pose_leaf list`; `src:pose_leaf`] CPR_DP_MEM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p:pose_pruning` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`src:pose_leaf`; `neighbors:pose_leaf list`; `p:pose_pruning`;
                `cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] CPR_POSEPRUNING_SOUND) THEN
  ASM_REWRITE_TAC[pose_covered] THEN ASM_MESON_TAC[]);;

(* Lean: structure ContinuousPruneStep {n} (domains : Fin n -> List PoseLeaf) *)
let cps_ok = new_definition
 `cps_ok n (domains:num->pose_leaf list) target neighbor plans <=>
    target < n /\ neighbor < n /\ ~(target = neighbor) /\
    dp_ok (domains target) (domains neighbor) plans`;;

(* Lean: ContinuousPruneStep.result (Function.update domains target ...) *)
let cps_result = new_definition
 `cps_result (domains:num->pose_leaf list) target plans =
    \i. if i = target then dp_result (domains target) plans else domains i`;;

(* Lean: ContinuousPruneStep.sound *)
let CPR_CONTINUOUSPRUNESTEP_SOUND = prove
 (`forall n domains target neighbor plans cq sq uq vq aq.
     cps_ok n domains target neighbor plans /\
     (forall i. i < n ==> cq i * cq i + sq i * sq i = &1 /\ &0 < aq i) /\
     (forall i. i < n ==> pose_covered (domains i) (cq i) (sq i) (uq i) (vq i) (aq i)) /\
     (forall i j. i < n /\ j < n /\ ~(i = j)
            ==> ldisj (cq i) (sq i) (uq i) (vq i) (aq i) (cq j) (sq j) (uq j) (vq j) (aq j))
     ==> forall i. i < n ==> pose_covered (cps_result domains target plans i)
                                    (cq i) (sq i) (uq i) (vq i) (aq i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cps_ok; cps_result] THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC CPR_DOMAINPRUNING_SOUND THEN
    MAP_EVERY EXISTS_TAC [`(domains:num->pose_leaf list) neighbor`;
      `(cq:num->real) neighbor`; `(sq:num->real) neighbor`; `(uq:num->real) neighbor`;
      `(vq:num->real) neighbor`; `(aq:num->real) neighbor`] THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;
