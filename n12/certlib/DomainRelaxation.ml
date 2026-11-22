(* ========================================================================= *)
(* Port of source/S12/DomainRelaxation.lean (Jatloe, N12-jatloe).            *)
(* LeafRelaxation source target <sameReference, proofs, checked>             *)
(*   -> proofs : ((real#lincon)list)list with lr_ok source target proofs.    *)
(* DomainRelaxation sources targets <destination, plans>                     *)
(*   -> dest : num->num, plans : ((real#lincon)list)list list, dr_ok.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/ContinuousPruning.ml";;

(* Lean: structure LeafRelaxation (its two proof fields) *)
let lr_ok = new_definition
 `lr_ok source target proofs <=>
    ae_reference (pl_angle source) (&1) = ae_reference (pl_angle target) (&1) /\
    forall r. MEM r (pl_inputs target) ==>
      exists terms. MEM terms proofs /\ limp_check 2 (pl_inputs source) r terms`;;

(* Lean: LeafRelaxation.sound *)
let DR_LEAFRELAXATION_SOUND = prove
 (`forall source target proofs c s u v a.
     lr_ok source target proofs /\ pose_realizes source c s u v a
     ==> pose_realizes target c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lr_ok; pose_realizes] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:lincon` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:lincon` o check (fun th ->
      can (find_term ((=) `limp_check`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC LI_LINEAR_IMPLICATION_SOUND THEN
    MAP_EVERY EXISTS_TAC [`2`; `pl_inputs source`; `terms:(real#lincon)list`] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: structure DomainRelaxation *)
let dr_ok = new_definition
 `dr_ok sources targets (dest:num->num) plans <=>
    LENGTH plans = LENGTH sources /\
    forall i. i < LENGTH sources ==>
        dest i < LENGTH targets /\ lr_ok (EL i sources) (EL (dest i) targets) (EL i plans)`;;

(* Lean: DomainRelaxation.sound *)
let DR_DOMAINRELAXATION_SOUND = prove
 (`forall sources targets dest plans c s u v a.
     dr_ok sources targets dest plans /\ pose_covered sources c s u v a
     ==> pose_covered targets c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dr_ok; pose_covered; MEM_EXISTS_EL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `l:pose_leaf` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `EL ((dest:num->num) i) (targets:pose_leaf list)` THEN CONJ_TAC THENL
   [EXISTS_TAC `(dest:num->num) i` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC DR_LEAFRELAXATION_SOUND THEN
    MAP_EVERY EXISTS_TAC [`EL i (sources:pose_leaf list)`;
                          `EL i (plans:(((real#lincon)list)list)list)`] THEN
    ASM_MESON_TAC[]]);;
