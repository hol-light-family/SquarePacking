(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositiveProfiles.lean          *)
(* (N12Compact.C1092MPPMAllNonpositive).  Literal frame transfers of the    *)
(* missing-negative profile.  counterclockwise (c,s,u,v,a) is               *)
(* (c, s, v, --u - a, a); MMMPEndingAxes.clockwise (c,s,u,v,a) is           *)
(* (c, s, --v - a, u, a).  Square D is c s u v a with its OpenSquare        *)
(* invariants as hypotheses.  MissingPredecessor / MissingSuccessor /       *)
(* ClearedSuccessor: c1092manp_missingPredecessor / _missingSuccessor /     *)
(* _clearedSuccessor.  StrongFaces (MissingNegativeProfile):                *)
(* c1092mnpg_strong_faces; Core / Cleared (AllNonpositiveCore):             *)
(* c1092anc_core / c1092anc_cleared.  Tag C1092MANP_.                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeActual.ml";;

(* Lean: counterclockwise (definition) and its OpenSquare invariants *)
let C1092MANP_COUNTERCLOCKWISE_SQUARE = prove
 (`forall c s u v a. lsquare c s u v a ==> lsquare c s v (--u - a) a`,
  REWRITE_TAC[lsquare]);;

(* Lean: inside_counterclockwise *)
let C1092MANP_INSIDE_COUNTERCLOCKWISE = prove
 (`forall c s u v a x y. linside c s v (--u - a) a x y <=> linside c s u v a (--y) x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: MissingPredecessor (structure) *)
let c1092manp_missingPredecessor = new_definition
 `c1092manp_missingPredecessor c s u v a <=>
    c977cc_normal c (--s) /\
    s - c <= u /\ u + a <= (&13 / &50) * s /\
    (&14 / &25) * c + s <= v /\ v + a <= c /\
    &252 / &373 <= --s`;;

(* Lean: MissingSuccessor (structure) *)
let c1092manp_missingSuccessor = new_definition
 `c1092manp_missingSuccessor c s u v a <=>
    c977cc_normal c (--s) /\
    --(&13 / &50) * s <= u /\ u + a <= c - s /\
    --c <= v /\ v + a <= --s - (&14 / &25) * c /\
    &252 / &373 <= --s`;;

(* Lean: missing_predecessor *)
let C1092MANP_MISSING_PREDECESSOR = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c (--s) /\ c1092mnpg_strong_faces c s u v a
     ==> c1092manp_missingPredecessor c s v (--u - a) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MNA_STRONGFACES_SINE_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092mnpg_strong_faces c s u v a` THEN
  REWRITE_TAC[c1092mnpg_strong_faces; c1092mnpg_faces; c1092manp_missingPredecessor] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: missing_successor *)
let C1092MANP_MISSING_SUCCESSOR = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c (--s) /\ c1092mnpg_strong_faces c s u v a
     ==> c1092manp_missingSuccessor c s (--v - a) u a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MNA_STRONGFACES_SINE_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092mnpg_strong_faces c s u v a` THEN
  REWRITE_TAC[c1092mnpg_strong_faces; c1092mnpg_faces; c1092manp_missingSuccessor] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: ClearedSuccessor (structure) *)
let c1092manp_clearedSuccessor = new_definition
 `c1092manp_clearedSuccessor c s u v a <=>
    c977cc_normal c (--s) /\
    --c <= v /\ &873 / &1000 < c /\ --s < &61 / &125 /\ s < &0 /\ c < &1 /\
    c * (u + a) - s * (v + a) < &1`;;

(* Lean: cleared_successor *)
let C1092MANP_CLEARED_SUCCESSOR = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     c1092anc_core c s u v a /\ c1092anc_cleared c s u v a
     ==> c1092manp_clearedSuccessor c s (--v - a) u a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092anc_core; c1092anc_cleared; c1092anc_faces; c1092manp_clearedSuccessor] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
