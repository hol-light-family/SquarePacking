(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOnePositiveRetainingEnding.lean      *)
(* (N12Compact.C1092MPPMOnePositive).  The complete local Lemma 3 after its *)
(* narrow source profile has been supplied.  Squares C = c s u v a,         *)
(* D = cD sD uD vD aD and the bar owner B = cB sB uB vB aB with OpenSquare   *)
(* invariants explicit; MMMPEndingAxes.clockwise D is (cD, sD, --vD - aD,    *)
(* uD, aD).  RetainingPairInput c1092opra_input; retaining_successor_cleared *)
(* C1092OPRC_RETAINING_SUCCESSOR_CLEARED; AllNonpositive.pair_impossible     *)
(* C1092MANPP_PAIR_IMPOSSIBLE.  Tag C1092OPRE_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMOnePositiveRetainingClearance.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositivePair.ml";;

(* Lean: retaining_successor_impossible *)
let C1092OPRE_RETAINING_SUCCESSOR_IMPOSSIBLE = prove
 (`forall c s u v a cD sD uD vD aD cB sB uB vB aB.
     c * c + s * s = &1 /\ &0 < a /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092opra_input c s u v a cD sD (--vD - aD) uD aD /\
     c1092anc_core cD sD uD vD aD /\ ~linside cD sD uD vD aD (&0) (--(&1 / &2)) /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cD sD uD vD aD cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092OPRC_RETAINING_SUCCESSOR_CLEARED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092opra_input] o check (c1092mpapo_head `c1092opra_input`)) THEN
  MATCH_MP_TAC (SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                       `cD:real`; `sD:real`; `--vD - aD`; `uD:real`; `aD:real`] C1092MANPP_PAIR_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
