(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositiveCycle.lean             *)
(* (N12Compact.C1092MPPMAllNonpositive), ALL-NEGATIVE-MIXED-FORWARD-ENDING  *)
(* sections 3 and 7.  Squares C, D, F, B, R are (cC, ..), (cD, ..), ... with *)
(* their OpenSquare invariants as hypotheses.  clockwise Q is                *)
(* (cQ, sQ, --vQ - aQ, uQ, aQ) (C1092MEA_INSIDE_CLOCKWISE); Core             *)
(* c1092anc_core, clearance C1092ANC_CLEARANCE (Cleared.close is the field   *)
(* &873 / &1000 < c of c1092anc_cleared), cleared_successor                  *)
(* C1092MANP_CLEARED_SUCCESSOR, pair_impossible C1092MANPP_PAIR_IMPOSSIBLE.  *)
(* retains : Fin 4 -> Prop is r : num -> bool used at i < 4, with Fin        *)
(* addition (i + k) MOD 4.  Tag C1092MANCY_.                                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositivePair.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveAlternating.ml";;

(* Lean: three_retaining_impossible *)
let C1092MANCY_THREE_RETAINING_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cD sD uD vD aD cF sF uF vF aF cB sB uB vB aB cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cF * cF + sF * sF = &1 /\ &0 < aF /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092anc_core cC sC uC vC aC /\ c1092anc_core cD sD uD vD aD /\
     c1092anc_core cF sF uF vF aF /\ aC = aD /\
     ldisj cC sC uC vC aC cD sD (--vD - aD) uD aD /\
     ldisj cD sD uD vD aD cF sF (--vF - aF) uF aF /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cC sC uC vC aC cB sB uB vB aB /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cR sR uR vR aR x (--(&1))) /\
     ldisj cD sD uD vD aD cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cC sC uC vC aC (&0) (--(&13 / &50))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ldisj cC sC uC vC aC cD sD (--vD - aD) uD aD` THEN
    REWRITE_TAC[ldisj; C1092MEA_INSIDE_CLOCKWISE; NOT_FORALL_THM] THEN
    MAP_EVERY EXISTS_TAC [`&0`; `--(&13 / &50)`] THEN
    ASM_REWRITE_TAC[REAL_NEG_0; REAL_NEG_NEG] THEN
    UNDISCH_TAC `c1092anc_core cD sD uD vD aD` THEN SIMP_TAC[c1092anc_core];
    ALL_TAC] THEN
  SUBGOAL_THEN `~linside cD sD uD vD aD (&0) (--(&13 / &50))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ldisj cD sD uD vD aD cF sF (--vF - aF) uF aF` THEN
    REWRITE_TAC[ldisj; C1092MEA_INSIDE_CLOCKWISE; NOT_FORALL_THM] THEN
    MAP_EVERY EXISTS_TAC [`&0`; `--(&13 / &50)`] THEN
    ASM_REWRITE_TAC[REAL_NEG_0; REAL_NEG_NEG] THEN
    UNDISCH_TAC `c1092anc_core cF sF uF vF aF` THEN SIMP_TAC[c1092anc_core];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092ANC_CLEARANCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092ANC_CLEARANCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] C1092MANP_CLEARED_SUCCESSOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                       `cD:real`; `sD:real`; `--vD - aD`; `uD:real`; `aD:real`] C1092MANPP_PAIR_IMPOSSIBLE) THEN
  MAP_EVERY (fun (c, d) -> FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[d] o
      check (fun th -> is_comb (concl th) && rator (concl th) = c)))
    [`c1092anc_cleared cC sC uC vC`, c1092anc_cleared; `c1092anc_core cD sD uD vD`, c1092anc_core] THEN
  ASM_REWRITE_TAC[C1092MEA_INSIDE_CLOCKWISE]);;

let C1092MANCY_FORALL_LT4 = prove
 (`forall Q. (forall i. i < 4 ==> Q i) <=> Q 0 /\ Q 1 /\ Q 2 /\ Q 3`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN GEN_TAC THEN
    SPEC_TAC(`i:num`, `i:num`) THEN
    REWRITE_TAC[ARITH_RULE `i < 4 <=> i = 0 \/ i = 1 \/ i = 2 \/ i = 3`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: binary_cycle *)
let C1092MANCY_BINARY_CYCLE = prove
 (`forall r:num->bool.
     (forall i. i < 4 ==> ~r i ==> ~r ((i + 1) MOD 4) ==> false) /\
     (forall i. i < 4 ==> r i ==> r ((i + 1) MOD 4) ==> r ((i + 2) MOD 4) ==> false) /\
     (forall i. i < 4 ==> r i ==> ~r ((i + 1) MOD 4) ==> ~r ((i + 3) MOD 4) ==> false)
     ==> false`,
  GEN_TAC THEN REWRITE_TAC[C1092MANCY_FORALL_LT4] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `(r:num->bool) 0` THEN ASM_CASES_TAC `(r:num->bool) 1` THEN
  ASM_CASES_TAC `(r:num->bool) 2` THEN ASM_CASES_TAC `(r:num->bool) 3` THEN
  ASM_REWRITE_TAC[]);;
