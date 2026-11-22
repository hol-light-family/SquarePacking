(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMFourCycleStates.lean                 *)
(* (N12Compact.C1092MPPMFourCycle).  Exhaustive sign patterns of four fixed  *)
(* actual sector frames.  A predicate P : Fin 4 -> Prop is P : num -> bool   *)
(* used at i < 4; addSector is c1092mar_addSector (MPPMActualRetaining).     *)
(* Tag C1092MFCS_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualRetaining.ml";;

(* Lean: AllNonpositive *)
let c1092mfcs_allNonpositive = new_definition
 `c1092mfcs_allNonpositive (P:num->bool) <=> forall i. i < 4 ==> ~P i`;;
(* Lean: AllPositive *)
let c1092mfcs_allPositive = new_definition
 `c1092mfcs_allPositive (P:num->bool) <=> forall i. i < 4 ==> P i`;;
(* Lean: OnePositive *)
let c1092mfcs_onePositive = new_definition
 `c1092mfcs_onePositive (P:num->bool) i <=>
    P i /\ ~P (c1092mar_addSector i 1) /\ ~P (c1092mar_addSector i 2) /\ ~P (c1092mar_addSector i 3)`;;
(* Lean: Sandwich *)
let c1092mfcs_sandwich = new_definition
 `c1092mfcs_sandwich (P:num->bool) i <=>
    P i /\ ~P (c1092mar_addSector i 1) /\ P (c1092mar_addSector i 2)`;;
(* Lean: AdjacentPositive *)
let c1092mfcs_adjacentPositive = new_definition
 `c1092mfcs_adjacentPositive (P:num->bool) i <=>
    P i /\ P (c1092mar_addSector i 1) /\ ~P (c1092mar_addSector i 2) /\ ~P (c1092mar_addSector i 3)`;;

let C1092MFCS_FORALL_LT4 = prove
 (`forall Q. (forall i. i < 4 ==> Q i) <=> Q 0 /\ Q 1 /\ Q 2 /\ Q 3`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `i:num` 4 THEN ASM_REWRITE_TAC[]]);;

let C1092MFCS_EXISTS_LT4 = prove
 (`forall Q. (exists i. i < 4 /\ Q i) <=> Q 0 \/ Q 1 \/ Q 2 \/ Q 3`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN C1092WP_ENUM_TAC `i:num` 4 THEN ASM_REWRITE_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `0`; EXISTS_TAC `1`; EXISTS_TAC `2`; EXISTS_TAC `3`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* Lean: classify *)
let C1092MFCS_CLASSIFY = prove
 (`forall P:num->bool. c1092mfcs_allNonpositive P \/ c1092mfcs_allPositive P \/
     (exists i. i < 4 /\ c1092mfcs_onePositive P i) \/ (exists i. i < 4 /\ c1092mfcs_sandwich P i) \/
     (exists i. i < 4 /\ c1092mfcs_adjacentPositive P i)`,
  GEN_TAC THEN
  REWRITE_TAC[c1092mfcs_allNonpositive; c1092mfcs_allPositive; C1092MFCS_FORALL_LT4; C1092MFCS_EXISTS_LT4;
              c1092mfcs_onePositive; c1092mfcs_sandwich; c1092mfcs_adjacentPositive; c1092mar_addSector] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY ASM_CASES_TAC [`(P:num->bool) 0`; `(P:num->bool) 1`; `(P:num->bool) 2`; `(P:num->bool) 3`] THEN
  ASM_REWRITE_TAC[]);;
