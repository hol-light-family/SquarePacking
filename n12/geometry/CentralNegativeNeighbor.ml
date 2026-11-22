(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeNeighbor.lean                     *)
(* (namespace N12Compact.CentralNegativeNeighbor).                           *)
(* The two incoming supports of a negative southeast neighbour force the     *)
(* same small central excess.  Squares A, B are 5-tuples (B.s = -t);         *)
(* Lean upper/lower are ABT_upper/ABT_lower; excess is cnnb_excess.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralNegativeNeighborBounds.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let CNN_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: own_axis *)
let CNN_OWN_AXIS = prove
 (`forall cA sA uA vA aA cB sB uB vB aB t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sB = --t /\ c977cc_normal cA sA /\ c977cc_normal cB t /\ &1 < aB /\
     linside cA sA uA vA aA (&2) (&2) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     uA + aA <= ABT_lower cB sB uB vB aB cA sA
     ==> sA < &2 / &5 /\ uA + aA <= &2 * (cA + sA) + (&9 / &100) * cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&2) (&2)` THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `t:real`] CNNB_OWN_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= cB * (cA - sA)`; `&0 <= sA * (cB - t)`; `&0 <= cA * cB - sA * t`;
    `&0 <= cA * t + sA * cB`] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`;
                `cA:real`; `sA:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (cA * cB - sA * t) * ((&3 * cB - t) - (uB + aB))`;
    `&0 <= (cA * t + sA * cB) * ((&2 * cB + &3 * t) - (vB + aB))`;
    `&0 <= ((cA * cB - sA * t) + (cA * t + sA * cB)) * (aB - &1)`] THEN
  SUBGOAL_THEN `uA + aA - &2 * (cA + sA) <= cA * (&1 - cB) * (&1 - t) - sA * (cB - t + t pow 2)`
    ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CNN_EQ_HINT `&3 * cA + &2 * sA` (ASSUME `cB pow 2 + t pow 2 = &1`)];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cA * (&4 / &45 - (&1 - cB) * (&1 - t))`;
    `&0 <= sA * ((cB - t + t pow 2) - &1 / &2)`;
    `uA + aA - &2 * (cA + sA) <= (&4 / &45) * cA - sA / &2`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: neighbor_axis *)
let CNN_NEIGHBOR_AXIS = prove
 (`forall cA sA uA vA aA cB sB uB (vB:real) aB t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sB = --t /\ c977cc_normal cA sA /\ c977cc_normal cB t /\
     aA = aB /\ &1 < aA /\ linside cA sA uA vA aA (&2) (&2) /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     uB + aB <= &3 * cB - t /\
     ABT_upper cA sA uA vA aA cB (--t) <= uB
     ==> sA < &2 / &5 /\ uA + aA <= &2 * (cA + sA) + (&9 / &100) * cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aB`)) THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&2) (&2)` THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= cB * (cA - sA)`; `&0 <= sA * (cB - t)`; `&0 <= cA * cB - sA * t`;
    `&0 <= cA * t + sA * cB`] THEN
  SUBGOAL_THEN `ABT_upper cA sA uA vA aA cB (--t) =
                (cA * cB - sA * t) * (uA + aA) - (cA * t + sA * cB) * vA` ASSUME_TAC THENL
   [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cB * cA + --t * sA) = cA * cB - sA * t /\
                  abs(--cB * sA + --t * cA) = cA * t + sA * cB` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (cA * t + sA * cB) * (((&47 / &20) * cA - (&33 / &20) * sA) - (vA + aA))`;
    `&0 < (&1 + (cA * t + sA * cB)) * (aA - &1)`] THEN
  SUBGOAL_THEN `(cA * cB - sA * t) * (uA + aA - &2 * (cA + sA)) < cnnb_excess cA sA cB t`
    ASSUME_TAC THENL
   [REWRITE_TAC[CNNB_EXCESS_DEF] THEN
    NLIN_TAC ~deg2:false
     [CNN_EQ_HINT `--(&2 * cB - (&47 / &20) * t)` (ASSUME `cA pow 2 + sA pow 2 = &1`)];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (cA * cB - sA * t) * (uA + aA - &2 * (cA + sA))`;
    `&0 < cnnb_excess cA sA cB t`] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `t:real`] CNNB_SMALL_OF_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `t:real`] CNNB_UPPER_BOUND) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (cA - &7 / &10) * cB`; `&0 <= (&2 / &5 - sA) * t`; `&0 < cA * cB - sA * t`;
    `&0 < (cA * cB - sA * t) * (&2 * (cA + sA) + (&9 / &100) * cA - (uA + aA))`] THEN
  NLIN_TAC []);;
