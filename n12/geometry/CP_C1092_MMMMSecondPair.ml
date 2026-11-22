(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMSecondPair.lean                      *)
(* (N12Compact.C1092MMMMSecondPair).  The second standardized MMMM pair uses *)
(* the small angle already proved by the first pair.                         *)
(* d = cC, r = sC, b = cB in the Lean notation; t = --sB (negative case) or  *)
(* t = sB (positive case).  NegativeFaces/PositiveFaces: c1092sct_*;         *)
(* lower_nn/lower_pn/lower_np/upper_np: C1092WS_*; strict_bounds:            *)
(* ABT_STRICT_BOUNDS; MMMMPairAxes.alternatives: C1092MPA_ALTERNATIVES.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMMFirstPair.ml";;

let C1092MSP_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MSP_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MSP_LIN_TAC; DISCH_TAC];;

let C1092MSP_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MSP_LIN_TAC; DISCH_TAC];;

let C1092MSP_WS_TAC th args =
  MP_TAC(SPECL args th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REAL_ARITH_TAC THEN C1092MSP_LIN_TAC;
    DISCH_TAC];;

let C1092MSP_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

(* Lean: negative_impossible (private) *)
let C1092MSP_NEGATIVE_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\
     c977cc_normal cC sC /\ c977cc_normal cB (--sB) /\
     sC < &7 / &50 /\ &99 / &100 < cC /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     c1092sct_negative_faces cB (--sB) uB vB aB /\
     uC + aC <= (&7 / &20) * (cC - sC) /\
     sC / &2 < vC + aC /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092sct_negative_faces] o
    check (fun th -> can (term_match [] `c1092sct_negative_faces b t p q a`) (concl th))) THEN
  C1092MSP_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < --sB` ASSUME_TAC THENL [C1092MSP_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
    C1092MPA_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MSP_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `&0`; `&0`; `--sB`; `cB:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING;
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  (* k = cB * sC - sB * cC > 0, alpha = cB * cC + sB * sC > 0 *)
  C1092MSP_LE_MUL_TAC `cB:real` `sC:real` THEN
  C1092MSP_LT_MUL_TAC `--sB` `cC:real` THEN
  C1092MSP_LT_MUL_TAC `cB:real` `cC - sC` THEN
  C1092MSP_LE_MUL_TAC `cB - --sB` `sC:real` THEN
  SUBGOAL_THEN `&0 < cB * sC - sB * cC /\ &0 < cB * cC + sB * sC` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MSP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cC pow 2 + sC pow 2 = &1) /\ (cB pow 2 + sB pow 2 = &1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* longitudinal *)
    C1092MSP_WS_TAC C1092WS_LOWER_PN
     [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cB:real`; `sB:real`;
      `cB * cC + sB * sC`; `--cB * sC + sB * cC`] THEN
    C1092MSP_LE_MUL_TAC `cB * cC + sB * sC` `(&7 / &20) * (cC - sC) - (uC + aC)` THEN
    C1092MSP_LT_MUL_TAC `cB * sC - sB * cC` `(vC + aC) - sC / &2` THEN
    C1092MSP_LT_MUL_TAC `aC - &1` `&1 + (cB * cC + sB * sC)` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `--sB`] C1092MPS_SMALL_NEGATIVE_LONGITUDINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `cB + --sB - (cB * cC + sB * sC) + (cB * cC + sB * sC) * (&7 / &20) * (cC - sC) -
      (cB * sC - sB * cC) * sC / &2 =
      cB * (&27 / &20 - cC - (&7 / &20) * cC * sC - (&17 / &20) * sC pow 2) +
      --sB * (&1 + sC - (&17 / &20) * cC * sC + (&7 / &20) * sC pow 2)` ASSUME_TAC THENL
     [UNDISCH_TAC `cC pow 2 + sC pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MSP_LIN_TAC;
    (* transverse *)
    C1092MSP_WS_TAC C1092WS_LOWER_NP
     [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC`; `cC:real`;
      `--(cB * sC - sB * cC)`; `cB * cC + sB * sC`] THEN
    C1092MSP_LT_MUL_TAC `cB * sC - sB * cC` `(uB + aC) - --(&7 / &20) * (cB + --sB)` THEN
    C1092MSP_LT_MUL_TAC `cB * cC + sB * sC` `cB - (&39 / &100) * --sB - &1 - vB` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `--sB`] C1092MPS_SMALL_NEGATIVE_TRANSVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(&7 / &20) * (cB * sC - sB * cC) * (cB + --sB) +
      (cB * cC + sB * sC) * (cB - (&39 / &100) * --sB - &1) =
      cC * (&1 - cB - (&13 / &20) * (--sB) pow 2 - (&1 / &25) * cB * --sB) +
      sC * (&7 / &20 + (&1 / &25) * (--sB) pow 2 - (&13 / &20) * cB * --sB + --sB)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MSP_LIN_TAC;
    (* own transverse of C *)
    C1092MSP_LIN_TAC]);;

(* Lean: Result (structure) *)
let C1092MSP_result = new_definition
 `C1092MSP_result cC sC uC vC aC cB sB uB vB aB <=>
    &0 < sB /\ &9 / &20 < sB /\ cB < &9 / &10 /\
    aC * (&1 + sB * cC - cB * sC) <=
    cB + sB + (sB * cC - cB * sC) * (uC + aC) - (cB * cC + sB * sC) * (vC + aC)`;;

(* Lean: result *)
let C1092MSP_RESULT = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\
     c977cc_normal cC sC /\ sC < &7 / &50 /\ &99 / &100 < cC /\
     &0 < cB /\ abs sB <= cB /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&13 / &50) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     ~linside cB sB uB vB aB (--(&1)) (&0) /\
     ~linside cB sB uB vB aB (--(&1)) (&1) /\
     ~linside cB sB uB vB aB (--(&39 / &100)) (&0) /\
     ~linside cB sB uB vB aB (--(&39 / &100)) (&1) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> C1092MSP_result cC sC uC vC aC cB sB uB vB aB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_ABS_BOUNDS] o
    check (fun th -> concl th = `abs sB <= cB`)) THEN
  C1092MSP_NORMAL_TAC THEN
  SUBGOAL_THEN `uC + aC <= (&7 / &20) * (cC - sC) /\ sC / &2 < vC + aC`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20))` THEN
      UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN
      UNDISCH_TAC `linside cC sC uC vC aC (&0) (--(&1 / &2))` THEN
      REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN C1092MSP_LIN_TAC;
      UNDISCH_TAC `linside cC sC uC vC aC (--(&1 / &2)) (&0)` THEN
      REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092MSP_LIN_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] C1092SCT_NEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
      C1092MSP_NEGATIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cB sB` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] C1092SCT_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092sct_positive_faces] o
    check (fun th -> can (term_match [] `c1092sct_positive_faces b t p q a`) (concl th))) THEN
  ASM_REWRITE_TAC[C1092MSP_result] THEN
  C1092MSP_NORMAL_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
    C1092MPA_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MSP_LIN_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  (* alpha = cB * cC + sB * sC > 0, k = sB * cC - cB * sC > 0 *)
  C1092MSP_LT_MUL_TAC `cB:real` `cC:real` THEN
  C1092MSP_LE_MUL_TAC `sB:real` `sC:real` THEN
  C1092MSP_LT_MUL_TAC `sB:real` `cC - &99 / &100` THEN
  C1092MSP_LE_MUL_TAC `sC:real` `&9 / &10 - cB` THEN
  SUBGOAL_THEN `&0 < sB * cC - cB * sC /\ &0 < cB * cC + sB * sC` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MSP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cC pow 2 + sC pow 2 = &1) /\ (cB pow 2 + sB pow 2 = &1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* longitudinal *)
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    C1092MSP_WS_TAC C1092WS_LOWER_NN
     [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cB:real`; `sB:real`;
      `cB * cC + sB * sC`; `--cB * sC + sB * cC`] THEN
    C1092MSP_LT_MUL_TAC `cB * cC + sB * sC` `(&7 / &20) * (cC - sC) - &1 - uC` THEN
    C1092MSP_LT_MUL_TAC `sB * cC - cB * sC` `--cC / &2 - vC` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`] C1092MPS_SMALL_POSITIVE_LONGITUDINAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    C1092MSP_LT_MUL_TAC `cB:real`
      `--(&7 / &10 - cC - (&7 / &20) * sC pow 2 + (&3 / &20) * cC * sC)` THEN
    C1092MSP_LT_MUL_TAC `sB:real`
      `--(--(&17 / &20) - sC + (&3 / &20) * sC pow 2 + (&7 / &20) * cC * sC)` THEN
    SUBGOAL_THEN
     `(cB * cC + sB * sC) * ((&7 / &20) * (cC - sC) - &1) -
      (sB * cC - cB * sC) * cC / &2 + (&7 / &20) * cB - (&7 / &20) * sB =
      cB * (&7 / &10 - cC - (&7 / &20) * sC pow 2 + (&3 / &20) * cC * sC) +
      sB * (--(&17 / &20) - sC + (&3 / &20) * sC pow 2 + (&7 / &20) * cC * sC)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `cC pow 2 + sC pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MSP_LIN_TAC;
    (* transverse *)
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    C1092MSP_WS_TAC C1092WS_LOWER_NN
     [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC`; `cC:real`;
      `sB * cC - cB * sC`; `cB * cC + sB * sC`] THEN
    C1092MSP_LT_MUL_TAC `sB * cC - cB * sC` `sB - (&39 / &100) * cB - &1 - uB` THEN
    C1092MSP_LT_MUL_TAC `cB * cC + sB * sC` `cB + sB - &1 - vB` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `sB:real`] C1092MPS_SMALL_POSITIVE_TRANSVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(sB * cC - cB * sC) * (sB - (&39 / &100) * cB - &1) +
      (cB * cC + sB * sC) * (cB + sB - &1) =
      --cC * (cB + sB - &1 - (&61 / &100) * cB * sB) +
      sC * (cB - sB + &39 / &100 + (&61 / &100) * sB pow 2)` ASSUME_TAC THENL
     [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MSP_LIN_TAC;
    (* own transverse *)
    C1092MSP_WS_TAC C1092WS_UPPER_NP
     [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
      `--(sB * cC - cB * sC)`; `cB * cC + sB * sC`] THEN
    C1092MSP_LIN_TAC]);;
