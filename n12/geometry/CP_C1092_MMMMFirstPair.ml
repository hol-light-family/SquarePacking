(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMFirstPair.lean                       *)
(* (N12Compact.C1092MMMMFirstPair).  The first MMMM pair forces a positive   *)
(* adjacent sign and a small central angle.                                  *)
(* d = cC, r = --sC, b = cB, t = sB in the Lean notation.                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMMNegativeNeighbor.ml";;

let C1092MFP_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MFP_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MFP_LIN_TAC; DISCH_TAC];;

let C1092MFP_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MFP_LIN_TAC; DISCH_TAC];;

(* Lean: Result (structure) *)
let C1092MFP_result = new_definition
 `C1092MFP_result cC sC uC vC aC cB sB uB vB aB <=>
    &0 < sB /\ c1092sct_positive_faces cB sB uB vB aB /\
    &9 / &20 < sB /\ cB < &9 / &10 /\ --sC < &7 / &50 /\ &99 / &100 < cC /\
    aC * (&1 + cB * --sC + sB * cC) <=
    cB + sB + (cB * --sC + sB * cC) * (uC + aC) -
    (cB * cC - sB * --sC) * (vC + aC)`;;

(* Lean: positive_support *)
let C1092MFP_POSITIVE_SUPPORT = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\
     c977cc_normal cC (--sC) /\ c977cc_normal cB sB /\ &0 < sB /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     uB + aB <= sB - (&39 / &100) * cB /\
     vB + aB <= cB + sB /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> aC * (&1 + cB * --sC + sB * cC) <=
         cB + sB + (cB * --sC + sB * cC) * (uC + aC) -
         (cB * cC - sB * --sC) * (vC + aC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  SUBGOAL_THEN `uC + aC <= (&7 / &20) * (cC + --sC)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20))` THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
    REPEAT CONJ_TAC THEN C1092MFP_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
    C1092MPA_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MFP_LIN_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  C1092MFP_LE_MUL_TAC `cB - sB` `cC:real` THEN
  C1092MFP_LE_MUL_TAC `sB:real` `cC - --sC` THEN
  C1092MFP_LE_MUL_TAC `cB:real` `--sC` THEN
  C1092MFP_LT_MUL_TAC `sB:real` `cC:real` THEN
  SUBGOAL_THEN `(cC pow 2 + sC pow 2 = &1) /\ (cB pow 2 + sB pow 2 = &1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* longitudinal *)
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cB:real`; `sB:real`;
                  `cB * cC + sB * sC`; `--cB * sC + sB * cC`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MFP_LIN_TAC;
      DISCH_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `--sC`] C1092MPS_POSITIVE_LONGITUDINAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    C1092MFP_LE_MUL_TAC `cB * cC + sB * sC` `(&7 / &20) * (cC + --sC) - &1 - uC` THEN
    C1092MFP_LT_MUL_TAC `--cB * sC + sB * cC` `--cC / &2 - vC` THEN
    C1092MFP_LE_MUL_TAC `cB:real`
      `--(&7 / &10 - cC - (&7 / &20) * (--sC) pow 2 - (&3 / &20) * cC * --sC)` THEN
    C1092MFP_LT_MUL_TAC `sB:real`
      `--(--(&17 / &20) + --sC + (&3 / &20) * (--sC) pow 2 - (&7 / &20) * cC * --sC)` THEN
    SUBGOAL_THEN
     `(cB * cC + sB * sC) * ((&7 / &20) * (cC + --sC) - &1) -
      (--cB * sC + sB * cC) * cC / &2 + (&7 / &20) * cB - (&7 / &20) * sB =
      cB * (&7 / &10 - cC - (&7 / &20) * (--sC) pow 2 - (&3 / &20) * cC * --sC) +
      sB * (--(&17 / &20) + --sC + (&3 / &20) * (--sC) pow 2 - (&7 / &20) * cC * --sC)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `cC pow 2 + sC pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MFP_LIN_TAC;
    (* transverse *)
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC`; `cC:real`;
                  `--cB * sC + sB * cC`; `cB * cC + sB * sC`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MFP_LIN_TAC;
      DISCH_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `sB:real`] C1092MPS_POSITIVE_TRANSVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092MFP_LT_MUL_TAC `--cB * sC + sB * cC` `sB - (&39 / &100) * cB - &1 - uB` THEN
    C1092MFP_LE_MUL_TAC `cB * cC + sB * sC` `cB + sB - &1 - vB` THEN
    SUBGOAL_THEN
     `(--cB * sC + sB * cC) * (sB - (&39 / &100) * cB - &1) +
      (cB * cC + sB * sC) * (cB + sB - &1) =
      --cC * (cB + sB - &1 - (&61 / &100) * cB * sB) +
      --sC * (sB - cB - &39 / &100 - (&61 / &100) * sB pow 2)` ASSUME_TAC THENL
     [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MFP_LIN_TAC;
    (* own transverse *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--(--cB * sC + sB * cC)`; `cB * cC + sB * sC`] C1092WS_UPPER_NP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MFP_LIN_TAC;
      DISCH_TAC] THEN
    C1092MFP_LIN_TAC]);;

(* Lean: result *)
let C1092MFP_RESULT = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\
     c977cc_normal cC (--sC) /\ &0 < cB /\ abs sB <= cB /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&13 / &50) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     ~linside cB sB uB vB aB (--(&1)) (&0) /\
     ~linside cB sB uB vB aB (--(&1)) (&1) /\
     ~linside cB sB uB vB aB (--(&39 / &100)) (&0) /\
     ~linside cB sB uB vB aB (--(&39 / &100)) (&1) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> C1092MFP_result cC sC uC vC aC cB sB uB vB aB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  SUBGOAL_THEN `&0 < sB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
      UNDISCH_TAC `abs sB <= cB` THEN UNDISCH_TAC `sB <= &0` THEN
      UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] C1092SCT_NEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] C1092MNN_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cB sB` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] C1092SCT_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092sct_positive_faces] o
    check (fun th -> can (term_match [] `c1092sct_positive_faces b t p q a`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
    C1092MFP_POSITIVE_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  SUBGOAL_THEN `uC + aC <= (&7 / &20) * (cC + --sC) /\ &0 < uC + aC /\ &0 < vC + aC`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20))` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
    DISCH_TAC THEN REPEAT CONJ_TAC THEN TRY C1092MFP_LIN_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(uC < cC * &7 / &20 + sC * --(&7 / &20) /\
                   cC * &7 / &20 + sC * --(&7 / &20) < uC + aC /\
                   vC < --sC * &7 / &20 + cC * --(&7 / &20) /\
                   --sC * &7 / &20 + cC * --(&7 / &20) < vC + aC)` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MFP_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `sB:real`; `aC:real`; `uC + aC`; `vC + aC`]
    C1092MPS_SMALL_OF_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[C1092MFP_result; c1092sct_positive_faces]);;
