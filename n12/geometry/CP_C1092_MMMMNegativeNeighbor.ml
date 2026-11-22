(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMNegativeNeighbor.lean                *)
(* (N12Compact.C1092MMMMNegativeNeighbor).  A nonpositive standardized       *)
(* central angle excludes the entire negative neighbor sign.                 *)
(* d = cC, r = --sC, b = cB, t = --sB in the Lean notation.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMMPairAxes.ml";;
needs "n12/geometry/CP_C1092_MMMMPairScalars.ml";;
needs "n12/geometry/CP_C1092_ShortChordTable.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

let C1092MNN_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MNN_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MNN_LIN_TAC; DISCH_TAC];;

let C1092MNN_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MNN_LIN_TAC; DISCH_TAC];;

(* discharge the hypotheses of a whole-support formula *)
let C1092MNN_WS_TAC th args =
  MP_TAC(SPECL args th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REAL_ARITH_TAC THEN C1092MNN_LIN_TAC;
    DISCH_TAC];;

let C1092MNN_SCALAR_TAC th =
  MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `--sB`] th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MNN_LIN_TAC; DISCH_TAC];;

(* Lean: impossible_faces *)
let C1092MNN_IMPOSSIBLE_FACES = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\
     c977cc_normal cC (--sC) /\ c977cc_normal cB (--sB) /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     --cB - --sB <= uB /\
     uB + aB <= --(&39 / &100) * cB /\
     vB + aB <= cB - (&39 / &100) * --sB /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
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
    REPEAT CONJ_TAC THEN C1092MNN_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
    C1092MPA_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MNN_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `&0`; `&0`; `--sB`; `cB:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING;
    STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  C1092MNN_LT_MUL_TAC `cB:real` `cC:real` THEN
  C1092MNN_LE_MUL_TAC `--sB` `--sC` THEN
  SUBGOAL_THEN `(cC pow 2 + sC pow 2 = &1) /\ (cB pow 2 + sB pow 2 = &1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= cB * --sC - --sB * cC` THEN
  REPEAT STRIP_TAC THENL
   [(* longitudinal, h >= 0 *)
    C1092MNN_WS_TAC C1092WS_LOWER_NN
     [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cB:real`; `sB:real`;
      `cB * cC + sB * sC`; `--cB * sC + sB * cC`] THEN
    C1092MNN_SCALAR_TAC C1092MPS_NEGATIVE_LONGITUDINAL_GE THEN
    C1092MNN_LE_MUL_TAC `cB * cC + sB * sC` `(&7 / &20) * (cC + --sC) - &1 - uC` THEN
    C1092MNN_LE_MUL_TAC `--cB * sC + sB * cC` `--cC / &2 - vC` THEN
    SUBGOAL_THEN
     `(cB * cC + sB * sC) * ((&7 / &20) * (cC + --sC) - &1) -
      (--cB * sC + sB * cC) * cC / &2 + (&7 / &20) * (cB + --sB) =
      cB * (&7 / &10 - cC - (&7 / &20) * (--sC) pow 2 - (&3 / &20) * cC * --sC) +
      --sB * (&17 / &20 - --sC - (&3 / &20) * (--sC) pow 2 + (&7 / &20) * cC * --sC)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `cC pow 2 + sC pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MNN_LIN_TAC;
    (* transverse, h >= 0 *)
    C1092MNN_WS_TAC C1092WS_LOWER_NN
     [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC`; `cC:real`;
      `--cB * sC + sB * cC`; `cB * cC + sB * sC`] THEN
    C1092MNN_SCALAR_TAC C1092MPS_NEGATIVE_TRANSVERSE_GE THEN
    C1092MNN_LE_MUL_TAC `--cB * sC + sB * cC` `--(&39 / &100) * cB - &1 - uB` THEN
    C1092MNN_LE_MUL_TAC `cB * cC + sB * sC` `cB - (&39 / &100) * --sB - &1 - vB` THEN
    SUBGOAL_THEN
     `(--cB * sC + sB * cC) * (--(&39 / &100) * cB - &1) +
      (cB * cC + sB * sC) * (cB - (&39 / &100) * --sB - &1) =
      cC * (&1 - cB + --sB - (--sB) pow 2) +
      --sC * (--(&39 / &100) - cB - --sB + cB * --sB)` ASSUME_TAC THENL
     [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MNN_LIN_TAC;
    (* own transverse of C *)
    C1092MNN_LIN_TAC;
    (* longitudinal, h < 0 *)
    C1092MNN_WS_TAC C1092WS_LOWER_PN
     [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cB:real`; `sB:real`;
      `cB * cC + sB * sC`; `--cB * sC + sB * cC`] THEN
    C1092MNN_SCALAR_TAC C1092MPS_NEGATIVE_LONGITUDINAL_LE THEN
    C1092MNN_LE_MUL_TAC `cB * cC + sB * sC` `(&7 / &20) * (cC + --sC) - (uC + aC)` THEN
    C1092MNN_LE_MUL_TAC `vC + aC` `--(--cB * sC + sB * cC)` THEN
    C1092MNN_LT_MUL_TAC `aC - &1` `&1 + (cB * cC + sB * sC)` THEN
    C1092MNN_LIN_TAC;
    (* transverse, h < 0 *)
    C1092MNN_WS_TAC C1092WS_LOWER_NP
     [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC`; `cC:real`;
      `--cB * sC + sB * cC`; `cB * cC + sB * sC`] THEN
    SUBGOAL_THEN `&0 < --sB` ASSUME_TAC THENL [C1092MNN_LIN_TAC; ALL_TAC] THEN
    C1092MNN_SCALAR_TAC C1092MPS_NEGATIVE_TRANSVERSE_LE THEN
    C1092MNN_LE_MUL_TAC `--(--cB * sC + sB * cC)`
      `(uB + aC) - (--(&7 / &20) * (cB + --sB))` THEN
    C1092MNN_LE_MUL_TAC `cB * cC + sB * sC` `cB - (&39 / &100) * --sB - &1 - vB` THEN
    SUBGOAL_THEN
     `--(&7 / &20) * (--cB * sC + sB * cC) * (cB + --sB) +
      (cB * cC + sB * sC) * (cB - (&39 / &100) * --sB - &1) =
      cC * (&1 - cB - (&13 / &20) * (--sB) pow 2 - (&1 / &25) * cB * --sB) +
      --sC * (--(&7 / &20) - (&1 / &25) * (--sB) pow 2 + (&13 / &20) * cB * --sB - --sB)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MNN_LIN_TAC;
    (* own transverse of C *)
    C1092MNN_LIN_TAC]);;

(* Lean: impossible *)
let C1092MNN_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\
     c977cc_normal cC (--sC) /\ c977cc_normal cB (--sB) /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     linside cB sB uB vB aB (--(&7 / &20)) (&7 / &20) /\
     linside cB sB uB vB aB (--(&1)) (&2 / &5) /\
     c1092sct_negative_faces cB (--sB) uB vB aB /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REWRITE_TAC[c1092sct_negative_faces] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C1092MNN_IMPOSSIBLE_FACES THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[]);;
