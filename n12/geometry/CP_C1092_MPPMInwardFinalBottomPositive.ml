(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalBottomPositive.lean       *)
(* (N12Compact.C1092MPPMInwardFinal.BottomAngle; Lean header: "Source only, *)
(* uncompiled").  The three support sources for a nonnegative actual bottom  *)
(* square of INWARD-BOTTOM-ANGLE.  Conventions of                            *)
(* MPPMInwardFinalBottomData.ml / MPPMInwardFinalBottomNegative.ml.          *)
(* Tag C1092IFBP_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomData.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomNegative.ml";;

(* Lean: positive_coefficients *)
let C1092IFBP_POSITIVE_COEFFICIENTS = prove
 (`forall cC sC cB sB. c977cc_normal cC (--sC) /\ sC < &0 /\ c977cc_normal cB sB
     ==> &0 <= cC * cB + sC * sB /\ &0 < --sC * cB + cC * sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (cC - --sC) * cB /\ &0 <= --sC * (cB - sB) /\ &0 < --sC * cB /\
                &0 <= cC * sB` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

let C1092IFBP_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092IFBD_CENTRAL_FACES) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092IFBD_POSITIVE_WALL) THEN
  ASM_REWRITE_TAC[c1092ifbd_faces] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C1092IFBN_OPEN_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cB:real`; `sB:real`] C1092IFBP_POSITIVE_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* Lean: positive_central *)
let C1092IFBP_POSITIVE_CENTRAL = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB sB /\\ ABT_upper cB sB uB vB aB (--sC) cC <= vC ==> F"
   C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBP_SETUP_TAC THEN
  SUBGOAL_THEN `--(&1) < ABT_upper cB sB uB vB aC (--sC) cC` MP_TAC THENL
   [ALL_TAC; RASM_ARITH_TAC] THEN
  C1092IFBD_PT_TAC [`linside cB sB uB vB aC (&0) (--(&543 / &500))`;
                    `linside cB sB uB vB aC (--(&13 / &50)) (--(&1))`] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC`; `cC:real`;
                `--sC * cB + cC * sB`; `cC * cB + sC * sB`] C1092TFSU_UPPER_POS_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `&0 < (--(sC:real) * cB + cC * sB) * (uB + aC + (&543 / &500) * sB) /\
    &0 <= (cC * cB + sC * sB) * (vB + aC - (&13 / &50) * sB + cB)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`] C1092IFBS_POSITIVE_CENTRAL_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `--sC`;
                `&1 + (&43 / &500) * sB pow 2 - (&13 / &50) * cB * sB`;
                `(&43 / &500) * cB * sB + (&13 / &50) * sB pow 2`] C1092IFBS_DOT_LE_ONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(--(sC:real) * cB + cC * sB) * (--(&543 / &500) * sB) +
    (cC * cB + sC * sB) * ((&13 / &50) * sB - cB) =
    --cC * (&1 + (&43 / &500) * sB pow 2 - (&13 / &50) * cB * sB) +
    sC * ((&43 / &500) * cB * sB + (&13 / &50) * sB pow 2)` ASSUME_TAC THENL
   [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: positive_u *)
let C1092IFBP_POSITIVE_U = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB sB /\\ &543 / &500 < cC - sC /\\ uB + aB <= ABT_lower cC sC uC vC aC cB sB ==> F"
   C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBP_SETUP_TAC THEN
  C1092IFBD_PT_TAC [`linside cB sB uB vB aC (&0) (--(&543 / &500))`] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cB:real`; `sB:real`;
                `cC * cB + sC * sB`; `--sC * cB + cC * sB`] C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `sB:real`] C1092IFBS_POSITIVE_U_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (cC * cB + sC * sB) * (--cC / &2 - uC) /\
    &0 <= (--(sC:real) * cB + cC * sB) * (--aC - vC) /\
    &0 < (--(sC:real) * cB + cC * sB) * (aC - &1)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: positive_v *)
let C1092IFBP_POSITIVE_V = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB sB /\\ &0 <= cC - sC - &1 + cC * sC + (&2 / &5) * sC pow 2 /\\ vB + aB <= ABT_lower cC sC uC vC aC (--sB) cB ==> F"
   C1092IFBD_VARS C1092IFBD_HYP),
  C1092IFBP_SETUP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                `--(--sC * cB + cC * sB)`; `cC * cB + sC * sB`] C1092WS_LOWER_NP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cB:real`; `sB:real`] C1092IFBS_POSITIVE_WALL_MARGIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 <= cC - sC - &1 + cC * sC + (&2 / &5) * sC pow 2` THEN
    REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (--(sC:real) * cB + cC * sB) * (uC - (--cC - (&2 / &5) * sC)) /\
    &0 <= (cC * cB + sC * sB) * (--aC - vC) /\
    &0 <= cB * (cB + sB)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((aC:real) - &1) * ((&1 + cB * (cB + sB)) / &2 + (--sC * cB + cC * sB) +
                                          (cC * cB + sC * sB))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: nonnegative_impossible *)
let C1092IFBP_NONNEGATIVE_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf
   "!%s. %s /\\ c977cc_normal cB sB /\\ C1092WPS_half cC (--sC) pow 2 - &2 * C1092WPS_half cC (--sC) + &1 / &5 <= &0 ==> F"
   C1092IFBD_VARS C1092IFBD_HYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal cC (--sC)` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092ifbd_input cC sC uC vC aC cB sB uB vB aB` THEN
    REWRITE_TAC[c1092ifbd_input] THEN STRIP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFBS_BAD_ARC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092IFBD_SEPARATORS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal cB sB` THEN
    REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  let close th =
    MATCH_MP_TAC th THEN
    MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                          `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC in
  STRIP_TAC THENL
   [close C1092IFBP_POSITIVE_CENTRAL; close C1092IFBP_POSITIVE_U; close C1092IFBP_POSITIVE_V]);;
