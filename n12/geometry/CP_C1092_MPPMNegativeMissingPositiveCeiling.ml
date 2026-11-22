(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeMissingPositiveCeiling.lean  *)
(* (namespace N12Compact.C1092MPPMNegativeMissingPositiveCeiling).  The      *)
(* genuine missing-negative predecessor cap gives the closed-arc 7/24        *)
(* ceiling for a positive forward owner.  Squares C = (cC, ..) and           *)
(* W = (cW, ..), unit normals and positive sides as explicit hypotheses.     *)
(* Input: c1092nmpcl_input; Normal: c977cc_normal; lower / upper: ABT_lower  *)
(* / ABT_upper; strict_bounds / ownU / ownV: ABT_STRICT_BOUNDS / ABT_OWNU /  *)
(* ABT_OWNV; lower_nn / lower_np: C1092WS_LOWER_NN / _NP;                    *)
(* TwoFifths.Support.upper_pos_pos: C1092TFSU_UPPER_POS_POS; ThreeSquare     *)
(* signed_axes: C1092SPTS_SIGNED_AXES; Scalars.P0 .. g2 / own_margin /       *)
(* coefficient_bounds / transverse_margin / last_margin: c1092nmpc_* /       *)
(* C1092NMPC_*.  The proof follows the sibling port                          *)
(* CP_C1092_MPPMNegativeOwnedPositiveCeiling.ml.  Tag C1092NMPCL_.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeMissingPositiveCeilingScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveCeiling.ml";;

(* Lean: Input (structure) *)
let c1092nmpcl_input = new_definition
 `c1092nmpcl_input cC sC uC vC aC cW sW uW vW aW <=>
    &1 < aC /\ aC = aW /\ c977cc_normal cC sC /\ &0 < sC /\
    c977cc_normal cW (--sW) /\ cW < &33 / &40 /\ &283 / &500 < --sW /\
    &23 / &50 < cW * --sW /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
    (&2 / &5) * sC - cC <= vC /\
    linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
    --cW + sW <= uW /\
    uW + aW <= (&13 / &50) * sW /\
    vW + aW <= (&543 / &500) * cW /\
    ldisj cC sC uC vC aC cW sW uW vW aW`;;

(* unpack the input keeping the linside facts; the side of W becomes aC *)
let C1092NMPCL_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092nmpcl_input]
    (ASSUME `c1092nmpcl_input cC sC uC vC aC cW sW uW vW aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME t)) THEN
                      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME t)))
    [`c977cc_normal cC sC`; `c977cc_normal cW (--sW)`];;

(* Lean: axes (private) *)
let C1092NMPCL_AXES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092nmpcl_input cC sC uC vC aC cW sW uW vW aW
     ==> uC + aC <= ABT_lower cW sW uW vW aW cC sC \/
         vC + aC <= ABT_lower cW sW uW vW aW (--sC) cC \/
         ABT_upper cC sC uC vC aC (--sW) cW <= vW`,
  C1092NMPCL_OPEN_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] C1092SPTS_SIGNED_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [RASM_ARITH_TAC;
    C1092NOPCL_CONE_TAC `--cC` `--sC`;
    RASM_ARITH_TAC;
    C1092NOPCL_CONE_TAC `sC:real` `--cC`;
    C1092NOPCL_CONE_TAC `cW:real` `sW:real`;
    C1092NOPCL_CONE_TAC `--cW` `--sW`;
    RASM_ARITH_TAC;
    C1092NOPCL_CONE_TAC `sW:real` `--cW`]);;

(* Lean: half_lt *)
let C1092NMPCL_HALF_LT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092nmpcl_input cC sC uC vC aC cW sW uW vW aW
     ==> sC / (&1 + cC) < &7 / &24`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092NMPCL_AXES) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN C1092NMPCL_OPEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cW` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cC * cW + sC * sW /\ &0 < cC * --sW + sC * cW` STRIP_ASSUME_TAC THENL
   [C1092NOPCL_PROD `&0 <= (cC - sC) * cW` THEN
    C1092NOPCL_PROD `&0 <= sC * (cW - --sW)` THEN
    C1092NOPCL_PROD `&0 < sC * cW` THEN
    C1092NOPCL_PROD `&0 <= cC * --sW` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&13 / &50) * cC < uC + aC` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (--(&13 / &50)) (&0)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vW + aC <= (&11 / &10) * cW` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = cC * cW + sC * sW` THEN
  ABBREV_TAC `ell = cC * --sW + sC * cW` THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [(* own *)
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `cC:real`; `sC:real`;
                  `k:real`; `ell:real`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092NOPCL_PROD `&0 <= k * ((&13 / &50) * sW - (uW + aC))` THEN
    C1092NOPCL_PROD `&0 <= ell * ((&11 / &10) * cW - (vW + aC))` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `--sW`] C1092NMPC_OWN_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `k + ell - (&13 / &50) * cC + (&13 / &50) * k * --sW - (&11 / &10) * ell * cW =
                  cC * c1092nmpc_P0 cW (--sW) + sC * c1092nmpc_Q0 cW (--sW)` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REWRITE_TAC[c1092nmpc_P0; c1092nmpc_Q0] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092NOPCL_PROD `&0 <= (aC - &1) * (k + ell)` THEN
    RASM_ARITH_TAC;
    (* transverse *)
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
                  `--ell`; `k:real`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092NOPCL_PROD `&0 <= ell * (uW - (--cW + sW))` THEN
    C1092NOPCL_PROD `&0 <= k * ((&543 / &500) * cW - (vW + aC))` THEN
    C1092NOPCL_PROD `&0 < (aC - &1) * (k + ell)` THEN
    SUBGOAL_THEN `ell * (cW + --sW) + (&543 / &500) * k * cW - k - ell =
                  cC * c1092nmpc_f2 cW (--sW) + sC * c1092nmpc_g2 cW (--sW)` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REWRITE_TAC[c1092nmpc_f2; c1092nmpc_g2] THEN
      UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MP_TAC(SPECL [`cW:real`; `--sW`] C1092NMPC_COEFFICIENT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    C1092NOPCL_PROD `&0 < cC * (&29 / &200 - c1092nmpc_f2 cW (--sW))` THEN
    C1092NOPCL_PROD `&0 < sC * (&461 / &1000 - c1092nmpc_g2 cW (--sW))` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`] C1092NMPC_TRANSVERSE_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RASM_ARITH_TAC;
    (* target *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
                  `ell:real`; `k:real`] C1092TFSU_UPPER_POS_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092NOPCL_PROD `&0 < ell * ((uC + aC) - --(&13 / &50) * cC)` THEN
    C1092NOPCL_PROD `&0 <= k * (vC - ((&2 / &5) * sC - cC))` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `--sW`] C1092NMPC_LAST_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 + k - (&11 / &10) * cW - (&13 / &50) * ell * cC + k * ((&2 / &5) * sC - cC) =
                  &1 - c1092nmpc_P1 cC sC * cW - c1092nmpc_Q1 cC sC * --sW` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REWRITE_TAC[c1092nmpc_P1; c1092nmpc_Q1] THEN
      UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092NOPCL_PROD `&0 <= (aC - &1) * (&1 + k)` THEN
    RASM_ARITH_TAC]);;
