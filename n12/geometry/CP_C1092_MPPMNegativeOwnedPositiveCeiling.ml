(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeOwnedPositiveCeiling.lean     *)
(* (namespace N12Compact.C1092MPPMNegativeOwnedPositiveCeiling).  Complete   *)
(* raw NEGATIVE-OWNED-POSITIVE-CEILING Theorem 1.  Squares C = (cC, ..) and  *)
(* W = (cW, ..), unit normals and positive sides as explicit hypotheses.     *)
(* Input: c1092nopcl_input; Normal: c977cc_normal; lower / upper: ABT_lower  *)
(* / ABT_upper; strict_bounds / ownU / ownV: ABT_STRICT_BOUNDS / ABT_OWNU /  *)
(* ABT_OWNV; lower_nn / lower_np: C1092WS_LOWER_NN / _NP;                    *)
(* TwoFifths.Support.upper_pos_pos: C1092TFSU_UPPER_POS_POS; ThreeSquare     *)
(* signed_axes: C1092SPTS_SIGNED_AXES; Scalars.P0 .. Q1 / own_margin /       *)
(* last_margin: c1092nopc_* / C1092NOPC_OWN_MARGIN / C1092NOPC_LAST_MARGIN.  *)
(* Tag C1092NOPCL_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveCeilingScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareGeometry.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

(* Lean: Input (structure) *)
let c1092nopcl_input = new_definition
 `c1092nopcl_input cC sC uC vC aC cW sW uW vW aW <=>
    &1 < aC /\ aC = aW /\ c977cc_normal cC sC /\ &0 < sC /\
    c977cc_normal cW (--sW) /\ &87 / &100 < cW /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
    (&2 / &5) * sC - cC <= vC /\
    linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
    vW + aW <= cW /\
    uW + aW <= (&7 / &20) * (cW + sW) /\
    --(&1) < cW * uW - sW * vW /\
    ldisj cC sC uC vC aC cW sW uW vW aW`;;

let C1092NOPCL_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;

let C1092NOPCL_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092NOPCL_LIN; ALL_TAC];;

(* unpack the input keeping the linside facts; the side of W becomes aC *)
let C1092NOPCL_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092nopcl_input]
    (ASSUME `c1092nopcl_input cC sC uC vC aC cW sW uW vW aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME t)) THEN
                      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME t)))
    [`c977cc_normal cC sC`; `c977cc_normal cW (--sW)`];;

let C1092NOPCL_CONE_TAC nx ny =
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC])
   [[`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&7 / &20)`,`--(&7 / &20)`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&1)`,`--(&13 / &50)`);
    [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`], (`--(&7 / &20)`,`&7 / &20`)] THEN
  RASM_ARITH_TAC;;

(* Lean: axes (private) *)
let C1092NOPCL_AXES = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092nopcl_input cC sC uC vC aC cW sW uW vW aW
     ==> uC + aC <= ABT_lower cW sW uW vW aW cC sC \/
         vC + aC <= ABT_lower cW sW uW vW aW (--sC) cC \/
         ABT_upper cC sC uC vC aC (--sW) cW <= vW`,
  C1092NOPCL_OPEN_TAC THEN
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
let C1092NOPCL_HALF_LT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092nopcl_input cC sC uC vC aC cW sW uW vW aW
     ==> sC / (&1 + cC) < &11 / &100`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092NOPCL_AXES) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN C1092NOPCL_OPEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `--sW < &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092NOPCL_PROD `&0 < (cW - &87 / &100) * (cW + &87 / &100)` THEN
    C1092NOPCL_PROD `&0 <= (--sW - &1 / &2) * (--sW + &1 / &2)` THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cC * cW + sC * sW /\ &0 < cC * --sW + sC * cW` STRIP_ASSUME_TAC THENL
   [C1092NOPCL_PROD `&0 < cC * (cW - --sW)` THEN
    C1092NOPCL_PROD `&0 <= (cC - sC) * --sW` THEN
    C1092NOPCL_PROD `&0 < sC * cW` THEN
    C1092NOPCL_PROD `&0 <= cC * --sW` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&13 / &50) * cC < uC + aC /\ (&13 / &50) * sC < vC + aC`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (--(&13 / &50)) (&0)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = cC * cW + sC * sW` THEN
  ABBREV_TAC `ell = cC * --sW + sC * cW` THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [(* own *)
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `cC:real`; `sC:real`;
                  `k:real`; `ell:real`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092NOPCL_PROD `&0 <= k * ((&7 / &20) * (cW + sW) - (uW + aC))` THEN
    C1092NOPCL_PROD `&0 <= ell * (cW - (vW + aC))` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `--sW`] C1092NOPC_OWN_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `k + ell - (&13 / &50) * cC - (&7 / &20) * k * (cW - --sW) - ell * cW =
                  cC * c1092nopc_P0 cW (--sW) + sC * c1092nopc_Q0 cW (--sW)` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REWRITE_TAC[c1092nopc_P0; c1092nopc_Q0] THEN
      UNDISCH_TAC `cC * cC + sC * sC = &1` THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092NOPCL_PROD `&0 <= (aC - &1) * (k + ell)` THEN
    RASM_ARITH_TAC;
    (* transverse *)
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`; `--sC`; `cC:real`;
                  `--ell`; `k:real`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092NOPCL_PROD `&0 < ell * ((cW * uW + --sW * vW) - --(&1))` THEN
    C1092NOPCL_PROD `&0 <= cC * (cW - (vW + aC))` THEN
    C1092NOPCL_PROD `&0 < ell * cW` THEN
    C1092NOPCL_PROD `&0 < (aC - &1) * (cC + ell * cW)` THEN
    SUBGOAL_THEN `cW * (--ell * (uW + aC) + k * vW) =
                  --ell * (cW * uW + --sW * vW) + cC * vW - ell * cW * aC` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `cW * ABT_lower cW sW uW vW aC (--sC) cC < (&1 - cW) * (ell - cC)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    C1092NOPCL_PROD `&0 <= (&1 - cW) * (cC * (&1 - --sW))` THEN
    C1092NOPCL_PROD `&0 < (cW - &87 / &100) * (sC * cW)` THEN
    SUBGOAL_THEN `(&1 - cW) * (ell - cC) < (&13 / &100) * sC * cW` ASSUME_TAC THENL
     [EXPAND_TAC "ell" THEN RASM_ARITH_TAC; ALL_TAC] THEN
    C1092NOPCL_PROD `&0 <= cW * (ABT_lower cW sW uW vW aC (--sC) cC - (vC + aC))` THEN
    C1092NOPCL_PROD `&0 < cW * ((vC + aC) - (&13 / &50) * sC)` THEN
    C1092NOPCL_PROD `&0 < sC * cW` THEN
    RASM_ARITH_TAC;
    (* target *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sW`; `cW:real`;
                  `ell:real`; `k:real`] C1092TFSU_UPPER_POS_POS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    C1092NOPCL_PROD `&0 < ell * ((uC + aC) - --(&13 / &50) * cC)` THEN
    C1092NOPCL_PROD `&0 <= k * (vC - ((&2 / &5) * sC - cC))` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cW:real`; `--sW`] C1092NOPC_LAST_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 + k - cW - (&13 / &50) * ell * cC + k * ((&2 / &5) * sC - cC) =
                  &1 - c1092nopc_P1 cC sC * cW - c1092nopc_Q1 cC sC * --sW` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["k"; "ell"] THEN
      REWRITE_TAC[c1092nopc_P1; c1092nopc_Q1] THEN
      UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092NOPCL_PROD `&0 <= (aC - &1) * (&1 + k)` THEN
    RASM_ARITH_TAC]);;
