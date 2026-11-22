(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallCenter.lean                     *)
(* (N12Compact.C1092ShortWallCenter).  The complete physical two-wall       *)
(* center theorem.  upper/lower are ABT_upper/ABT_lower; NarrowData is       *)
(* C1092SWN_narrowData; allowance is C1092SWS_allowance; X, Y are            *)
(* C1092SWRM_X, C1092SWRM_Y; canonical_frame / positive_frame are            *)
(* CLF_CANONICAL_FRAME / CLF_POSITIVE_FRAME; turnFrame W is the 5-tuple      *)
(* (--s, c, v, --u - a, a); pullSwap is (s, c, u, --v - a, a).               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortWallCubicCap.ml";;
needs "n12/geometry/CP_C1092_ShortWallRightAxes.ml";;
needs "n12/geometry/CP_C1092_ShortWallRightMargin.ml";;
needs "n12/geometry/CP_C1092_ShortWallNarrow.ml";;
needs "n12/geometry/CP_C1092_ShortWallCrossing.ml";;
needs "n12/geometry/CentralWallPairSupport.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C1092SWCE_LIN = NLIN_TAC ~deg2:false [];;

let C1092SWCE_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092SWCE_LIN; ALL_TAC];;

let C1092SWCE_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092SWCE_LIN; ALL_TAC];;

(* an identity modulo the unit relation of the given hypothesis term *)
let C1092SWCE_RING tm unit = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(if unit = `true` then ALL_TAC else UNDISCH_TAC unit) THEN
   REWRITE_TAC[C1092SWRM_X; C1092SWRM_Y; C1092SWS_allowance] THEN CONV_TAC REAL_RING; ALL_TAC];;

(* Lean: supports (private) *)
let C1092SWCE_SUPPORTS = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     &0 <= cA * cR + sA * sR
     ==> ABT_upper cA sA uA vA aA cR sR =
           (cA * cR + sA * sR) * (uA + aA / &2) + (cA * sR - sA * cR) * (vA + aA / &2) +
           aA * ((cA * cR + sA * sR) + abs(cA * sR - sA * cR)) / &2 /\
         ABT_lower cR sR uR vR aR cA sA =
           (cA * cR + sA * sR) * (uR + aR / &2) - (cA * sR - sA * cR) * (vR + aR / &2) -
           aR * ((cA * cR + sA * sR) + abs(cA * sR - sA * cR)) / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[C981SF_UPPER_IN_BANDS; C981SF_LOWER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(cR * cA + sR * sA) = cA * cR + sA * sR /\
                abs(--cR * sA + sR * cA) = abs(cA * sR - sA * cR) /\
                abs(cA * cR + sA * sR) = cA * cR + sA * sR /\
                abs(--cA * sR + sA * cR) = abs(cA * sR - sA * cR)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* turnFrame as a 5-tuple *)
let C1092SWCE_TURN = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1092SWCE_LCONT_TURN = prove
 (`forall c s u v a. lcont c s u v a ==> lcont (--s) c v (--u - a) a`,
  REWRITE_TAC[lcont; C1092SWCE_TURN]);;

(* Lean: canonical_impossible (private) *)
let C1092SWCE_CANONICAL_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ aA = aR /\ aA = aT /\
     lcont cR sR uR vR aR /\ lcont cT sT uT vT aT /\ &2 <= lcx cT sT uT vT aT /\
     c977cc_normal cA sA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&1197 / &500) /\
     linside cT sT uT vT aT (&1197 / &500) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aT`)) THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&1197 / &500) (&3)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cT sT uT vT aA` THEN REWRITE_TAC[ldisj] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] C1092SWN_OF_MISSING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aA:real`] C1092SWCC_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092SWN_narrowData] o
    check (fun th -> can (term_match [] `C1092SWN_narrowData c s u v a`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal cA sA`)) THEN
  SUBGOAL_THEN `&0 < cA` ASSUME_TAC THENL [C1092SWCE_LIN; ALL_TAC] THEN
  C1092SWCE_FACT `&12 * sA <= &5 * cA` THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] C1092SWC_OUTER_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the canonical frame W of R *)
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cW:real` (X_CHOOSE_THEN `sW:real` (X_CHOOSE_THEN `uW:real`
    (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `aW:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aA`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  SUBGOAL_THEN `lcont cW sW uW vW aA /\ ldisj cA sA uA vA aA cW sW uW vW aA /\
                linside cW sW uW vW aA (&1543 / &500) (&2) /\
                linside cW sW uW vW aA (&3) (&1197 / &500)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lcont; ldisj] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] C1092SWRA_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  MP_TAC(ASSUME `linside cW sW uW vW aA (&1543 / &500) (&2)`) THEN
  MP_TAC(ASSUME `linside cW sW uW vW aA (&3) (&1197 / &500)`) THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  (* wall facts used in both signs *)
  C1092SWCE_PROD `&0 <= cA * sA` THEN
  ASM_CASES_TAC `&0 <= sW` THENL
   [SUBGOAL_THEN `c977cc_normal cW sW` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN C1092SWCE_LIN; ALL_TAC] THEN
    C1092SWCE_PROD `&0 < cA * cW` THEN C1092SWCE_PROD `&0 <= sA * sW` THEN
    ASM_CASES_TAC `&0 <= cA * sW - sA * cW` THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
          C1092SWC_CENTRAL_AXIS_IMPOSSIBLE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092SWCE_LIN; REWRITE_TAC[]];
        MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
          CWPS_WALL_AXIS_IMPOSSIBLE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092SWCE_LIN; REWRITE_TAC[]]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`] C977CSB_SINE_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWCE_LIN; DISCH_TAC] THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] C1092SWCE_SUPPORTS) THEN
    ANTS_TAC THENL [C1092SWCE_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `abs(cA * sW - sA * cW) = --(cA * sW - sA * cW)` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> abs x = --x`) THEN C1092SWCE_LIN; STRIP_TAC] THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] CWE_RIGHT_WALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092SWCE_PROD `&0 <= sW * ((--sW * (&1543 / &500) + cW * &2) - vW)` THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [C1092SWCE_PROD `&0 <= (cA * cW + sA * sW) * (&4 - (cW * (uW + aA) - sW * vW))` THEN
      C1092SWCE_PROD `&0 <= sA * ((--sW * (&1543 / &500) + cW * &2) - vW)` THEN
      C1092SWCE_RING
       `cW * ((cA * cW + sA * sW) * uW - (cA * sW - sA * cW) * vW) =
        (cA * cW + sA * sW) * (cW * (uW + aA) - sW * vW) + sA * vW - aA * cW * (cA * cW + sA * sW)`
       `cW * cW + sW * sW = &1` THEN
      MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`] C1092SWS_CENTRAL_POSITIVE_BELOW) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWCE_LIN; DISCH_TAC] THEN
      C1092SWCE_PROD `&0 < (aA - &1) * (cW * (&1 + (cA * cW + sA * sW)))` THEN
      C1092SWCE_PROD `&0 <= cW * (((cA * cW + sA * sW) * uW - (cA * sW - sA * cW) * vW) -
                                 (uA + aA))` THEN
      C1092SWCE_PROD `&0 <= cW * (uA - &2 * (cA + sA))` THEN
      C1092SWCE_LIN;
      MP_TAC(SPECL [`cA:real`; `sA:real`] C1092SWS_CUBIC_BASELINE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWCE_LIN; DISCH_TAC] THEN
      C1092SWCE_PROD `&0 <= (cA * cW + sA * sW) * (uA - &2 * (cA + sA))` THEN
      C1092SWCE_PROD `&0 <= --(cA * sW - sA * cW) *
                       ((&3 * cA - (&5 / &2) * sA + C1092SWS_allowance cA sA) - aA - vA)` THEN
      C1092SWCE_RING
       `(cA * cW + sA * sW) * (&2 * (cA + sA)) +
        (cA * sW - sA * cW) * (&3 * cA - (&5 / &2) * sA + C1092SWS_allowance cA sA) =
        cW * C1092SWRM_X cA sA + sW * C1092SWRM_Y cA sA`
       `cA * cA + sA * sA = &1` THEN
      MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`] C1092SWRM_ORDERED) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWCE_LIN; DISCH_TAC] THEN
      C1092SWCE_PROD `&0 < (aA - &1) *
                       (cW * ((cA * cW + sA * sW) - (cA * sW - sA * cW) + &1))` THEN
      C1092SWCE_FACT `cW * C1092SWRM_X cA sA + sW * C1092SWRM_Y cA sA +
                      aA * ((cA * cW + sA * sW) - (cA * sW - sA * cW)) <= uW` THEN
      C1092SWCE_PROD `&0 <= cW * (uW - (cW * C1092SWRM_X cA sA + sW * C1092SWRM_Y cA sA +
                                       aA * ((cA * cW + sA * sW) - (cA * sW - sA * cW))))` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
      C1092SWCE_LIN];
    ALL_TAC] THEN
  (* negative wall sine: w = --sW *)
  SUBGOAL_THEN `c977cc_normal cW (--sW)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN C1092SWCE_LIN; ALL_TAC] THEN
  C1092SWCE_PROD `&0 < cW * (cA - sA)` THEN
  C1092SWCE_PROD `&0 <= sA * (cW - --sW)` THEN
  C1092SWCE_PROD `&0 <= cA * --sW` THEN
  C1092SWCE_PROD `&0 <= sA * cW` THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] C1092SWCE_SUPPORTS) THEN
  ANTS_TAC THENL [C1092SWCE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `abs(cA * sW - sA * cW) = --(cA * sW - sA * cW)` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> abs x = --x`) THEN C1092SWCE_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] C1092SWCE_LCONT_TURN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`--sW:real`; `cW:real`; `vW:real`; `--uW - aA:real`; `aA:real`] CWE_RIGHT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    UNDISCH_TAC `cW * cW + sW * sW = &1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  C1092SWCE_FACT `cW * (uW + aA) + --sW * (vW + aA) <= &4` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C1092SWCE_PROD `&0 <= (cA * cW + sA * sW) * (&4 - (cW * (uW + aA) + --sW * (vW + aA)))` THEN
    C1092SWCE_PROD `&0 <= sA * ((--sW * (&1543 / &500) + cW * &2) - vW)` THEN
    C1092SWCE_RING
     `cW * ((cA * cW + sA * sW) * uW - (cA * sW - sA * cW) * vW) =
      (cA * cW + sA * sW) * (cW * (uW + aA) + --sW * (vW + aA)) + sA * vW -
      aA * (cA * cW + sA * sW) * (cW + --sW)` `cW * cW + sW * sW = &1` THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `--sW:real`] C1092SWS_CENTRAL_NEGATIVE_BELOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWCE_LIN; DISCH_TAC] THEN
    C1092SWCE_PROD `&0 <= (cA * cW + sA * sW) * (cW + --sW)` THEN
    C1092SWCE_PROD `&0 < (aA - &1) * (cW + (cA * cW + sA * sW) * (cW + --sW))` THEN
    C1092SWCE_PROD `&0 <= cW * (((cA * cW + sA * sW) * uW - (cA * sW - sA * cW) * vW) -
                               (uA + aA))` THEN
    C1092SWCE_PROD `&0 <= cW * (uA - &2 * (cA + sA))` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]) THEN
    C1092SWCE_LIN;
    ALL_TAC] THEN
  C1092SWCE_PROD `&0 <= (cA * cW + sA * sW) * (uA - &2 * (cA + sA))` THEN
  C1092SWCE_PROD `&0 <= --(cA * sW - sA * cW) *
                   ((&3 * cA - (&5 / &2) * sA + C1092SWS_allowance cA sA) - aA - vA)` THEN
  C1092SWCE_RING
   `(cA * cW + sA * sW) * (&2 * (cA + sA)) +
    (cA * sW - sA * cW) * (&3 * cA - (&5 / &2) * sA + C1092SWS_allowance cA sA) =
    cW * C1092SWRM_X cA sA + sW * C1092SWRM_Y cA sA` `cA * cA + sA * sA = &1` THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] C1092SWS_CUBIC_BASELINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWCE_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] C1092SWS_NEGATIVE_WALL_BASELINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWCE_LIN; DISCH_TAC] THEN
  C1092SWCE_PROD `&0 <= sA * sA * sA` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `x pow 3 = x * x * x`; REAL_POW_2]) THEN
  C1092SWCE_PROD `&0 <= cW * (sA * sA / &2 - (&1 - cA) * (&1 - sA) - sA * C1092SWS_allowance cA sA)` THEN
  C1092SWCE_PROD `&0 <= --sW * (cA - sA - &303 / &500 + sA * sA + cA * sA / &2 -
                               cA * C1092SWS_allowance cA sA)` THEN
  C1092SWCE_PROD `&0 < (aA - &1) * ((cA * cW + sA * sW) + --(cA * sW - sA * cW))` THEN
  C1092SWCE_RING
   `cW * C1092SWRM_X cA sA + sW * C1092SWRM_Y cA sA +
    ((cA * cW + sA * sW) + --(cA * sW - sA * cW)) - &3 * cW + (&1197 / &500) * --sW =
    cW * (sA * sA / &2 - (&1 - cA) * (&1 - sA) - sA * C1092SWS_allowance cA sA) +
    --sW * (cA - sA - &303 / &500 + sA * sA + cA * sA / &2 - cA * C1092SWS_allowance cA sA)`
   `true` THEN
  C1092SWCE_LIN);;

(* pullSwap facts *)
let C1092SWCE_LCX_PULLSW = prove
 (`forall c s u v a. lcx s c u (--v - a) a = lcy c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: point *)
let C1092SWCE_POINT = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ aA = aR /\ aA = aT /\
     lcont cR sR uR vR aR /\ lcont cT sT uT vT aT /\
     &2 <= lcy cR sR uR vR aR /\ &2 <= lcx cT sT uT vT aT /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&1197 / &500) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&1197 / &500) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aT`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = aA`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th; ldisj]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  ASM_CASES_TAC `s' <= c'` THENL
   [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `aA:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
                  `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aA:real`]
      C1092SWCE_CANONICAL_IMPOSSIBLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ldisj; c977cc_normal; REAL_POW_2]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`s':real`; `c':real`; `u':real`; `--v' - aA:real`; `aA:real`;
                `sT:real`; `cT:real`; `uT:real`; `--vT - aA:real`; `aA:real`;
                `sR:real`; `cR:real`; `uR:real`; `--vR - aA:real`; `aA:real`]
    C1092SWCE_CANONICAL_IMPOSSIBLE) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REWRITE_TAC[LINSIDE_PULLSW; ldisj; C1092SWCE_LCX_PULLSW; c977cc_normal; REAL_POW_2] THEN
  ASM_SIMP_TAC[LCONT_PULLSW] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC) THEN
  TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]);;
