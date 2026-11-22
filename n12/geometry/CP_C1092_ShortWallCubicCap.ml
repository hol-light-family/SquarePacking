(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallCubicCap.lean                   *)
(* (N12Compact.C1092ShortWallCubicCap).  The physical top wall gives a cubic *)
(* cap on the central upper face in both surviving SAT comparisons.          *)
(* exists_positive_frame (with both centre coordinates) is C1092SWCC_FRAME;  *)
(* the pullSwap right wall is CWE_RIGHT_WALL on the swapped 5-tuple.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortWallNarrow.ml";;
needs "n12/geometry/CP_C1092_ShortWallPenalty.ml";;
needs "n12/geometry/CP_C1092_ShortWallAllowance.ml";;

let C1092SWCC_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SWCC_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWCC_LIN_TAC; DISCH_TAC];;

let C1092SWCC_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWCC_LIN_TAC; DISCH_TAC];;

(* S12.exists_positive_frame: a nonnegative face frame with the same centre *)
let C1092SWCC_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 <= c' /\ &0 <= s' /\ a' = a /\
           lcx c' s' u' v' a' = lcx c s u v a /\ lcy c' s' u' v' a' = lcy c s u v a /\
           forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y`,
  let fin = REWRITE_TAC[linside; lcx; lcy] THEN ASM_REAL_ARITH_TAC in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= c` THEN ASM_CASES_TAC `&0 <= s` THENL
  [MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
   ASM_REWRITE_TAC[];
   MAP_EVERY EXISTS_TAC [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`] THEN fin;
   MAP_EVERY EXISTS_TAC [`s:real`; `--c:real`; `--v - a:real`; `u:real`; `a:real`] THEN fin;
   MAP_EVERY EXISTS_TAC [`--c:real`; `--s:real`; `--u - a:real`; `--v - a:real`; `a:real`] THEN
   fin]);;

(* Lean: cap *)
let C1092SWCC_CAP = prove
 (`forall cA sA uA vA aA cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ aA = aT /\
     c977cc_normal cA sA /\ C1092SWN_narrowData cA sA uA vA aA /\
     lcont cT sT uT vT aT /\ &2 <= lcx cT sT uT vT aT /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cT sT uT vT aT (&1197 / &500) (&3) /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> vA + aA <= &3 * cA - (&5 / &2) * sA + C1092SWS_allowance cA sA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aT`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[C1092SWN_narrowData] o
    check (fun th -> can (term_match [] `C1092SWN_narrowData c s u v a`) (concl th))) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] C1092SWS_NARROW_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWCC_LIN_TAC; STRIP_TAC] THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  SUBGOAL_THEN `&0 < cA` ASSUME_TAC THENL [C1092SWCC_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aA:real`] C1092SWCC_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aA`)) THEN
  SUBGOAL_THEN `lcont cW sW uW vW aA /\ &2 <= lcx cW sW uW vW aA /\
                linside cW sW uW vW aA (&1197 / &500) (&3) /\
                ldisj cA sA uA vA aA cW sW uW vW aA` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[lcont; ldisj] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the top wall of W *)
  MP_TAC(SPECL [`sW:real`; `cW:real`; `uW:real`; `--vW - aA`; `aA:real`] CWE_RIGHT_WALL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LCONT_PULLSW] THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
    REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`] C1092SWP_PENALTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < cW + sW` ASSUME_TAC THENL
   [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN UNDISCH_TAC `&0 <= cW` THEN
    UNDISCH_TAC `&0 <= sW` THEN POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
    NLIN_TAC []; ALL_TAC] THEN
  C1092SWCC_LT_MUL_TAC `sA:real` `cW + sW` THEN
  C1092SWCC_LE_MUL_TAC `cW:real` `cA - sA` THEN
  SUBGOAL_THEN `&0 < cA * cW + sA * sW` ASSUME_TAC THENL [C1092SWCC_LIN_TAC; ALL_TAC] THEN
  (* lowerCap *)
  SUBGOAL_THEN `ABT_lower cW sW uW vW aA (--sA) cA <
                &3 * cA - (&5 / &2) * sA + C1092SWS_allowance cA sA` ASSUME_TAC THENL
   [REWRITE_TAC[ABT_lower; tss_support_radius; C1092SWS_allowance] THEN
    SUBGOAL_THEN `abs(--sA * cW + cA * sW) = abs(cA * sW - sA * cW) /\
                  abs(-- --sA * sW + cA * cW) = cA * cW + sA * sW` (fun th -> REWRITE_TAC[th])
    THENL [CONJ_TAC THENL [AP_TERM_TAC THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    C1092SWCC_LE_MUL_TAC `cA:real` `&4 - (sW * (uW + aA) - cW * (--vW - aA))` THEN
    C1092SWCC_LE_MUL_TAC `sA:real` `lcx cW sW uW vW aA - &2` THEN
    C1092SWCC_LE_MUL_TAC `cA:real` `sA:real` THEN
    SUBGOAL_THEN `&0 <= cA pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]; ALL_TAC] THEN
    C1092SWCC_LT_MUL_TAC `aA - &1` `&1 + cA pow 2 + cA * sA` THEN
    C1092SWCC_LE_MUL_TAC `aA:real`
      `(&2 * cA * cW + cA * sW + sA * sW + abs(cA * sW - sA * cW)) - (&1 + cA pow 2 + cA * sA)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lcx; lcy]) THEN REWRITE_TAC[lcx; lcy] THEN
    C1092SWCC_LIN_TAC;
    ALL_TAC] THEN
  (* ownCap *)
  SUBGOAL_THEN `vW < &3 * cW - (&5 / &2) * sW + C1092SWS_allowance cW sW` ASSUME_TAC THENL
   [REWRITE_TAC[C1092SWS_allowance] THEN
    C1092SWCC_LE_MUL_TAC `cW:real` `&4 - (sW * (uW + aA) - cW * (--vW - aA))` THEN
    C1092SWCC_LE_MUL_TAC `sW:real` `lcx cW sW uW vW aA - &2` THEN
    C1092SWCC_LE_MUL_TAC `cW:real` `sW:real` THEN
    SUBGOAL_THEN `&0 <= cW pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]; ALL_TAC] THEN
    C1092SWCC_LT_MUL_TAC `aA - &1` `&1 + cW pow 2 + cW * sW` THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] LCENTRE_COORDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
    C1092SWCC_LIN_TAC;
    ALL_TAC] THEN
  (* the strip point *)
  SUBGOAL_THEN `exists x y. linside cA sA uA vA aA x y /\ uW < cW * x + sW * y /\
                      cW * x + sW * y < uW + aA` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `cW * (&5 / &2) + sW * &3 < uW + aA` THENL
     [MAP_EVERY EXISTS_TAC [`&5 / &2`; `&3`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `linside cW sW uW vW aA (&1197 / &500) (&3)` THEN
      REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092SWCC_LIN_TAC;
      MP_TAC(SPECL [`cW:real`; `sW:real`; `&5 / &2 - &47 / &20`; `&3 - &47 / &20`]
        FSAF_SHORT_PROJECTIONS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
      MAP_EVERY EXISTS_TAC [`&47 / &20`; `&47 / &20`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `linside cW sW uW vW aA (&1197 / &500) (&3)` THEN
      REWRITE_TAC[linside] THEN STRIP_TAC THEN CONJ_TAC THEN C1092SWCC_LIN_TAC];
    ALL_TAC] THEN
  (* the four axes *)
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  let sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
  and sqW = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`] in
  ABT_SB_TAC sqW `&1197 / &500` `&3` `cA:real` `sA:real` THEN
  ABT_SB_TAC sqW `&1197 / &500` `&3` `--sA` `cA:real` THEN
  ABT_SB_TAC sqA `x:real` `y:real` `cW:real` `sW:real` THEN
  ABT_SB_TAC sqA `&5 / &2` `&3` `--sW` `cW:real` THEN
  ABT_OWN_TAC sqA THEN ABT_OWN_TAC sqW THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  (* now 8 cases; the two surviving ones are handled below *)
  FIRST [MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092SWCC_LIN_TAC;
         C1092SWCC_LIN_TAC;
         ALL_TAC] THEN
  (* the case upper A (--sW) cW <= vW *)
  SUBGOAL_THEN `&12 / &25 < (&5 / &2) * cA + &3 * sA - uA /\
                &1 / &4 < uA + aA - ((&5 / &2) * cA + &3 * sA)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092SWCC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ABT_upper cA sA uA vA aA (--sW) cW =
    --(cA * sW - sA * cW) * (uA + aA / &2) + (cA * cW + sA * sW) * (vA + aA / &2) +
    aA * (abs(cA * sW - sA * cW) + (cA * cW + sA * sW)) / &2` ASSUME_TAC THENL
   [REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN
    SUBGOAL_THEN `abs(--sW * cA + cW * sA) = abs(cA * sW - sA * cW) /\
                  abs(-- --sW * sA + cW * cA) = cA * cW + sA * sW` (fun th -> REWRITE_TAC[th])
    THENL [CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (cA * sW - sA * cW)` THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`] C1092SWA_ABOVE) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1092SWCC_LIN_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `abs (cA * sW - sA * cW) = (cA * sW - sA * cW)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
    C1092SWCC_LE_MUL_TAC `(cA * sW - sA * cW):real` `((&5 / &2) * cA + &3 * sA - uA) - &7 / &20` THEN
    SUBGOAL_THEN `ABT_upper cA sA uA vA aA (--sW) cW =
                  &3 * cW - (&5 / &2) * sW +
                  (cA * cW + sA * sW) * (vA + aA - (&3 * cA - (&5 / &2) * sA)) +
                  (cA * sW - sA * cW) * ((&5 / &2) * cA + &3 * sA - uA)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092SWCC_LT_MUL_TAC `(cA * cW + sA * sW):real`
      `(vA + aA - (&3 * cA - (&5 / &2) * sA)) - C1092SWS_allowance cA sA` THEN
    C1092SWCC_LIN_TAC;
    MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`] C1092SWA_BELOW) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1092SWCC_LIN_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `abs (cA * sW - sA * cW) = --(cA * sW - sA * cW)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    C1092SWCC_LE_MUL_TAC `--(cA * sW - sA * cW)` `(uA + aA - ((&5 / &2) * cA + &3 * sA)) - &1 / &200` THEN
    SUBGOAL_THEN `ABT_upper cA sA uA vA aA (--sW) cW =
                  &3 * cW - (&5 / &2) * sW +
                  (cA * cW + sA * sW) * (vA + aA - (&3 * cA - (&5 / &2) * sA)) -
                  (cA * sW - sA * cW) * (uA + aA - ((&5 / &2) * cA + &3 * sA))` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092SWCC_LT_MUL_TAC `(cA * cW + sA * sW):real`
      `(vA + aA - (&3 * cA - (&5 / &2) * sA)) - C1092SWS_allowance cA sA` THEN
    C1092SWCC_LIN_TAC]);;
