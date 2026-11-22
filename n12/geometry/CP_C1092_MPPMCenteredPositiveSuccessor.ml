(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCenteredPositiveSuccessor.lean        *)
(* (N12Compact.C1092MPPMCenteredPositive).  CENTERED-POSITIVE-INWARD §§3-5. *)
(* Conventions of MPPMCenteredPositiveData.ml: C = cC sC uC vC aC,           *)
(* E = cE sE uE vE aE, Input is c1092mcpd_input, Normal is c977cc_normal,    *)
(* NegativeSuccessor is c1092ifsu_negsucc, ABTransverse lower / upper are    *)
(* ABT_lower / ABT_upper, the OrdinaryNegativeHalfpoint Frame is            *)
(* c1092onh_frame, WallProfileScalars.half is C1092WPS_half.  Tag C1092CPS_. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCenteredPositiveData.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCenteredCaps.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessor.ml";;

let C1092CPS_LP hs = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false hs;;

(* Lean: successor_profile *)
let C1092CPS_SUCCESSOR_PROFILE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ &0 < cE /\ abs sE <= cE /\
     c1092mcpd_input cC sC uC vC aC cE sE uE vE aE
     ==> sE < &0 /\ c1092ifsu_negsucc cE sE uE vE aE /\
         &99 / &100 < cC /\ sC < &7 / &50 /\
         &1 + (cC * --sE + sC * cE) < cE - sE + (cC * --sE + sC * cE) * (vC + aC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092MCPD_CENTER_CAPS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092MCPD_SUCCESSOR_NEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  SUBGOAL_THEN `c977cc_normal cE (--sE)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN UNDISCH_TAC `abs sE <= cE` THEN
    UNDISCH_TAC `cE * cE + sE * sE = &1` THEN UNDISCH_TAC `sE < &0` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092onh_frame cC sC /\ c1092onh_frame cE (--sE)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092onh_frame] THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
      check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --sE /\ --sE <= cE` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `abs sE <= cE` THEN UNDISCH_TAC `sE < &0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `abs sE <= cE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092MCPD_SUCCESSOR_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092mcpd_successorFaces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092NPP_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092mcpd_input cC sC uC vC aC cE sE uE vE aE` THEN
  REWRITE_TAC[c1092mcpd_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  (* j > 0, and the C center gives 0 < uC + aC *)
  SUBGOAL_THEN `&0 < cC * --sE + sC * cE` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < uC + aC /\ uC < &0 /\ vC < &0 /\ &0 < vC + aC` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (cC * cE - sC * --sE) * (uC + aC)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the two supports *)
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                `cC * cE - sC * --sE`; `cC * --sE + sC * cE`] C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`]
    C1092WS_FORMULAS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `cE * cC + sE * sC = cC * cE - sC * --sE /\
                --cE * sC + sE * cC = --(cC * --sE + sC * cE)` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`;
               REAL_ARITH `&0 < x ==> max (--x) (&0) = &0`] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN DISCH_TAC THEN
  (* positive_axes *)
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092NPPT_POSITIVE_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(--vC <= ABT_lower cE sE uE vE aC sC (--cC))` (fun th -> REWRITE_TAC[th]) THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `&7 / &20`; `--(&7 / &20)`;
                  `sC:real`; `--cC`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cC * cC + sC * sC = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t -> t = `ABT_lower` || t = `ABT_upper`)) (concl th)
    then ALL_TAC else NO_TAC)) THEN
  (* sharpV, via the full G face capG *)
  SUBGOAL_THEN `vE + aC <= --sE - (&2 / &5) * cE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `uE + aC <= cE + (&2 / &5) * --sE` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~linside cE sE uE vE aC (&1) (--(&2 / &5))` THEN REWRITE_TAC[linside] THEN
      UNDISCH_TAC `linside cE sE uE vE aC (&2 / &5) (--(&1))` THEN REWRITE_TAC[linside] THEN
      STRIP_TAC THEN C1092CPS_LP [];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092POS_FIRST_EXIT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(cC * cE - sC * --sE) * (uE + aC) <= (cC * cE - sC * --sE) * (cE + (&2 / &5) * --sE) /\
                    (cC * --sE + sC * cE) * (vE + aC) <= (cC * --sE + sC * cE) * --sE /\
                    &0 <= (aC - &1) * ((cC * cE - sC * --sE) + (cC * --sE + sC * cE))`
        STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_LMUL) THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      C1092CPS_LP [];
      MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092POS_FIRST_TARGET) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(cC * --sE + sC * cE) * (vC + aC) <= (cC * --sE + sC * cE) * ((&7 / &20) * (cC + sC)) /\
                    &0 < (aC - &1) * (&1 + (cC * --sE + sC * cE))`
        STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LT_MUL] THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      C1092CPS_LP []];
    ALL_TAC] THEN
  (* necessary *)
  SUBGOAL_THEN `&1 + (cC * --sE + sC * cE) < cE - sE + (cC * --sE + sC * cE) * (vC + aC)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092POS_FINAL_SOURCE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(cC * cE - sC * --sE) * (uE + aC) <= (cC * cE - sC * --sE) * (cE + --sE) /\
                    (cC * --sE + sC * cE) * (vE + aC) <= (cC * --sE + sC * cE) * (--sE - (&2 / &5) * cE) /\
                    &0 <= (aC - &1) * ((cC * cE - sC * --sE) + (cC * --sE + sC * cE))`
        STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_LMUL) THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      C1092CPS_LP [];
      SUBGOAL_THEN `&0 < (aC - &1) * (&1 + (cC * --sE + sC * cE))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      C1092CPS_LP []];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`; `vC + aC`] C1092POS_SHALLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&99 / &100 < cC` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (&7 / &50 - sC) * (&7 / &50 + sC)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092ifsu_negsucc]);;

(* Lean: height_margin (private) *)
let C1092CPS_HEIGHT_MARGIN = prove
 (`forall c s d t H.
     c977cc_normal c s /\ c977cc_normal d t /\ &99 / &100 < c /\ s < &7 / &50 /\ &0 < t /\
     &157 / &843 < C1092WPS_half d t /\
     &1 + (c * t + s * d) < d + t + (c * t + s * d) * H
     ==> &93 / &500 + (&33 / &50) * s < H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFBS_HALF_IDENTITY) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092IFBS_HALF_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)))) THEN
  SUBGOAL_THEN `C1092WPS_half c s < &2 / &25` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&99 / &100 < c ==> &0 < &1 + c`; ASSUME `&99 / &100 < c`] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * C1092WPS_half c s <= s * &2 / &25` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `s * &2 / &25 = s * (&2 / &25)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * t <= s * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&1 + (&23 / &25) * s) * (&1 - (&93 / &500 + (&33 / &50) * s)) <=
      (c + s) * (&1 - (&93 / &500 + (&33 / &50) * s)) /\
    &0 <= s * (&1111 / &12500 - (&759 / &1250) * s)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - C1092WPS_half d t < (c + s) * (&1 - (&93 / &500 + (&33 / &50) * s))`
    ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `t * (&1 - C1092WPS_half d t) < t * ((c + s) * (&1 - (&93 / &500 + (&33 / &50) * s))) /\
    (t * (c + s)) * (&1 - (&93 / &500 + (&33 / &50) * s)) <=
      (c * t + s * d) * (&1 - (&93 / &500 + (&33 / &50) * s)) /\
    (c * t + s * d) * H <= (c * t + s * d) * (&93 / &500 + (&33 / &50) * s)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: bounds *)
let C1092CPS_BOUNDS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c977cc_normal cC sC /\ &0 < cE /\ abs sE <= cE /\
     c1092mcpd_input cC sC uC vC aC cE sE uE vE aE
     ==> &99 / &100 < cC /\ sC < &7 / &50 /\
         &93 / &500 + (&33 / &50) * sC < vC + aC /\
         uC + aC <= (&7 / &50) * cC - sC / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092CPS_SUCCESSOR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092IFCC_SUCCESSOR_SHARP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `c1092ifsu_negsucc cE sE uE vE aC` THEN REWRITE_TAC[c1092ifsu_negsucc] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&343 / &500`; `cE:real`; `--sE`] C1092IFSU_WIDTH_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C1092CPS_HEIGHT_MARGIN THEN
    MAP_EVERY EXISTS_TAC [`cC:real`; `cE:real`; `--sE`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092mcpd_input cC sC uC vC aC cE sE uE vE aC` THEN
  REWRITE_TAC[c1092mcpd_input; ldisj] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&7 / &50`; `--(&1 / &2)`]) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  UNDISCH_TAC `linside cC sC uC vC aC (&0) (&0)` THEN
  UNDISCH_TAC `linside cC sC uC vC aC (--(&1 / &100)) (--(&27 / &50))` THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;
