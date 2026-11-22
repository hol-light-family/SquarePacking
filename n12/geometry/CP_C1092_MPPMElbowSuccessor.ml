(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMElbowSuccessor.lean                  *)
(* (N12Compact.C1092MPPMElbowSuccessor).  ELBOW-SUCCESSOR Theorem 1.         *)
(* Profile: c1092ep_profile; kappa / sigma / F1 / F3: c1092eis_*;            *)
(* ElbowSuccessorScalars: C1092ESS_*; positive_axes / upper_pn /             *)
(* upper_nonpositive: C1092MEI_*; lower_pn / lower_nn / formulas: C1092WS_*; *)
(* upper_nn: C1092MEA_UPPER_NN; ClosedFrames.canonical_frame:                *)
(* CLF_CANONICAL_FRAME.                                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMElbowIsolation.ml";;
needs "n12/geometry/CP_C1092_MPPMElbowSuccessorScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C1092MES_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MES_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MES_LIN_TAC; DISCH_TAC];;

let C1092MES_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MES_LIN_TAC; DISCH_TAC];;

let C1092MES_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MES_LIN_TAC;;

(* use a scalar lemma C1092ESS_* / C1092EIS_* about (cC,sC,cE,sE) *)
let C1092MES_SCALAR_TAC th defs =
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] th) THEN
  ASM_REWRITE_TAC(defs @ [c1092eis_kappa; c1092eis_sigma; c977cc_normal; REAL_POW_2]) THEN
  DISCH_TAC;;

let C1092MES_FORMULA_TAC th args =
  MP_TAC(SPECL args th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    (fun (asl,w as g) -> if is_eq w then
       (REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN C1092MES_LIN_TAC) g
     else C1092MES_LIN_TAC g);
    DISCH_TAC];;

let C1092MES_CSQ = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MES_ESQ = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`];;

(* Lean: nonnegative_impossible *)
let C1092MES_NONNEGATIVE_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c1092ep_profile cC sC uC vC aC /\ c977cc_normal cE sE /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
     ~linside cE sE uE vE aE (&1) (--(&2 / &5)) /\
     ~linside cE sE uE vE aE (&1) (--(&1)) /\
     ~linside cE sE uE vE aE (&0) (--(&543 / &500)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092ep_profile]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC o rev) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  MP_TAC(SPECL (C1092MES_CSQ @ C1092MES_ESQ) C1092MEI_POSITIVE_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MES_LIN_TAC;
    DISCH_TAC] THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> let t = concl th in not(is_neg t) && not(is_forall t) &&
       can (find_term ((=) `linside`)) t) ths)) THEN
  SUBGOAL_THEN `uE + aC <= cE - (&2 / &5) * sE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MES_MISS_TAC `~linside cE sE uE vE aC (&1) (--(&2 / &5))`; ALL_TAC] THEN
  SUBGOAL_THEN `sC <= &7 / &25 /\
     (cC * cE + sC * sE) * (cC + sC) + (cC * sE - sC * cE) * (cC - sC) = cE + sE`
     STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [C1092MES_LIN_TAC;
      UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  C1092MES_LT_MUL_TAC `cC:real` `cE:real` THEN C1092MES_LE_MUL_TAC `sC:real` `sE:real` THEN
  SUBGOAL_THEN `&0 < cC * cE + sC * sE` ASSUME_TAC THENL [C1092MES_LIN_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [(* own *)
    ASM_CASES_TAC `&0 <= cC * sE - sC * cE` THENL
     [C1092MES_FORMULA_TAC C1092WS_LOWER_PN (C1092MES_ESQ @
        [`cC:real`; `sC:real`; `cC * cE + sC * sE`; `--(cC * sE - sC * cE)`]) THEN
      C1092MES_LE_MUL_TAC `cC * cE + sC * sE` `(cE - (&2 / &5) * sE - aC) - uE` THEN
      C1092MES_LE_MUL_TAC `cC * sE - sC * cE` `(vE + aC) + (&7 / &20) * (cE + sE)` THEN
      C1092MES_LT_MUL_TAC `aC - &1` `&1 + (cC * cE + sC * sE)` THEN
      C1092MES_SCALAR_TAC C1092ESS_OWN_AFTER [] THEN C1092MES_LIN_TAC;
      SUBGOAL_THEN `cC * sE - sC * cE <= &0` ASSUME_TAC THENL
       [UNDISCH_TAC `~(&0 <= cC * sE - sC * cE)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      C1092MES_FORMULA_TAC C1092WS_LOWER_NN (C1092MES_ESQ @
        [`cC:real`; `sC:real`; `cC * cE + sC * sE`; `--(cC * sE - sC * cE)`]) THEN
      C1092MES_LE_MUL_TAC `cC * cE + sC * sE` `(cE - (&2 / &5) * sE - aC) - uE` THEN
      C1092MES_LE_MUL_TAC `--(cC * sE - sC * cE)` `(--cE - (&2 / &5) * sE) - vE` THEN
      C1092MES_LT_MUL_TAC `aC - &1` `&1 + (cC * cE + sC * sE)` THEN
      C1092MES_SCALAR_TAC C1092ESS_OWN_BEFORE [] THEN C1092MES_LIN_TAC];
    (* transverse normal of C *)
    C1092MES_FORMULA_TAC C1092MEI_UPPER_NONPOSITIVE (C1092MES_CSQ @
      [`sC:real`; `--cC`; `&0`; `--(&1)`]) THEN
    MP_TAC(SPECL (C1092MES_ESQ @ [`&7 / &20`; `--(&7 / &20)`; `sC:real`; `--cC`])
      ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN UNDISCH_TAC `cC * cC + sC * sC = &1` THEN
      REAL_ARITH_TAC; STRIP_TAC] THEN
    C1092MES_LIN_TAC;
    (* neighbor along E *)
    ASM_CASES_TAC `&0 <= cC * sE - sC * cE` THENL
     [C1092MES_FORMULA_TAC C1092MEA_UPPER_NN (C1092MES_CSQ @
        [`cE:real`; `sE:real`; `cC * cE + sC * sE`; `cC * sE - sC * cE`]) THEN
      C1092MES_LE_MUL_TAC `cC * cE + sC * sE` `(uC + aC) - (aC - cC - (&2 / &5) * sC)` THEN
      C1092MES_LE_MUL_TAC `cC * sE - sC * cE` `(vC + aC) - (aC + (&2 / &5) * sC - cC)` THEN
      C1092MES_LT_MUL_TAC `aC - &1` `&1 + (cC * cE + sC * sE) + (cC * sE - sC * cE)` THEN
      C1092MES_SCALAR_TAC C1092EIS_SECOND_NONNEGATIVE [c1092eis_F1] THEN C1092MES_LIN_TAC;
      SUBGOAL_THEN `cC * sE - sC * cE <= &0` ASSUME_TAC THENL
       [UNDISCH_TAC `~(&0 <= cC * sE - sC * cE)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      C1092MES_FORMULA_TAC C1092MEI_UPPER_PN (C1092MES_CSQ @
        [`cE:real`; `sE:real`; `cC * cE + sC * sE`; `cC * sE - sC * cE`]) THEN
      C1092MES_LE_MUL_TAC `cC * cE + sC * sE` `(uC + aC) - (aC - cC - (&2 / &5) * sC)` THEN
      C1092MES_LE_MUL_TAC `--(cC * sE - sC * cE)` `((&7 / &20) * (cC + sC) - aC) - vC` THEN
      C1092MES_LT_MUL_TAC `aC - &1` `&1 + (cC * cE + sC * sE) - (cC * sE - sC * cE)` THEN
      C1092MES_SCALAR_TAC C1092EIS_FOURTH_NONNEGATIVE [c1092eis_F3] THEN C1092MES_LIN_TAC];
    (* transverse normal of E *)
    MP_TAC(SPECL (C1092MES_ESQ @ [`&7 / &20`; `--(&7 / &20)`; `sE:real`; `--cE`])
      ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN UNDISCH_TAC `cE * cE + sE * sE = &1` THEN
      REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_CASES_TAC `&0 <= cC * sE - sC * cE` THENL
     [C1092MES_FORMULA_TAC C1092MEI_UPPER_PN (C1092MES_CSQ @
        [`sE:real`; `--cE`; `cC * sE - sC * cE`; `--(cC * cE + sC * sE)`]) THEN
      C1092MES_LE_MUL_TAC `cC * sE - sC * cE` `(uC + aC) - (aC - cC - (&2 / &5) * sC)` THEN
      C1092MES_LE_MUL_TAC `cC * cE + sC * sE` `((&7 / &20) * (cC + sC) - aC) - vC` THEN
      ASM_CASES_TAC `uE + aC <= cE - sE` THENL
       [SUBGOAL_THEN `&130 * sE < &43 * cE` ASSUME_TAC THENL
         [ASM_CASES_TAC `--(&543 / &500) * sE <= uE` THENL
           [MATCH_MP_TAC C1092ESS_NARROW_WIDTH THEN ASM_REWRITE_TAC[] THEN
            C1092MES_LIN_TAC;
            SUBGOAL_THEN `--(&543 / &500) * cE <= vE` ASSUME_TAC THENL
             [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
              SUBGOAL_THEN `uE < --(&543 / &500) * sE` ASSUME_TAC THENL
               [UNDISCH_TAC `~(--(&543 / &500) * sE <= uE)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
              C1092MES_MISS_TAC `~linside cE sE uE vE aC (&0) (--(&543 / &500))`;
              ALL_TAC] THEN
            C1092MES_LIN_TAC];
          ALL_TAC] THEN
        MP_TAC(SPECL [`cE:real`; `sE:real`] C1092ESS_CORNER_ANGLE) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        C1092MES_SCALAR_TAC C1092ESS_TRANSVERSE_AFTER_SMALL [] THEN
        C1092MES_LT_MUL_TAC `aC - &1` `(cC * cE + sC * sE) + (cC * sE - sC * cE)` THEN
        C1092MES_LIN_TAC;
        SUBGOAL_THEN `--cE - sE <= vE` ASSUME_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          SUBGOAL_THEN `cE - sE < uE + aC` ASSUME_TAC THENL
           [UNDISCH_TAC `~(uE + aC <= cE - sE)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
          C1092MES_MISS_TAC `~linside cE sE uE vE aC (&1) (--(&1))`; ALL_TAC] THEN
        C1092MES_FORMULA_TAC C1092WS_LOWER_PN (C1092MES_ESQ @
          [`sE:real`; `--cE`; `&0`; `--(&1)`]) THEN
        C1092MES_SCALAR_TAC C1092ESS_TRANSVERSE_CORNER [] THEN
        C1092MES_LT_MUL_TAC `aC - &1` `&1 + (cC * cE + sC * sE) + (cC * sE - sC * cE)` THEN
        C1092MES_LIN_TAC];
      SUBGOAL_THEN `cC * sE - sC * cE <= &0` ASSUME_TAC THENL
       [UNDISCH_TAC `~(&0 <= cC * sE - sC * cE)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      C1092MES_FORMULA_TAC C1092MEI_UPPER_NONPOSITIVE (C1092MES_CSQ @
        [`sE:real`; `--cE`; `cC * sE - sC * cE`; `--(cC * cE + sC * sE)`]) THEN
      C1092MES_LE_MUL_TAC `--(cC * sE - sC * cE)` `(--(&13 / &50) * sC - aC) - uC` THEN
      C1092MES_LE_MUL_TAC `cC * cE + sC * sE` `((&7 / &20) * (cC + sC) - aC) - vC` THEN
      C1092MES_LT_MUL_TAC `aC - &1` `(cC * cE + sC * sE) - (cC * sE - sC * cE)` THEN
      C1092MES_SCALAR_TAC C1092ESS_TRANSVERSE_BEFORE [] THEN
      C1092MES_LIN_TAC]]);;

(* Lean: negative_successor *)
let C1092MES_NEGATIVE_SUCCESSOR = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c1092ep_profile cC sC uC vC aC /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
     ~linside cE sE uE vE aE (&1) (--(&2 / &5)) /\
     ~linside cE sE uE vE aE (&1) (--(&1)) /\
     ~linside cE sE uE vE aE (&0) (--(&543 / &500)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> exists cF sF uF vF aF. cF * cF + sF * sF = &1 /\ &0 < aF /\ aF = aE /\
           (forall x y. linside cF sF uF vF aF x y <=> linside cE sE uE vE aE x y) /\
           c977cc_normal cF (--sF) /\ sF < &0 /\
           ~linside cE sE uE vE aE (&0) (--(&13 / &50))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL C1092MES_ESQ CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real`
    (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = aC`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL (C1092MES_CSQ @ [`c:real`; `s:real`; `u:real`; `v:real`; `aC:real`])
      C1092MES_NONNEGATIVE_IMPOSSIBLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ldisj; c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_ABS_BOUNDS] o
    check (fun th -> concl th = `abs s <= c`)) THEN
  SUBGOAL_THEN `~linside cE sE uE vE aC (&0) (--(&13 / &50))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `linside c s u v aC (&0) (--(&13 / &50)) /\ linside c s u v aC (&13 / &50) (--(&1)) /\ linside c s u v aC (&2 / &5) (--(&1))` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[linside] THEN STRIP_TAC THEN
    SUBGOAL_THEN `linside c s u v aC (&0) (--(&1 / &2))` MP_TAC THENL
     [REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MES_LIN_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092ep_profile]) THEN
    POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC o rev) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `aC:real`] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC);;
