(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMElbowIsolation.lean                  *)
(* (N12Compact.C1092MPPMElbowIsolation).  NONORDINARY-ISOLATION Theorem 2    *)
(* on the actual two squares.  ElbowProfile.Profile: c1092ep_profile;        *)
(* kappa / sigma / F0..F3: c1092eis_*; upper / lower: ABT_upper / ABT_lower; *)
(* formulas, lower_pn, lower_nn: C1092WS_*; upper_nn: C1092MEA_UPPER_NN;     *)
(* upper_neg / lower_neg: C1092TFSU_UPPER_NEG / C1092TFSU_LOWER_NEG;         *)
(* clockwise D = (cD, sD, --vD - aD, uD, aD), inside_clockwise:              *)
(* C1092MEA_INSIDE_CLOCKWISE.                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMElbowIsolationScalars.ml";;
needs "n12/geometry/CP_C1092_ElbowProfile.ml";;
needs "n12/geometry/CP_C1092_MMMP_EndingAxes.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

let C1092MEI_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092MEI_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MEI_LIN_TAC; DISCH_TAC];;

let C1092MEI_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092MEI_LIN_TAC; DISCH_TAC];;

(* Lean: upper_pn *)
let C1092MEI_UPPER_PN = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ &0 <= d /\ e <= &0
     ==> ABT_upper c s u v a nx ny = d * (u + a) + e * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`;
               REAL_ARITH `e <= &0 ==> max e (&0) = &0`] THEN REAL_ARITH_TAC);;

(* Lean: upper_nonpositive *)
let C1092MEI_UPPER_NONPOSITIVE = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ d <= &0 /\ e <= &0
     ==> ABT_upper c s u v a nx ny = d * u + e * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `d <= &0 ==> max d (&0) = &0`;
               REAL_ARITH `e <= &0 ==> max e (&0) = &0`] THEN REAL_ARITH_TAC);;

(* Lean: positive_axes *)
let C1092MEI_POSITIVE_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     aC = aE /\ &0 < cC /\ &0 < sC /\ &0 < cE /\ &0 <= sE /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         ABT_upper cC sC uC vC aC sC (--cC) <= ABT_lower cE sE uE vE aE sC (--cC) \/
         ABT_upper cC sC uC vC aC cE sE <= uE \/
         ABT_upper cC sC uC vC aC sE (--cE) <= ABT_lower cE sE uE vE aE sE (--cE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  let qs = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
  and rs = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] in
  let dirs = [`cC:real`,`sC:real`; `--sC`,`cC:real`; `cE:real`,`sE:real`; `--sE`,`cE:real`] in
  ABT_ALL_SB_TAC [qs,(`--(&7 / &20)`,`--(&7 / &20)`); rs,(`&7 / &20`,`--(&7 / &20)`)] dirs THEN
  ABT_OWN_TAC qs THEN ABT_OWN_TAC rs THEN
  MP_TAC(REWRITE_RULE[REAL_NEG_NEG] (SPECL (qs @ [`--sC`; `cC:real`]) C1092TFSU_UPPER_NEG)) THEN
  MP_TAC(REWRITE_RULE[REAL_NEG_NEG] (SPECL (rs @ [`--sC`; `cC:real`]) C1092TFSU_LOWER_NEG)) THEN
  MP_TAC(REWRITE_RULE[REAL_NEG_NEG] (SPECL (qs @ [`--sE`; `cE:real`]) C1092TFSU_UPPER_NEG)) THEN
  MP_TAC(REWRITE_RULE[REAL_NEG_NEG] (SPECL (rs @ [`--sE`; `cE:real`]) C1092TFSU_LOWER_NEG)) THEN
  REPEAT DISCH_TAC THEN ABT_ARITH_TAC);;

(* Lean: impossible *)
let C1092MEI_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cD sD uD vD aD.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     &1 < aC /\ aC = aD /\
     c1092ep_profile cC sC uC vC aC /\ c1092ep_profile cD sD uD vD aD /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cD sD uD vD aD (--(&7 / &20)) (--(&7 / &20)) /\
     linside cD sD uD vD aD (--(&13 / &50)) (&0) /\
     (forall x y. ~(linside cC sC uC vC aC x y /\ linside cD sD uD vD aD y (--x)))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aD`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092ep_profile; c977cc_normal]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONJ_ASSOC]) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC o rev) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  (* E = clockwise D *)
  SUBGOAL_THEN `linside cD sD (--vD - aC) uD aC (&7 / &20) (--(&7 / &20)) /\
                linside cD sD (--vD - aC) uD aC (&0) (--(&13 / &50)) /\
                ldisj cC sC uC vC aC cD sD (--vD - aC) uD aC` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[C1092MEA_INSIDE_CLOCKWISE; ldisj; REAL_NEG_NEG; REAL_NEG_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cD:real`; `sD:real`; `--vD - aC`; `uD:real`; `aC:real`]
    C1092MEI_POSITIVE_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MEI_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `sC pow 2 + (--cC) pow 2 = &1 /\ sD pow 2 + (--cD) pow 2 = &1 /\ sC <= &7 / &25` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `cD * cD + sD * sD = &1` THEN REAL_ARITH_TAC;
      C1092MEI_LIN_TAC]; ALL_TAC] THEN
  (* the two orientation facts used for blocked transverse normals *)
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `&0`; `--(&1 / &2)`; `sC:real`; `--cC`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `--vD - aC`; `uD:real`; `aC:real`;
                `&0`; `--(&13 / &50)`; `sC:real`; `--cC`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `&0`; `--(&1 / &2)`; `sD:real`; `--cD`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `--vD - aC`; `uD:real`; `aC:real`;
                `&0`; `--(&13 / &50)`; `sD:real`; `--cD`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  (* kappa = cC * cD + sC * sD, sigma = cC * sD - sC * cD *)
  C1092MEI_LT_MUL_TAC `cC:real` `cD:real` THEN C1092MEI_LE_MUL_TAC `sC:real` `sD:real` THEN
  SUBGOAL_THEN `&0 < cC * cD + sC * sD` ASSUME_TAC THENL [C1092MEI_LIN_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [(* own *)
    ASM_CASES_TAC `&0 <= cC * sD - sC * cD` THENL
     [MP_TAC(SPECL [`cD:real`; `sD:real`; `--vD - aC`; `uD:real`; `aC:real`;
                    `cC:real`; `sC:real`; `cC * cD + sC * sD`; `--(cC * sD - sC * cD)`]
        C1092WS_LOWER_PN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MEI_LIN_TAC;
        DISCH_TAC] THEN
      C1092MEI_LE_MUL_TAC `cC * cD + sC * sD` `(cD - (&2 / &5) * sD - aC) - (--vD - aC)` THEN
      C1092MEI_LE_MUL_TAC `cC * sD - sC * cD` `uD - (--cD - (&2 / &5) * sD)` THEN
      C1092MEI_LT_MUL_TAC `aC - &1` `&1 + (cC * cD + sC * sD) + (cC * sD - sC * cD)` THEN
      MP_TAC(SPECL [`cC:real`; `sC:real`; `cD:real`; `sD:real`] C1092EIS_FIRST_NONNEGATIVE) THEN
      ASM_REWRITE_TAC[c1092eis_F0; c1092eis_kappa; c1092eis_sigma; c977cc_normal; REAL_POW_2] THEN
      DISCH_TAC THEN C1092MEI_LIN_TAC;
      MP_TAC(SPECL [`cD:real`; `sD:real`; `--vD - aC`; `uD:real`; `aC:real`;
                    `cC:real`; `sC:real`; `cC * cD + sC * sD`; `--(cC * sD - sC * cD)`]
        C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MEI_LIN_TAC;
        DISCH_TAC] THEN
      C1092MEI_LE_MUL_TAC `cC * cD + sC * sD` `(cD - (&2 / &5) * sD - aC) - (--vD - aC)` THEN
      C1092MEI_LE_MUL_TAC `--(cC * sD - sC * cD)` `(--(&13 / &50) * sD - aC) - uD` THEN
      C1092MEI_LT_MUL_TAC `aC - &1` `&1 + (cC * cD + sC * sD) - (cC * sD - sC * cD)` THEN
      SUBGOAL_THEN `cC * sD - sC * cD <= &0` ASSUME_TAC THENL
       [UNDISCH_TAC `~(&0 <= cC * sD - sC * cD)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`cC:real`; `sC:real`; `cD:real`; `sD:real`] C1092EIS_THIRD_NONNEGATIVE) THEN
      ASM_REWRITE_TAC[c1092eis_F2; c1092eis_kappa; c1092eis_sigma; c977cc_normal; REAL_POW_2] THEN
      DISCH_TAC THEN C1092MEI_LIN_TAC];
    (* blocked transverse normal of C *)
    C1092MEI_LIN_TAC;
    (* neighbor *)
    ASM_CASES_TAC `&0 <= cC * sD - sC * cD` THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cD:real`; `sD:real`; `cC * cD + sC * sD`; `cC * sD - sC * cD`]
        C1092MEA_UPPER_NN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MEI_LIN_TAC;
        DISCH_TAC] THEN
      C1092MEI_LE_MUL_TAC `cC * cD + sC * sD` `(uC + aC) - (aC - cC - (&2 / &5) * sC)` THEN
      C1092MEI_LE_MUL_TAC `cC * sD - sC * cD` `(vC + aC) - (aC + (&2 / &5) * sC - cC)` THEN
      C1092MEI_LT_MUL_TAC `aC - &1` `&1 + (cC * cD + sC * sD) + (cC * sD - sC * cD)` THEN
      MP_TAC(SPECL [`cC:real`; `sC:real`; `cD:real`; `sD:real`] C1092EIS_SECOND_NONNEGATIVE) THEN
      ASM_REWRITE_TAC[c1092eis_F1; c1092eis_kappa; c1092eis_sigma; c977cc_normal; REAL_POW_2] THEN
      DISCH_TAC THEN C1092MEI_LIN_TAC;
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cD:real`; `sD:real`; `cC * cD + sC * sD`; `cC * sD - sC * cD`]
        C1092MEI_UPPER_PN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MEI_LIN_TAC;
        DISCH_TAC] THEN
      C1092MEI_LE_MUL_TAC `cC * cD + sC * sD` `(uC + aC) - (aC - cC - (&2 / &5) * sC)` THEN
      C1092MEI_LE_MUL_TAC `--(cC * sD - sC * cD)` `((&7 / &20) * (cC + sC) - aC) - vC` THEN
      C1092MEI_LT_MUL_TAC `aC - &1` `&1 + (cC * cD + sC * sD) - (cC * sD - sC * cD)` THEN
      SUBGOAL_THEN `cC * sD - sC * cD <= &0` ASSUME_TAC THENL
       [UNDISCH_TAC `~(&0 <= cC * sD - sC * cD)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`cC:real`; `sC:real`; `cD:real`; `sD:real`] C1092EIS_FOURTH_NONNEGATIVE) THEN
      ASM_REWRITE_TAC[c1092eis_F3; c1092eis_kappa; c1092eis_sigma; c977cc_normal; REAL_POW_2] THEN
      DISCH_TAC THEN C1092MEI_LIN_TAC];
    (* blocked transverse normal of E *)
    C1092MEI_LIN_TAC]);;
