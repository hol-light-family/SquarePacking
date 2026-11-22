(* ========================================================================= *)
(* Port of Compact/Geometry/C868UpperPoint.lean (Jatloe, N12-jatloe).         *)
(* Positive canonical lower-left square A and upper central square H: their  *)
(* separation forces H to contain the top auxiliary point (1.74,3).          *)
(* Normal: c977cc_normal; lower/upper: ABT_lower/ABT_upper;                  *)
(* C868CentralSeparation.positive: C868CSEP_POSITIVE;                        *)
(* C868UpperPointMargins.above/below/steep: C868UPM_ABOVE/BELOW/STEEP.       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C868CentralSeparation.ml";;
needs "n12/geometry/C868UpperPointMargins.ml";;
needs "n12/geometry/CentralPositiveTransverse.ml";;

(* Lean: point *)
let C868UP_POINT = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cA sA /\ c977cc_normal cH sH /\ aA = aH /\ &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ldisj cA sA uA vA aA cH sH uH vH aH
     ==> linside cH sH uH vH aH (&87 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`]
    C868CSEP_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aH`)) THEN
  PCT_NORMAL_TAC THEN
  ABT_SB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aH:real`]
    `&87 / &50` `&2` `--sH` `cH:real` THEN
  ABT_SB_TAC [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`]
    `&47 / &20` `&47 / &20` `--sA` `cA:real` THEN
  UNDISCH_TAC `linside cA sA uA vA aH (&87 / &50) (&2)` THEN
  UNDISCH_TAC `linside cH sH uH vH aH (&33 / &20) (&47 / &20)` THEN
  UNDISCH_TAC `linside cH sH uH vH aH (&47 / &20) (&47 / &20)` THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < cH /\ &0 < cA` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PRODLT_TAC `cH:real` `cA:real` THEN PCT_PROD_TAC `sH:real` `sA:real` THEN
  SUBGOAL_THEN `&0 < cH * cA + sH * sA` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PRODLT_TAC `cH * cA + sH * sA` `aH - &1` THEN
  let pp = MP_TAC(SPECL [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`;
                         `--sA`; `cA:real`] PCT_LOWER_PP) THEN
           ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC;
                           DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]
  and np = MP_TAC(SPECL [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`;
                         `--sA`; `cA:real`] CPTR_LOWER_NP) THEN
           ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC;
                           DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] in
  SUBGOAL_THEN `--sH * &87 / &50 + cH * &3 < vH + aH` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [RASM_ARITH_TAC;
    ASM_CASES_TAC `&0 <= sH * cA - cH * sA` THENL
    [MP_TAC(SPECL [`cH:real`; `sH:real`; `cA:real`; `sA:real`] C868UPM_ABOVE) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN pp THEN
     PCT_PROD_TAC `sH * cA - cH * sA` `(cH * &33 / &20 + sH * &47 / &20) - uH` THEN
     PCT_PROD_TAC `cH * cA + sH * sA` `(--sH * &87 / &50 + cH * &3) - (vH + aH)` THEN
     SUBGOAL_THEN `(sH * cA - cH * sA) * (cH * (&33 / &20) + sH * (&47 / &20)) +
                   (cH * cA + sH * sA) * (--sH * (&87 / &50) + cH * &3) =
                   &3 * cA - (&87 / &50) * sA -
                   (sH * cA - cH * sA) * ((&9 / &100) * cH + (&13 / &20) * sH)`
     ASSUME_TAC THENL
     [UNDISCH_TAC `cH * cH + sH * sH = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     RASM_ARITH_TAC;
     SUBGOAL_THEN `sH * cA - cH * sA <= &0` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
     MP_TAC(SPECL [`cH:real`; `sH:real`; `cA:real`; `sA:real`] C868UPM_BELOW) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC THEN np THEN
     PCT_PROD_TAC `--(sH * cA - cH * sA)` `(uH + aH) - (cH * &47 / &20 + sH * &47 / &20)` THEN
     PCT_PROD_TAC `cH * cA + sH * sA` `(--sH * &87 / &50 + cH * &3) - (vH + aH)` THEN
     SUBGOAL_THEN `(sH * cA - cH * sA) * (cH * (&47 / &20) + sH * (&47 / &20)) +
                   (cH * cA + sH * sA) * (--sH * (&87 / &50) + cH * &3) =
                   &3 * cA - (&87 / &50) * sA +
                   (sH * cA - cH * sA) * ((&61 / &100) * cH - (&13 / &20) * sH)`
     ASSUME_TAC THENL
     [UNDISCH_TAC `cH * cH + sH * sH = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     RASM_ARITH_TAC]]; ALL_TAC] THEN
  SUBGOAL_THEN `cH * &87 / &50 + sH * &3 < uH + aH` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&61 * cH < &65 * sH` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [RASM_ARITH_TAC;
    SUBGOAL_THEN `&61 * sA < &35 * cA` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    PCT_PROD_TAC `cA:real` `&10 * sH - &9 * cH` THEN
    PCT_PROD_TAC `cH:real` `&3 * cA - &5 * sA` THEN
    SUBGOAL_THEN `&0 < sH * cA - cH * sA` ASSUME_TAC THENL
    [RASM_ARITH_TAC; ALL_TAC] THEN
    pp THEN
    PCT_PROD_TAC `sH * cA - cH * sA` `(cH * &87 / &50 + sH * &3) - (uH + aH)` THEN
    PCT_PROD_TAC `cH * cA + sH * sA` `(--sH * &47 / &20 + cH * &47 / &20) - vH` THEN
    PCT_PRODLT_TAC `sH * cA - cH * sA` `aH - &1` THEN
    SUBGOAL_THEN
     `(&2 * cA - (&87 / &50) * sA) -
      ((sH * cA - cH * sA) * (cH * (&87 / &50) + sH * &3 - &1) +
       (cH * cA + sH * sA) * (--sH * (&47 / &20) + cH * (&47 / &20))) =
      cA * (sH - &7 / &20 - (&13 / &20) * sH pow 2 + (&61 / &100) * cH * sH) +
      sA * ((&61 / &100) * sH pow 2 + (&13 / &20) * cH * sH - cH)` ASSUME_TAC THENL
    [UNDISCH_TAC `cH * cH + sH * sH = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&61 * cH <= &65 * sH /\ &61 * sA <= &35 * cA` ASSUME_TAC THENL
    [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cH:real`; `sH:real`; `cA:real`; `sA:real`] C868UPM_STEEP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;
