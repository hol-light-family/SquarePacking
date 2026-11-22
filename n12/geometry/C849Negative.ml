(* ========================================================================= *)
(* Port of Compact/Geometry/C849Negative.lean (N12Compact.C849Negative).     *)
(* The complete canonical negative-B sector.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C849NegativeLongitudinal.ml";;
needs "n12/geometry/C849NegativeSupport.ml";;
needs "n12/geometry/C849NegativeCorner.ml";;

(* Lean: transverse_impossible (private) *)
let C849N_TRANSVERSE_IMPOSSIBLE = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cB /\ sB <= &0 /\ --sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     &1 < aB /\ aB = aL /\
     lcont cL sL uL vL aL /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     --sL * (&19 / &25) + cL * (&187 / &100) <= vL /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     aB * (cB - sB) + &4 * sB <= uB /\
     (uB + aB <= (&113 / &50) * cB + &3 * sB \/
      vB + aB <= --(&113 / &50) * sB + &3 * cB) /\
     ABT_upper cL sL uL vL aL (--sB) cB <= vB
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aL`)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C849NL_LIN_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside; lcx]) THEN
  MP_TAC(SPECL [`aB:real`; `cB:real`; `--sB`; `cL:real`; `sL:real`; `uL:real`; `vL:real`;
                `ABT_upper cL sL uL vL aB (--sB) cB`] C849NS_SUPPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN TRY C849NL_LIN_TAC THEN
    REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL [C849NL_LIN_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C849NL_LE_MUL_TAC `aB - &1` `&1 + cB + --sB` THEN
    SUBGOAL_THEN `&50 / &63 <= cB` ASSUME_TAC THENL [C849NL_LIN_TAC; ALL_TAC] THEN
    C849NL_LE_MUL_TAC `--sB - (&4 / &5) * cB` `--sB + (&4 / &5) * cB` THEN
    NLIN_TAC [SQ_NONNEG `cB - &50 / &63`];
    NLIN_FACTS_TAC [SQ_NONNEG `cB + sB`; SQ_NONNEG `cB - --sB - &10 / &7`]
     [`cB - sB <= &10 / &7`] THEN
    C849NL_LIN_TAC]);;

(* Lean: impossible *)
let C849N_IMPOSSIBLE = prove
 (`forall cB sB uB vB aB cL sL uL vL aL cE sE uE vE aE.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cE * cE + sE * sE = &1 /\ &0 < aE /\
     &0 < cB /\ sB <= &0 /\ --sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     &1 < aB /\ aB <= &1001 / &1000 /\ aB = aL /\ aE = aB /\
     lcont cL sL uL vL aL /\ lcont cE sE uE vE aE /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     ~linside cB sB uB vB aB (&2) (&5 / &2) /\
     ~linside cB sB uB vB aB (&113 / &50) (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     linside cE sE uE vE aE (&1) (&1543 / &500) /\
     linside cE sE uE vE aE (&457 / &500) (&3) /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cB sB uB vB aB cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aL`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aB`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aB:real`] C849NC_LOWER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C849NP_RIGHT_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C849NP_UPPER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] C849NBL_ALTERNATIVES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`]
      C849N_TRANSVERSE_IMPOSSIBLE);
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`]
      C849NL_IMPOSSIBLE)] THEN
  ASM_REWRITE_TAC[]);;
