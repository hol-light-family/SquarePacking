(* ========================================================================= *)
(* Port of Compact/Geometry/BLLongitudinal.lean (N12Compact.BLLongitudinal). *)
(* Two original missing points eliminate L's remaining transverse separator.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/BLSeparation.ml";;

(* Lean: no_negative_transverse_cap *)
let BLL_NO_NEGATIVE_TRANSVERSE_CAP = prove
 (`forall cL sL uL vL aL.
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cL /\ sL <= &0 /\ abs sL <= cL /\ &1 < aL /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     vL + aL <= --sL * (&33 / &20) + cL * (&47 / &20)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= cL + sL` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `sL:real`; SQ_NONNEG `cL + sL`]
   [`cL <= &1`; `cL - sL <= &10 / &7`] THEN
  SUBGOAL_THEN
   `cL * (&19 / &25) + sL * (&187 / &100) <= uL \/
    --sL * (&19 / &25) + cL * (&187 / &100) <= vL`
  MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> false) ==> p \/ q`) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term ((=) `&19 / &25`)) (concl th))) THEN
    REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [SUBGOAL_THEN `uL + aL <= cL * (&33 / &20) + sL * (&33 / &20)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        can (find_term ((=) `&33 / &20`)) (concl th))) THEN
      REWRITE_TAC[] THEN RASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&100 < &89 * cL - &22 * sL` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC [SQ_NONNEG `&22 * cL + &89 * sL`];
    RASM_ARITH_TAC]);;

(* Lean: two_directed_alternatives *)
let BLL_TWO_DIRECTED_ALTERNATIVES = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     &0 < cL /\ abs sL <= cL /\ &1 < aL /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     aB = aL /\
     ldisj cB sB uB vB aB cL sL uL vL aL
     ==> C977CB_pairRadius cB sB aB cL sL aL <=
           cB * (lcx cB sB uB vB aB - lcx cL sL uL vL aL) +
           sB * (lcy cB sB uB vB aB - lcy cL sL uL vL aL) \/
         C977CB_pairRadius cL sL aL cB sB aB <=
           cL * (lcx cB sB uB vB aB - lcx cL sL uL vL aL) +
           sL * (lcy cB sB uB vB aB - lcy cL sL uL vL aL)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aB:real = aL`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aL:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
    BLS_THREE_DIRECTED_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~r ==> p \/ q \/ r ==> p \/ q`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `sL <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  (* radius *)
  SUBGOAL_THEN `C977CB_pairRadius cL sL aL cB sB aL =
                aL / &2 + tss_support_radius cB sB aL (--sL) cL` ASSUME_TAC THENL
   [REWRITE_TAC[C977CB_pairRadius; tss_support_radius;
      REAL_ARITH `abs(--sL * cB + cL * sB) = abs(cL * sB - sL * cB)`;
      REAL_ARITH `abs(-- --sL * sB + cL * cB) = abs(cL * cB + sL * sB)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aL:real`;
                `&33 / &20`; `&47 / &20`; `--sL`; `cL:real`] TSS_CLOSED_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] LCENTRE_COORDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
    BLL_NO_NEGATIVE_TRANSVERSE_CAP) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs(--sL * (&33 / &20 - lcx cB sB uB vB aL) +
                   cL * (&47 / &20 - lcy cB sB uB vB aL)) <=
               tss_support_radius cB sB aL (--sL) cL` THEN
  UNDISCH_TAC `C977CB_pairRadius cL sL aL cB sB aL <=
           --sL * (lcx cB sB uB vB aL - lcx cL sL uL vL aL) +
           cL * (lcy cB sB uB vB aL - lcy cL sL uL vL aL)` THEN
  UNDISCH_TAC `--sL * lcx cL sL uL vL aL + cL * lcy cL sL uL vL aL = vL + aL / &2` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
