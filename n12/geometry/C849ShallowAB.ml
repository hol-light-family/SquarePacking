(* ========================================================================= *)
(* Port of Compact/Geometry/C849ShallowAB.lean (N12Compact.C849ShallowAB).   *)
(* The complementary shallow positive-B sector.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C849SteepAB.ml";;
needs "n12/geometry/C849ShallowMargins.ml";;

let C849SHAB_LIN_TAC = NLIN_TAC ~deg2:false [];;

(* helpers: scalar facts used inside in_frame *)
let C849SHAB_AUX = prove
 (`forall c s. c * c + s * s = &1 /\ &0 <= c /\ &0 <= s
         ==> (&7 / &10) * (c + s) <= &1 /\ (s <= c ==> s <= &71 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c + s - &10 / &7`];
    DISCH_TAC THEN NLIN_FACTS_TAC [] [`&0 <= (c - s) * (c + s)`] THEN
    NLIN_TAC [SQ_NONNEG `s - &71 / &100`]]);;

(* Lean: in_frame *)
let C849SHAB_IN_FRAME = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &0 < cA /\ &0 <= sA /\ &0 < cB /\ &0 <= sB /\
     &3 * cB <= &7 * sB /\ sB <= (&4 / &5) * cB /\
     aA = aB /\ &1 < aB /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aB`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LINSIDE_CLOSED] THEN C849SHAB_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`]
    C849SAB_FACE_MODES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`; `&33 / &20`; `&47 / &20`]
    C849SAB_COMPOSE) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `cA:real`; `sA:real`; `&33 / &20`; `&47 / &20`]
    C849SAB_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C849SAB_LT_MUL_TAC `cB:real` `cA:real` THEN C849SAB_LE_MUL_TAC `sB:real` `sA:real` THEN
  SUBGOAL_THEN `&0 < cB * cA + sB * sA` ASSUME_TAC THENL [C849SHAB_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cB * cA + sB * sA` ASSUME_TAC THENL [C849SHAB_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`; `cB:real`; `sB:real`]
    C849SAB_UPPER_FORMULA) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C849SAB_LOWER_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `cB * sA - sB * cA <= &0 ==> sA <= cA` ASSUME_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C849SAB_LE_MUL_TAC `cA:real` `cB - sB` THEN C849SAB_LT_MUL_TAC `cB:real` `sA - cA` THEN
    C849SHAB_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] C849SHAB_AUX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C849SHAB_LIN_TAC; STRIP_TAC] THEN
  C849SAB_LT_MUL_TAC `aB - &1` `cB * cA + sB * sA` THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `&33 / &20`; `&47 / &20`; `--sA`; `cA:real`] ABT_CLOSED_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside]) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
    is_disj(concl th) && is_conj(lhand(concl th)))) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `vB:real`)) (lhand(concl th)))) THEN
  ASM_CASES_TAC `&0 <= cB * sA - sB * cA` THEN
  (SUBGOAL_THEN `abs(cB * sA - sB * cA) = if &0 <= cB * sA - sB * cA
                   then cB * sA - sB * cA else --(cB * sA - sB * cA)` MP_TAC THENL
    [REAL_ARITH_TAC;
     ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) THENL
   [(* mode 1, axis B, e >= 0 *)
    C849SAB_LE_MUL_TAC `cB * sA - sB * cA` `uA - (cA * &33 / &20 + sA * &47 / &20)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `vA - (--sA * &47 / &20 + cA * &33 / &20)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `&1 - (&7 / &10) * (cA + sA)` THEN
    C849SAB_LE_MUL_TAC `cB * sA - sB * cA` `aB:real` THEN
    C849SHAB_LIN_TAC;
    (* mode 1, axis B, e < 0 *)
    C849SAB_LE_MUL_TAC `--(cB * sA - sB * cA)` `cA * &2 + sA * &113 / &50 - uA` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `vA - (--sA * &47 / &20 + cA * &33 / &20)` THEN
    C849SAB_MARGIN_TAC C849SHM_LOWERV_B_NEG THEN C849SHAB_LIN_TAC;
    (* mode 1, axis A *)
    C849SHAB_LIN_TAC;
    C849SHAB_LIN_TAC;
    (* mode 2, axis B, e >= 0 *)
    C849SAB_LE_MUL_TAC `cB * sA - sB * cA` `uA - (cA * &47 / &20 + sA * &33 / &20)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `vA - (--sA * &3 + cA * &12 / &5)` THEN
    C849SAB_LT_MUL_TAC `aB - &1` `(cB * cA + sB * sA) + (cB * sA - sB * cA)` THEN
    C849SAB_MARGIN_TAC C849SHM_LOWERU_B_POS THEN C849SHAB_LIN_TAC;
    (* mode 2, axis B, e < 0 *)
    SUBGOAL_THEN `sA <= cA` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN C849SHAB_LIN_TAC; ALL_TAC] THEN
    C849SAB_LE_MUL_TAC `--(cB * sA - sB * cA)` `cA * &2 + sA * &113 / &50 - uA` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `vA - (--sA * &3 + cA * &12 / &5)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `(&3 / &4) * cA - (&13 / &20) * sA` THEN
    C849SAB_MARGIN_TAC C849SHM_LOWERV_B_NEG THEN C849SHAB_LIN_TAC;
    (* mode 2, axis A, e >= 0 *)
    C849SAB_LE_MUL_TAC `cB * sA - sB * cA` `uB + aB - (cB * &2 + sB * &1543 / &500)` THEN
    C849SAB_LE_MUL_TAC `cB * cA + sB * sA` `--sB * &33 / &20 + cB * &47 / &20 - vB` THEN
    C849SAB_MARGIN_TAC C849SHM_LOWERU_A_POS THEN C849SHAB_LIN_TAC;
    (* mode 2, axis A, e < 0 *)
    SUBGOAL_THEN `sA <= cA` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN C849SHAB_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sA <= &71 / &100` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    C849SHAB_LIN_TAC]);;
