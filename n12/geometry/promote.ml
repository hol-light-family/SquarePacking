(* ========================================================================= *)
(* Phase 2: promoted owner budgets (Jatloe: Compact/Bridge/PromotedOwnerBudget).*)
(* If an exempt square j0 is known to own an auxiliary point of kind k, the   *)
(* budget counts j0 among the non-exempt squares.                             *)
(* ========================================================================= *)

needs "n12/phase1/step6.ml";;

let SQUARE_BUDGET_P = prove
 (`forall c1 c2 a b l r k i L j0 L0. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r /\
       k < 2 /\ i < 12 /\ owned (c1 i) (c2 i) (a i) (b i) l = set_of_list L /\
       j0 < 12 /\ ~(auxown k (c1 j0) (c2 j0) (a j0) (b j0) l = {}) /\
       owned (c1 j0) (c2 j0) (a j0) (b j0) l = set_of_list L0
       ==> CARD (auxown k (c1 i) (c2 i) (a i) (b i) l) +
           CARD (set_of_list (FILTER (\m. (~pairin (PKS k) (bitset m) \/ bitset m = set_of_list L0) /\
                                          ~(bitset m = set_of_list L)) r))
           <= 10`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\j. auxown k ((c1:num->real) j) (c2 j) (a j) (b j) l`;
                 `{j | pairin (PKS k) (owned ((c1:num->real) j) (c2 j) (a j) (b j) l) /\ ~(j = j0)}`; `i:num`]
                BUDGET_INDIV) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[AUXOWN_SUBSET10; AUXOWN_DISJ] THEN REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM] THEN
    X_GEN_TAC `j:num` THEN ASM_CASES_TAC `j:num = j0` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `k:num`; `j:num`] SQUARE_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MESON_TAC[CARD_CLAUSES; ARITH_RULE `~(1 <= 0)`];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `y = z ==> x + y <= 10 ==> x + z <= 10`) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `r:num list`;
                `\G. (~pairin (PKS k) G \/ G = set_of_list L0) /\ ~(G = set_of_list L)`] COUNT_ROW) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN
  ASM_CASES_TAC `j < 12` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `forall m. m < 12 ==> (owned (c1 j) (c2 j) (a j) (b j) l = owned (c1 m) (c2 m) (a m) (b m) l <=> j = m)`
    (fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j0:num` th)) THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC OWNED_INJ THEN
      MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN CONV_TAC TAUT);;
