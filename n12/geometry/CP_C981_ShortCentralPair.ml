(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShortCentralPair.lean                      *)
(* (N12Compact.C981CompletionShortCentralPair).  A northeast central owner   *)
(* and the actual southeast outward owner.  The Lean half turn reverse q is  *)
(* the square (c, s, 4(c+s)-u-a, 4(c-s)-v-a, a); canonical_frame is          *)
(* CLF_CANONICAL_FRAME.                                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_ShortOutwardLock.ml";;
needs "n12/geometry/CP_C981_NegativePair.ml";;

(* Lean: inside_reverse (private; reverse_c, reverse_s, reverse_side hold by *)
(* construction)                                                             *)
let C981SCP_INSIDE_REVERSE = prove
 (`forall c s u v a x y.
     linside c s (&4 * (c + s) - u - a) (&4 * (c - s) - v - a) a x y <=>
     linside c s u v a (&4 - x) (&4 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let C981SCP_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &0 < cC /\ sC <= &0 /\ abs sC <= cC /\ &1 < aC /\ aC = aB /\
     linside cC sC uC vC aC (&2) (&2) /\
     linside cC sC uC vC aC (&2) (&5 / &2) /\
     linside cC sC uC vC aC (&47 / &20) (&47 / &20) /\
     ~linside cC sC uC vC aC (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&8 / &5) /\
     ~linside cB sB uB vB aB (&3) (&1) /\
     ~linside cB sB uB vB aB (&1543 / &500) (&2) /\
     ~linside cB sB uB vB aB (&113 / &50) (&2) /\
     ~linside cB sB uB vB aB (&12 / &5) (&1) /\
     (forall z. &113 / &50 <= z /\ z <= &273 / &100 ==> ~linside cB sB uB vB aB z (&1)) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cD:real` (X_CHOOSE_THEN `sD:real` (X_CHOOSE_THEN `uD:real`
    (X_CHOOSE_THEN `vD:real` (X_CHOOSE_THEN `aD:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aB`)) THEN
  ASM_CASES_TAC `&0 <= sD` THENL
  [MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aB:real`]
     C981SOL_NONNEGATIVE_IMPOSSIBLE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
   ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`;
                `&4 * (cC + sC) - uC - aB`; `&4 * (cC - sC) - vC - aB`; `aB:real`;
                `cD:real`; `sD:real`;
                `&4 * (cD + sD) - uD - aB`; `&4 * (cD - sD) - vD - aB`; `aB:real`;
                `--sC:real`; `--sD:real`] C981NPR_IMPOSSIBLE) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REWRITE_TAC[C981SCP_INSIDE_REVERSE; ldisj; c977cc_normal; REAL_NEG_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG;
    REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC);;
