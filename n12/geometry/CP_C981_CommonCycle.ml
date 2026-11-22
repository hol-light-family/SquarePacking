(* ========================================================================= *)
(* Port of Compact/Completion/C981/CommonCycle.lean                           *)
(* (N12Compact.C981CompletionCommonCycle).  Shared all-orientation ending    *)
(* for the eight common C981 rows.  The Lean rotate q (turn^3 o pullSwap o   *)
(* pullY) is the 5-tuple (c, s, 4c - v - a, u - 4s, a) (C981CC_INSIDE_ROTATE).*)
(* canonical_frame is CLF_CANONICAL_FRAME.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_UpperPoint.ml";;
needs "n12/geometry/CP_C981_CentralPositivePoint.ml";;
needs "n12/geometry/CP_C981_NegativePair.ml";;
needs "n12/geometry/CP_C981_SteepPositivePair.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: inside_rotate (private; rotate_c, rotate_s, rotate_side hold by    *)
(* construction)                                                             *)
let C981CC_INSIDE_ROTATE = prove
 (`forall c s u v a x y.
     linside c s (&4 * c - v - a) (u - &4 * s) a x y <=> linside c s u v a y (&4 - x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* replace a square by its canonical frame in all assumptions *)
let C981CC_FRAME_TAC sq names =
  let [c;s;u;v;a] = sq and [c';s';u';v';a'] = names in
  MP_TAC(SPECL sq CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN c' (X_CHOOSE_THEN s' (X_CHOOSE_THEN u'
    (X_CHOOSE_THEN v' (X_CHOOSE_THEN a' STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = mk_eq(a',a))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC);;

(* Lean: impossible *)
let C981CC_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\
     linside cC sC uC vC aC (&2) (&2) /\ linside cC sC uC vC aC (&3 / &2) (&2) /\
     linside cC sC uC vC aC (&2) (&5 / &2) /\ linside cC sC uC vC aC (&33 / &20) (&47 / &20) /\
     ~linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     (forall y. &113 / &50 <= y ==> y <= &14 / &5 ==> ~linside cC sC uC vC aC (&1) y) /\
     linside cB sB uB vB aB (&47 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&113 / &50) (&3) /\ linside cB sB uB vB aB (&12 / &5) (&3) /\
     ~linside cB sB uB vB aB (&2) (&12 / &5) /\ ~linside cB sB uB vB aB (&2) (&3) /\
     ~linside cB sB uB vB aB (&3) (&12 / &5) /\ ~linside cB sB uB vB aB (&3) (&3) /\
     ~linside cB sB uB vB aB (&3) (&64 / &25) /\ ~linside cB sB uB vB aB (&3) (&5 / &2) /\
     ~linside cB sB uB vB aB (&2) (&1543 / &500) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  C981CC_FRAME_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
                   [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  C981CC_FRAME_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`]
                   [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aC:real`] C981UP_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `&0 <= sA` THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aC:real`] C981CPP_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cA (--sA)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      is_real_rel(rand(concl th)) || can (term_match [] `--x <= y /\ y <= x`) (concl th)))) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ldisj cA sA (&4 * cA - vA - aC) (uA - &4 * sA) aC
                      cD sD (&4 * cD - vD - aC) (uD - &4 * sD) aC` ASSUME_TAC THENL
   [REWRITE_TAC[ldisj; C981CC_INSIDE_ROTATE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sD` THENL
   [MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aC:real`] C981UP_POSITIVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `c977cc_normal cD sD` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV (REWRITE_RULE[C981CC_INSIDE_ROTATE]
      (SPECL [`cA:real`; `sA:real`; `&4 * cA - vA - aC`; `uA - &4 * sA`; `aC:real`;
                  `cD:real`; `sD:real`; `&4 * cD - vD - aC`; `uD - &4 * sD`; `aC:real`;
                  `--sA:real`] C981SPP_IMPOSSIBLE))) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> false`) THEN
    ASM_SIMP_TAC[REAL_NEG_NEG; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cD (--sD)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      is_real_rel(rand(concl th)) || can (term_match [] `--x <= y /\ y <= x`) (concl th)))) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV (REWRITE_RULE[C981CC_INSIDE_ROTATE]
      (SPECL [`cA:real`; `sA:real`; `&4 * cA - vA - aC`; `uA - &4 * sA`; `aC:real`;
                `cD:real`; `sD:real`; `&4 * cD - vD - aC`; `uD - &4 * sD`; `aC:real`;
                `--sA:real`; `--sD:real`] C981NPR_IMPOSSIBLE))) THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> false`) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;
