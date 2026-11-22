(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NearCrossing.lean                   *)
(* (N12Compact.C1092MMMPNearCrossing).  The missing-center half-angle point  *)
(* with the compulsory .39 wall endpoint retained.  Normal: c977cc_normal;   *)
(* NearCrossingSupport.impossible: C1092NCSP_IMPOSSIBLE; centerY: lcy.       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_NearCrossingSupport.ml";;

let C1092NCR_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092NCR_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092NCR_LIN_TAC; DISCH_TAC];;

let C1092NCR_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092NCR_LIN_TAC; DISCH_TAC];;

(* Lean: point *)
let C1092NCR_POINT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW c s.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC = c /\ sC = --s /\ c977cc_normal c s /\ &1 < aC /\ aC = aW /\ &0 <= vC /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     linside cW sW uW vW aW (&1) (&39 / &100) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> linside cC sC uC vC aC (s / (&1 + c)) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let t = concl th in is_eq t && is_var(lhand t) &&
      mem (fst(dest_var(lhand t))) ["cC"; "sC"]))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> let t = concl th in not(is_neg t) && not(is_forall t) &&
       can (find_term ((=) `linside`)) t && can (find_term ((=) `uC:real`)) t) ths)) THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [C1092NCR_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [C1092NCR_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s / (&1 + c)) * (&1 + c) = s /\ &0 < s / (&1 + c)` MP_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `&0 < &1 + c` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SPEC_TAC(`s / (&1 + c)`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s * z = &1 - c` ASSUME_TAC THENL
   [SUBGOAL_THEN `(s * z) * (&1 + c) = (&1 - c) * (&1 + c)` MP_TAC THENL
     [UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN UNDISCH_TAC `&0 < &1 + c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092NCR_LE_MUL_TAC `c - &1` `c + &1` THEN C1092NCR_LT_MUL_TAC `s:real` `s:real` THEN
    C1092NCR_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z < &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092NCR_LE_MUL_TAC `z - &1 / &2` `&1 + c` THEN C1092NCR_LIN_TAC; ALL_TAC] THEN
  C1092NCR_LE_MUL_TAC `z:real` `&1 - c` THEN
  (* crossing *)
  SUBGOAL_THEN `uC < --z` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ABBREV_TAC `r0 = (&1 - z) * (&1 - z) / &2` THEN
    SUBGOAL_THEN `c - s * r0 = &1 - z /\ s + c * r0 = &1 - r0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r0" THEN
      UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN CONJ_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r0 /\ r0 <= &1 / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r0" THEN
      C1092NCR_LT_MUL_TAC `&1 - z` `&1 - z` THEN C1092NCR_LE_MUL_TAC `z:real` `&2 - z` THEN
      CONJ_TAC THEN C1092NCR_LIN_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `r0 <= &39 / &100` THENL
     [(* the near wall point would be owned *)
      SUBGOAL_THEN `linside c (--s) uC vC aC (&1) (&39 / &100)` ASSUME_TAC THENL
       [REWRITE_TAC[linside] THEN
        C1092NCR_LE_MUL_TAC `s:real` `&39 / &100 - r0` THEN
        REPEAT CONJ_TAC THEN C1092NCR_LIN_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[ldisj];
      ALL_TAC] THEN
    SUBGOAL_THEN `&39 / &100 < r0` ASSUME_TAC THENL
     [UNDISCH_TAC `~(r0 <= &39 / &100)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `linside c (--s) uC vC aC (&1) r0` ASSUME_TAC THENL
     [REWRITE_TAC[linside] THEN
      C1092NCR_LE_MUL_TAC `s:real` `&1 / &2 - r0` THEN
      C1092NCR_LT_MUL_TAC `c:real` `r0:real` THEN
      REPEAT CONJ_TAC THEN C1092NCR_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `z < &3 / &25` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092NCR_LE_MUL_TAC `z - &3 / &25` `&47 / &25 - z` THEN
      UNDISCH_TAC `(&1 - z) * (&1 - z) / &2 = r0` THEN
      UNDISCH_TAC `~(r0 <= &39 / &100)` THEN
      UNDISCH_TAC `&0 <= (z - &3 / &25) * (&47 / &25 - z)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `--s`; `uC:real`; `vC:real`; `aC:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`;
                  `c:real`; `s:real`; `z:real`; `r0:real`] C1092NCSP_IMPOSSIBLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092NCR_LIN_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092NCR_LIN_TAC);;
