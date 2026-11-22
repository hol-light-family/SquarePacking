(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ContinuousAnchorCenter.lean   *)
(* (namespace N12Compact.Completion.OtherCases.C1089.ContinuousAnchorCenter)*)
(* INWARD-EXTENDED-ANCHOR-CENTER, Theorem 1.  Normal: c977cc_normal;        *)
(* short_projections: WFP_SP; canonical_frame: CLF_CANONICAL_FRAME;         *)
(* ContinuousAnchorSupport.impossible: C1089CAP_IMPOSSIBLE.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousAnchorSupport.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: positive_impossible (private) *)
let C1089CAC_POSITIVE_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cC sC /\ &1 < aC /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cC sC uC vC aC (&1) (&2 / &5) /\
     ~linside cC sC uC vC aC (&2 / &5) (&1) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  MP_TAC(INST [`cC:real`,`c:real`; `sC:real`,`s:real`] (WFP_SP `&37 / &50` `&3 / &5`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`linside cC sC uC vC aC (&7 / &20) (&7 / &20)`;
                         `linside cC sC uC vC aC (&13 / &50) (&0)`;
                         `linside cC sC uC vC aC (&1) (&2 / &5)`] THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--sC + (&13 / &50) * cC <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `ldisj cC sC uC vC aC cW sW uW vW aW` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1`; `&13 / &50`]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vC + aC <= cC - (&2 / &5) * sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cC sC uC vC aC (&2 / &5) (&1)` THEN
    REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: point *)
let C1089CAC_POINT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aC /\ aC = aW /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     linside cC sC uC vC aC (&1) (&2 / &5) /\
     ~linside cC sC uC vC aC (&2 / &5) (&1) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\ &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> linside cC sC uC vC aC (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`cV:real`; `sV:real`; `uV:real`; `vV:real`; `aV:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ldisj cV sV uV vV aV cW sW uW vW aW` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cC sC uC vC aC cW sW uW vW aW` THEN REWRITE_TAC[ldisj] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) &&
      can (find_term ((=) `cV:real`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aV:real = aC`)) THEN
  ASM_CASES_TAC `&0 <= sV` THENL
   [SUBGOAL_THEN `false` CONTR_TAC THEN
    MP_TAC(SPECL [`cV:real`; `sV:real`; `uV:real`; `vV:real`; `aC:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
      C1089CAC_POSITIVE_IMPOSSIBLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `linside cV sV uV vV aC (&0) (&0)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= vV` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cV sV uV vV aC (&0) (&0)` THEN REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`linside cV sV uV vV aC (&0) (&13 / &50)`;
                           `linside cV sV uV vV aC (&13 / &50) (&0)`] THEN
    REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cV:real`; `sV:real`; `uV:real`; `vV:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    C1089CAP_IMPOSSIBLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;
