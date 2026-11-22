(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/SouthwestPoint.lean                *)
(* (N12Compact.CommonCases.SouthwestPoint).  Three owned anchors and four    *)
(* singleton exclusions force the near-center point (39/20,39/20).           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let CCSWP_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside; lclosed; REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;;

(* turnFrame^3 (pullSwap r) as a 5-tuple *)
let CCSWP_SWAPPED_INSIDE = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive (private) *)
let CCSWP_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&2) (&87 / &50) /\
      linside c s u v a (&87 / &50) (&2) /\
      ~linside c s u v a (&1) (&33 / &20) /\
      ~linside c s u v a (&87 / &50) (&1)
      ==> linside c s u v a (&39 / &20) (&39 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&19 / &20` `&3 / &10`) THEN
  MP_TAC(WFP_SP `--(&37 / &50)` `&13 / &20`) THEN
  MP_TAC(WFP_SP `&21 / &100` `&19 / &20`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN CCSWP_LIN_TAC);;

(* Lean: point *)
let CCSWP_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&2) (&87 / &50) /\
      linside c s u v a (&87 / &50) (&2) /\
      ~linside c s u v a (&1) (&33 / &20) /\
      ~linside c s u v a (&87 / &50) (&1) /\
      ~linside c s u v a (&33 / &20) (&1) /\
      ~linside c s u v a (&1) (&87 / &50)
      ==> linside c s u v a (&39 / &20) (&39 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) then
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
      else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC CCSWP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`c1:real`; `--s1`; `v1:real`; `u1:real`; `a:real`] CCSWP_POSITIVE) THEN
    REWRITE_TAC[CCSWP_SWAPPED_INSIDE] THEN
    ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;
