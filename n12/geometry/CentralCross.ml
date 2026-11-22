(* ========================================================================= *)
(* Port of Compact/Geometry/CentralCross.lean                                *)
(*                                                                           *)
(* pullSwap q = (s, c, u, --v - a, a); closed_swap (private in Lean) is      *)
(* LCLOSED_PULLSW of p2_base.                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareAForced.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: point *)
let CCR_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     lclosed c s u v a (&2) (&113 / &50) /\
     lclosed c s u v a (&113 / &50) (&2) /\
     lclosed c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&12 / &5) (&3)
     ==> linside c s u v a (&2) (&5 / &2) \/ linside c s u v a (&5 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `sr = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    NLIN_FACTS_TAC [] [`cr <= &1`; `&1 <= cr`] THEN
    SUBGOAL_THEN `cr = &1` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    DISJ1_TAC THEN MATCH_MP_TAC FSAF_AXIS_POINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `sr <= cr` THENL
   [DISJ1_TAC THEN MATCH_MP_TAC FSAF_POSITIVE_SHALLOW_POINT THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN
    MP_TAC(SPECL [`sr:real`; `cr:real`; `ur:real`; `--vr - a:real`; `a:real`]
      FSAF_POSITIVE_SHALLOW_POINT) THEN
    REWRITE_TAC[LINSIDE_PULLSW; LCLOSED_PULLSW] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]]);;

(* Lean: cut_point *)
let CCR_CUT_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     lclosed c s u v a (&2) (&113 / &50) /\
     lclosed c s u v a (&113 / &50) (&2) /\
     lclosed c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&12 / &5) (&3)
     ==> linside c s u v a (&2) (&12 / &5) \/ linside c s u v a (&12 / &5) (&2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CCR_POINT) THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN STRIP_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC FSAF_ROW_POINT THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN
    MP_TAC(SPECL [`s:real`; `c:real`; `u:real`; `--v - a:real`; `a:real`] FSAF_ROW_POINT) THEN
    REWRITE_TAC[LINSIDE_PULLSW; LCLOSED_PULLSW] THEN ASM_REWRITE_TAC[]]);;
