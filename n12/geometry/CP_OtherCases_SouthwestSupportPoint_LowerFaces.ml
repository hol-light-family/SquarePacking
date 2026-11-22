(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SouthwestSupportPoint/              *)
(* LowerFaces.lean (N12Compact.Completion.OtherCases.SouthwestSupportPoint. *)
(* LowerFaces).  Section 2 of C974-C976-SW-SUPPORT-POINT.  Input:            *)
(* ocswsp_input; short_projections: WFP_SP; increasing_projection:          *)
(* CCOS_INCREASING_PROJECTION.  The Lean frame                              *)
(* turnFrame^3 (pullSwap q) is the square (c, t, v, u, a) when s = --t.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Inputs.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;

let OCSWSPLF_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: positive_data (private) *)
let OCSWSPLF_POSITIVE_DATA = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
      linside c s u v a (--(&13 / &50)) (&0) /\
      ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20)) /\
      ~linside c s u v a (--(&2 / &5)) (--(&1)) /\
      ~linside c s u v a (--(&1)) (--(&13 / &50))
      ==> &2 / &5 * s - c <= v /\ --c - &13 / &50 * s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let lfN = `~linside c s u v a (--(&7 / &20)) (&7 / &20)`
  and lfE = `~linside c s u v a (&7 / &20) (--(&7 / &20))`
  and lfB = `~linside c s u v a (--(&2 / &5)) (--(&1))`
  and lfL = `~linside c s u v a (--(&1)) (--(&13 / &50))` in
  let proj a b =
    MP_TAC(SPECL [`c:real`; `s:real`; a; b] CCOS_INCREASING_PROJECTION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] in
  MP_TAC(WFP_SP `&3 / &4` `&13 / &20`) THEN MP_TAC(WFP_SP `--(&3 / &5)` `&37 / &50`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  proj `&1 / &20` `&27 / &20` THEN proj `&7 / &10` `&7 / &10` THEN
  SUBGOAL_THEN `&2 / &5 * s - c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `--(&2 / &5) * c - s <= u` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCSWSPLF_KEEP_TAC [lfB];
      ALL_TAC] THEN
    SUBGOAL_THEN `v + a <= &7 / &20 * (c + s)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCSWSPLF_KEEP_TAC [lfN];
      ALL_TAC] THEN
    SUBGOAL_THEN `--(&7 / &20) * (s + c) <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCSWSPLF_KEEP_TAC [lfE];
      ALL_TAC] THEN
    OCSWSPLF_KEEP_TAC [];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCSWSPLF_KEEP_TAC [lfL]);;

(* Lean: positive *)
let OCSWSPLF_POSITIVE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a /\
      &0 < c /\ &0 <= s /\ s <= c
      ==> &2 / &5 * s - c <= v /\ --c - &13 / &50 * s <= u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocswsp_input] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL OCSWSPLF_POSITIVE_DATA) THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `--(&1 / &2)`)) (concl th))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: negative *)
let OCSWSPLF_NEGATIVE = prove
 (`forall c s u v a t.
      c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a /\
      s = --t /\ &0 < c /\ &0 <= t /\ t <= c
      ==> &2 / &5 * t - c <= u /\ --(&13 / &50) * t - c <= v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocswsp_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `v:real`; `u:real`; `a:real`] OCSWSPLF_POSITIVE_DATA) THEN
  SUBGOAL_THEN `forall x y. linside c t v u a x y <=> linside c (--t) u v a y x`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `--(&1 / &2)`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REAL_ARITH_TAC]);;
