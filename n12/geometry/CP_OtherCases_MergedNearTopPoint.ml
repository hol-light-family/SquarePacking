(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedNearTopPoint.lean             *)
(* (namespace N12Compact.Completion.OtherCases.MergedNearTopPoint).         *)
(* The nearer upper auxiliary fixes the merged owner's canonical sign.      *)
(* CanonicalScalars.bounds: CCCS_BOUNDS; canonical_frame: CLF_CANONICAL_FRAME*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let OCMNTP_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: negative_span_impossible *)
let OCMNTP_NEGATIVE_SPAN_IMPOSSIBLE = prove
 (`forall c t. &0 < c /\ &0 <= t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\
         &27 / &20 * c + &9 / &100 * t < &1001 / &1000
         ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `c < &3 / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&16 / &25 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    NLIN_FACTS_TAC []
     [`&0 < (&3 / &4 - c) * (&3 / &4 + c)`; `&0 <= (&16 / &25 - t) * (&16 / &25 + t)`] THEN
    NLIN_TAC ~deg2:false [];
    ASM_REAL_ARITH_TAC]);;

(* Lean: positive_point (private) *)
let OCMNTP_POSITIVE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&87 / &50) (&3) /\
      ~linside c s u v a (&1) (&113 / &50)
      ==> linside c s u v a (&2) (&113 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c + s * &113 / &50 <= u` ASSUME_TAC THENL
   [OCMNTP_LIN_TAC; ALL_TAC] THEN
  OCMNTP_LIN_TAC);;

(* Lean: point *)
let OCMNTP_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ a <= &1001 / &1000 /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&87 / &50) (&3) /\
      ~linside c s u v a (&1) (&113 / &50)
      ==> linside c s u v a (&2) (&113 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
    else NO_TAC)) THEN
  ASM_CASES_TAC `&0 < s1` THENL
   [MATCH_MP_TAC OCMNTP_POSITIVE_POINT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC OCMNTP_NEGATIVE_SPAN_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `--s1`] THEN
    REWRITE_TAC[REAL_POW_NEG; REAL_POW_2; ARITH] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN OCMNTP_LIN_TAC]);;
