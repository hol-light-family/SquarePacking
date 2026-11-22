(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SouthwestSupportPoint/              *)
(*   SegmentSupport.lean                                                     *)
(* (N12Compact.Completion.OtherCases.SouthwestSupportPoint.SegmentSupport).  *)
(* C974-C976-SW-SUPPORT-POINT section 3.  Square q is c s u v a; Input is    *)
(* ocswsp_input; LowerFaces.negative is OCSWSPLF_NEGATIVE; short_projections *)
(* is WFP_SHORT_PROJECTIONS; SegmentCorner.crossing_order is                 *)
(* SEGC_CROSSING_ORDER; upper_in_bands is C981SF_UPPER_IN_BANDS.  Tag        *)
(* OCSWSPSS_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_LowerFaces.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/SegmentCorner.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let OCSWSPSS_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* the endpoint G = (13/50, 0) of the southeast segment *)
let OCSWSPSS_ENDPOINT_TAC =
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `&9 / &100`)) (concl th) then
    ASSUME_TAC(REWRITE_RULE[] (CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
      (SPEC `&1` th))) else NO_TAC);;

(* Lean: positive *)
let OCSWSPSS_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a /\
     &0 < c /\ &0 <= s /\ s <= c
     ==> u + a <= (&13 / &50) * c \/ ABT_upper c s u v a (&35) (&9) <= &91 / &10`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocswsp_input] THEN STRIP_TAC THEN DISJ1_TAC THEN
  OCSWSPSS_ENDPOINT_TAC THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (&0) (--(&13 / &50))`; `linside c s u v a (--(&13 / &50)) (&0)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  OCSWSPSS_MISS_TAC `~linside c s u v a (&13 / &50) (&0)`);;

(* Lean: negative *)
let OCSWSPSS_NEGATIVE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ocswsp_input c s u v a /\
     s = --t /\ &0 < c /\ &0 <= t /\ t <= c
     ==> u + a <= (&13 / &50) * c \/ ABT_upper c s u v a (&35) (&9) <= &91 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`] OCSWSPLF_NEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ocswsp_input c s u v a` THEN REWRITE_TAC[ocswsp_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  OCSWSPSS_ENDPOINT_TAC THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c (--t) u v a (--(&7 / &20)) (--(&7 / &20))`;
    `linside c (--t) u v a (&0) (--(&13 / &50))`;
    `linside c (--t) u v a (--(&13 / &50)) (&0)`] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `&61 / &100`; `&13 / &20`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  SUBGOAL_THEN `(&7 / &20) * (t - c) < v + a` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&7 / &20) * (c + t)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCSWSPSS_MISS_TAC `~linside c (--t) u v a (&7 / &20) (--(&7 / &20))`; ALL_TAC] THEN
  ASM_CASES_TAC `u + a <= (&13 / &50) * c` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `v + a <= (&13 / &50) * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCSWSPSS_MISS_TAC `~linside c (--t) u v a (&13 / &50) (&0)`; ALL_TAC] THEN
  MP_TAC(SPECL [`--u - a`; `--u:real`; `v:real`; `v + a`;
                `--((&7 / &20) * (c + t))`; `(&7 / &20) * (t - c)`;
                `--((&13 / &50) * c)`; `(&13 / &50) * t`] SEGC_CROSSING_ORDER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    X_GEN_TAC `w:real` THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `w:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&9 / &100`)) (concl th))) THEN
    REWRITE_TAC[linside] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(&35 * c + &9 * --t) = &35 * c - &9 * t /\
                abs(--(&35) * --t + &9 * c) = &35 * t + &9 * c`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC);;
