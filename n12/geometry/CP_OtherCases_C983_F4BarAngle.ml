(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4BarAngle.lean                *)
(* (N12Compact.Completion.OtherCases.C983.F4BarAngle).  C983-F4-BAR-ANGLE-   *)
(* REDUCTION, Theorem 1.  E = (c,s,u,v,a), E.s = -t is written s = --t.      *)
(* BottomBarSupport.negative: CCBBS_NEGATIVE; S12.short_projections:         *)
(* WFP_SHORT_PROJECTIONS; F4BarAngleScalars: C983FBAS_*.  Tag C983FBA_.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4BarAngleScalars.ml";;
needs "n12/geometry/CP_OtherCases_BottomBarSupport.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C983FBA_FACT t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;

(* Lean: bounds *)
let C983FBA_BOUNDS = prove
 (`forall c s u v a t alpha beta.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (&0) /\
     linside c s u v a (&1) (--(&13 / &50)) /\
     ~linside c s u v a (&0) (--(&13 / &50)) /\
     ~linside c s u v a alpha beta /\
     (forall x. &13 / &50 <= x /\ x <= &4 / &5 ==> ~linside c s u v a x (--(&1))) /\
     ((alpha = &21 / &40 /\ beta = &1 / &8) \/ (alpha = &21 / &50 /\ beta = &4 / &25))
     ==> &13 / &50 * t <= u /\ &4 / &5 * t - c <= v /\
         v + a <= alpha * t + beta * c /\ t / (&1 + c) < &3 / &20`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C983FBA_FACT `&0 <= alpha /\ alpha <= &21 / &40 /\ &0 < beta /\ beta <= &4 / &25 /\
                beta <= alpha - &13 / &50 /\ alpha + &3 * beta = &9 / &10`
    (FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC) o
       check (fun th -> is_disj(concl th) && is_eq(lhand(lhand(concl th))))) THEN
     CONV_TAC REAL_RAT_REDUCE_CONV) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th) &&
     lhand(concl th) = `&0 <= alpha`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  C983FBA_FACT `c pow 2 + t pow 2 = &1`
    (UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC) THEN
  CCBBS_UNFOLD_TAC [`linside c (--t) u v a (&7 / &20) (--(&7 / &20))`;
                    `linside c (--t) u v a (&13 / &50) (&0)`;
                    `linside c (--t) u v a (&1) (--(&13 / &50))`] THEN
  C983FBA_FACT `v + a <= alpha * t + beta * c`
    (C983FBA_FACT `&0 <= c * (alpha - &13 / &50 - beta)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&0 <= beta * (c - t)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&0 <= t * (alpha - &13 / &50)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&0 < c * beta`
       (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&0 < c * (&1 - alpha)`
       (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&0 <= t * (beta + &13 / &50)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `~linside c (--t) u v a alpha beta`)) THEN
     REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []) THEN
  MP_TAC(SPECL [`c:real`; `--t`; `&21 / &50`; `--(&21 / &40)`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  C983FBA_FACT `v < --(&13 / &50) * c`
    (C983FBA_FACT `&0 <= t * (&21 / &40 - alpha)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&0 <= c * (&4 / &25 - beta)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     NLIN_TAC ~deg2:false []) THEN
  C983FBA_FACT `&13 / &50 * t <= u`
    (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o check (fun th ->
       concl th = `~linside c (--t) u v a (&0) (--(&13 / &50))`)) THEN
     REWRITE_TAC[linside] THEN RASM_ARITH_TAC) THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `t:real`] CCBBS_NEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IMP_CONJ] THEN RASM_ARITH_TAC;
                  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)] THEN
  C983FBA_FACT `&4 / &5 * t - c <= v`
    (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C983FBA_FACT `--(&1) <= --t * (u + a) + c * v`
       (UNDISCH_TAC `&4 / &5 * t - c <= v \/ --(&1) <= --t * (u + a) + c * v` THEN
        RASM_ARITH_TAC) THEN
     C983FBA_FACT `u + a <= &4 / &5 * c + t`
       (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `&4 / &5` o check (is_forall o concl)) THEN
        CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
        REWRITE_TAC[linside] THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&1 < &4 / &5 * c + &37 / &50 * t` RASM_ARITH_TAC THEN
     MP_TAC(SPECL [`c:real`; `t:real`] C983FBAS_SLOPE) THEN
     (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
     MP_TAC(SPECL [`c:real`; `t:real`; `alpha:real`; `beta:real`] C983FBAS_VERTEX_GAP) THEN
     (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC]) THEN
     C983FBA_FACT `&0 <= t * (u - &13 / &50 * t)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&0 <= c * ((alpha * t + beta * c) - (v + a))`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     C983FBA_FACT `&0 < (a - &1) * (c + t)`
       (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
     NLIN_TAC ~deg2:false []) THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `alpha:real`; `beta:real`] C983FBAS_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[]);;
