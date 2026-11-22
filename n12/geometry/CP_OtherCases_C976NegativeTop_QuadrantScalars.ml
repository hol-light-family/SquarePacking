(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976NegativeTop/QuadrantScalars.lean*)
(* (namespace N12Compact.Completion.OtherCases.C976NegativeTop).            *)
(* Exact quadrant estimates, sections 2 and 4 of the C976 negative ending.  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: quadrant_bounds *)
let C976NTQ_QUADRANT_BOUNDS = prove
 (`forall C S. &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\ (&2 / &3) * S <= C
     ==> &11 / &20 < C /\ S < &5 / &6 /\ C <= &1 /\ &1 <= C + S /\
         &1 + (&4 / &5) * C * S <= C + S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `S:real`; SQ_NONNEG `C - S:real`]
   [`&0 <= (C - (&2 / &3) * S) * (C + (&2 / &3) * S)`; `&0 <= C * S`;
    `&11 / &20 < C`; `S < &5 / &6`; `C <= &1`; `&1 <= C + S`; `C + S <= &3 / &2`;
    `&0 <= (&3 / &2 - (C + S)) * ((C + S) - &1)`] THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC []);;

(* Lean: lower_exit_margin *)
let C976NTQ_LOWER_EXIT_MARGIN = prove
 (`forall c s C S. &0 < c /\ &0 <= s /\ &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\
             (&2 / &3) * S <= C
     ==> min ((&13 / &50) * c) ((&37 / &50) * s) <= (c * S + s * C) * (&1 - (&3 / &4) * S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C976NTQ_QUADRANT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - (&3 / &4) * S` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= S * (&15 / &8 - (&9 / &4) * S)`; `&0 <= C * S`;
    `&1 / &3 <= (S + C / &3) * (&1 - (&3 / &4) * S)`;
    `&0 <= ((&13 / &37 - &1 / &3) * C) * (&1 - (&3 / &4) * S)`;
    `&1 / &3 <= (S + (&13 / &37) * C) * (&1 - (&3 / &4) * S)`] THEN
  SUBGOAL_THEN `&0 <= c * ((S + (&13 / &37) * C) * (&1 - (&3 / &4) * S) - &13 / &50)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s <= (&13 / &37) * c` THENL
   [SUBGOAL_THEN `min ((&13 / &50) * c) ((&37 / &50) * s) = (&37 / &50) * s` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `&0 <= C * (&1 - (&3 / &4) * S) - &37 / &50` THENL
     [SUBGOAL_THEN `&0 <= (c * S) * (&1 - (&3 / &4) * S) /\
                    &0 <= s * (C * (&1 - (&3 / &4) * S) - &37 / &50)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      NLIN_TAC [];
      SUBGOAL_THEN `&0 <= ((&13 / &37) * c - s) * (&37 / &50 - C * (&1 - (&3 / &4) * S))`
        ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      NLIN_TAC []];
    SUBGOAL_THEN `min ((&13 / &50) * c) ((&37 / &50) * s) = (&13 / &50) * c` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (s - (&13 / &37) * c) * (C * (&1 - (&3 / &4) * S))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    NLIN_TAC []]);;

(* Lean: wall_delta *)
let C976NTQ_WALL_DELTA = prove
 (`forall C S. &0 < C /\ &0 < S /\ C pow 2 + S pow 2 = &1
     ==> (&1 / &10) * S < &1 - (&1 - S) / C - (&18 / &25) * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e = (&1 - S) / C` THEN
  SUBGOAL_THEN `C * e = &1 - S` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `e * (&1 + S) = C` ASSUME_TAC THENL
   [SUBGOAL_THEN `C * (e * (&1 + S)) = C * C` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING;
      ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + e) * (&1 - e - (&41 / &50) * S) =
                S * ((e - &41 / &100) pow 2 + &119 / &10000)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 - e pow 2 = S * (&1 + e pow 2)` MP_TAC THENL
     [UNDISCH_TAC `C * e = &1 - S` THEN UNDISCH_TAC `e * (&1 + S) = C` THEN
      CONV_TAC REAL_RING;
      CONV_TAC REAL_RING]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < S * ((e - &41 / &100) pow 2 + &119 / &10000)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `e - &41 / &100` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - e - (&41 / &50) * S` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&1 + e) * (&1 - e - (&41 / &50) * S) <= &0` MP_TAC THENL
     [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;
