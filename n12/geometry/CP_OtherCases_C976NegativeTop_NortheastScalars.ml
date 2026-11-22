(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976NegativeTop/NortheastScalars.lean*)
(* (namespace N12Compact.Completion.OtherCases.C976NegativeTop).            *)
(* C976-NEGATIVE-NE-TOP-ENDING.md, section 3: the strict scalar margin      *)
(* excluding the northeast-square axis.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: projection_lt_one (private) *)
let C976NTNE_PROJECTION_LT_ONE = prove
 (`forall c s a b. c pow 2 + s pow 2 = &1 /\ a pow 2 + b pow 2 < &1
             ==> a * c + b * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a * c + b * s) pow 2 + (b * c - a * s) pow 2 = a pow 2 + b pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC [SQ_NONNEG `b * c - a * s`; SQ_NONNEG `a * c + b * s - &1`]);;

(* Lean: kink_margin (private) *)
let C976NTNE_KINK_MARGIN = prove
 (`forall c s C S p b.
     c pow 2 + s pow 2 = &1 /\ C pow 2 + S pow 2 = &1 /\
     &0 <= p * S + b * C /\ p * S + b * C < &1 /\
     &0 <= b * S - p * C /\ b * S - p * C <= &1
     ==> &0 < &1 - p * c - b * s - min (c * C - s * S) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S * c + C * s) pow 2 + (C * c - S * s) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `S * c + C * s <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `C * c - S * s`; SQ_NONNEG `S * c + C * s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `(p * S + b * C) * (S * c + C * s) <= (p * S + b * C) * &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(p * S + b * C) * (S * c + C * s) - (p * c + b * s) =
                (b * S - p * C) * (C * c - S * s)` ASSUME_TAC THENL
   [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c * C - s * S` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> min x (&0) = &0`] THEN
    SUBGOAL_THEN `&0 <= (b * S - p * C) * (c * C - s * S)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> min x (&0) = x`] THEN
    SUBGOAL_THEN `&0 <= (&1 - (b * S - p * C)) * --(c * C - s * S)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]);;

(* Lean: northeast_endpoint (private) *)
let C976NTNE_NORTHEAST_ENDPOINT = prove
 (`forall C S eta. &11 / &20 <= C /\ &7 / &10 <= S /\ S <= &1 /\
             C pow 2 + S pow 2 = &1 /\ eta * (&1 + S) = C
     ==> &0 < &2 - (&36 / &25) * C + eta * S - (&43 / &25) * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &43 * C pow 2 - &36 * C + &7 + (&7 - &11 * C) * S` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN ASM_CASES_TAC `C <= &7 / &11` THENL
     [SUBGOAL_THEN `&0 <= (S - &7 / &10) * (&7 - &11 * C) /\
                    &0 <= (C - &11 / &20) * (&43 * C - &401 / &20)` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 <= (&1 - S) * (&11 * C - &7) /\
                    &0 <= (C - &11 / &20) * (&43 * C - &467 / &20)` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + S) * (&2 - (&36 / &25) * C + eta * S - (&43 / &25) * S) =
                (&43 * C pow 2 - &36 * C + &7 + (&7 - &11 * C) * S) / &25` ASSUME_TAC THENL
   [UNDISCH_TAC `eta * (&1 + S) = C` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + S) * --(&2 - (&36 / &25) * C + eta * S - (&43 / &25) * S)`
    MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC);;

(* Lean: northeast_margin *)
let C976NTNE_NORTHEAST_MARGIN = prove
 (`forall c s C S. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
             &0 < C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\ (&2 / &3) * S <= C
     ==> &0 < &1 + c * ((&1 - S) / C + S - &43 / &25) - s * (&36 / &25 - C) -
              min (c * C - s * S) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `eta = (&1 - S) / C` THEN
  SUBGOAL_THEN `C <= &1 /\ S <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `S:real`; SQ_NONNEG `C:real`;
      SQ_NONNEG `C - &1`; SQ_NONNEG `S - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eta` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `eta * C = &1 - S` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `eta * (&1 + S) = C` ASSUME_TAC THENL
   [SUBGOAL_THEN `C * (eta * (&1 + S)) = C * C` MP_TAC THENL
     [UNDISCH_TAC `eta * C = &1 - S` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
      CONV_TAC REAL_RING;
      ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ]]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= eta + S` ASSUME_TAC THENL
   [SUBGOAL_THEN `C * (eta + S - &1) = (&1 - S) * (&1 - C)` ASSUME_TAC THENL
     [UNDISCH_TAC `eta * C = &1 - S` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&1 - S) * (&1 - C)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `min (c * C - s * S) (&0) <= &0` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&4 / &5 <= C` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `&18 / &25`; `&16 / &25`] C976NTNE_PROJECTION_LT_ONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
    SUBGOAL_THEN `c * --(&18 / &25) <= c * (eta + S - &43 / &25) /\
                  (&36 / &25 - C) * s <= (&16 / &25) * s` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C <= &4 / &5` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&7 / &10 <= C` THENL
   [SUBGOAL_THEN `&7 / &50 <= C * (&1 - C)` ASSUME_TAC THENL
     [NLIN_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `(eta + S - &1) * (&1 + S) = C * (&1 - C)` ASSUME_TAC THENL
     [UNDISCH_TAC `eta * (&1 + S) = C` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (eta + S - &1) * (&1 - S)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&107 / &100 <= eta + S` ASSUME_TAC THENL
     [NLIN_TAC []; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &20`; `&37 / &50`] C976NTNE_PROJECTION_LT_ONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
    SUBGOAL_THEN `c * --(&13 / &20) <= c * (eta + S - &43 / &25) /\
                  (&36 / &25 - C) * s <= (&37 / &50) * s` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C <= &7 / &10` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (C - (&2 / &3) * S) * (C + (&2 / &3) * S)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&11 / &20 < C` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&11 / &20 - C) * (&11 / &20 + C)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&7 / &10 < S` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&7 / &10 - C) * (&7 / &10 + C) /\
                  &0 <= (&7 / &10 - S) * (&7 / &10 + S)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `eta <= C` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= eta * S` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `eta * (&1 + S) = C` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `p = &43 / &25 - eta - S` THEN
  ABBREV_TAC `b = &36 / &25 - C` THEN
  SUBGOAL_THEN `&0 < p /\ &0 < b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "b"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p * S + b * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `eta:real`] C976NTNE_NORTHEAST_ENDPOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `p * S + b * C < &1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "b"] THEN
    UNDISCH_TAC `&0 < &2 - (&36 / &25) * C + eta * S - (&43 / &25) * S` THEN
    UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b * S - p * C = &1 + (&11 / &25) * S - (&43 / &25) * C` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "b"] THEN UNDISCH_TAC `eta * C = &1 - S` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C:real`; `S:real`; `p:real`; `b:real`]
    C976NTNE_KINK_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXPAND_TAC ["p"; "b"] THEN REAL_ARITH_TAC);;
