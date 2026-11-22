(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointCentralAligned.lean         *)
(* (N12Compact.C1092MPPMCrosspointSupport.Central).  STEEP-POSITIVE-CENTRAL- *)
(* SCALAR sections 1--2.  Normal is c977cc_normal; G00 etc. are c1092mcs_*;  *)
(* canonical/steep bounds C1092PRS_*; UnitCircleChord is CCUCC_*.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointSupportScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

(* Lean: diagonalValue (definition) *)
let c1092mcca_diagonalValue = new_definition
 `c1092mcca_diagonalValue (c:real) (s:real) =
    &2 * (c + s) - &2 - (&1043 / &500) * c * s + (&14 / &25) * s pow 2`;;

(* Lean: diagonal_lower *)
let C1092MCCA_DIAGONAL_LOWER = prove
 (`forall c s. c977cc_normal c s /\ &3 / &5 <= s ==> &1 / &3125 <= c1092mcca_diagonalValue c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  ABBREV_TAC `J = &2 * (c + &4 / &5 - s - &3 / &5) -
                  (&1043 / &500) * (c * (c + &4 / &5) - (&3 / &5) * (s + &3 / &5)) +
                  (&14 / &25) * (s + &3 / &5) * (c + &4 / &5)` THEN
  SUBGOAL_THEN `&0 <= J` ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN
   C1092PRS_PROD `&0 <= (&4 / &5 - c) * (&4 / &5 + c)` THEN
   C1092PRS_PROD `&0 <= (s - &3 / &5) * (c + &4 / &5)` THEN
   NLIN_TAC []; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (s - &3 / &5) * J` THEN
  SUBGOAL_THEN `(c + &4 / &5) * (c1092mcca_diagonalValue c s - &1 / &3125) = (s - &3 / &5) * J`
  ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN REWRITE_TAC[c1092mcca_diagonalValue] THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 < (c + &4 / &5) * (&1 / &3125 - c1092mcca_diagonalValue c s)` THEN
  RASM_ARITH_TAC);;

(* Lean: aligned_C *)
let C1092MCCA_ALIGNED_C = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s
     ==> &1 / &3125 <= c1092mcs_G00 c s d t c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCCA_DIAGONAL_LOWER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092PRS_NORMAL_TAC THEN
  REWRITE_TAC[c1092mcs_G00; c1092mcs_k; c1092mcs_kC; c1092mcs_kE; c1092mcs_deltaC;
              c1092mcs_deltaE; c1092mcs_C0; c1092mcs_E0;
              REAL_ARITH `c * s - s * c = &0`; REAL_ABS_0] THEN
  ASM_CASES_TAC `t <= s` THENL
  [MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] CCUCC_CROSS_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
   ABBREV_TAC `A = &2 * c + (&1043 / &500) * s - c * s - &2` THEN
   ABBREV_TAC `B = s * (&36 / &25 - s)` THEN
   SUBGOAL_THEN `&0 <= A /\ &0 <= B /\ &0 <= B * c - A * s` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    C1092PRS_PROD `&0 <= s * (&36 / &25 - s)` THEN
    C1092PRS_PROD `&0 <= s * (&2 - (&14 / &25) * c - (&1043 / &500) * s)` THEN
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `A:real`; `B:real`] CCUCC_INCREASING) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `s - A * c - B * s = c1092mcca_diagonalValue c s` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[c1092mcca_diagonalValue] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `forall g v. g = s - A * d - B * t /\ s - A * c - B * s = v /\
                 A * d + B * t <= A * c + B * s /\ &1 / &3125 <= v ==> &1 / &3125 <= g`) THEN
   EXISTS_TAC `c1092mcca_diagonalValue c s` THEN ASM_REWRITE_TAC[] THEN
   MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
   SUBGOAL_THEN `s <= t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CCUCC_CROSS_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= c * t - s * d ==> abs(d * s - t * c) = c * t - s * d`] THEN
   ABBREV_TAC `A = &2 * c + (&1043 / &500) * s - &1 - c * (c + s)` THEN
   ABBREV_TAC `B = s * (&36 / &25 - c - s)` THEN
   SUBGOAL_THEN `&0 <= A /\ &0 <= B /\ &0 <= A * s - B * c` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    C1092PRS_PROD `&0 <= (&4 / &5 - c) * (c + s)` THEN
    C1092PRS_PROD `&0 <= s * (&36 / &25 - c - s)` THEN
    C1092PRS_PROD `&0 <= s * ((&14 / &25) * c + (&1043 / &500) * s - &1)` THEN
    REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `A:real`; `B:real`] CCUCC_DECREASING) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `s - A * c - B * s = c1092mcca_diagonalValue c s` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[c1092mcca_diagonalValue] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `forall g v. g = s - A * d - B * t /\ s - A * c - B * s = v /\
                 A * d + B * t <= A * c + B * s /\ &1 / &3125 <= v ==> &1 / &3125 <= g`) THEN
   EXISTS_TAC `c1092mcca_diagonalValue c s` THEN ASM_REWRITE_TAC[] THEN
   MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING]);;
