(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4BarAngleScalars.lean         *)
(* (N12Compact.Completion.OtherCases.C983.F4BarAngleScalars).  The one-      *)
(* variable estimates of C983-F4-BAR-ANGLE-REDUCTION, Theorem 1.             *)
(* C981CompletionHalfAngle.half / data = c981ha_half / C981HA_DATA.          *)
(* PARTIAL PORT: the trigonometric items J (def), derivative (private) and   *)
(* monotone (private; MonotoneOn J on [0,pi/4] via Real.cos/sin and the      *)
(* derivative) are not ported (no transcendentals in the port's base, see    *)
(* CP_OtherCases_C983_F4MergedCenterMonotone.ml); they are used only inside  *)
(* the Lean proof of vertex_gap, whose statement is algebraic and is proved  *)
(* here by the half-angle substitution z = s/(1+c) instead.  Tag C983FBAS_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4MergedCenterMonotone.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;

let C983FBAS_FACT t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;

(* Lean: slope *)
let C983FBAS_SLOPE = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
         &1 < &4 / &5 * c + &37 / &50 * s
         ==> c / &3 < s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C983FBAS_FACT `&0 <= (c - &3 * s) * (&8649 / &2500 * c - &3653 / &2500 * s)`
    (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
  C983FBAS_FACT `&0 < (&4 / &5 * c + &37 / &50 * s - &1) * (&4 / &5 * c + &37 / &50 * s + &1)`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
  NLIN_TAC ~deg2:false []);;

(* helper: the alpha = 21/40 endpoint of vertex_gap in half-angle form *)
let C983FBAS_ENDPOINT = prove
 (`forall c s z. (&1 + z pow 2) * c = &1 - z pow 2 /\ (&1 + z pow 2) * s = &2 * z /\
           &0 <= z /\ z <= &1 / &2 /\ c / &3 < s
           ==> &0 < c + s - &1 - &3 / &10 * c pow 2 + &13 / &50 * s pow 2 +
                    &21 / &40 * (c pow 2 / &3 - c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983FBAS_FACT `&0 < &1 + z pow 2` (MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC) THEN
  C983FBAS_FACT `(&3 * s - c) * (&1 + z pow 2) = &6 * z - &1 + z pow 2`
    (MAP_EVERY UNDISCH_TAC [`(&1 + z pow 2) * c = &1 - z pow 2`; `(&1 + z pow 2) * s = &2 * z`] THEN
     CONV_TAC REAL_RING) THEN
  C983FBAS_FACT `&0 < (&3 * s - c) * (&1 + z pow 2)`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
  C983FBAS_FACT `&1622 / &10000 <= z` (NLIN_TAC []) THEN
  C983FBAS_FACT `(c + s - &1 - &3 / &10 * c pow 2 + &13 / &50 * s pow 2 +
                  &21 / &40 * (c pow 2 / &3 - c * s)) * (&1 + z pow 2) pow 2 =
                 -- &17 / &8 * z pow 4 + &61 / &20 * z pow 3 - &71 / &100 * z pow 2 +
                 &19 / &20 * z - &1 / &8`
    (MAP_EVERY UNDISCH_TAC [`(&1 + z pow 2) * c = &1 - z pow 2`; `(&1 + z pow 2) * s = &2 * z`] THEN
     CONV_TAC REAL_RING) THEN
  C983FBAS_FACT `&0 < -- &17 / &8 * z pow 4 + &61 / &20 * z pow 3 - &71 / &100 * z pow 2 +
                 &19 / &20 * z - &1 / &8`
    (let h1 = TAC_PROOF(([], `&1622 / &10000 <= z ==> &0 <= z - &1622 / &10000`), REAL_ARITH_TAC)
     and h2 = TAC_PROOF(([], `z <= &1 / &2 ==> &0 <= &1 / &2 - z`), REAL_ARITH_TAC) in
     let a1 = UNDISCH h1 and a2 = UNDISCH h2 in
     let hs = [a1; a2; MATCH_MP REAL_LE_MUL (CONJ a1 a1); MATCH_MP REAL_LE_MUL (CONJ a1 a2);
               MATCH_MP REAL_LE_MUL (CONJ a2 a2)] in
     NLIN_TAC hs) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C983FBAS_FACT `&0 < (&1 + z pow 2) pow 2` (MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]) THEN
  NLIN_TAC []);;

(* Lean: vertex_gap *)
let C983FBAS_VERTEX_GAP = prove
 (`forall c s alpha beta. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\ c / &3 < s /\
     &0 <= alpha /\ alpha <= &21 / &40 /\ &0 <= beta /\ alpha + &3 * beta = &9 / &10
     ==> &0 < c + s - &1 - alpha * c * s - beta * c pow 2 + &13 / &50 * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_DATA) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC]) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `c981ha_half c s`] C983FBAS_ENDPOINT) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  C983FBAS_FACT `&0 <= (&21 / &40 - alpha) * (c * (s - c / &3))`
    (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
      [RASM_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC]) THEN
  C983FBAS_FACT `(alpha + &3 * beta - &9 / &10) * c pow 2 = &0`
    (UNDISCH_TAC `alpha + &3 * beta = &9 / &10` THEN CONV_TAC REAL_RING) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: half *)
let C983FBAS_HALF = prove
 (`forall c s alpha beta. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
     ((alpha = &21 / &40 /\ beta = &1 / &8) \/ (alpha = &21 / &50 /\ beta = &4 / &25)) /\
     &1 < (&1 + beta) * c + (alpha - &4 / &5) * s
     ==> s / (&1 + c) < &3 / &20`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_DATA) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[c981ha_half] THEN ABBREV_TAC `z = s / (&1 + c)` THEN STRIP_TAC THEN
  C983FBAS_FACT `&0 < &1 + z pow 2` (MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC) THEN
  C983FBAS_FACT `&0 < (&1 + z pow 2) * ((&1 + beta) * c + (alpha - &4 / &5) * s - &1)`
    (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC) THEN
  C983FBAS_FACT `(&1 + z pow 2) * ((&1 + beta) * c + (alpha - &4 / &5) * s - &1) =
                 beta - (&2 + beta) * z pow 2 + &2 * (alpha - &4 / &5) * z`
    (MAP_EVERY UNDISCH_TAC [`(&1 + z pow 2) * c = &1 - z pow 2`; `(&1 + z pow 2) * s = &2 * z`] THEN
     CONV_TAC REAL_RING) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) o
    check (is_disj o concl)) THEN
  NLIN_TAC []);;
