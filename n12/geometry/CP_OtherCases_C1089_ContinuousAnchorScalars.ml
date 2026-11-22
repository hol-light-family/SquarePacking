(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ContinuousAnchorScalars.lean *)
(* (namespace N12Compact.Completion.OtherCases.C1089.ContinuousAnchorScalars)*)
(* Normal: c977cc_normal; C1092MMMPOuterArmScalars: C1092MOAS_*.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_C1092_MMMP_OuterArmScalars.ml";;

(* Lean: first *)
let C1089CAS_FIRST = prove
 (`forall c s h b. c977cc_normal c s /\ &0 < s /\ &0 <= h /\ &0 <= b /\
             h pow 2 + b pow 2 = &1 /\ &0 <= s * h - c * b
     ==> &0 <= &1 / &2 + h pow 2 / &2 + h * b / &2 +
               h * (c pow 2 - (&2 / &5) * c * s + s - &2) +
               b * (c * s - (&2 / &5) * s pow 2 - c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092MOAS_FIRST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&7 / &20 * (c - s)) * (s * h - c * b)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 / &2 + h pow 2 / &2 + h * b / &2 + h * (c pow 2 - (&2 / &5) * c * s + s - &2) +
    b * (c * s - (&2 / &5) * s pow 2 - c) =
    (&1 / &2 + h pow 2 / &2 + h * b / &2 +
       h * (c pow 2 - (&3 / &4) * c * s + s + (&7 / &20) * s pow 2 - &2) +
       b * ((&13 / &20) * c * s - (&2 / &5) * s pow 2 - c + (&7 / &20) * c pow 2)) +
    (&7 / &20 * (c - s)) * (s * h - c * b)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: second *)
let C1089CAS_SECOND = prove
 (`forall c s h b. c977cc_normal c s /\ &0 <= h /\ &0 <= b /\
             h pow 2 + b pow 2 = &1 /\ s * h - c * b <= &0
     ==> &0 <= &1 / &2 + h pow 2 / &2 + h * b / &2 +
               h * (&1 - (&37 / &50) * s pow 2 - (&2 / &5) * c * s - &2) +
               b * ((&37 / &50) * c * s - (&2 / &5) * s pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MOAS_ENDPOINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o check (fun th -> concl th = `c977cc_normal c s`)) THEN
  C1092MOAS_NORMAL_TAC THEN
  C1092MOAS_PROD_TAC [`&0 <= c * b`; `&0 <= s * h`] THEN
  C1092MOAS_PROD_TAC [`&0 <= (c * b - s * h) * (c * b + s * h)`] THEN
  SUBGOAL_THEN `(c * b) pow 2 - (s * h) pow 2 = b pow 2 - s pow 2` ASSUME_TAC THENL
   [UNDISCH_TAC `h pow 2 + b pow 2 = &1` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s <= b` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= (b - s) * (s + b)`] THEN
  SUBGOAL_THEN `h <= c` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092MOAS_QUADRATIC_MONOTONE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C1092MOAS_PROD_TAC [`&0 <= c * s`; `&0 <= s * ((&37 / &50) * c - (&2 / &5) * s)`] THEN
  SUBGOAL_THEN `(&1 - (&37 / &50) * s pow 2 - (&2 / &5) * c * s) - &1 <= &0 /\
                &0 <= (&37 / &50) * c * s - (&2 / &5) * s pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  C1092MOAS_PROD_TAC
   [`&0 <= (c - h) * --((&1 - (&37 / &50) * s pow 2 - (&2 / &5) * c * s) - &1)`;
    `&0 <= (b - s) * ((&37 / &50) * c * s - (&2 / &5) * s pow 2)`] THEN
  SUBGOAL_THEN
   `(&1 - c) pow 2 / &2 + c * s / &2 +
    c * ((&1 - (&37 / &50) * s pow 2 - (&2 / &5) * c * s) - &1) +
    s * ((&37 / &50) * c * s - (&2 / &5) * s pow 2) =
    ((&1 - c) pow 2 + s * (c - &4 / &5)) / &2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
