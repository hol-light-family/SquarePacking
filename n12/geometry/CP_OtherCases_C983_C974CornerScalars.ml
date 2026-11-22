(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974CornerScalars.lean         *)
(* (namespace N12Compact.Completion.OtherCases.C983.C974CornerScalars).      *)
(* Exact scalar identities in C974-THREE-SQUARE-ENDING sections 3-4.  The    *)
(* Lean `let z := s/(1+c)` is expanded in place.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

let C983CS_DEN = prove
 (`forall x. &0 < &1 + x pow 2`,
  GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `forall z. &0 <= z ==> &0 < &1 + z`) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

(* Lean: normal_forms *)
let C983CS_NORMAL_FORMS = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> &0 <= s / (&1 + c) /\ s / (&1 + c) <= &1 /\
             c = (&1 - (s / (&1 + c)) pow 2) / (&1 + (s / (&1 + c)) pow 2) /\
             s = &2 * (s / (&1 + c)) / (&1 + (s / (&1 + c)) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C1092WPS_QUARTER_DATA) THEN
  REWRITE_TAC[C1092WPS_half] THEN
  MP_TAC(SPEC `s / (&1 + c)` C983CS_DEN) THEN
  SPEC_TAC(`s / (&1 + c)`,`z:real`) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: cubic_gap *)
let C983CS_CUBIC_GAP = prove
 (`forall d t z c s w. &0 < z /\ z < &1 / &3 /\ z <= w /\ w <= &1 /\
     d = (&1 - z pow 2) / (&1 + z pow 2) /\ t = &2 * z / (&1 + z pow 2) /\
     c = (&1 - w pow 2) / (&1 + w pow 2) /\ s = &2 * w / (&1 + w pow 2)
     ==> &0 < (&1 - t / &2) * (c * d + s * t) - &1 + w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:real` C983CS_DEN) THEN MP_TAC(SPEC `w:real` C983CS_DEN) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `exists v. &0 <= v /\ v <= &1 /\ w = z + v * (&1 - z)` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(w - z) / (&1 - z)` THEN
    SUBGOAL_THEN `&0 < &1 - z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `b0 = z pow 3 * (&1 + z pow 2) pow 2` THEN
  ABBREV_TAC `b1 = (&1 + z pow 2) * (&1 + z + z pow 2) * (&3 * z pow 2 - &2 * z + &1) / &3` THEN
  ABBREV_TAC `b2 = &2 * z * (&2 * z pow 4 - z pow 3 + &5 * z pow 2 - &3 * z + &3) / &3` THEN
  ABBREV_TAC `b3 = &4 * z * (z pow 2 - z + &1)` THEN
  SUBGOAL_THEN `(&1 + z pow 2) pow 2 * (&1 + w pow 2) *
     ((&1 - t / &2) * (c * d + s * t) - &1 + w) =
     ((&1 + z pow 2) - z) * ((&1 - w pow 2) * (&1 - z pow 2) + &4 * w * z) -
     (&1 + z pow 2) pow 2 * (&1 + w pow 2) * (&1 - w)` ASSUME_TAC THENL
   [MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = v)))
     [`d:real`; `t:real`; `c:real`; `s:real`] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < &1 + z pow 2`; `&0 < &1 + w pow 2`] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + z pow 2) - z) * ((&1 - w pow 2) * (&1 - z pow 2) + &4 * w * z) -
     (&1 + z pow 2) pow 2 * (&1 + w pow 2) * (&1 - w) =
     b0 * (&1 - v) pow 3 + &3 * b1 * v * (&1 - v) pow 2 +
     &3 * b2 * v pow 2 * (&1 - v) + b3 * v pow 3` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["b0"; "b1"; "b2"; "b3"] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `w = z + v * (&1 - z)`
      then SUBST1_TAC th else NO_TAC) THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b0 /\ &0 < b1 /\ &0 < b2 /\ &0 < b3` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["b0"; "b1"; "b2"; "b3"] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `z - &1 / &3`; SQ_NONNEG `z - &1 / &2`; SQ_NONNEG `z:real`]
     [`&0 < &1 + z + z pow 2`; `&0 < &3 * z pow 2 - &2 * z + &1`;
      `&0 <= z pow 2 * (&1 / &3 - z)`; `&0 <= z pow 4`;
      `&0 < &2 * z pow 4 - z pow 3 + &5 * z pow 2 - &3 * z + &3`;
      `&0 < z pow 2 - z + &1`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b0 * (&1 - v) pow 3 + &3 * b1 * v * (&1 - v) pow 2 +
     &3 * b2 * v pow 2 * (&1 - v) + b3 * v pow 3` ASSUME_TAC THENL
   [ASM_CASES_TAC `v = &1` THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 - v` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < b0 * (&1 - v) pow 3 /\ &0 <= &3 * b1 * v * (&1 - v) pow 2 /\
                  &0 <= &3 * b2 * v pow 2 * (&1 - v) /\ &0 <= b3 * v pow 3` MP_TAC THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN NO_TAC) THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; REAL_POS];
      REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + z pow 2) pow 2 * (&1 + w pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(&1 + z pow 2) pow 2 * (&1 + w pow 2)`;
     `--((&1 - t / &2) * (c * d + s * t) - &1 + w)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC);;

(* Lean: steep_gain *)
let C983CS_STEEP_GAIN = prove
 (`forall d t. &4 / &5 < d /\ &0 < t /\ t < &3 / &5 /\ d pow 2 + t pow 2 = &1
         ==> &1 < (d + (&3 / &2) * t) * (&1 - t / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`] [`d <= &1`] THEN
  NLIN_FACTS_TAC [] [`&0 <= (&1 - d) * (&1 + d - &9 / &5)`] THEN
  NLIN_FACTS_TAC [] [`--(&5 / &9) * t pow 2 <= d - &1`;
     `&0 <= t * (&1 - d)`; `&0 < t * (&1 - (&47 / &36) * t)`] THEN
  NLIN_TAC []);;
