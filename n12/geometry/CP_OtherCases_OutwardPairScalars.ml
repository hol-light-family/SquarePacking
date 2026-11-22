(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OutwardPairScalars.lean             *)
(* (namespace N12Compact.Completion.OtherCases.OutwardPairScalars).         *)
(* The two coupled-support margins for the outward southeast pair.          *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;              *)
(* SharpPointScalars.half_before: OCSPS_HALF_BEFORE; CanonicalProjection.   *)
(* before: CCCP_BEFORE; CanonicalScalars.bounds: CCCS_BOUNDS.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: cubic_positive (private) *)
let OCOPS_CUBIC_POSITIVE = prove
 (`forall t. &0 <= t /\ t <= &3 / &10
       ==> &0 < &20 - &66 * t + &40 * t pow 2 - &75 * t pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &75 * t pow 2 - &35 / &2 * t + &243 / &4` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN NLIN_TAC [SQ_NONNEG `t - &7 / &60`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&3 / &10 - t) * (&75 * t pow 2 - &35 / &2 * t + &243 / &4)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: norm_gap (private) *)
let OCOPS_NORM_GAP = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ C1092WPS_half c s < &3 / &10
         ==> (&2 - c - s + &1 / &5 * c * s) pow 2 +
             (&1 - c + s - &1 / &5 * s pow 2) pow 2 < &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `t = C1092WPS_half c s` THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `t * (&1 + c) = s` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `t:real` OCOPS_CUBIC_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 - (&2 - c - s + &1 / &5 * c * s) pow 2 -
                (&1 - c + s - &1 / &5 * s pow 2) pow 2 =
                &6 * (c - &1) + &12 / &5 * s + &9 / &25 * s pow 2 - &4 / &5 * c * s`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `&25 * (&1 + t pow 2) pow 2 *
      (&6 * (c - &1) + &12 / &5 * s + &9 / &25 * s pow 2 - &4 / &5 * c * s) =
    &4 * t * (&20 - &66 * t + &40 * t pow 2 - &75 * t pow 3)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&25 * (&1 + t pow 2) pow 2 *
        (&6 * (c - &1) + &12 / &5 * s + &9 / &25 * s pow 2 - &4 / &5 * c * s) =
      &25 * (&6 * (&1 + t pow 2) * ((&1 + t pow 2) * c - (&1 + t pow 2)) +
             &12 / &5 * (&1 + t pow 2) * ((&1 + t pow 2) * s) +
             &9 / &25 * ((&1 + t pow 2) * s) pow 2 -
             &4 / &5 * ((&1 + t pow 2) * c) * ((&1 + t pow 2) * s))` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &25 * (&1 + t pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &6 * (c - &1) + &12 / &5 * s + &9 / &25 * s pow 2 - &4 / &5 * c * s`
    MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&25 * (&1 + t pow 2) pow 2`;
      `--(&6 * (c - &1) + &12 / &5 * s + &9 / &25 * s pow 2 - &4 / &5 * c * s)`]
      REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&4 * t`; `&20 - &66 * t + &40 * t pow 2 - &75 * t pow 3`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&25 * (&1 + t pow 2) pow 2 *
      (&6 * (c - &1) + &12 / &5 * s + &9 / &25 * s pow 2 - &4 / &5 * c * s) =
      &4 * t * (&20 - &66 * t + &40 * t pow 2 - &75 * t pow 3)` THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&1 - (&2 - c - s + &1 / &5 * c * s) pow 2 -
                (&1 - c + s - &1 / &5 * s pow 2) pow 2 =
                &6 * (c - &1) + &12 / &5 * s + &9 / &25 * s pow 2 - &4 / &5 * c * s` THEN
    REAL_ARITH_TAC]);;

(* Lean: first_margin *)
let OCOPS_FIRST_MARGIN = prove
 (`forall c s C S. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\ C pow 2 + S pow 2 = &1 /\
             C1092WPS_half c s < &3 / &10
             ==> &0 < &1 + (c * S + s * C) + (c * C - s * S) -
                      (c * S + s * C) * (c + s) - (c * C - s * S) * (c - &4 / &5 * s) - C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCOPS_NORM_GAP) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = &2 - c - s + &1 / &5 * c * s` THEN
  ABBREV_TAC `B = &1 - c + s - &1 / &5 * s pow 2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(A * C + B * S) pow 2 + (A * S - B * C) pow 2 = A pow 2 + B pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `A * C + B * S < &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `A * S - B * C` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(A * C + B * S) - &1` REAL_LE_POW_2) THEN
    UNDISCH_TAC `(A * C + B * S) pow 2 + (A * S - B * C) pow 2 = A pow 2 + B pow 2` THEN
    UNDISCH_TAC `A pow 2 + B pow 2 < &1` THEN
    SPEC_TAC(`A * C + B * S`,`x:real`) THEN SPEC_TAC(`A * S - B * C`,`y:real`) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (c * S + s * C) + (c * C - s * S) -
      (c * S + s * C) * (c + s) - (c * C - s * S) * (c - &4 / &5 * s) - C =
      &1 - A * C - B * S` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: second_margin *)
let OCOPS_SECOND_MARGIN = prove
 (`forall c s C S. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
             &0 < C /\ &0 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1 /\
             C1092WPS_half c s < &3 / &10
             ==> &0 < &1 + (c * C - s * S) + (c * S + s * C) +
                      &7 / &20 * (c * C - s * S) * (S - C) - (c * S + s * C) * C - c - s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `A = &1 - C - S + &7 / &20 * C pow 2 + &13 / &20 * C * S` THEN
  ABBREV_TAC `B = &2 - C + S - &13 / &20 * S pow 2 - &7 / &20 * C * S` THEN
  SUBGOAL_THEN `&0 <= C * S` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A <= &7 / &20` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MP_TAC(SPEC `S:real` REAL_LE_POW_2) THEN
    UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN UNDISCH_TAC `&0 <= C * S` THEN
    UNDISCH_TAC `&1 + &4 / &5 * C * S <= C + S` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * S <= &1 / &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `C - S` REAL_LE_POW_2) THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - C) pow 2 < &9 / &100` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (C - &7 / &10) * (&13 / &10 - C)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `A + B <= &8 / &5` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `(&1 - C) pow 2 < &9 / &100` THEN UNDISCH_TAC `C * S <= &1 / &2` THEN
    UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c - s) * (&7 / &20 - A) /\ &0 <= s * (&8 / &5 - (A + B))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&91 / &109`; `&60 / &109`; `&3 / &10`]
    OCSPS_HALF_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&91 / &109`; `&60 / &109`; `&7 / &20`; `&5 / &4`]
    CCCP_BEFORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 + (c * C - s * S) + (c * S + s * C) +
      &7 / &20 * (c * C - s * S) * (S - C) - (c * S + s * C) * C - c - s =
      &1 - A * c - B * s` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;
