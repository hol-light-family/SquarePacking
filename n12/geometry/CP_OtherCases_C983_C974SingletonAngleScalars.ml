(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974SingletonAngleScalars.lean *)
(* (N12Compact.Completion.OtherCases.C983.C974MissingCorner).  The calculus  *)
(* estimate of MISSING-CORNER-MIDPOINT §1.4 (equation (14)).  The Lean       *)
(* private calculus helpers (D, G, G1, Q, Q1, Q2, endpoint, interval_data,   *)
(* derivative_*, Q2_negative, endpoint_values, Q_positive, G_lower) only     *)
(* serve the public theorem singleton_angle_G; they are replaced here by an  *)
(* algebraic half-angle argument: with y = t / (1 + d), (G - 1/4) times      *)
(* (1 + y^2)^2 is the quartic 1/8 - y + 9/4 y^2 - 27/8 y^4, positive on the  *)
(* interval 0 <= y, y^2 + 3 y <= 1 that 3 t <= 2 d defines.                  *)
(* (Lean header: "Source only, uncompiled".)  Tag C974SAS_.                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974SingletonSign.ml";;

(* the quartic on the half-angle interval *)
let C974SAS_QUARTIC = prove
 (`forall y. &0 <= y /\ y pow 2 + &3 * y <= &1
       ==> &0 < &1 / &8 - y + &9 / &4 * y pow 2 - &27 / &8 * y pow 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`y <= &1 / &3`; `&0 <= y * (&1 - y pow 2 - &3 * y)`;
                     `&0 <= y pow 2 * (&1 - y pow 2 - &3 * y)`] THEN
  NLIN_TAC [SQ_NONNEG `y - &3 / &10`; SQ_NONNEG `y pow 2 - &1 / &11`]);;

(* Lean: singleton_angle_G *)
let C974SAS_SINGLETON_ANGLE_G = prove
 (`forall d t. &0 < d /\ &0 <= t /\ d pow 2 + t pow 2 = &1 /\ &3 * t <= &2 * d
         ==> &1 / &4 < (&7 / &4) * d - (&11 / &8) * d pow 2 - (&1 / &4) * d * t - t / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `y = t / (&1 + d)` THEN
  SUBGOAL_THEN `&0 < &1 + d` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y * (&1 + d) = t` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    UNDISCH_TAC `&0 < &1 + d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= y` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < &1 + d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * y = &1 - d` ASSUME_TAC THENL
   [MP_TAC(SPECL [`t * y`; `&1 - d`; `&1 + d`] REAL_EQ_MUL_RCANCEL) THEN
    SUBGOAL_THEN `~(&1 + d = &0)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < &1 + d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`y * (&1 + d) = t`; `d pow 2 + t pow 2 = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `d * (&1 + y pow 2) = &1 - y pow 2 /\ t * (&1 + y pow 2) = &2 * y`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MAP_EVERY UNDISCH_TAC [`y * (&1 + d) = t`; `t * y = &1 - d`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + y pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y pow 2 + &3 * y <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&2 * d - &3 * t) * (&1 + y pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&3 * t <= &2 * d` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `&0 < &1 + y pow 2` THEN REAL_ARITH_TAC];
      MAP_EVERY UNDISCH_TAC
       [`d * (&1 + y pow 2) = &1 - y pow 2`; `t * (&1 + y pow 2) = &2 * y`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real` C974SAS_QUARTIC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((&7 / &4) * d - (&11 / &8) * d pow 2 - (&1 / &4) * d * t - t / &4 - &1 / &4) *
    (&1 + y pow 2) pow 2 = &1 / &8 - y + &9 / &4 * y pow 2 - &27 / &8 * y pow 4`
    ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`d * (&1 + y pow 2) = &1 - y pow 2`; `t * (&1 + y pow 2) = &2 * y`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + y pow 2) pow 2` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  UNDISCH_TAC
   `((&7 / &4) * d - (&11 / &8) * d pow 2 - (&1 / &4) * d * t - t / &4 - &1 / &4) *
    (&1 + y pow 2) pow 2 = &1 / &8 - y + &9 / &4 * y pow 2 - &27 / &8 * y pow 4` THEN
  UNDISCH_TAC `&0 < &1 / &8 - y + &9 / &4 * y pow 2 - &27 / &8 * y pow 4` THEN
  SPEC_TAC(`(&1 + y pow 2) pow 2`, `D:real`) THEN
  SPEC_TAC(`(&7 / &4) * d - (&11 / &8) * d pow 2 - (&1 / &4) * d * t - t / &4`, `E:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 / &4 - E) * D` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(E - &1 / &4) * D = &1 / &8 - y + &9 / &4 * y pow 2 - &27 / &8 * y pow 4`;
    `&0 < &1 / &8 - y + &9 / &4 * y pow 2 - &27 / &8 * y pow 4`] THEN
  REAL_ARITH_TAC);;
