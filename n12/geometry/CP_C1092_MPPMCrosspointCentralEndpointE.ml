(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointCentralEndpointE.lean       *)
(* (N12Compact.C1092MPPMCrosspointSupport.Central), STEEP-POSITIVE-CENTRAL-  *)
(* SCALAR section 3.  Normal is c977cc_normal; G00 etc. are c1092mcs_*;      *)
(* diagonalValue / diagonal_lower: c1092mcca_ / C1092MCCA_; UnitCircleChord: *)
(* CCUCC_*; canonical/steep bounds C1092PRS_*.  Lean C, S are CC, SS.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointCentralAligned.ml";;

let C1092MCCE_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: coefficients (private) *)
let C1092MCCE_COEFFICIENTS = prove
 (`forall d t. c977cc_normal d t
     ==> &9 / &10 <= d * (&2 - d) /\
         --(&11 / &20) <= &2 - (&1043 / &500) * d - (&36 / &25) * t + d * t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= (d - &7 / &10) * (&13 / &10 - d)` THEN
  C1092PRS_PROD `&0 <= d * t` THEN
  SUBGOAL_THEN `(&1043 / &500) * d + (&36 / &25) * t < &51 / &20` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 <= ((&1043 / &500) * d + (&36 / &25) * t - &51 / &20) *
                        ((&1043 / &500) * d + (&36 / &25) * t + &51 / &20)` THEN
   MP_TAC(SPEC `(&36 / &25) * d - (&1043 / &500) * t` REAL_LE_POW_2) THEN DISCH_TAC THEN
   C1092MCCE_LP_TAC; ALL_TAC] THEN
  C1092MCCE_LP_TAC);;

(* Lean: move_up (private) *)
let C1092MCCE_MOVE_UP = prove
 (`forall c s CC SS A B. c977cc_normal c s /\ c977cc_normal CC SS /\ &3 / &5 <= s /\
                   &3 / &5 <= SS /\ SS <= s /\ &9 / &10 <= A /\ --(&11 / &20) <= B
                   ==> --A * CC + B * SS <= --A * c + B * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`CC:real`; `SS:real`] C1092PRS_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= (A - &9 / &10) * (s + SS)` THEN
  C1092PRS_PROD `&0 <= (B + &11 / &20) * (c + CC)` THEN
  SUBGOAL_THEN `&0 <= A * (s + SS) + B * (c + CC)` ASSUME_TAC THENL
  [C1092MCCE_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (s - SS) * (A * (s + SS) + B * (c + CC))` THEN
  SUBGOAL_THEN `(c + CC) * ((--A * c + B * s) - (--A * CC + B * SS)) =
                (s - SS) * (A * (s + SS) + B * (c + CC))` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `CC pow 2 + SS pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 < (c + CC) * ((--A * CC + B * SS) - (--A * c + B * s))` THEN
  RASM_ARITH_TAC);;

(* Lean: lowerValue (private definition) *)
let c1092mcce_lowerValue = new_definition
 `c1092mcce_lowerValue (d:real) (t:real) =
    &6 / &5 - (&4629 / &2500) * d + (&4 / &5) * d pow 2 - (&108 / &125) * t +
    (&3 / &5) * d * t`;;

(* Lean: lower_endpoint (private) *)
let C1092MCCE_LOWER_ENDPOINT = prove
 (`forall d t. c977cc_normal d t /\ t <= &3 / &5 ==> &1 / &3125 <= c1092mcce_lowerValue d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&4 / &5`; `&3 / &5`] CCUCC_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
                  DISCH_TAC] THEN
  ABBREV_TAC `J = (t + &3 / &5) * ((&4 / &5) * d - &2129 / &2500) +
                  (d + &4 / &5) * (&108 / &125 - (&3 / &5) * d)` THEN
  SUBGOAL_THEN `&0 <= J` ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN
   C1092PRS_PROD `&0 <= (t + &3 / &5) * ((&4 / &5) * d - &2129 / &2500 + &11 / &50)` THEN
   C1092PRS_PROD `&0 <= (d + &4 / &5) * (&108 / &125 - (&3 / &5) * d - &33 / &125)` THEN
   C1092MCCE_LP_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (&3 / &5 - t) * J` THEN
  SUBGOAL_THEN `(d + &4 / &5) * (c1092mcce_lowerValue d t - &1 / &3125) = (&3 / &5 - t) * J`
  ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN REWRITE_TAC[c1092mcce_lowerValue] THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 < (d + &4 / &5) * (&1 / &3125 - c1092mcce_lowerValue d t)` THEN
  RASM_ARITH_TAC);;

(* Lean: aligned_E *)
let C1092MCCE_ALIGNED_E = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s
     ==> &1 / &3125 <= c1092mcs_G00 c s d t d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MCCE_COEFFICIENTS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092PRS_NORMAL_TAC THEN
  REWRITE_TAC[c1092mcs_G00; c1092mcs_k; c1092mcs_kC; c1092mcs_kE; c1092mcs_deltaC;
              c1092mcs_deltaE; c1092mcs_C0; c1092mcs_E0;
              REAL_ARITH `d * t - t * d = &0`; REAL_ABS_0] THEN
  ASM_CASES_TAC `t <= s` THENL
  [MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] CCUCC_CROSS_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= d * s - t * c ==> abs(c * t - s * d) = s * d - c * t`] THEN
   ABBREV_TAC `A = d * (&2 - d)` THEN
   ABBREV_TAC `B = &2 - (&1043 / &500) * d - (&36 / &25) * t + d * t` THEN
   MATCH_MP_TAC(REAL_ARITH `forall g. g = d - A * c + B * s /\ &1 / &3125 <= d - A * c + B * s
                 ==> &1 / &3125 <= g`) THEN
   CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_CASES_TAC `&3 / &5 <= t` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `A:real`; `B:real`]
      C1092MCCE_MOVE_UP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`d:real`; `t:real`] C1092MCCA_DIAGONAL_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `d - A * d + B * t = c1092mcca_diagonalValue d t` ASSUME_TAC THENL
    [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[c1092mcca_diagonalValue] THEN
     UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`c:real`; `s:real`; `&4 / &5`; `&3 / &5`; `A:real`; `B:real`]
      C1092MCCE_MOVE_UP) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
    MP_TAC(SPECL [`d:real`; `t:real`] C1092MCCE_LOWER_ENDPOINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `d - A * (&4 / &5) + B * (&3 / &5) = c1092mcce_lowerValue d t`
    ASSUME_TAC THENL
    [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[c1092mcce_lowerValue] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `s <= t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CCUCC_CROSS_ORDER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
   ABBREV_TAC `A = d * (&2 - d - t)` THEN
   ABBREV_TAC `B = &1 - (&1043 / &500) * d + t * (d + t - &36 / &25)` THEN
   SUBGOAL_THEN `&0 <= A /\ &0 <= --B /\ &0 <= --B * d - A * t` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    C1092PRS_PROD `&0 <= d * (&2 - d - t)` THEN
    C1092PRS_PROD `&0 <= t * --(d + t - &36 / &25)` THEN
    C1092PRS_PROD `&0 <= d * ((&1043 / &500) * d - (&14 / &25) * t - &1)` THEN
    C1092MCCE_LP_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`; `A:real`; `--B:real`] CCUCC_INCREASING) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(SPECL [`d:real`; `t:real`] C1092MCCA_DIAGONAL_LOWER) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `d - A * d + B * t = c1092mcca_diagonalValue d t` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[c1092mcca_diagonalValue] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `forall g. g = d - A * c + B * s /\ &1 / &3125 <= d - A * c + B * s
                 ==> &1 / &3125 <= g`) THEN
   CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REAL_ARITH_TAC; RASM_ARITH_TAC]]);;
