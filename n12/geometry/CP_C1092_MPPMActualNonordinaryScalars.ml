(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualNonordinaryScalars.lean        *)
(* (N12Compact.C1092MPPMActualNonordinary).  Exact scalar margins for       *)
(* ELBOW-EXCLUSION Theorem 3.  Normal is c977cc_normal.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ElbowProfile.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_MMMP_PositiveInwardHalfangle.ml";;

let C1092MANS_LIN = NLIN_TAC ~deg2:false [];;

let C1092MANS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MANS_LIN; ALL_TAC];;

let C1092MANS_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092MANS_LIN; ALL_TAC];;

let C1092MANS_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C1092MANS_NORMALS_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  REWRITE_TAC[REAL_POW_2];;

(* Lean: normal_sum *)
let C1092MANS_NORMAL_SUM = prove
 (`forall d t. c977cc_normal d t
         ==> &1 <= d + t /\ d + t < &10 / &7 /\ (&4 / &5) * (d * t) <= d + t - &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MANS_NORMALS_TAC THEN
  C1092MANS_PROD `&0 <= d * t` THEN
  SUBGOAL_THEN `&1 <= d + t` ASSUME_TAC THENL
   [C1092MANS_CONTRA THEN C1092MANS_PROD `&0 < (&1 - (d + t)) * (&1 + d + t)` THEN C1092MANS_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `d + t < &10 / &7` ASSUME_TAC THENL
   [C1092MANS_CONTRA THEN C1092MANS_PROD `&0 <= (d + t - &10 / &7) * (d + t + &10 / &7)` THEN
    MP_TAC(SPEC `d - t:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN C1092MANS_LIN;
    ALL_TAC] THEN
  C1092MANS_PROD `&0 <= (d + t - &1) * (&3 / &2 - d - t)` THEN
  ASM_REWRITE_TAC[] THEN C1092MANS_LIN);;

(* Lean: relative_bounds *)
let C1092MANS_RELATIVE_BOUNDS = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &24 / &25 < c /\ &0 < s /\ s < &7 / &25
             ==> &0 < c * d - s * t /\ &0 < c * t + s * d /\
                 c * d - s * t <= &1 /\ c * t + s * d <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MANS_NORMALS_TAC THEN
  C1092MANS_PROD `&0 < (c - s) * d` THEN
  C1092MANS_PROD `&0 <= s * (d - t)` THEN
  C1092MANS_PROD `&0 <= c * t` THEN
  C1092MANS_PROD `&0 < s * d` THEN
  SUBGOAL_THEN `(c * d - s * t) * (c * d - s * t) + (c * t + s * d) * (c * t + s * d) = &1`
    ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c * c + s * s = &1`; `d * d + t * t = &1`] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY C1092MANS_LIN THENL
   [NLIN_TAC [SQ_NONNEG `c * t + s * d`; SQ_NONNEG `c * d - s * t - &1`];
    NLIN_TAC [SQ_NONNEG `c * d - s * t`; SQ_NONNEG `c * t + s * d - &1`]]);;

(* Lean: source_longitudinal *)
let C1092MANS_SOURCE_LONGITUDINAL = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < c /\ &0 < s
             ==> &0 < &1 - c - (&2 / &5) * s + (c * d - s * t) * (&1 - d - t) +
                      (c * t + s * d) * (&1 - t + (&2 / &5) * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MANS_NORMAL_SUM) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN C1092MANS_NORMALS_TAC THEN
  C1092MANS_PROD `&0 <= d * t` THEN
  C1092MANS_PROD `&0 < s * s` THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  C1092MANS_PROD `&0 <= c * (d + t - &1 - (&3 / &5) * (d * t))` THEN
  C1092MANS_PROD `&0 <= t * t` THEN
  C1092MANS_PROD `&0 <= s * (d - t + (&3 / &5) * t * t)` THEN
  SUBGOAL_THEN
   `&1 - c - (&2 / &5) * s + (c * d - s * t) * (&1 - d - t) +
    (c * t + s * d) * (&1 - t + (&2 / &5) * d) =
    (&1 - c) + c * (d + t - &1 - (&3 / &5) * (d * t)) + s * (d - t + (&3 / &5) * t * t)`
    SUBST1_TAC THENL
   [UNDISCH_TAC `d * d + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MANS_LIN);;

(* the dot bound: a vector of norm < 1 against a unit vector *)
let C1092MANS_DOT = prove
 (`forall A B d t. A pow 2 + B pow 2 < &1 /\ d pow 2 + t pow 2 = &1 ==> A * d + B * t < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(A * d + B * t) pow 2 + (A * t - B * d) pow 2 = A pow 2 + B pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MANS_CONTRA THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092MANS_PROD `&0 <= (A * d + B * t - &1) * (A * d + B * t + &1)` THEN
  NLIN_TAC [SQ_NONNEG `A * t - B * d`]);;

(* Lean: successor_longitudinal *)
let C1092MANS_SUCCESSOR_LONGITUDINAL = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < c /\ &0 < s /\
             s / (&1 + c) < &7 / &50
             ==> &0 < &1 - d - t + (c * d - s * t) * (&1 - c - (&2 / &5) * s) +
                      (c * t + s * d) * (&1 - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&2 - c - s + (&2 / &5) * c * s) pow 2 +
                (&1 - c + s - (&2 / &5) * s pow 2) pow 2 < &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `s:real`] C1092MPIH_HALF_IDENTITIES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `c977cc_normal c s` THEN SIMP_TAC[c977cc_normal]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s / (&1 + c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `s / (&1 + c) < &7 / &50` THEN REWRITE_TAC[C1092WPS_half] THEN
    SPEC_TAC(`s / (&1 + c)`,`z:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
     [MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c = (&1 - z pow 2) / (&1 + z pow 2) /\ s = (&2 * z) / (&1 + z pow 2)`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN
      MAP_EVERY UNDISCH_TAC [`z * (&1 + c) = s`; `s * z = &1 - c`] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&1 - ((&2 - (&1 - z pow 2) / (&1 + z pow 2) - (&2 * z) / (&1 + z pow 2) +
             (&2 / &5) * (&1 - z pow 2) / (&1 + z pow 2) * (&2 * z) / (&1 + z pow 2)) pow 2 +
            (&1 - (&1 - z pow 2) / (&1 + z pow 2) + (&2 * z) / (&1 + z pow 2) -
             (&2 / &5) * ((&2 * z) / (&1 + z pow 2)) pow 2) pow 2) =
      (&4 * z * (&15 - &59 * z + &55 * z pow 2 - &75 * z pow 3)) /
      (&25 * (&1 + z pow 2) pow 2)` MP_TAC THENL
     [UNDISCH_TAC `&0 < &1 + z pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&4 * z * (&15 - &59 * z + &55 * z pow 2 - &75 * z pow 3)) /
                       (&25 * (&1 + z pow 2) pow 2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_POW_2; REAL_ARITH `z pow 3 = z * z * z`] THEN
        C1092MANS_PROD `&0 <= (z * z) * (&55 - &75 * z)` THEN C1092MANS_LIN;
        MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&2 - c - s + (&2 / &5) * c * s`; `&1 - c + s - (&2 / &5) * s pow 2`;
                `d:real`; `t:real`] C1092MANS_DOT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal d t` THEN SIMP_TAC[c977cc_normal];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &1 - y ==> y < &1 ==> &0 < x`) THEN
  UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: source_transverse *)
let C1092MANS_SOURCE_TRANSVERSE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &24 / &25 < c /\ &0 < s /\ s < &7 / &25
             ==> &0 < &1 - s + (c * d - s * t) * (&1 - (&543 / &500) * d) +
                      (c * t + s * d) * (&1 - d - t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MANS_RELATIVE_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MANS_NORMAL_SUM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092MANS_NORMALS_TAC THEN
  C1092MANS_PROD `&0 <= (c * d - s * t) * (&1 - d)` THEN
  C1092MANS_PROD `&0 <= (&1 - (c * t + s * d)) * (d + t - &1)` THEN
  C1092MANS_LIN);;

(* Lean: successor_transverse *)
let C1092MANS_SUCCESSOR_TRANSVERSE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &24 / &25 < c /\ &0 < s /\ s < &7 / &25
             ==> &0 < &1 + ((c * d - s * t) + (c * t + s * d)) * (&1 - c) +
                      (&2 / &5) * ((c * d - s * t) - (c * t + s * d)) * s - t + (&2 / &5) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MANS_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MANS_NORMALS_TAC THEN
  C1092MANS_PROD `&0 <= ((c * d - s * t) + (c * t + s * d)) * (&1 - c)` THEN
  C1092MANS_PROD `&0 <= ((c * d - s * t) - (c * t + s * d) + &1) * s` THEN
  C1092MANS_LIN);;
