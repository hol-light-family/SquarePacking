(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointG01.lean           *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport).  NEGATIVE-WALL-SCALARS  *)
(* section 7: the complete G01 boundary mode.  G01, G00, width, kC, deltaC, *)
(* C0, P, Q, P2, Q2, FE, deltaE, Quarter: c1092mncs_*; Normal: c977cc_normal;*)
(* G01Quartic (poly, T, endpoints, bernstein, steep_bounds, half_bound,     *)
(* lower_coefficient, parameter_identity / _bound / _order): C1092G01Q_*;   *)
(* coefficient_bounds / FE_*: C1092MNCF_*; G00_nonnegative:                 *)
(* C1092MNCC_G00_NONNEGATIVE; half / quarter_data: C1092WPS_half /          *)
(* C1092WPS_QUARTER_DATA.  Tag C1092NG01_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG01Quartic.ml";;

let C1092NG01_LIN = REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092NG01_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   TRY(MATCH_MP_TAC REAL_POW_LE) THEN C1092NG01_LIN; ALL_TAC];;

let C1092NG01_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092NG01_LIN; ALL_TAC];;

let C1092NG01_QUARTER_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;

(* Lean: central_order (private) *)
let C1092NG01_CENTRAL_ORDER = prove
 (`forall c s h r. c977cc_normal c s /\ c1092mncs_quarter h r /\ h <= r
             ==> &0 <= c1092mncs_deltaC c s h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN C1092NG01_QUARTER_TAC THEN
  REWRITE_TAC[c1092mncs_deltaC] THEN
  C1092NG01_PROD `&0 <= (c - s) * r` THEN C1092NG01_PROD `&0 <= s * (r - h)` THEN
  C1092NG01_LIN);;

(* Lean: first_formula (private) *)
let C1092NG01_FIRST_FORMULA = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ c1092mncs_quarter h r /\ h <= r /\
                 c1092mncs_deltaE d t h r <= &0
     ==> c1092mncs_G01 c s d t h r =
         (c - s) * h pow 2 + (c + s) * h * r + s -
         (&2 * c + s - &1 - s * c1092mncs_P d t) * h - s * (&2 - c1092mncs_Q d t) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NG01_CENTRAL_ORDER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MNCF_FE_LOWER_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[c1092mncs_G01; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  C1092NG01_QUARTER_TAC THEN
  REWRITE_TAC[c1092mncs_kC; c1092mncs_deltaC; c1092mncs_C0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: second_formula (private) *)
let C1092NG01_SECOND_FORMULA = prove
 (`forall c s d t h r. c977cc_normal c s /\ c1092mncs_quarter h r /\ h <= r /\
                 &0 <= c1092mncs_deltaE d t h r
     ==> c1092mncs_G01 c s d t h r =
         (c - s) * h pow 2 + (c + s) * h * r + s -
         (&2 * c + s - &1 + s * c1092mncs_P2 d t) * h - s * (&2 + c1092mncs_Q2 d t) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NG01_CENTRAL_ORDER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MNCF_FE_UPPER_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[c1092mncs_G01; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  C1092NG01_QUARTER_TAC THEN
  REWRITE_TAC[c1092mncs_kC; c1092mncs_deltaC; c1092mncs_C0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: aligned (private) *)
let C1092NG01_ALIGNED = prove
 (`forall c s d t. c977cc_normal d t ==> c1092mncs_G01 c s d t t d = c1092mncs_G00 c s d t t d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092MNCF_FE_ALIGNED) THEN
  ASM_REWRITE_TAC[c1092mncs_G01; c1092mncs_G00; c1092mncs_width] THEN
  REWRITE_TAC[c1092mncs_deltaE; REAL_ARITH `t * d - d * t = &0`; REAL_ABS_0] THEN
  REWRITE_TAC[c1092mncs_kC; c1092mncs_ell; c1092mncs_kE; c1092mncs_deltaC] THEN
  SPEC_TAC(`abs(c * d - s * t)`, `w:real`) THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[c977cc_normal]) THEN
  CONV_TAC REAL_RING);;

(* Lean: aligned_endpoint (private) *)
let C1092NG01_ALIGNED_ENDPOINT = prove
 (`forall c s d t A B. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ &8 * t <= &3 * d /\
                 c1092mncs_G01 c s d t t d =
                 (c - s) * t pow 2 + (c + s) * t * d + s - A * t - B * d
                 ==> &0 <= c1092g01q_T c s A B (C1092WPS_half d t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1092mncs_quarter t d` ASSUME_TAC THENL
   [UNDISCH_TAC `c977cc_normal d t` THEN
    REWRITE_TAC[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] THEN
    STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `t:real`; `d:real`]
    C1092MNCC_G00_NONNEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092NG01_ALIGNED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `A:real`; `B:real`; `t:real`; `d:real`]
    C1092G01Q_PARAMETER_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let C1092NG01_COEFF_TAC =
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MNCF_COEFFICIENT_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G01Q_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092G01Q_HALF_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC;;

(* Lean: first_interval (private) *)
let C1092NG01_FIRST_INTERVAL = prove
 (`forall c s d t z. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ &8 * t <= &3 * d /\
               C1092WPS_half d t <= z /\ z <= &5 / &12
               ==> &0 <= c1092g01q_T c s (&2 * c + s - &1 - s * c1092mncs_P d t)
                                         (s * (&2 - c1092mncs_Q d t)) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`;
                `&2 * c + s - &1 - s * c1092mncs_P d t`; `s * (&2 - c1092mncs_Q d t)`]
    C1092NG01_ALIGNED_ENDPOINT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `t:real`; `d:real`]
    C1092NG01_FIRST_FORMULA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter; c1092mncs_deltaE;
                    REAL_ARITH `t * d - d * t = &0`; REAL_LE_REFL] THEN
    UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  C1092NG01_COEFF_TAC THEN
  REWRITE_TAC[c1092g01q_T] THEN MATCH_MP_TAC C1092G01Q_ENDPOINTS THEN
  MAP_EVERY EXISTS_TAC [`C1092WPS_half d t`; `&5 / &12`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092g01q_T]) THEN
  C1092NG01_PROD `&0 <= s * c1092mncs_P d t` THEN
  C1092NG01_PROD `&0 <= s * (&3 / &10 - c1092mncs_P d t)` THEN
  C1092NG01_PROD `&0 <= s * (&1 - c1092mncs_Q d t)` THEN
  C1092NG01_PROD `&0 <= s * (&1 / &5 - (&1 - c1092mncs_Q d t))` THEN
  C1092NG01_PROD `&0 <= s * (c1092mncs_P d t - (&1 - c1092mncs_Q d t))` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[c1092g01q_poly] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  C1092NG01_LIN);;

(* Lean: last_interval (private) *)
let C1092NG01_LAST_INTERVAL = prove
 (`forall c s d t z. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ &8 * t <= &3 * d /\
               &0 <= z /\ z <= C1092WPS_half d t
               ==> &0 <= c1092g01q_T c s (&2 * c + s - &1 + s * c1092mncs_P2 d t)
                                         (s * (&2 + c1092mncs_Q2 d t)) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`;
                `&2 * c + s - &1 + s * c1092mncs_P2 d t`; `s * (&2 + c1092mncs_Q2 d t)`]
    C1092NG01_ALIGNED_ENDPOINT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `t:real`; `d:real`]
    C1092NG01_SECOND_FORMULA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter; c1092mncs_deltaE;
                    REAL_ARITH `t * d - d * t = &0`; REAL_LE_REFL] THEN
    UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092G01Q_LOWER_COEFFICIENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092NG01_COEFF_TAC THEN
  ASM_CASES_TAC `C1092WPS_half d t = &0` THENL
   [SUBGOAL_THEN `z = C1092WPS_half d t` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C1092WPS_half d t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s - (s * (&2 + c1092mncs_Q2 d t))) = s * t * (&1 - (&61 / &100) * d - (&13 / &20) * t)` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_Q2] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092NG01_PROD `&0 <= s * (t * (&1 - (&61 / &100) * d - (&13 / &20) * t) +
                   (&3 / &2) * (&1 / &3 - c1092mncs_P2 d t) * C1092WPS_half d t - (&21 / &8) * C1092WPS_half d t pow 3)` THEN
  C1092NG01_PROD `&0 <= s * (c1092mncs_P2 d t - &1 / &3)` THEN
  C1092NG01_PROD `&0 <= s * (c1092mncs_P2 d t - &1 / &3) * C1092WPS_half d t` THEN
  C1092NG01_PROD `&0 <= s * C1092WPS_half d t pow 3` THEN
  C1092NG01_PROD `&0 <= s * (&13 / &20 - c1092mncs_P2 d t)` THEN
  C1092NG01_FACT `&2 * s * (&1 / &3 - c1092mncs_P2 d t) <= (&2 * (c + s - (&2 * c + s - &1 + s * c1092mncs_P2 d t)))` THEN
  C1092NG01_FACT `&0 <= (&4 * c - &2 * s)` THEN
  C1092NG01_FACT `&3 * c <= &4 * s` THEN
  C1092NG01_FACT `--(&21 / &2) * s <= (--(&2) * (c + s + (&2 * c + s - &1 + s * c1092mncs_P2 d t)))` THEN
  C1092NG01_PROD `&0 <= ((&2 * (c + s - (&2 * c + s - &1 + s * c1092mncs_P2 d t))) / &4 - (&3 / &2) * s * (&1 / &3 - c1092mncs_P2 d t)) * C1092WPS_half d t` THEN
  C1092NG01_PROD `&0 <= ((&2 * (c + s - (&2 * c + s - &1 + s * c1092mncs_P2 d t))) / &2 - (&3 / &2) * s * (&1 / &3 - c1092mncs_P2 d t)) * C1092WPS_half d t` THEN
  C1092NG01_PROD `&0 <= (&3 * (&2 * (c + s - (&2 * c + s - &1 + s * c1092mncs_P2 d t))) / &4 - (&3 / &2) * s * (&1 / &3 - c1092mncs_P2 d t)) * C1092WPS_half d t` THEN
  C1092NG01_PROD `&0 <= (&4 * c - &2 * s) * C1092WPS_half d t pow 2` THEN
  C1092NG01_PROD `&0 <= ((--(&2) * (c + s + (&2 * c + s - &1 + s * c1092mncs_P2 d t))) / &4 + (&21 / &8) * s) * C1092WPS_half d t pow 3` THEN
  UNDISCH_TAC `&0 <= c1092g01q_T c s (&2 * c + s - &1 + s * c1092mncs_P2 d t) (s * (&2 + c1092mncs_Q2 d t)) (C1092WPS_half d t)` THEN
  REWRITE_TAC[c1092g01q_T] THEN DISCH_TAC THEN
  MATCH_MP_TAC C1092G01Q_BERNSTEIN THEN EXISTS_TAC `C1092WPS_half d t` THEN
  ASM_REWRITE_TAC[] THEN C1092NG01_LIN);;

let C1092NG01_HALF_ORDER = prove
 (`forall w z k d. &0 <= w /\ &0 <= z /\ k * d = &2 * (w - z) * (&1 + w * z) /\ &0 < k
   ==> (&0 <= d ==> z <= w) /\ (d <= &0 ==> w <= z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + w * z` ASSUME_TAC THENL
   [MP_TAC(SPECL [`w:real`; `z:real`] REAL_LE_MUL) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`z - w`; `&1 + w * z`] REAL_LT_MUL) THEN
    MP_TAC(SPECL [`k:real`; `d:real`] REAL_LE_MUL);
    MP_TAC(SPECL [`w - z`; `&1 + w * z`] REAL_LT_MUL) THEN
    MP_TAC(SPECL [`k:real`; `--d`] REAL_LE_MUL)] THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: G01_nonnegative *)
let C1092NG01_G01_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ &8 * t <= &3 * d /\
                 c1092mncs_quarter h r /\ h <= r
                 ==> &0 <= c1092mncs_G01 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092G01Q_PARAMETER_ORDER) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092G01Q_PARAMETER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  MP_TAC(SPECL [`r:real`; `h:real`] C1092WPS_QUARTER_DATA) THEN
  UNDISCH_TAC `c1092mncs_quarter h r` THEN UNDISCH_TAC `c977cc_normal d t` THEN
  REWRITE_TAC[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
         ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  MP_TAC(SPECL [`C1092WPS_half d t`; `C1092WPS_half r h`;
                `(&1 + C1092WPS_half d t pow 2) * (&1 + C1092WPS_half r h pow 2)`;
                `c1092mncs_deltaE d t h r`] C1092NG01_HALF_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    STRIP_TAC] THEN
  SUBGOAL_THEN `c1092mncs_quarter h r` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter]; ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal d t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal]; ALL_TAC] THEN
  MATCH_MP_TAC C1092G01Q_NONNEG_OF_MUL THEN
  EXISTS_TAC `(&1 + C1092WPS_half r h pow 2) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c1092mncs_deltaE d t h r` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `C1092WPS_half r h`]
      C1092NG01_LAST_INTERVAL) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `(&2 * c + s - &1 + s * c1092mncs_P2 d t)`; `(s * (&2 + c1092mncs_Q2 d t))`; `h:real`; `r:real`]
      C1092G01Q_PARAMETER_IDENTITY) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
      C1092NG01_SECOND_FORMULA);
    MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `C1092WPS_half r h`]
      C1092NG01_FIRST_INTERVAL) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `&2 * c + s - &1 - s * c1092mncs_P d t`;
                  `s * (&2 - c1092mncs_Q d t)`; `h:real`; `r:real`]
      C1092G01Q_PARAMETER_IDENTITY) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
      C1092NG01_FIRST_FORMULA)] THEN
  ASM_REWRITE_TAC[] THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] ORELSE ALL_TAC) THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  (ANTS_TAC THENL [ASM_MESON_TAC[REAL_NOT_LE; REAL_LT_IMP_LE]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> &0 <= x ==> &0 <= y`) THEN CONV_TAC REAL_RING);;
