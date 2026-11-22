(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointG10Low.lean        *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport).  NEGATIVE-WALL-SCALARS  *)
(* G10 below the diagonal.  G10, FC, kE, deltaE, E0, Quarter, ... are the    *)
(* c1092mncs_* constants; half / quarter_data are C1092WPS_half /            *)
(* C1092WPS_QUARTER_DATA.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointClamp.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let C1092MNG10L_LIN = NLIN_TAC ~deg2:false [];;

let C1092MNG10L_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MNG10L_LIN; ALL_TAC];;

let C1092MNG10L_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092MNG10L_LIN; ALL_TAC];;

let C1092MNG10L_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C1092MNG10L_QUARTER_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;

let C1092MNG10L_POS_OF_MUL = prove
 (`forall x k. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: G10_before *)
let C1092MNG10L_G10_BEFORE = prove
 (`forall c s d t h r. c977cc_normal d t /\ c1092mncs_quarter h r /\ c1092mncs_deltaE d t h r <= &0
     ==> c1092mncs_G10 c s d t h r =
         t * (h * (h + r - &2) - c1092mncs_FC c s h r - (&13 / &50) * r) +
         d * r * (h + r - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNG10L_QUARTER_TAC THEN
  REWRITE_TAC[c1092mncs_G10] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REWRITE_TAC[c1092mncs_kE; c1092mncs_deltaE; c1092mncs_E0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: low_polynomial (private) *)
let C1092MNG10L_LOW_POLYNOMIAL = prove
 (`forall h r. c1092mncs_quarter h r /\ &4 / &5 <= h /\ r <= &3 / &5
         ==> &0 < r * (h + r - &1) + (&3 / &8) * (h * (h + r - &21 / &25) - (&57 / &50) * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNG10L_QUARTER_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092WPS_QUARTER_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `C1092WPS_half h r <= &1 / &3` MP_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN
    SUBGOAL_THEN `&0 < &1 + h` (fun th -> SIMP_TAC[REAL_LE_LDIV_EQ; th]) THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half h r`,`z:real`) THEN GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h = (&1 - z pow 2) / (&1 + z pow 2) /\ r = (&2 * z) / (&1 + z pow 2)`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&200 * (&1 + z pow 2) pow 2) *
    (r * (h + r - &1) + (&3 / &8) * (h * (h + r - &21 / &25) - (&57 / &50) * r)) =
    &138 * z pow 4 - &1121 * z pow 3 + &650 * z pow 2 - &21 * z + &12` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `h:real`)) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `r:real`)) THEN
    UNDISCH_TAC `&0 < &1 + z pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &138 * z pow 4 - &1121 * z pow 3 + &650 * z pow 2 - &21 * z + &12`
    ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_ARITH `z pow 3 = z * z * z`;
                REAL_ARITH `z pow 4 = (z * z) * (z * z)`] THEN
    C1092MNG10L_PROD `&0 <= (z * z) * (&1 / &3 - z)` THEN
    C1092MNG10L_PROD `&0 <= (z * z) * (z * z)` THEN
    MP_TAC(SPEC `z - &63 / &1658` REAL_LE_SQUARE) THEN DISCH_TAC THEN C1092MNG10L_LIN;
    ALL_TAC] THEN
  MATCH_MP_TAC C1092MNG10L_POS_OF_MUL THEN
  EXISTS_TAC `&200 * (&1 + z pow 2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      can (find_term ((=) `&1121`)) (concl th) then SUBST1_TAC th else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* Lean: G10_low_nonnegative *)
let C1092MNG10L_G10_LOW_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ &8 * t <= &3 * d /\
                 c1092mncs_quarter h r /\ &4 / &5 <= h /\ r <= &3 / &5
                 ==> &0 <= c1092mncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MNCC_SHALLOW_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_LOW_CAP) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG10L_LOW_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> concl th =
    `&93 / &100 <= d /\ t <= &9 / &25`)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNG10L_G10_BEFORE) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  C1092MNG10L_QUARTER_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092MNG10L_PROD `&0 <= (&9 / &25 - t) * r` THEN
  C1092MNG10L_PROD `&0 <= (d - &93 / &100) * h` THEN
  ANTS_TAC THENL [REWRITE_TAC[c1092mncs_deltaE] THEN C1092MNG10L_LIN; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&1 <= h + r` ASSUME_TAC THENL
   [C1092MNG10L_CONTRA THEN C1092MNG10L_PROD `&0 <= h * r` THEN
    C1092MNG10L_PROD `&0 < (&1 - (h + r)) * (&1 + h + r)` THEN C1092MNG10L_LIN; ALL_TAC] THEN
  C1092MNG10L_PROD `&0 <= t * ((--(&29 / &25) * h + (&22 / &25) * r) - c1092mncs_FC c s h r)` THEN
  C1092MNG10L_PROD `&0 <= r * (h + r - &1)` THEN
  C1092MNG10L_PROD `&0 <= d * (r * (h + r - &1))` THEN
  ASM_CASES_TAC `&0 <= h * (h + r - &21 / &25) - (&57 / &50) * r` THENL
   [C1092MNG10L_PROD `&0 <= t * (h * (h + r - &21 / &25) - (&57 / &50) * r)` THEN
    C1092MNG10L_LIN;
    ALL_TAC] THEN
  C1092MNG10L_PROD `&0 <= (&3 * d / &8 - t) * --(h * (h + r - &21 / &25) - (&57 / &50) * r)` THEN
  C1092MNG10L_PROD `&0 <= d * (r * (h + r - &1) + (&3 / &8) * (h * (h + r - &21 / &25) -
                                                             (&57 / &50) * r))` THEN
  C1092MNG10L_LIN);;

(* Lean: G10_middle_nonnegative *)
let C1092MNG10L_G10_MIDDLE_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ &8 * t <= &3 * d /\
                 c977cc_normal h r /\ &3 / &5 <= r
                 ==> &0 <= c1092mncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_MIDDLE_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal h r`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal h r`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`; `h:real`; `r:real`] C1092MNCC_G00_NONNEGATIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092mncs_kC h r h r = &1 /\ c1092mncs_deltaC h r h r = &0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_kC; c1092mncs_deltaC] THEN
    UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[c1092mncs_G00; c1092mncs_width; c1092mncs_G10] THEN ASM_REWRITE_TAC[REAL_ABS_0] THEN
  REWRITE_TAC[c1092mncs_ell; c1092mncs_kE; c1092mncs_C0] THEN DISCH_TAC THEN
  C1092MNG10L_PROD `&0 <= t * ((r - &1) - c1092mncs_FC c s h r)` THEN
  C1092MNG10L_LIN);;
