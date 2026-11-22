(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointG10High.lean       *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport).  NEGATIVE-WALL-SCALARS  *)
(* section 4 above the boundary diagonal and the closed-quarter dispatcher. *)
(* G10, FC, kE, deltaE, E0, Quarter: c1092mncs_*; Normal: c977cc_normal;    *)
(* G10_before / G10_low_nonnegative / G10_middle_nonnegative: C1092MNG10L_*;*)
(* FC_high_cap: C1092NCCL_FC_HIGH_CAP.  Tag C1092NG10H_.                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG10Low.ml";;

let C1092NG10H_LIN = REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092NG10H_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092NG10H_LIN; ALL_TAC];;

let C1092NG10H_QUARTER_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;

(* Lean: highCore (definition) *)
let c1092ng10h_highCore = new_definition
 `c1092ng10h_highCore (h:real) (r:real) (u:real) =
    (&1 + u pow 2) * (h + r) - &1 - (&3 / &2) * u pow 2 - (&7 / &20) * u`;;

(* Lean: highCore_nonnegative *)
let C1092NG10H_HIGHCORE_NONNEGATIVE = prove
 (`forall h r u. c1092mncs_quarter h r /\ &0 < r /\ r <= &1 /\ &0 <= u /\ u <= &3 / &8 /\
           h = u * r
           ==> &0 <= c1092ng10h_highCore h r u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NG10H_QUARTER_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `h = u * r` then SUBST_ALL_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `r pow 2 * (&1 + u pow 2) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(u * r) pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `r * ((&1 + u pow 2) * (u * r + r) - (&1 + u)) = (&1 + u) * (&1 - r)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `r pow 2 * (&1 + u pow 2) = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092NG10H_PROD `&0 <= (&1 + u) * (&1 - r)` THEN
  SUBGOAL_THEN `&0 <= (&1 + u pow 2) * (u * r + r) - (&1 + u)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`r:real`; `--((&1 + u pow 2) * (u * r + r) - (&1 + u))`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [C1092NG10H_LIN; DISCH_TAC] THEN C1092NG10H_LIN;
    ALL_TAC] THEN
  C1092NG10H_PROD `&0 <= u * (&13 / &20 - (&3 / &2) * u)` THEN
  REWRITE_TAC[c1092ng10h_highCore] THEN C1092NG10H_LIN);;

(* Lean: large_sum (private) *)
let C1092NG10H_LARGE_SUM = prove
 (`forall h r u. c1092mncs_quarter h r /\ h <= r /\ &3 / &8 <= u /\ h = u * r
           ==> &32 / &25 <= h + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NG10H_QUARTER_TAC THEN
  C1092NG10H_PROD `&0 <= r * (&8 * u - &3)` THEN
  SUBGOAL_THEN `&0 <= &8 * h - &3 * r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `h:real`
                            then SUBST1_TAC th else NO_TAC) THEN C1092NG10H_LIN;
    ALL_TAC] THEN
  C1092NG10H_PROD `&0 <= (&8 * h - &3 * r) * (&8 * r - &3 * h)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092NG10H_PROD `&0 < (&32 / &25 - (h + r)) * (&32 / &25 + (h + r))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092NG10H_LIN);;

(* Lean: G10_after *)
let C1092NG10H_G10_AFTER = prove
 (`forall c s d t h r. c1092mncs_quarter h r /\ &0 <= c1092mncs_deltaE d t h r
     ==> c1092mncs_G10 c s d t h r =
         t * (&1 + h * r - &2 * h - c1092mncs_FC c s h r - (&13 / &50) * r) +
         d * r * (r - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NG10H_QUARTER_TAC THEN
  REWRITE_TAC[c1092mncs_G10] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REWRITE_TAC[c1092mncs_kE; c1092mncs_deltaE; c1092mncs_E0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: G10_high_nonnegative *)
let C1092NG10H_G10_HIGH_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &8 * t <= &3 * d /\
                 c1092mncs_quarter h r /\ h <= r
                 ==> &0 <= c1092mncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_HIGH_CAP) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092MNG10L_G10_BEFORE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `h:real`; `r:real`]
    C1092NG10H_G10_AFTER) THEN
  ASM_REWRITE_TAC[c1092mncs_deltaE] THEN
  SPEC_TAC(`c1092mncs_G10 c s d t h r`, `G:real`) THEN GEN_TAC THEN
  SPEC_TAC(`c1092mncs_FC c s h r`, `F0:real`) THEN GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  C1092NG10H_QUARTER_TAC THEN
  SUBGOAL_THEN `r <= &1 /\ h + r <= &3 / &2` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN CONJ_TAC THEN
    NLIN_TAC [SQ_NONNEG `h:real`; SQ_NONNEG `r - &1`; SQ_NONNEG `h - r`;
              SQ_NONNEG `h + r - &3 / &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [C1092NG10H_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `r = &0 /\ h = &0` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = h / r` THEN
  SUBGOAL_THEN `h = u * r /\ &0 <= u /\ u <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LE_DIV; REAL_LT_IMP_LE;
                 REAL_LE_LDIV_EQ] THEN C1092NG10H_LIN;
    ALL_TAC] THEN
  C1092NG10H_PROD `&0 <= t * (--h / &2 + (&9 / &100) * r - F0)` THEN
  SUBGOAL_THEN `r pow 2 * (&1 + u pow 2) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_CASES_TAC `t * r - d * h <= &0` THENL
   [(* ---------------- before: deltaE <= 0 ---------------- *)
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `t * r - d * h <= &0`
      then MP_TAC th else NO_TAC) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `t <= d * u` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092NG10H_PROD `&0 < r * (t - d * u)` THEN
      UNDISCH_TAC `t * r - d * h <= &0` THEN ASM_REWRITE_TAC[] THEN C1092NG10H_LIN;
      ALL_TAC] THEN
    ABBREV_TAC `A = u * ((h + r) - &3 / &2) - &7 / &20` THEN
    C1092NG10H_PROD `&0 <= u * (&3 / &2 - (h + r))` THEN
    SUBGOAL_THEN `A <= &0` ASSUME_TAC THENL [EXPAND_TAC "A" THEN C1092NG10H_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `r * (t * A + d * ((h + r) - &1)) <=
                  t * (h * (h + r - &2) - F0 - (&13 / &50) * r) + d * r * (h + r - &1)`
      ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN
      UNDISCH_TAC `&0 <= t * (--h / &2 + (&9 / &100) * r - F0)` THEN
      FIRST_ASSUM(fun th -> if concl th = `h = u * r` then SUBST1_TAC th else NO_TAC) THEN
      DISCH_TAC THEN C1092NG10H_LIN;
      ALL_TAC] THEN
    ASM_CASES_TAC `u <= &3 / &8` THENL
     [MP_TAC(SPECL [`h:real`; `r:real`; `u:real`] C1092NG10H_HIGHCORE_NONNEGATIVE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter] THEN C1092NG10H_LIN; DISCH_TAC] THEN
      C1092NG10H_PROD `&0 <= r * ((d * u - t) * --A)` THEN
      C1092NG10H_PROD `&0 <= (d * r) * c1092ng10h_highCore h r u` THEN
      SUBGOAL_THEN `r * (t * A + d * ((h + r) - &1)) - d * r * c1092ng10h_highCore h r u =
                    r * (t - d * u) * A` ASSUME_TAC THENL
       [EXPAND_TAC "A" THEN REWRITE_TAC[c1092ng10h_highCore] THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      C1092NG10H_LIN;
      ALL_TAC] THEN
    MP_TAC(SPECL [`h:real`; `r:real`; `u:real`] C1092NG10H_LARGE_SUM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter] THEN C1092NG10H_LIN; DISCH_TAC] THEN
    C1092NG10H_PROD `&0 <= ((h + r) - &32 / &25) * (&1 + (&3 / &8) * u)` THEN
    SUBGOAL_THEN `&0 <= (h + r) - &1 + (&3 / &8) * A` ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN C1092NG10H_LIN; ALL_TAC] THEN
    C1092NG10H_PROD `&0 <= r * ((&3 * d / &8 - t) * --A)` THEN
    C1092NG10H_PROD `&0 <= (r * d) * ((h + r) - &1 + (&3 / &8) * A)` THEN
    C1092NG10H_LIN;
    (* ---------------- after: 0 <= deltaE ---------------- *)
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `&0 <= t * r - d * h`
      then MP_TAC th else NO_TAC) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `d * u <= t` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092NG10H_PROD `&0 < r * (d * u - t)` THEN
      UNDISCH_TAC `~(t * r - d * h <= &0)` THEN ASM_REWRITE_TAC[] THEN C1092NG10H_LIN;
      ALL_TAC] THEN
    SUBGOAL_THEN `u <= &3 / &8` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092NG10H_PROD `&0 < d * (u - &3 / &8)` THEN C1092NG10H_LIN;
      ALL_TAC] THEN
    C1092NG10H_PROD `&0 <= u * (&1 - r)` THEN
    SUBGOAL_THEN `h <= &3 / &8` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if concl th = `h = u * r` then SUBST1_TAC th else NO_TAC) THEN
      C1092NG10H_LIN;
      ALL_TAC] THEN
    ABBREV_TAC `A = &1 + h * r - (&3 / &2) * h - (&7 / &20) * r` THEN
    C1092NG10H_PROD `&0 <= h * r` THEN
    SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [EXPAND_TAC "A" THEN C1092NG10H_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `t * A + d * r * (r - &1) <=
                  t * (&1 + h * r - &2 * h - F0 - (&13 / &50) * r) + d * r * (r - &1)`
      ASSUME_TAC THENL [EXPAND_TAC "A" THEN C1092NG10H_LIN; ALL_TAC] THEN
    MP_TAC(SPECL [`h:real`; `r:real`; `u:real`] C1092NG10H_HIGHCORE_NONNEGATIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter] THEN C1092NG10H_LIN; DISCH_TAC] THEN
    SUBGOAL_THEN `u * A + r * (r - &1) = r * c1092ng10h_highCore h r u` ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN REWRITE_TAC[c1092ng10h_highCore] THEN
      FIRST_ASSUM(fun th -> if concl th = `h = u * r` then SUBST1_TAC th else NO_TAC) THEN
      UNDISCH_TAC `r pow 2 * (&1 + u pow 2) = &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    C1092NG10H_PROD `&0 <= (t - d * u) * A` THEN
    C1092NG10H_PROD `&0 <= (d * r) * c1092ng10h_highCore h r u` THEN
    SUBGOAL_THEN `d * (u * A + r * (r - &1)) = d * (r * c1092ng10h_highCore h r u)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    C1092NG10H_LIN]);;

(* Lean: G10_nonnegative *)
let C1092NG10H_G10_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ &8 * t <= &3 * d /\
                 c1092mncs_quarter h r
                 ==> &0 <= c1092mncs_G10 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `h <= r` THENL
   [MATCH_MP_TAC C1092NG10H_G10_HIGH_NONNEGATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal h r` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092mncs_quarter h r` THEN
    REWRITE_TAC[c977cc_normal; c1092mncs_quarter; c1092mcs_quarter] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r <= &3 / &5` THENL
   [MATCH_MP_TAC C1092MNG10L_G10_LOW_NONNEGATIVE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c1092mncs_quarter h r` THEN
    REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter; REAL_POW_2] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092NG10H_PROD `&0 < (&4 / &5 - h) * (&4 / &5 + h)` THEN
    C1092NG10H_PROD `&0 <= (&3 / &5 - r) * (&3 / &5 + r)` THEN
    C1092NG10H_LIN;
    MATCH_MP_TAC C1092MNG10L_G10_MIDDLE_NONNEGATIVE THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;
