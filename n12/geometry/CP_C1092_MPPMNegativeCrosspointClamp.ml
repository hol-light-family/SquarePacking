(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointClamp.lean          *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport).  The unperturbed C       *)
(* support clamps in NEGATIVE-WALL-SCALARS section 3.  Normal is             *)
(* c977cc_normal; FC, kC, deltaC, Quarter are c1092mncs_*;                   *)
(* CrosspointSupport.steep_bounds C1092G10_STEEP_BOUNDS; dot_le_one          *)
(* C977CSB_DOT_LE_ONE; SteepPositiveNegativeProfile.Scalars.envelope         *)
(* C1092SNP_ENVELOPE (f, B are c1092snp_f, c1092snp_B).                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointCentral.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveNegativeProfileScalars.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C1092NCCL_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092NCCL_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092NCCL_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092NCCL_QUARTER_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mncs_quarter x y`) (concl th)));;

(* Lean: FC_lower_formula *)
let C1092NCCL_FC_LOWER_FORMULA = prove
 (`forall c s h r. c1092mncs_deltaC c s h r <= &0
     ==> c1092mncs_FC c s h r =
         (--c - s + c * s / &2) * h + (c - s + c pow 2 / &2 + s pow 2) * r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= c1092mncs_deltaC c s h r` THEN
  ASM_REWRITE_TAC[c1092mncs_FC] THENL
  [SUBGOAL_THEN `c1092mncs_deltaC c s h r = &0` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[c1092mncs_kC; c1092mncs_deltaC] THEN CONV_TAC REAL_RING;
   REWRITE_TAC[c1092mncs_kC; c1092mncs_deltaC] THEN REAL_ARITH_TAC]);;

(* Lean: FC_upper_formula *)
let C1092NCCL_FC_UPPER_FORMULA = prove
 (`forall c s h r. c977cc_normal c s /\ &0 <= c1092mncs_deltaC c s h r
     ==> c1092mncs_FC c s h r =
         (--c + s - s pow 2) * h + (&1 + c * s - c - s) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[c1092mncs_FC] THEN
  UNDISCH_TAC `c977cc_normal c s` THEN
  REWRITE_TAC[c977cc_normal; c1092mncs_kC; c1092mncs_deltaC] THEN STRIP_TAC THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: FC_low_cap *)
let C1092NCCL_FC_LOW_CAP = prove
 (`forall c s h r. c977cc_normal c s /\ &3 / &5 <= s /\ c1092mncs_quarter h r /\
             &4 / &5 <= h /\ r <= &3 / &5
             ==> c1092mncs_FC c s h r <= --(&29 / &25) * h + (&22 / &25) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MNCC_NORMAL_TAC THEN C1092NCCL_QUARTER_TAC THEN
  C1092NCCL_PROD `&0 <= c * (&3 / &5 - r)` THEN
  C1092NCCL_PROD `&0 <= s * (h - &4 / &5)` THEN
  SUBGOAL_THEN `c1092mncs_deltaC c s h r <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[c1092mncs_deltaC] THEN C1092NCCL_LP_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[C1092NCCL_FC_LOWER_FORMULA] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092NCCL_PROD `&0 <= (c + s - &7 / &5) * (&1 - (c + s + &7 / &5) / &4)` THEN
  C1092NCCL_PROD `&0 <= (s - &3 / &5) * (&1 - (s + &3 / &5) / &2)` THEN
  SUBGOAL_THEN `--c - s + c * s / &2 <= --(&29 / &25) /\
                c - s + (c * c) / &2 + s * s <= &22 / &25`
  STRIP_ASSUME_TAC THENL [C1092NCCL_LP_TAC; ALL_TAC] THEN
  C1092NCCL_PROD `&0 <= (--(&29 / &25) - (--c - s + c * s / &2)) * h` THEN
  C1092NCCL_PROD `&0 <= (&22 / &25 - (c - s + (c * c) / &2 + s * s)) * r` THEN
  C1092NCCL_LP_TAC);;

(* Lean: FC_middle_cap *)
let C1092NCCL_FC_MIDDLE_CAP = prove
 (`forall c s h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal h r /\ &3 / &5 <= r
             ==> c1092mncs_FC c s h r <= r - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092MNCC_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092NCCL_PROD `&0 < c * h` THEN C1092NCCL_PROD `&0 <= s * r` THEN
  SUBGOAL_THEN `(c * h + s * r) * (c * h + s * r) + (c * r - s * h) * (c * r - s * h) = &1 /\
                r = (c * h + s * r) * s + (c * r - s * h) * c` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `h * h + r * r = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092NCCL_PROD `&0 <= (c * h + s * r) * (&1 - (c * h + s * r))` THEN
  REWRITE_TAC[c1092mncs_FC; c1092mncs_kC; c1092mncs_deltaC] THEN
  COND_CASES_TAC THENL
  [C1092NCCL_PROD `&0 <= s * (h - r)` THEN
   C1092NCCL_PROD `&0 <= r * (&1 / &5 - (c - s))` THEN
   SUBGOAL_THEN `c * r - s * h < &3 / &20` ASSUME_TAC THENL [C1092NCCL_LP_TAC; ALL_TAC] THEN
   C1092NCCL_PROD `&0 <= (c * r - s * h) * (&3 / &20 - (c * r - s * h))` THEN
   SUBGOAL_THEN `&1 - (c * h + s * r) <= (&3 / &20) * (c * r - s * h)` ASSUME_TAC THENL
   [C1092NCCL_LP_TAC; ALL_TAC] THEN
   C1092NCCL_PROD `&0 <= (c * r - s * h) * (&17 / &20 - s)` THEN
   C1092NCCL_LP_TAC;
   SUBGOAL_THEN `c * r - s * h <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   C1092NCCL_PROD `&0 <= r * (c - s)` THEN
   C1092NCCL_PROD `&0 <= s * (&1 / &5 - (h - r))` THEN
   SUBGOAL_THEN `--(c * r - s * h) < &3 / &20` ASSUME_TAC THENL [C1092NCCL_LP_TAC; ALL_TAC] THEN
   C1092NCCL_PROD `&0 <= --(c * r - s * h) * (&3 / &20 + (c * r - s * h))` THEN
   SUBGOAL_THEN `&1 - (c * h + s * r) <= --(&3 / &20) * (c * r - s * h)` ASSUME_TAC THENL
   [C1092NCCL_LP_TAC; ALL_TAC] THEN
   C1092NCCL_PROD `&0 <= --(c * r - s * h) * (&17 / &20 - c / &2)` THEN
   C1092NCCL_LP_TAC]);;

(* Lean: FC_high_cap *)
let C1092NCCL_FC_HIGH_CAP = prove
 (`forall c s h r. c977cc_normal c s /\ c1092mncs_quarter h r /\ h <= r
             ==> c1092mncs_FC c s h r <= --h / &2 + (&9 / &100) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SNP_ENVELOPE) THEN
  ASM_REWRITE_TAC[c1092snp_f; c1092snp_B] THEN STRIP_TAC THEN
  C1092MNCC_NORMAL_TAC THEN C1092NCCL_QUARTER_TAC THEN
  C1092NCCL_PROD `&0 <= (c - s) * r` THEN C1092NCCL_PROD `&0 <= s * (r - h)` THEN
  SUBGOAL_THEN `&0 <= c1092mncs_deltaC c s h r` ASSUME_TAC THENL
  [REWRITE_TAC[c1092mncs_deltaC] THEN C1092NCCL_LP_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[C1092NCCL_FC_UPPER_FORMULA] THEN
  C1092NCCL_PROD `&0 <= (--(&1 / &2) - (--c + s - s pow 2)) * h` THEN
  C1092NCCL_PROD `&0 <= (&9 / &100 - (&1 + c * s - c - s)) * r` THEN
  C1092NCCL_LP_TAC);;
