(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointG11.lean     *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointSupport).  Full MISSING-    *)
(* NEGATIVE-WALL-SCALARS G11*, with a uniform rational positive margin.     *)
(* Normal is c977cc_normal; Quarter, kC, FC are c1092mncs_*; G11 / G11star  *)
(* / FE c1092mmncs_*; FE_first_cap / FE_second_cap C1092MMNCE_*;            *)
(* NegativeCrosspointSupport.FC_*_cap C1092NCCL_FC_*_CAP; low / middle /    *)
(* high_remainder C1092MNCGR_*; half, normal_half, half_order, steep_half,  *)
(* rho_bounds C1092MCBH_* (rho = c1092mpba_diagonal); QuadraticArc value /  *)
(* nonnegative c1092mpqa_value / C1092MPQA_NONNEGATIVE; cosH, sinH          *)
(* c1092sps_*.  The private models lowModel, middleModel, highModel are     *)
(* c1092mncg11_*.  Tag C1092MNCG11_.                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointEnvelope.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointG11Remainders.ml";;

let C1092MNCG11_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MNCG11_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092MNCG11_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092MNCG11_QUARTER_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mncs_quarter x y`) (concl th)));;

let C1092MNCG11_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: perturbation (private) *)
let C1092MNCG11_PERTURBATION = prove
 (`forall epsilon c s h r. c977cc_normal c s /\ c1092mncs_quarter h r /\ epsilon <= &43 / &500
     ==> epsilon * s * h * c1092mncs_kC c s h r <= (&9 / &200) * h * (h + r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCG11_QUARTER_TAC THEN C1092MNCG11_NORMAL_TAC THEN
  SUBGOAL_THEN `c * s <= &1 / &2` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  C1092MNCG11_PROD `&0 <= (c - s) * (c + s)` THEN
  SUBGOAL_THEN `s * s <= &1 / &2` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MNCG11_LP_TAC; ALL_TAC] THEN
  C1092MNCG11_PROD `&0 <= h * (&1 / &2 - c * s)` THEN
  C1092MNCG11_PROD `&0 <= r * (&1 / &2 - s * s)` THEN
  SUBGOAL_THEN `&0 <= c1092mncs_kC c s h r /\ s * c1092mncs_kC c s h r <= (h + r) / &2`
    STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092mncs_kC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    C1092MNCG11_LP_TAC]; ALL_TAC] THEN
  C1092MNCG11_PROD `&0 <= (&43 / &500 - epsilon) * ((s * h) * c1092mncs_kC c s h r)` THEN
  C1092MNCG11_PROD `&0 <= h * ((h + r) / &2 - s * c1092mncs_kC c s h r)` THEN
  C1092MNCG11_PROD `&0 <= h * (h + r)` THEN
  C1092MNCG11_LP_TAC);;

(* Lean: lowModel, middleModel, highModel (private definitions) *)
let c1092mncg11_lowModel = new_definition
 `c1092mncg11_lowModel (h:real) (r:real) =
    h + r - &177 / &200 - (&67 / &200) * r pow 2 - (&147 / &200) * h * r`;;
let c1092mncg11_middleModel = new_definition
 `c1092mncg11_middleModel (h:real) (r:real) =
    &2 * h + r - &409 / &200 - (&171 / &200) * h * r + (&33 / &40) * r pow 2`;;
let c1092mncg11_highModel = new_definition
 `c1092mncg11_highModel (h:real) (r:real) =
    h + r - &309 / &200 + (&173 / &200) * r pow 2 - (&101 / &200) * h * r`;;

(* the diagonal point sqrt 2 / 2 is normal *)
let C1092MNCG11_DIAGONAL_NORMAL = prove
 (`c977cc_normal (sqrt(&2) / &2) (sqrt(&2) / &2)`,
  REWRITE_TAC[c977cc_normal; REAL_LE_REFL] THEN
  MP_TAC(SPEC `&2` SQRT_POW_2) THEN MP_TAC(SPEC `&2` SQRT_POS_LE) THEN
  REWRITE_TAC[REAL_POS] THEN REPEAT DISCH_TAC THEN CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC;
   REWRITE_TAC[REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* the value of a QuadraticArc expression at the diagonal endpoint rho *)
let C1092MNCG11_RHO_VALUE = prove
 (`forall a b C A B. c1092mpqa_value a b C A B c1092mpba_diagonal =
               (a + b) / &2 + C + (A + B) * (sqrt(&2) / &2)`,
  REPEAT GEN_TAC THEN STRIP_ASSUME_TAC C1092MCBH_RHO_BOUNDS THEN
  MP_TAC C1092MNCG11_DIAGONAL_NORMAL THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c1092mpqa_value] THEN
  UNDISCH_TAC `(sqrt (&2) / &2) pow 2 + (sqrt (&2) / &2) pow 2 = &1` THEN
  CONV_TAC REAL_RING);;

let C1092MNCG11_SQRT_LOWER = prove
 (`&7 / &10 <= sqrt(&2) / &2`,
  MP_TAC(MATCH_MP C977CC_NORMAL_BOUNDS C1092MNCG11_DIAGONAL_NORMAL) THEN REAL_ARITH_TAC);;

let C1092MNCG11_ARC_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC;
         REWRITE_TAC[c1092mpqa_value; c1092sps_cosH; c1092sps_sinH] THEN
         CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
         MP_TAC C1092MNCG11_SQRT_LOWER THEN REAL_ARITH_TAC;
         ASM_REAL_ARITH_TAC];;

(* Lean: low_model_positive (private) *)
let C1092MNCG11_LOW_MODEL_POSITIVE = prove
 (`forall h r. c1092mncs_quarter h r /\ &4 / &5 <= h /\ r <= &3 / &5
     ==> &1 / &100 <= c1092mncg11_lowModel h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCG11_QUARTER_TAC THEN
  SUBGOAL_THEN `c977cc_normal h r` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MCBH_NORMAL_HALF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `&4 / &5`; `&3 / &5`] C1092MCBH_HALF_ORDER) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
   ALL_TAC] THEN
  SUBGOAL_THEN `c1092mcbh_half (&4 / &5) (&3 / &5) = &1 / &3` SUBST1_TAC THENL
  [REWRITE_TAC[c1092mcbh_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  ABBREV_TAC `z = c1092mcbh_half h r` THEN
  MP_TAC(SPECL [`&67 / &200`; `--(&147 / &200)`; `--(&123 / &100)`; `&1`; `&1`;
                `&0`; `z:real`; `&1 / &3`] C1092MPQA_NONNEGATIVE) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092MNCGR_LOW_REMAINDER THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[c1092mpqa_value; c1092sps_cosH; c1092sps_sinH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[c1092mpqa_value; c1092sps_cosH; c1092sps_sinH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092mpqa_value; c1092mncg11_lowModel] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
  REPEAT DISCH_TAC THEN C1092MNCG11_LP_TAC);;

(* Lean: middle_model_positive (private) *)
let C1092MNCG11_MIDDLE_MODEL_POSITIVE = prove
 (`forall h r. c977cc_normal h r /\ &3 / &5 <= r
     ==> &1 / &100 <= c1092mncg11_middleModel h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MCBH_NORMAL_HALF) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MCBH_STEEP_HALF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  STRIP_ASSUME_TAC C1092MCBH_RHO_BOUNDS THEN
  SUBGOAL_THEN `&1 / &3 <= c1092mpba_diagonal` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092MNCG11_PROD `&0 <= c1092mpba_diagonal * (&1 / &3 - c1092mpba_diagonal)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MNCG11_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 / &3`; `c1092mcbh_half h r`; `c1092mpba_diagonal`]
    C1092MNCGR_MIDDLE_REMAINDER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`--(&33 / &40)`; `--(&171 / &200)`; `--(&123 / &100)`; `&2`; `&1`;
                `&1 / &3`; `c1092mcbh_half h r`; `c1092mpba_diagonal`] C1092MPQA_NONNEGATIVE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[C1092MNCG11_RHO_VALUE] THEN C1092MNCG11_ARC_ANTS_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092mpqa_value; c1092mncg11_middleModel] THEN
  UNDISCH_TAC `c977cc_normal h r` THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  REPEAT STRIP_TAC THEN C1092MNCG11_LP_TAC);;

(* Lean: high_model_positive (private) *)
let C1092MNCG11_HIGH_MODEL_POSITIVE = prove
 (`forall h r. c1092mncs_quarter h r /\ h <= r ==> &1 / &100 <= c1092mncg11_highModel h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCG11_QUARTER_TAC THEN
  SUBGOAL_THEN `c977cc_normal r h` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `h:real`] C1092MCBH_NORMAL_HALF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC C1092MCBH_RHO_BOUNDS THEN
  MP_TAC(SPECL [`c1092mcbh_half r h`; `c1092mpba_diagonal`] C1092MNCGR_HIGH_REMAINDER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`&173 / &200`; `--(&101 / &200)`; `--(&311 / &200)`; `&1`; `&1`;
                `&0`; `c1092mcbh_half r h`; `c1092mpba_diagonal`] C1092MPQA_NONNEGATIVE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[C1092MNCG11_RHO_VALUE] THEN C1092MNCG11_ARC_ANTS_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092mpqa_value; c1092mncg11_highModel] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
  REPEAT DISCH_TAC THEN C1092MNCG11_LP_TAC);;

(* Lean: middle_scalar_lower *)
let C1092MNCG11_MIDDLE_SCALAR_LOWER = prove
 (`forall h r. c977cc_normal h r /\ &3 / &5 <= r
     ==> &1 / &100 <= &2 * h + r - &409 / &200 - (&171 / &200) * h * r + (&33 / &40) * r pow 2`,
  REWRITE_TAC[GSYM c1092mncg11_middleModel; C1092MNCG11_MIDDLE_MODEL_POSITIVE]);;

(* Lean: G11star_lower *)
let C1092MNCG11_G11STAR_LOWER = prove
 (`forall epsilon c s d t h r.
     c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ &252 / &373 <= t /\
     c1092mncs_quarter h r /\ epsilon <= &43 / &500
     ==> &1 / &100 <= c1092mmncs_G11star epsilon c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`epsilon:real`; `c:real`; `s:real`; `h:real`; `r:real`]
    C1092MNCG11_PERTURBATION) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCE_FE_FIRST_CAP) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MMNCE_FE_SECOND_CAP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C1092MNCG11_QUARTER_TAC THEN
  REWRITE_TAC[c1092mmncs_G11star; c1092mmncs_G11] THEN
  ASM_CASES_TAC `r <= &3 / &5` THENL
  [SUBGOAL_THEN `&4 / &5 <= h` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNCG11_PROD `&0 <= (&3 / &5 - r) * (&3 / &5 + r)` THEN
    C1092MNCG11_PROD `&0 < (&4 / &5 - h) * (&4 / &5 + h)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MNCG11_LP_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_LOW_CAP) THEN
   MP_TAC(SPECL [`h:real`; `r:real`] C1092MNCG11_LOW_MODEL_POSITIVE) THEN
   ASM_REWRITE_TAC[c1092mncg11_lowModel] THEN REPEAT DISCH_TAC THEN
   C1092MNCG11_PROD `&0 <= h * ((--(&29 / &25) * h + (&22 / &25) * r) - c1092mncs_FC c s h r)` THEN
   C1092MNCG11_PROD `&0 <= r * ((--(&19 / &100) * h - (&39 / &50) * r) - c1092mmncs_FE d t h r)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MNCG11_LP_TAC;
   ASM_CASES_TAC `h <= r` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_HIGH_CAP) THEN
    MP_TAC(SPECL [`h:real`; `r:real`] C1092MNCG11_HIGH_MODEL_POSITIVE) THEN
    ASM_REWRITE_TAC[c1092mncg11_highModel] THEN REPEAT DISCH_TAC THEN
    C1092MNCG11_PROD `&0 <= h * ((--h / &2 + (&9 / &100) * r) - c1092mncs_FC c s h r)` THEN
    C1092MNCG11_PROD `&0 <= r * (((&37 / &100) * h - (&33 / &25) * r) - c1092mmncs_FE d t h r)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MNCG11_LP_TAC;
    SUBGOAL_THEN `c977cc_normal h r /\ &3 / &5 <= r` STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NCCL_FC_MIDDLE_CAP) THEN
    MP_TAC(SPECL [`h:real`; `r:real`] C1092MNCG11_MIDDLE_MODEL_POSITIVE) THEN
    ASM_REWRITE_TAC[c1092mncg11_middleModel] THEN REPEAT DISCH_TAC THEN
    C1092MNCG11_PROD `&0 <= h * ((r - &1) - c1092mncs_FC c s h r)` THEN
    C1092MNCG11_PROD `&0 <= r * ((--(&19 / &100) * h - (&39 / &50) * r) - c1092mmncs_FE d t h r)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MNCG11_LP_TAC]]);;
