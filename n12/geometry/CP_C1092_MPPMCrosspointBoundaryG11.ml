(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointBoundaryG11.lean            *)
(* (N12Compact.C1092MPPMCrosspointSupport).  The complete boundary-scalar   *)
(* G11 inequality.  Normal is c977cc_normal; G11, FC, FE, Quarter are       *)
(* c1092mcs_*; FC caps C1092G10_FC_*_CAP; FE_low_cap C1092MCBEV_FE_LOW_CAP; *)
(* lower_endpoint_D C1092MCBE_LOWER_ENDPOINT_D; P, Q, FE_after,             *)
(* coefficient_bounds / _difference c1092mcbc_ / C1092MCBC_*;               *)
(* alignedBoundary(_positive) c1092mcba_ / C1092MCBA_*; half, rho_bounds,   *)
(* normal_half C1092MCBH_* (rho = c1092mpba_diagonal); QuadraticArc value / *)
(* nonnegative / upper_remainder c1092mpqa_value / C1092MPQA_NONNEGATIVE /  *)
(* C1092MPQR_UPPER_REMAINDER; cosH, sinH c1092sps_*.  Tag C1092G11_.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryEnvelope.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryEndpoints.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryHalf.ml";;

let C1092G11_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092G11_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092G11_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092G11_QUARTER_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mcs_quarter x y`) (concl th)));;

let C1092G11_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: G11_low_positive *)
let C1092G11_G11_LOW_POSITIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r /\ &4 / &5 <= h /\ r <= &3 / &5
                 ==> &0 < c1092mcs_G11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092G10_FC_LOW_CAP) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MCBEV_FE_LOW_CAP) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MCBE_LOWER_ENDPOINT_D) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C1092G11_QUARTER_TAC THEN
  C1092G11_PROD `&0 <= h * ((--(&3496 / &3125) * h + (&11387 / &12500) * r) -
                            c1092mcs_FC c s h r)` THEN
  C1092G11_PROD `&0 <= r * ((h - (&14 / &25) * r - &1 + &1 / &3125) -
                            c1092mcs_FE d t h r)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REWRITE_TAC[c1092mcs_G11] THEN C1092G11_LP_TAC);;

(* Lean: G11_middle_positive *)
let C1092G11_G11_MIDDLE_POSITIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c977cc_normal h r /\ &3 / &5 <= r
                 ==> &0 < c1092mcs_G11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092G10_FC_MIDDLE_CAP) THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `d:real`; `t:real`] C1092MCBA_ALIGNEDBOUNDARY_POSITIVE) THEN
  ASM_REWRITE_TAC[c1092mcba_alignedBoundary] THEN REPEAT DISCH_TAC THEN
  C1092G11_NORMAL_TAC THEN
  C1092G11_PROD `&0 <= h * (((&543 / &500) * r - &1) - c1092mcs_FC c s h r)` THEN
  REWRITE_TAC[c1092mcs_G11] THEN C1092G11_LP_TAC);;

(* Lean: G11High (definition) *)
let c1092g11_G11High = new_definition
 `c1092g11_G11High (d:real) (t:real) (h:real) (r:real) =
    h + r - &2 + (&457 / &1000) * h pow 2 - (&129 / &1000 + c1092mcbc_P d t) * h * r +
    c1092mcbc_Q d t * r pow 2`;;

(* Lean: G11_high_bound *)
let C1092G11_G11_HIGH_BOUND = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r /\ h <= r
                 ==> c1092g11_G11High d t h r <= c1092mcs_G11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092G10_FC_HIGH_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092G11_QUARTER_TAC THEN C1092G11_NORMAL_TAC THEN
  C1092G11_PROD `&0 <= (d - t) * r` THEN C1092G11_PROD `&0 <= t * (r - h)` THEN
  SUBGOAL_THEN `&0 <= c1092mcs_deltaE d t h r` ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_deltaE] THEN C1092G11_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `h:real`; `r:real`] C1092MCBC_FE_AFTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092G11_PROD `&0 <= h * ((--(&457 / &1000) * h + (&129 / &1000) * r) -
                            c1092mcs_FC c s h r)` THEN
  ASM_REWRITE_TAC[c1092mcs_G11; c1092g11_G11High; REAL_POW_2] THEN C1092G11_LP_TAC);;

(* Lean: G11High_vertical *)
let C1092G11_G11HIGH_VERTICAL = prove
 (`forall d t. c977cc_normal d t ==> &0 <= c1092g11_G11High d t (&0) (&1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C1092MCBC_COEFFICIENT_BOUNDS) THEN
  REWRITE_TAC[c1092g11_G11High] THEN REAL_ARITH_TAC);;

(* Lean: G11High_diagonal *)
let C1092G11_G11HIGH_DIAGONAL = prove
 (`forall d t v. c977cc_normal d t /\ c977cc_normal v v ==> &0 < c1092g11_G11High d t v v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MCBC_COEFFICIENT_DIFFERENCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092G11_NORMAL_TAC THEN
  SUBGOAL_THEN `c1092g11_G11High d t v v =
                &2 * v - &459 / &250 + (c1092mcbc_Q d t - c1092mcbc_P d t) / &2`
    SUBST1_TAC THENL
  [REWRITE_TAC[c1092g11_G11High] THEN
   UNDISCH_TAC `v pow 2 + v pow 2 = &1` THEN CONV_TAC REAL_RING;
   ASM_REAL_ARITH_TAC]);;

(* Lean: G11High_form *)
let C1092G11_G11HIGH_FORM = prove
 (`forall d t h r. c1092mcs_quarter h r
     ==> c1092g11_G11High d t h r =
         (c1092mcbc_Q d t - &457 / &1000) * r pow 2 -
         (&129 / &1000 + c1092mcbc_P d t) * r * h - &1543 / &1000 + h + r`,
  REWRITE_TAC[c1092mcs_quarter; c1092g11_G11High] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* the diagonal point sqrt 2 / 2 is normal *)
let C1092G11_DIAGONAL_NORMAL = prove
 (`c977cc_normal (sqrt(&2) / &2) (sqrt(&2) / &2)`,
  REWRITE_TAC[c977cc_normal; REAL_LE_REFL] THEN
  MP_TAC(SPEC `&2` SQRT_POW_2) THEN MP_TAC(SPEC `&2` SQRT_POS_LE) THEN
  REWRITE_TAC[REAL_POS] THEN REPEAT DISCH_TAC THEN CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC;
   REWRITE_TAC[REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Lean: G11_high_nonnegative *)
let C1092G11_G11_HIGH_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r /\ h <= r
                 ==> &0 <= c1092mcs_G11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c1092g11_G11High d t h r` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC C1092G11_G11_HIGH_BOUND THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `c977cc_normal r h` ASSUME_TAC THENL
  [C1092G11_QUARTER_TAC THEN ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPECL [`r:real`; `h:real`] C1092MCBH_NORMAL_HALF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC C1092MCBH_RHO_BOUNDS THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MCBC_COEFFICIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z = c1092mcbh_half r h` THEN
  ABBREV_TAC `rh0 = c1092mpba_diagonal` THEN
  MP_TAC(SPECL [`c1092mcbc_Q d t - &457 / &1000`; `--(&129 / &1000 + c1092mcbc_P d t)`;
                `-- &1543 / &1000`; `&1`; `&1`; `&0`; `z:real`; `rh0:real`]
               C1092MPQA_NONNEGATIVE) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092MPQR_UPPER_REMAINDER THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[c1092mpqa_value; c1092sps_cosH; c1092sps_sinH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`d:real`; `t:real`; `sqrt(&2) / &2`] C1092G11_G11HIGH_DIAGONAL) THEN
    ASM_REWRITE_TAC[C1092G11_DIAGONAL_NORMAL] THEN
    MP_TAC(SPECL [`d:real`; `t:real`; `sqrt(&2) / &2`; `sqrt(&2) / &2`]
      C1092G11_G11HIGH_FORM) THEN
    ANTS_TAC THENL
    [MP_TAC C1092G11_DIAGONAL_NORMAL THEN
     REWRITE_TAC[c977cc_normal; c1092mcs_quarter] THEN REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[c1092mpqa_value] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
   ASM_REWRITE_TAC[c1092mpqa_value] THEN
   ASM_SIMP_TAC[C1092G11_G11HIGH_FORM] THEN REAL_ARITH_TAC]);;

(* Lean: G11_nonnegative *)
let C1092G11_G11_NONNEGATIVE = prove
 (`forall c s d t h r. c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\
                 c1092mcs_quarter h r
                 ==> &0 <= c1092mcs_G11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092G11_QUARTER_TAC THEN
  ASM_CASES_TAC `r <= &3 / &5` THENL
  [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC C1092G11_G11_LOW_POSITIVE THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092G11_PROD `&0 <= (&3 / &5 - r) * (&3 / &5 + r)` THEN
   C1092G11_PROD `&0 < (&4 / &5 - h) * (&4 / &5 + h)` THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092G11_LP_TAC;
   ASM_CASES_TAC `h <= r` THENL
   [MATCH_MP_TAC C1092G11_G11_HIGH_NONNEGATIVE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC C1092G11_G11_MIDDLE_POSITIVE THEN
    ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC]]);;
