(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveRetainingSteepScalars.lean   *)
(* (N12Compact.C1092MPPMPositiveRetainingSteep.Scalars).  Exact closed-      *)
(* interval inequalities for POSITIVE-RETAINING-ANGLE-AND-ORIGINS Thm 1.     *)
(* Normal is c977cc_normal.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092PRS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092PRS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; RASM_ARITH_TAC]; ALL_TAC];;

(* Lean: kappa, sigma, uPlus, uMinus, ePlus, eMinus (definitions) *)
let c1092prs_kappa = new_definition
 `c1092prs_kappa (c:real) (s:real) (d:real) (t:real) = c * d + s * t`;;
let c1092prs_sigma = new_definition
 `c1092prs_sigma (c:real) (s:real) (d:real) (t:real) = c * t - s * d`;;
let c1092prs_uPlus = new_definition
 `c1092prs_uPlus c s d t =
    &1 + c1092prs_kappa c s d t - (c + s) - c1092prs_kappa c s d t * d / &2 -
    (&13 / &50) * c1092prs_sigma c s d t * d`;;
let c1092prs_uMinus = new_definition
 `c1092prs_uMinus c s d t =
    &1 - (c + s) + c1092prs_kappa c s d t * (&1 - d / &2) - c1092prs_sigma c s d t`;;
let c1092prs_ePlus = new_definition
 `c1092prs_ePlus c s d t =
    &1 + c1092prs_kappa c s d t + c1092prs_sigma c s d t - d / &2 -
    c1092prs_kappa c s d t * (c + s) + c1092prs_sigma c s d t * ((&2 / &5) * s - c)`;;
let c1092prs_eMinus = new_definition
 `c1092prs_eMinus c s d t =
    &1 + c1092prs_kappa c s d t - c1092prs_sigma c s d t - d / &2 -
    c1092prs_kappa c s d t * (c + s) + c1092prs_sigma c s d t * s`;;

(* Lean: canonical_bounds *)
let C1092PRS_CANONICAL_BOUNDS = prove
 (`forall c s. c977cc_normal c s
     ==> &0 < c /\ c <= &1 /\ &0 <= s /\ s < &71 / &100 /\ c + s < &71 / &50`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092PRS_NORMAL_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [RASM_ARITH_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 <= (s - &71 / &100) * (s + &71 / &100)` THEN
   C1092PRS_PROD `&0 <= (c - s) * (c + s)` THEN RASM_ARITH_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 <= (c + s - &71 / &50) * (c + s + &71 / &50)` THEN
   NLIN_TAC [SQ_NONNEG `c - s:real`]]);;

(* Lean: relative_unit *)
let C1092PRS_RELATIVE_UNIT = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> c1092prs_kappa c s d t pow 2 + c1092prs_sigma c s d t pow 2 = &1`,
  REWRITE_TAC[c977cc_normal; c1092prs_kappa; c1092prs_sigma] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
  CONV_TAC REAL_RING);;

(* Lean: relative_bounds *)
let C1092PRS_RELATIVE_BOUNDS = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &7 / &10 < c1092prs_kappa c s d t /\ c1092prs_kappa c s d t <= &1 /\
         --(&71 / &100) < c1092prs_sigma c s d t /\ c1092prs_sigma c s d t < &71 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092PRS_RELATIVE_UNIT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c1092prs_kappa c s d t /\ --s <= c1092prs_sigma c s d t /\
                c1092prs_sigma c s d t <= t` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092prs_kappa; c1092prs_sigma] THEN
   C1092PRS_PROD `&0 < c * d` THEN C1092PRS_PROD `&0 <= s * t` THEN
   C1092PRS_PROD `&0 <= c * t` THEN C1092PRS_PROD `&0 <= s * (&1 - d)` THEN
   C1092PRS_PROD `&0 <= t * (&1 - c)` THEN C1092PRS_PROD `&0 <= s * d` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c1092prs_kappa c s d t pow 2 + c1092prs_sigma c s d t pow 2 = &1` THEN
  ABBREV_TAC `k = c1092prs_kappa c s d t` THEN
  ABBREV_TAC `z = c1092prs_sigma c s d t` THEN DISCH_TAC THEN
  SUBGOAL_THEN `--(&71 / &100) < z /\ z < &71 / &100` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092PRS_PROD `&0 < (&71 / &100 - z) * (&71 / &100 + z)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 <= (&7 / &10 - k) * (&7 / &10 + k)` THEN RASM_ARITH_TAC;
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 < (k - &1) * (k + &1)` THEN
   MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN RASM_ARITH_TAC]);;

(* Lean: steep_bounds *)
let C1092PRS_STEEP_BOUNDS = prove
 (`forall d t. c977cc_normal d t /\ &3 / &5 <= t ==> d <= &4 / &5 /\ (&3 / &2) * d + t <= &9 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  C1092PRS_PROD `&0 <= (t - &3 / &5) * (t + &3 / &5)` THEN
  SUBGOAL_THEN `d <= &4 / &5` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 < (d - &4 / &5) * (d + &4 / &5)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092PRS_PROD `&0 <= (&4 / &5 - d) * ((&3 / &2) * (t + &3 / &5) - (d + &4 / &5))` THEN
  SUBGOAL_THEN `&0 <= (t + &3 / &5) * (&9 / &5 - (&3 / &2) * d - t)` MP_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 < (t + &3 / &5) * --(&9 / &5 - (&3 / &2) * d - t)` THEN
  RASM_ARITH_TAC);;

let C1092PRS_ABBREV_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092PRS_RELATIVE_UNIT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092PRS_RELATIVE_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PRS_NORMAL_TAC;;

(* Lean: u_positive *)
let C1092PRS_U_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= t /\
             &0 <= c1092prs_sigma c s d t
             ==> &0 < c1092prs_uPlus c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_ABBREV_TAC THEN
  SUBGOAL_THEN `c1092prs_uPlus c s d t =
                &1 - c1092prs_kappa c s d t * ((&3 / &2) * d + t - &1) -
                c1092prs_sigma c s d t * (t - (&37 / &50) * d)` SUBST1_TAC THENL
  [REWRITE_TAC[c1092prs_uPlus; c1092prs_kappa; c1092prs_sigma] THEN
   UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092PRS_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092prs_kappa c s d t pow 2 + c1092prs_sigma c s d t pow 2 = &1` THEN
  ABBREV_TAC `k = c1092prs_kappa c s d t` THEN
  ABBREV_TAC `z = c1092prs_sigma c s d t` THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 <= k * (&4 / &5 - ((&3 / &2) * d + t - &1))` THEN
  C1092PRS_PROD `&0 <= z * (&1 / &5 - (t - (&37 / &50) * d))` THEN
  SUBGOAL_THEN `((&4 / &5) * k + (&1 / &5) * z) pow 2 <= &17 / &25` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `k / &5 - (&4 / &5) * z`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 / &5) * k + (&1 / &5) * z < &1` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: u_negative *)
let C1092PRS_U_NEGATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= t /\
             c1092prs_sigma c s d t <= &0
             ==> &0 < c1092prs_uMinus c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_ABBREV_TAC THEN
  REWRITE_TAC[c1092prs_uMinus] THEN
  C1092PRS_PROD `&0 <= (c1092prs_kappa c s d t - &7 / &10) * (&1 - d / &2)` THEN
  RASM_ARITH_TAC);;

(* Lean: e_positive *)
let C1092PRS_E_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= t /\
             &0 <= c1092prs_sigma c s d t
             ==> &0 < c1092prs_ePlus c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_ABBREV_TAC THEN
  SUBGOAL_THEN `c1092prs_ePlus c s d t =
                &1 - (&3 / &2) * d - t + c1092prs_kappa c s d t +
                c1092prs_sigma c s d t * (&1 - (&3 / &5) * s)` SUBST1_TAC THENL
  [REWRITE_TAC[c1092prs_ePlus; c1092prs_kappa; c1092prs_sigma] THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - (&3 / &5) * s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c1092prs_kappa c s d t pow 2 + c1092prs_sigma c s d t pow 2 = &1` THEN
  ABBREV_TAC `k = c1092prs_kappa c s d t` THEN
  ABBREV_TAC `z = c1092prs_sigma c s d t` THEN
  ABBREV_TAC `w = &1 - (&3 / &5) * s` THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 <= (k - &7 / &10) * w` THEN
  SUBGOAL_THEN `&0 <= (&1 + k) * w - z` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= z * ((&1 + k) * w - z)` THEN
  SUBGOAL_THEN `(&1 + k) * (k + z * w - &1) = z * ((&1 + k) * w - z)` ASSUME_TAC THENL
  [UNDISCH_TAC `k pow 2 + z pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= k + z * w` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092PRS_PROD `&0 < (&1 + k) * (&1 - (k + z * w))` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: e_negative *)
let C1092PRS_E_NEGATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= t /\
             c1092prs_sigma c s d t <= &0
             ==> &0 < c1092prs_eMinus c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_ABBREV_TAC THEN
  SUBGOAL_THEN `c1092prs_eMinus c s d t =
                &1 - (&3 / &2) * d + c1092prs_kappa c s d t * (&1 - s) -
                c1092prs_sigma c s d t` SUBST1_TAC THENL
  [REWRITE_TAC[c1092prs_eMinus; c1092prs_kappa; c1092prs_sigma] THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092PRS_PROD `&0 <= (c1092prs_kappa c s d t - &7 / &10) * (&1 - s)` THEN
  RASM_ARITH_TAC);;
