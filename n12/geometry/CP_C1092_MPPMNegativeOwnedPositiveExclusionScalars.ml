(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeOwnedPositiveExclusionScalars *)
(* .lean (N12Compact.C1092MPPMNegativeOwnedPositiveExclusion.Scalars).       *)
(* NEGATIVE-OWNED-POSITIVE-OWNED-EXCLUSION.  Normal is c977cc_normal;        *)
(* norm_lt is C1092NPP_NORM_LT; quarter_data is C1092WPS_QUARTER_DATA (the   *)
(* half angle t/(1+d)); the cosH/sinH rewriting of the Lean proof is         *)
(* replaced by the equivalent half-angle relations.  Tag c1092nope_.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveCeilingScalars.ml";;

let C1092NOPE_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092NOPE_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092NOPE_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

(* Lean: Pu, Qu, Pf, Qf, bracket (definitions) *)
let c1092nope_Pu = new_definition
 `c1092nope_Pu (d:real) (t:real) = &2 - d - t + (&11 / &25) * d * t`;;
let c1092nope_Qu = new_definition
 `c1092nope_Qu (d:real) (t:real) = &1 - d + t - (&11 / &25) * t pow 2`;;
let c1092nope_Pf = new_definition
 `c1092nope_Pf (c:real) (s:real) = &1 - c - s + (&13 / &20) * c * s + (&7 / &20) * c pow 2`;;
let c1092nope_Qf = new_definition
 `c1092nope_Qf (c:real) (s:real) =
    &2 - c + s - (&7 / &20) * c * s - (&13 / &20) * s pow 2`;;
let c1092nope_bracket = new_definition
 `c1092nope_bracket (y:real) = &1875 * y pow 3 - &1450 * y pow 2 + &1446 * y - &350`;;

(* the half-angle data for t/(1+d), with the abbreviation x *)
let C1092NOPE_HALF_TAC =
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NOPE_LP_TAC; ALL_TAC] THEN
  UNDISCH_TAC `t / (&1 + d) <= &7 / &32` THEN REWRITE_TAC[GSYM C1092WPS_half] THEN
  SPEC_TAC(`C1092WPS_half d t`,`x:real`) THEN GEN_TAC THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

(* Lean: recipient_bounds *)
let C1092NOPE_RECIPIENT_BOUNDS = prove
 (`forall d t. c977cc_normal d t /\ t / (&1 + d) <= &7 / &32 ==> t < &21 / &50 /\ &15 * t < &11 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN C1092NOPE_HALF_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092NOPE_PROD `&0 <= x * x` THEN
  C1092NOPE_PROD `&0 <= (&7 / &32 - x) * (&7 / &32 + x)` THEN
  C1092NOPE_PROD `&0 <= (&7 / &32 - x) * (&2 - (&21 / &50) * (x + &7 / &32))` THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
  [C1092NOPE_PROD `&0 <= (&1 + x * x) * (t - &21 / &50)`;
   C1092NOPE_PROD `&0 <= (&1 + x * x) * (&15 * t - &11 * d)`] THEN
  C1092NOPE_LP_TAC);;

(* the half-angle form of the norm defect (identity step of longitudinal) *)
let C1092NOPE_LONGITUDINAL_IDENTITY = prove
 (`forall d t x. (&1 + x pow 2) * d = &1 - x pow 2 /\ (&1 + x pow 2) * t = &2 * x
     ==> &625 * (&1 + x pow 2) pow 2 *
         (&1 - c1092nope_Pu d t pow 2 - c1092nope_Qu d t pow 2) =
         --(&4) * x * c1092nope_bracket x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d = (&1 - x pow 2) / (&1 + x pow 2) /\ t = (&2 * x) / (&1 + x pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
  [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092nope_Pu; c1092nope_Qu; c1092nope_bracket] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)) THEN
  CONV_TAC REAL_FIELD);;

(* Lean: longitudinal *)
let C1092NOPE_LONGITUDINAL = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < t /\ t / (&1 + d) <= &7 / &32
     ==> &0 < &1 - c1092nope_Pu d t * c - c1092nope_Qu d t * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN C1092NOPE_HALF_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `x:real`] C1092NOPE_LONGITUDINAL_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `x = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LZERO]) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092nope_bracket x < &0` ASSUME_TAC THENL
  [REWRITE_TAC[c1092nope_bracket; REAL_ARITH `x pow 3 = x * x * x`; REAL_POW_2] THEN
   C1092NOPE_PROD `&0 <= x * x` THEN
   C1092NOPE_PROD `&0 <= (&7 / &32 - x) * (x * x + x * (&7 / &32) + (&7 / &32) * (&7 / &32))` THEN
   C1092NOPE_LP_TAC; ALL_TAC] THEN
  C1092NOPE_PROD `&0 < x * --c1092nope_bracket x` THEN
  MP_TAC(SPECL [`c1092nope_Pu d t`; `c1092nope_Qu d t`; `c:real`; `s:real`; `&1`]
    C1092NPP_NORM_LT) THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &625 * (&1 + x pow 2) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  C1092NOPE_PROD `&0 <= (&625 * (&1 + x pow 2) pow 2) *
     --(&1 - c1092nope_Pu d t pow 2 - c1092nope_Qu d t pow 2)` THEN
  C1092NOPE_LP_TAC);;

(* Lean: transverse *)
let C1092NOPE_TRANSVERSE = prove
 (`forall c s d t. c977cc_normal c s /\ &87 / &100 < c /\ c977cc_normal d t /\ t < &21 / &50
     ==> &0 < &1 - c1092nope_Pf c s * d - c1092nope_Qf c s * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092NOPE_PROD `&0 <= s * (&1 - (&13 / &20) * c)` THEN
  C1092NOPE_PROD `&0 <= (c - &87 / &100) * (&1 - (&7 / &20) * (c + &87 / &100))` THEN
  SUBGOAL_THEN `c1092nope_Pf c s < &2 / &5` ASSUME_TAC THENL
  [REWRITE_TAC[c1092nope_Pf; REAL_POW_2] THEN C1092NOPE_LP_TAC; ALL_TAC] THEN
  C1092NOPE_PROD `&0 <= s * (c - &87 / &100)` THEN
  C1092NOPE_PROD `&0 <= (s - &1391 / &2600) * (s - &1391 / &2600)` THEN
  SUBGOAL_THEN `c1092nope_Qf c s < &33 / &25` ASSUME_TAC THENL
  [REWRITE_TAC[c1092nope_Qf; REAL_POW_2] THEN C1092NOPE_LP_TAC; ALL_TAC] THEN
  C1092NOPE_PROD `&0 < (&2 / &5 - c1092nope_Pf c s) * d` THEN
  C1092NOPE_PROD `&0 <= (&33 / &25 - c1092nope_Qf c s) * t` THEN
  C1092NOPE_LP_TAC);;
