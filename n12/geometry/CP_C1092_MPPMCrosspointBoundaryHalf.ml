(* ========================================================================= *)
(* Phase 2: Compact/Completion/C1092/MPPMCrosspointBoundaryHalf.lean        *)
(* (namespace N12Compact.C1092MPPMCrosspointSupport).  Closed half-angle    *)
(* coordinates for the boundary-scalar joins.  half is c1092mcbh_half;      *)
(* rho (abbrev of C1092MPPMMissingPositiveBoundaries.Arc.diagonal) is        *)
(* c1092mpba_diagonal; Quarter is c1092mcs_quarter; Normal is c977cc_normal; *)
(* cosH / sinH are c1092sps_cosH / c1092sps_sinH; Real.sqrt is sqrt.         *)
(* Tag C1092MCBH_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointQuadraticRemainders.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10Clamp.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundArc.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C1092ShallowPositiveScalars.ml";;

(* Lean: half *)
let c1092mcbh_half = new_definition `c1092mcbh_half (c:real) (s:real) = s / (&1 + c)`;;

(* the defining relations of half on the quarter circle *)
let C1092MCBH_HALF_DATA = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> &0 <= c1092mcbh_half c s /\ c1092mcbh_half c s <= &1 /\
         c1092mcbh_half c s * (&1 + c) = s /\
         (&1 + c1092mcbh_half c s pow 2) * c = &1 - c1092mcbh_half c s pow 2 /\
         (&1 + c1092mcbh_half c s pow 2) * s = &2 * c1092mcbh_half c s`,
  REWRITE_TAC[c1092mcbh_half; GSYM C1092WPS_half; C1092WPS_QUARTER_DATA]);;

let C1092MCBH_COS_SIN = prove
 (`forall z c s. (&1 + z pow 2) * c = &1 - z pow 2 /\ (&1 + z pow 2) * s = &2 * z
     ==> c1092sps_cosH z = c /\ c1092sps_sinH z = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
  SIMP_TAC[REAL_EQ_LDIV_EQ; C1092SPS_HALF_DEN_POS] THEN ASM_REAL_ARITH_TAC);;

(* Lean: quarter_half *)
let C1092MCBH_QUARTER_HALF = prove
 (`forall c s. c1092mcs_quarter c s
     ==> &0 <= c1092mcbh_half c s /\ c1092mcbh_half c s <= &1 /\
         c1092sps_cosH (c1092mcbh_half c s) = c /\ c1092sps_sinH (c1092mcbh_half c s) = s`,
  REWRITE_TAC[c1092mcs_quarter] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP C1092MCBH_HALF_DATA) THEN
  ASM_SIMP_TAC[C1092MCBH_COS_SIN]);;

(* Lean: rho_bounds *)
let C1092MCBH_RHO_BOUNDS = prove
 (`&0 < c1092mpba_diagonal /\ c1092mpba_diagonal < &5 / &12 /\
   c1092mpba_diagonal pow 2 + &2 * c1092mpba_diagonal = &1 /\
   c1092sps_cosH c1092mpba_diagonal = sqrt(&2) / &2 /\
   c1092sps_sinH c1092mpba_diagonal = sqrt(&2) / &2`,
  STRIP_ASSUME_TAC C1092MPBA_DIAGONAL_DATA THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092mpba_diagonal pow 2 + &2 * c1092mpba_diagonal = &1` THEN
  REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  NLIN_TAC [REAL_LE_MUL2]);;

(* Lean: normal_half *)
let C1092MCBH_NORMAL_HALF = prove
 (`forall c s. c977cc_normal c s
     ==> &0 <= c1092mcbh_half c s /\ c1092mcbh_half c s <= c1092mpba_diagonal /\
         &0 <= &1 - &2 * c1092mcbh_half c s - c1092mcbh_half c s pow 2 /\
         c1092sps_cosH (c1092mcbh_half c s) = c /\ c1092sps_sinH (c1092mcbh_half c s) = s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal c s`)) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCBH_HALF_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[C1092MCBH_COS_SIN] THEN
  STRIP_ASSUME_TAC C1092MCBH_RHO_BOUNDS THEN
  ABBREV_TAC `z = c1092mcbh_half c s` THEN
  SUBGOAL_THEN `&0 <= &1 - &2 * z - z pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(c - s) * (&1 + z pow 2) = &1 - &2 * z - z pow 2` (SUBST1_TAC o SYM) THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN NLIN_TAC []);;

(* Lean: half_order *)
let C1092MCBH_HALF_ORDER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t
     ==> c1092mcbh_half c s <= c1092mcbh_half d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCBH_HALF_DATA) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MCBH_HALF_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `x = c1092mcbh_half c s` THEN ABBREV_TAC `y = c1092mcbh_half d t` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_TAC []);;

(* Lean: steep_half *)
let C1092MCBH_STEEP_HALF = prove
 (`forall c s. c977cc_normal c s /\ &3 / &5 <= s ==> &1 / &3 <= c1092mcbh_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092G10_STEEP_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[c1092mcbh_half] THEN
  SUBGOAL_THEN `&0 < &1 + c` (fun th -> SIMP_TAC[th; REAL_LE_RDIV_EQ]) THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;
