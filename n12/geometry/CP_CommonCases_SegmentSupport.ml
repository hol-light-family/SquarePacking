(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/SegmentSupport.lean                *)
(* (N12Compact.CommonCases.SegmentSupport).  Support consequences for a      *)
(* segment avoiding an open rectangle.                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SegmentCorner.ml";;

(* Lean: endpoint_exits (private) *)
let CCSS_ENDPOINT_EXITS = prove
 (`forall lU hU lV hV u v.
      ~(lU < u /\ u < hU /\ lV < v /\ v < hV)
      ==> u <= lU \/ hU <= u \/ v <= lV \/ hV <= v`,
  REAL_ARITH_TAC);;

(* instantiate the avoidance hypothesis at parameter tt *)
let CCSS_AVOID_TAC tt =
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC tt o check (fun th -> is_forall(concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC;;

let CCSS_ENDPOINTS_TAC =
  FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> is_forall(concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID; REAL_ADD_RID] THEN
  REPEAT DISCH_TAC;;

(* Lean: vertical *)
let CCSS_VERTICAL = prove
 (`forall lU hU lV hV u0 v0 u1 v1.
      (lU < &0 /\ &0 < hU /\ lV < &0 /\ &0 < hV) /\
      u1 = u0 /\ u0 < &0 /\ v0 < &0 /\ &0 < v1 /\
      (forall t. &0 <= t ==> t <= &1 ==>
        ~(lU < (&1 - t) * u0 + t * u1 /\ (&1 - t) * u0 + t * u1 < hU /\
          lV < (&1 - t) * v0 + t * v1 /\ (&1 - t) * v0 + t * v1 < hV))
      ==> u0 <= lU`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `u1:real = u0`)) THEN
  SUBGOAL_THEN `&0 < v1 - v0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--v0 / (v1 - v0)`) THEN
  SUBGOAL_THEN `--v0 / (v1 - v0) * (v1 - v0) = --v0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `T0 = --v0 / (v1 - v0)` THEN
  SUBGOAL_THEN `(&1 - T0) * v0 + T0 * v1 = &0` SUBST1_TAC THENL
   [UNDISCH_TAC `T0 * (v1 - v0) = --v0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(&1 - T0) * u0 + T0 * u0 = u0`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: increasing *)
let CCSS_INCREASING = prove
 (`forall lU hU lV hV u0 v0 u1 v1.
      (lU < &0 /\ &0 < hU /\ lV < &0 /\ &0 < hV) /\
      u0 < &0 /\ v0 < &0 /\ &0 < v1 /\ &0 < u1 - u0 /\ &0 < v1 - v0 /\
      u1 - u0 < hU - lU /\ v1 - v0 < hV - lV /\
      (v1 - v0) * u0 - (u1 - u0) * v0 < &0 /\
      (forall t. &0 <= t ==> t <= &1 ==>
        ~(lU < (&1 - t) * u0 + t * u1 /\ (&1 - t) * u0 + t * u1 < hU /\
          lV < (&1 - t) * v0 + t * v1 /\ (&1 - t) * v0 + t * v1 < hV))
      ==> u1 <= lU \/
          (v1 - v0) * lU - (u1 - u0) * hV >= (v1 - v0) * u0 - (u1 - u0) * v0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `u1 <= lU` THEN ASM_REWRITE_TAC[real_ge] THEN
  CCSS_ENDPOINTS_TAC THEN
  SUBGOAL_THEN `u0 <= lU \/ v0 <= lV` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `hU <= u1 \/ hV <= v1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`lV:real`; `hV:real`; `lU:real`; `hU:real`;
                  `v0:real`; `u0:real`; `v1:real`; `u1:real`] SEGC_CROSSING_ORDER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN CCSS_AVOID_TAC `t:real`;
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN
    NLIN_FACTS_TAC [] [`&0 < (v1 - v0) * hU`; `&0 < (u1 - u0) * --lV`] THEN
    NLIN_TAC ~deg2:false [];
    MP_TAC(SPECL [`lU:real`; `hU:real`; `lV:real`; `hV:real`;
                  `u0:real`; `v0:real`; `u1:real`; `v1:real`] SEGC_CROSSING_ORDER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN CCSS_AVOID_TAC `t:real`;
      REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* Lean: decreasing *)
let CCSS_DECREASING = prove
 (`forall lU hU lV hV u0 v0 u1 v1.
      (lU < &0 /\ &0 < hU /\ lV < &0 /\ &0 < hV) /\
      u1 < &0 /\ v0 < &0 /\ &0 < v1 /\ &0 < u0 - u1 /\ &0 < v1 - v0 /\
      u0 - u1 < hU - lU /\ v1 - v0 < hV - lV /\
      (v1 - v0) * u0 + (u0 - u1) * v0 < &0 /\
      (forall t. &0 <= t ==> t <= &1 ==>
        ~(lU < (&1 - t) * u0 + t * u1 /\ (&1 - t) * u0 + t * u1 < hU /\
          lV < (&1 - t) * v0 + t * v1 /\ (&1 - t) * v0 + t * v1 < hV))
      ==> u0 <= lU \/
          (v1 - v0) * lU + (u0 - u1) * lV >= (v1 - v0) * u0 + (u0 - u1) * v0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `u0 <= lU` THEN ASM_REWRITE_TAC[real_ge] THEN
  CCSS_ENDPOINTS_TAC THEN
  SUBGOAL_THEN `hU <= u0 \/ v0 <= lV` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u1 <= lU \/ hV <= v1` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`lV:real`; `hV:real`; `--hU`; `--lU`;
                  `v0:real`; `--u0`; `v1:real`; `--u1`] SEGC_CROSSING_ORDER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN CCSS_AVOID_TAC `t:real`;
      REAL_ARITH_TAC];
    MP_TAC(SPECL [`--hV`; `--lV`; `lU:real`; `hU:real`;
                  `--v1`; `u1:real`; `--v0`; `u0:real`] SEGC_CROSSING_ORDER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN CCSS_AVOID_TAC `&1 - t`;
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN
    NLIN_FACTS_TAC [] [`&0 < (v1 - v0) * hU`; `&0 < (u0 - u1) * hV`] THEN
    NLIN_TAC ~deg2:false [];
    ASM_REAL_ARITH_TAC]);;
