(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/PointScalars.lean       *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints).  Exact scalar *)
(* steps in C976-LEFT-UPPER-POINTS.  half / quarter_data are C1092WPS_half / *)
(* C1092WPS_QUARTER_DATA; CanonicalScalars.bounds is CCCS_BOUNDS.  Purely    *)
(* scalar.  Tag OCC976PS_.                                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_PointInputs.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: endpoint (private) *)
let OCC976PS_ENDPOINT = prove
 (`forall c s m n k z. c pow 2 + s pow 2 = &1 /\
     z <= k * (m * c + n * s) /\
     k pow 2 * (m pow 2 + n pow 2) < &1
     ==> z < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k * (m * c + n * s)) pow 2 + (k * (n * c - m * s)) pow 2 =
                k pow 2 * (m pow 2 + n pow 2)` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `k * (n * c - m * s)` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `k * (m * c + n * s) < &1` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= (k * (m * c + n * s)) pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN
      SUBGOAL_THEN `&0 <= (k * (m * c + n * s) - &1) * (k * (m * c + n * s) + &1)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let OCC976PS_ENDPOINT_TAC m n k =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC OCC976PS_ENDPOINT THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; m; n; k] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REAL_ARITH_TAC;;

(* Lean: upper_v_span *)
let OCC976PS_UPPER_V_SPAN = prove
 (`forall c s. c pow 2 + s pow 2 = &1 /\ (&21 / &65) * c <= s
         ==> (&26 / &25) * c + (&1 / &50) * s < &1`,
  OCC976PS_ENDPOINT_TAC `&65` `&21` `&3401 / &233300`);;

(* Lean: inward_span *)
let OCC976PS_INWARD_SPAN = prove
 (`forall c s. c pow 2 + s pow 2 = &1 ==> (&21 / &25) * c + (&27 / &100) * s < &1`,
  OCC976PS_ENDPOINT_TAC `&21 / &25` `&27 / &100` `&1`);;

let OCC976PS_POS_CANCEL = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

(* Lean: small_corner_margin *)
let OCC976PS_SMALL_CORNER_MARGIN = prove
 (`forall c s. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\ s <= (&21 / &65) * c
         ==> &1 < c + (&3 / &20) * c * s + (&7 / &20) * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `&0 < C1092WPS_half c s` MP_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z <= &8 / &25` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (z - &8 / &25) * (&1 + c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &3 - &6 * z - &3 * z pow 2 - &20 * z pow 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&8 / &25 - z) *
        (&6 + &3 * (&8 / &25 + z) + &20 * ((&8 / &25) pow 2 + (&8 / &25) * z + z pow 2))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < y - &1 ==> &1 < y`) THEN
  MATCH_MP_TAC OCC976PS_POS_CANCEL THEN EXISTS_TAC `&10 * (&1 + z pow 2) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&10 * (&1 + z pow 2) pow 2) * ((c + (&3 / &20) * c * s + (&7 / &20) * s pow 2) - &1) =
                z * (&3 - &6 * z - &3 * z pow 2 - &20 * z pow 3)` SUBST1_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);;

(* Lean: farther_margin *)
let OCC976PS_FARTHER_MARGIN = prove
 (`forall c s. &0 < c /\ &0 < s /\ c pow 2 + s pow 2 = &1 /\
         (&37 / &65) * c <= s /\ s <= (&3 / &4) * c
         ==> &0 < (&37 / &100) * c + (&11 / &100) * s - &189 / &625 -
                  (&91 / &2500) * c pow 2 - (&42 / &625) * c * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&3 * c - &4 * s) * (&3 * c + &4 * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `&4 / &5 <= c /\ s <= &3 / &5 /\ c <= &1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &4 / &5`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&3 / &5 - s) * ((s + &3 / &5) - (c + &4 / &5) / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &5 - s) / &2 <= c - &4 / &5` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= (c - &4 / &5) - (&3 / &5 - s) / &2
                             ==> (&3 / &5 - s) / &2 <= c - &4 / &5`) THEN
    MATCH_MP_TAC(REAL_ARITH `forall k y. &0 < k /\ (&0 < k ==> &0 <= y) ==> &0 <= y`) THEN
    EXISTS_TAC `c + &4 / &5` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= (c + &4 / &5) * ((c - &4 / &5) - (&3 / &5 - s) / &2)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_MUL_EQ]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c - &4 / &5) * ((&37 / &100 - (&91 / &2500) * (c + &4 / &5) -
                       (&42 / &625) * s) - &1 / &4) /\
                &0 <= (&3 / &5 - s) * (&3 / &50 - (&11 / &100 - (&42 / &625) * (&4 / &5)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
