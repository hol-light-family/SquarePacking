(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SouthwestSupportPoint/Scalars.lean  *)
(* (N12Compact.Completion.OtherCases.SouthwestSupportPoint.Scalars).  The   *)
(* five whole-interval scalar comparisons via the half-angle substitution.  *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;              *)
(* Polynomials.p1..p5 / pi_positive: ocswspp_p1.. / OCSWSPP_Pi_POSITIVE.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Polynomials.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: f1 *)
let ocswsps_f1 = new_definition
 `ocswsps_f1 (c:real) s =
    (&35 * c + &9 * s) + (&9 * c - &35 * s) -
    (&35 * c + &9 * s) * (&73 / &100 * c + &1 / &25 * s) +
    (&9 * c - &35 * s) * (&2 / &5 * s - c) - &91 / &10`;;
(* Lean: f2 *)
let ocswsps_f2 = new_definition
 `ocswsps_f2 (c:real) s =
    (&35 * c + &9 * s) * (&1 - &73 / &100 * c - &1 / &25 * s) -
    &13 / &50 * c * (&9 * c - &35 * s) - &91 / &10`;;
(* Lean: f3 *)
let ocswsps_f3 = new_definition
 `ocswsps_f3 (c:real) s = c + s - &24 / &25 + &31 / &100 * s pow 2 - &27 / &25 * c * s`;;
(* Lean: f4 *)
let ocswsps_f4 = new_definition
 `ocswsps_f4 (c:real) s =
    (&35 * c - &9 * s) + (&35 * s + &9 * c) +
    (&35 * c - &9 * s) * (--(&73 / &100) * c + &1 / &25 * s) -
    (&35 * s + &9 * c) * c - &91 / &10`;;
(* Lean: f5 *)
let ocswsps_f5 = new_definition
 `ocswsps_f5 (c:real) s =
    (&35 * c - &9 * s) + (&35 * s + &9 * c) +
    (&35 * c - &9 * s) * (--(&73 / &100) * c + &1 / &25 * s) +
    (&35 * s + &9 * c) * (--(&13 / &50) * s - c) - &91 / &10`;;

(* Lean: scale_quadratic (private) *)
let OCSWSPS_SCALE_QUADRATIC = prove
 (`forall c s t k0 k1 k2 k3 k4 k5.
      (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
      ==> (&1 + t pow 2) pow 2 *
            (k0 + k1 * c + k2 * s + k3 * c pow 2 + k4 * c * s + k5 * s pow 2) =
          k0 * (&1 + t pow 2) pow 2 + k1 * (&1 + t pow 2) * (&1 - t pow 2) +
          k2 * (&1 + t pow 2) * (&2 * t) + k3 * (&1 - t pow 2) pow 2 +
          k4 * (&1 - t pow 2) * (&2 * t) + k5 * (&2 * t) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(&1 + t pow 2) pow 2 * (k0 + k1 * c + k2 * s + k3 * c pow 2 + k4 * c * s + k5 * s pow 2) =
    k0 * (&1 + t pow 2) pow 2 + k1 * (&1 + t pow 2) * ((&1 + t pow 2) * c) +
    k2 * (&1 + t pow 2) * ((&1 + t pow 2) * s) + k3 * ((&1 + t pow 2) * c) pow 2 +
    k4 * ((&1 + t pow 2) * c) * ((&1 + t pow 2) * s) + k5 * ((&1 + t pow 2) * s) pow 2`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* Lean: unscale (private) *)
let OCSWSPS_UNSCALE = prove
 (`forall t f p. (&1 + t pow 2) pow 2 * f = p /\ &0 < p ==> &0 < f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (&1 + t pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(&1 + t pow 2) pow 2`; `--f`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 < p` THEN UNDISCH_TAC `(&1 + t pow 2) pow 2 * f = p` THEN
  REAL_ARITH_TAC);;

let OCSWSPS_ID_TAC fdef pdef coeffs =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL ([`c:real`; `s:real`; `t:real`] @ coeffs) OCSWSPS_SCALE_QUADRATIC) THEN
  ASM_REWRITE_TAC[fdef; pdef] THEN REAL_ARITH_TAC;;

(* Lean: f1_identity *)
let OCSWSPS_F1_IDENTITY = prove
 (`forall c s t. (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
           ==> (&1 + t pow 2) pow 2 * ocswsps_f1 c s = ocswspp_p1 t`,
  OCSWSPS_ID_TAC ocswsps_f1 ocswspp_p1
   [`--(&91 / &10)`; `&44`; `--(&26)`; `--(&691 / &20)`; `&3063 / &100`; `--(&359 / &25)`]);;

(* Lean: f2_identity *)
let OCSWSPS_F2_IDENTITY = prove
 (`forall c s t. (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
           ==> (&1 + t pow 2) pow 2 * ocswsps_f2 c s = ocswspp_p2 t`,
  OCSWSPS_ID_TAC ocswsps_f2 ocswspp_p2
   [`--(&91 / &10)`; `&35`; `&9`; `--(&2789 / &100)`; `&113 / &100`; `--(&9 / &25)`]);;

(* Lean: f3_identity *)
let OCSWSPS_F3_IDENTITY = prove
 (`forall c s t. (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
           ==> (&1 + t pow 2) pow 2 * ocswsps_f3 c s = ocswspp_p3 t`,
  OCSWSPS_ID_TAC ocswsps_f3 ocswspp_p3
   [`--(&24 / &25)`; `&1`; `&1`; `&0`; `--(&27 / &25)`; `&31 / &100`]);;

(* Lean: f4_identity *)
let OCSWSPS_F4_IDENTITY = prove
 (`forall c s t. (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
           ==> (&1 + t pow 2) pow 2 * ocswsps_f4 c s = ocswspp_p4 t`,
  OCSWSPS_ID_TAC ocswsps_f4 ocswspp_p4
   [`--(&91 / &10)`; `&44`; `&26`; `--(&691 / &20)`; `--(&2703 / &100)`; `--(&9 / &25)`]);;

(* Lean: f5_identity *)
let OCSWSPS_F5_IDENTITY = prove
 (`forall c s t. (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
           ==> (&1 + t pow 2) pow 2 * ocswsps_f5 c s = ocswspp_p5 t`,
  OCSWSPS_ID_TAC ocswsps_f5 ocswspp_p5
   [`--(&91 / &10)`; `&44`; `&26`; `--(&691 / &20)`; `--(&2937 / &100)`; `--(&473 / &50)`]);;

(* quarter data as assumptions with t = half c s abbreviated *)
let OCSWSPS_QD_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `t = C1092WPS_half c s` THEN
  SUBGOAL_THEN `&0 <= &1 + t pow 2 /\ &0 <= t pow 2` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC];;

(* Lean: canonical_half_upper *)
let OCSWSPS_CANONICAL_HALF_UPPER = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> C1092WPS_half c s < &5 / &12`,
  REPEAT STRIP_TAC THEN OCSWSPS_QD_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + t pow 2) * (c - s) /\
                &0 <= (t - &5 / &12) * (t + &5 / &12)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: positive_low *)
let OCSWSPS_POSITIVE_LOW = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &0 <= &9 * c - &35 * s
         ==> &0 < ocswsps_f1 c s`,
  REPEAT STRIP_TAC THEN OCSWSPS_QD_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + t pow 2) * (&9 * c - &35 * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t <= &1 / &7` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC OCSWSPS_UNSCALE THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `ocswspp_p1 t`] THEN
  ASM_SIMP_TAC[OCSWSPS_F1_IDENTITY; OCSWSPP_P1_POSITIVE]);;

(* Lean: positive_high *)
let OCSWSPS_POSITIVE_HIGH = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &9 * c - &35 * s <= &0
         ==> &0 < ocswsps_f2 c s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSWSPS_CANONICAL_HALF_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN OCSWSPS_QD_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + t pow 2) * (&35 * s - &9 * c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &8 <= t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&1 / &8 - t) * (&1 / &8 + t)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC OCSWSPS_UNSCALE THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `ocswspp_p2 t`] THEN
  ASM_SIMP_TAC[OCSWSPS_F2_IDENTITY; OCSWSPP_P2_POSITIVE; REAL_LT_IMP_LE]);;

(* Lean: positive_vertex *)
let OCSWSPS_POSITIVE_VERTEX = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         s <= &3 / &4 * c
         ==> &0 < ocswsps_f3 c s`,
  REPEAT STRIP_TAC THEN OCSWSPS_QD_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + t pow 2) * (&3 * c - &4 * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t <= &1 / &3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (t - &1 / &3) * (&3 * t + &9)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC OCSWSPS_UNSCALE THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `ocswspp_p3 t`] THEN
  ASM_SIMP_TAC[OCSWSPS_F3_IDENTITY; OCSWSPP_P3_POSITIVE]);;

(* Lean: negative_lower *)
let OCSWSPS_NEGATIVE_LOWER = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> &0 < ocswsps_f4 c s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSWSPS_CANONICAL_HALF_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN OCSWSPS_QD_TAC THEN
  MATCH_MP_TAC OCSWSPS_UNSCALE THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `ocswspp_p4 t`] THEN
  ASM_SIMP_TAC[OCSWSPS_F4_IDENTITY; OCSWSPP_P4_POSITIVE; REAL_LT_IMP_LE]);;

(* Lean: half_lower_of_span *)
let OCSWSPS_HALF_LOWER_OF_SPAN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
         &1 < &73 / &100 * c + &24 / &25 * s
         ==> &4 / &25 < C1092WPS_half c s`,
  REPEAT STRIP_TAC THEN OCSWSPS_QD_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + t pow 2) * ((&73 / &100 * c + &24 / &25 * s) - &1)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + t pow 2) * ((&73 / &100 * c + &24 / &25 * s) - &1)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&4 / &25 - t) * (&48 / &25 - &173 / &100 * (&4 / &25 + t))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_upper *)
let OCSWSPS_NEGATIVE_UPPER = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\
         &4 / &25 <= C1092WPS_half c s
         ==> &0 < ocswsps_f5 c s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCSWSPS_CANONICAL_HALF_UPPER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN OCSWSPS_QD_TAC THEN
  MATCH_MP_TAC OCSWSPS_UNSCALE THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `ocswspp_p5 t`] THEN
  ASM_SIMP_TAC[OCSWSPS_F5_IDENTITY; OCSWSPP_P5_POSITIVE; REAL_LT_IMP_LE]);;
