(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976MergedLeft/Scalars.lean         *)
(* (N12Compact.Completion.OtherCases.C976MergedLeft).  Exact full-interval   *)
(* certificates of C976-MERGED-LEFT-ENDING sections 3--5.                    *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;               *)
(* CommonCases.CanonicalScalars.bounds: CCCS_BOUNDS; BernsteinQuartic.value /*)
(* positive: ccbq_value / CCBQ_POSITIVE; CanonicalProjection.before / after: *)
(* CCCP_BEFORE / CCCP_AFTER.  The rational substitution c = (1-t^2)/(1+t^2), *)
(* s = 2t/(1+t^2) is done by REAL_FIELD from the half-angle relations.       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_CommonCases_BernsteinQuartic.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_Inputs.ml";;

let OCC976MLS_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* an identity in c, s proved through the half angle t *)
let occ976mls_half_identity tm = prove(tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + t pow 2` ASSUME_TAC THENL
  [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c = (&1 - t pow 2) / (&1 + t pow 2) /\ s = (&2 * t) / (&1 + t pow 2)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
  [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `&0 < x ==> ~(x = &0)`)) THEN
  CONV_TAC REAL_FIELD);;

let OCC976MLS_SMALL_IDENTITY = occ976mls_half_identity
 `forall c s t. (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
     ==> &10 * (&1 + t pow 2) pow 2 * (c + (&3 / &20) * c * s + (&7 / &20) * s pow 2 - &1) =
         t * (&3 - &6 * t - &3 * t pow 2 - &20 * t pow 3)`;;

let OCC976MLS_LOWER_IDENTITY = occ976mls_half_identity
 `forall c s t. (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
     ==> (&1 + t pow 2) pow 2 * ((&37 / &100) * c + (&11 / &100) * s - &27 / &80 +
           (&351 / &10000) * s pow 2 - (&81 / &1250) * c * s) =
         (&325 + &904 * t - &5346 * t pow 2 + &3496 * t pow 3 - &7075 * t pow 4) / &10000`;;

let OCC976MLS_QUARTER_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (find_term
    (can (term_match [] `C1092WPS_half c s`))) o concl))) THEN
  SPEC_TAC(`C1092WPS_half c s`,`t:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN DISCH_TAC;;

let OCC976MLS_POS_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let OCC976MLS_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let OCC976MLS_POS_SQ = prove
 (`forall t. &0 < &1 + t pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

(* Lean: small_corner_margin *)
let OCC976MLS_SMALL_CORNER_MARGIN = prove
 (`forall c s. &0 < c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\ s <= (&38 / &65) * c
     ==> &1 < c + (&3 / &20) * c * s + (&7 / &20) * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  OCC976MLS_QUARTER_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t <= &8 / &25` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`t - &8 / &25`; `&1 + c`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &3 - &6 * t - &3 * t pow 2 - &20 * t pow 3` ASSUME_TAC THENL
  [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
   OCC976MLS_PROD_TAC `&8 / &25 - t`
     `&6 + &3 * (&8 / &25 + t) + &20 * ((&8 / &25) pow 2 + (&8 / &25) * t + t pow 2)` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `t:real`] OCC976MLS_SMALL_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`t:real`; `&3 - &6 * t - &3 * t pow 2 - &20 * t pow 3`] REAL_LT_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:real` OCC976MLS_POS_SQ) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &10 * (&1 + t pow 2) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c + (&3 / &20) * c * s + (&7 / &20) * s pow 2 - &1` MP_TAC THENL
  [MATCH_MP_TAC OCC976MLS_POS_OF_MUL THEN EXISTS_TAC `&10 * (&1 + t pow 2) pow 2` THEN
   CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; NLIN_TAC ~deg2:false []]; REAL_ARITH_TAC]);;

(* Lean: top_span *)
let OCC976MLS_TOP_SPAN = prove
 (`forall c s. c pow 2 + s pow 2 = &1 /\ (&38 / &65) * c <= s ==> c + (&23 / &100) * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&65 * c + &38 * s) pow 2 <= &5669` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `&38 * c - &65 * s`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&3687 / &283450) * (&65 * c + &38 * s) < &1` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: cosine_small *)
let OCC976MLS_COSINE_SMALL = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ (&38 / &65) * c < s ==> c < &7 / &8`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&65 * s - &38 * c`; `&65 * s + &38 * c`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  NLIN_TAC []);;

(* Lean: half_small_of_cosine *)
let OCC976MLS_HALF_SMALL_OF_COSINE = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &50 / &63 < c
     ==> C1092WPS_half c s < &17 / &50`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCC976MLS_QUARTER_TAC THEN
  SUBGOAL_THEN `(&1 + c) * t pow 2 = &1 - c` ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  OCC976MLS_PROD_TAC `t pow 2` `c - &50 / &63` THEN
  SUBGOAL_THEN `t pow 2 < &13 / &113` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: lower_corner_margin *)
let OCC976MLS_LOWER_CORNER_MARGIN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ C1092WPS_half c s <= &17 / &50
     ==> &0 < (&37 / &100) * c + (&11 / &100) * s - &27 / &80 +
              (&351 / &10000) * s pow 2 - (&81 / &1250) * c * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCC976MLS_QUARTER_TAC THEN
  MP_TAC(SPECL [`(&50 / &17) * t`; `&13 / &400`; `&5023 / &125000`; `&939201 / &25000000`;
                `&4388639 / &156250000`; `&14305853 / &2500000000`] CCBQ_POSITIVE) THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ccbq_value ((&50 / &17) * t) (&13 / &400) (&5023 / &125000)
                 (&939201 / &25000000) (&4388639 / &156250000) (&14305853 / &2500000000) =
                (&325 + &904 * t - &5346 * t pow 2 + &3496 * t pow 3 - &7075 * t pow 4) / &10000`
    SUBST1_TAC THENL [REWRITE_TAC[ccbq_value] THEN CONV_TAC REAL_RING; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `t:real`] OCC976MLS_LOWER_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:real` OCC976MLS_POS_SQ) THEN DISCH_TAC THEN
  MATCH_MP_TAC OCC976MLS_POS_OF_MUL THEN EXISTS_TAC `(&1 + t pow 2) pow 2` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

(* Lean: early_span *)
let OCC976MLS_EARLY_SPAN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ C1092WPS_half c s <= &7 / &20
     ==> (&27 / &100) * c + (&63 / &50) * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCC976MLS_QUARTER_TAC THEN
  OCC976MLS_PROD_TAC `&7 - &20 * t` `&40 + &14 * t` THEN
  SUBGOAL_THEN `(&1 + t pow 2) * (&280 * c - &351 * s) = (&7 - &20 * t) * (&40 + &14 * t)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN
   UNDISCH_TAC `(&1 + t pow 2) * s = &2 * t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `t:real` OCC976MLS_POS_SQ) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&351 * s <= &280 * c` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
   MATCH_MP_TAC OCC976MLS_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + t pow 2` THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&351 / &449`; `&280 / &449`; `&27 / &100`; `&63 / &50`]
    CCCP_BEFORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
                  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

(* Lean: target_span *)
let OCC976MLS_TARGET_SPAN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &7 / &20 <= C1092WPS_half c s
     ==> (&26 / &25) * c + (&27 / &100) * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCC976MLS_QUARTER_TAC THEN
  OCC976MLS_PROD_TAC `&20 * t - &7` `&40 + &14 * t` THEN
  SUBGOAL_THEN `(&1 + t pow 2) * (&351 * s - &280 * c) = (&20 * t - &7) * (&40 + &14 * t)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN
   UNDISCH_TAC `(&1 + t pow 2) * s = &2 * t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPEC `t:real` OCC976MLS_POS_SQ) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&280 * c <= &351 * s` ASSUME_TAC THENL
  [MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
   MATCH_MP_TAC OCC976MLS_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + t pow 2` THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&351 / &449`; `&280 / &449`; `&26 / &25`; `&27 / &100`]
    CCCP_AFTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
                  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;
