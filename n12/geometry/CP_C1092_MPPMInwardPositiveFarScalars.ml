(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveFarScalars.lean        *)
(* (N12Compact.C1092MPPMInwardPositive.FarScalars).  POSITIVE-MISSING-      *)
(* INWARD-FAR-ENDING sections 5--6 (Lean header: "Source only, uncompiled"). *)
(* Normal: c977cc_normal; half/cosH/sinH: C1092WPS_half / c1092sps_cosH /    *)
(* c1092sps_sinH; NegativeScalars.k/ell/forms: c1092ipns_k / c1092ipns_ell / *)
(* C1092IPNS_FORMS; UnitCircleChord.decreasing: CCUCC_DECREASING;            *)
(* sine_le_twice_half: C1092IPP_SINE_LE_TWICE_HALF.  Tag C1092IPFS_.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveNegativeScalars.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveProfile.ml";;

(* Lean: alpha *)
let c1092ipfs_alpha = new_definition
 `c1092ipfs_alpha (c:real) (s:real) = (&13 / &50) * c - (&43 / &500) * s`;;

(* Lean: gamma *)
let c1092ipfs_gamma = new_definition
 `c1092ipfs_gamma (c:real) (s:real) = (&13 / &50) * s + (&43 / &500) * c`;;

(* Lean: L0 *)
let c1092ipfs_L0 = new_definition
 `c1092ipfs_L0 (c:real) (s:real) = c1092ipfs_alpha c s + c1092ipfs_gamma c s - &7059 / &25000`;;

(* Lean: A1 (private) *)
let c1092ipfs_A1 = new_definition
 `c1092ipfs_A1 (c:real) (s:real) = &2 - c - s + (&43 / &500) * s pow 2 + (&2 / &5) * c * s`;;

(* Lean: B1 (private) *)
let c1092ipfs_B1 = new_definition
 `c1092ipfs_B1 (c:real) (s:real) = &1 - c + s + (&43 / &500) * c * s - (&2 / &5) * s pow 2`;;

(* Lean: A2 (private) *)
let c1092ipfs_A2 = new_definition
 `c1092ipfs_A2 (c:real) (s:real) = c1092ipfs_gamma c s - s * c1092ipfs_L0 c s`;;

(* Lean: B2 (private) *)
let c1092ipfs_B2 = new_definition
 `c1092ipfs_B2 (c:real) (s:real) = c1092ipfs_gamma c s - c * c1092ipfs_L0 c s`;;

(* 0 < z from 0 < k (1 + x^2)^2 z with 0 < k *)
let C1092IPFS_POS_OF_ID = prove
 (`forall k x z. &0 < k /\ &0 < k * (&1 + x pow 2) pow 2 * z ==> &0 < z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < k * (&1 + x pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT; C1092SPS_HALF_DEN_POS]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < k * (&1 + x pow 2) pow 2 * z` THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ]);;

let C1092IPFS_ID1 = prove
 (`forall x. &250 * (&1 + x pow 2) pow 2 *
       (&60 * c1092ipfs_A1 (c1092sps_cosH x) (c1092sps_sinH x) -
        &91 * c1092ipfs_B1 (c1092sps_cosH x) (c1092sps_sinH x)) =
       &15000 - &67413 * x + &56060 * x pow 2 - &83587 * x pow 3 - &500 * x pow 4`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  REWRITE_TAC[c1092ipfs_A1; c1092ipfs_B1; c1092sps_cosH; c1092sps_sinH] THEN CONV_TAC REAL_FIELD);;

let C1092IPFS_ID2 = prove
 (`forall x. &13625 * (&1 + x pow 2) pow 2 *
       (&1 - c1092ipfs_A1 (c1092sps_cosH x) (c1092sps_sinH x) * (&91 / &109) -
        c1092ipfs_B1 (c1092sps_cosH x) (c1092sps_sinH x) * (&60 / &109)) =
       (&10 * x + &3) * (&750 - &3380 * x + &2879 * x pow 2 - &3550 * x pow 3)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  REWRITE_TAC[c1092ipfs_A1; c1092ipfs_B1; c1092sps_cosH; c1092sps_sinH] THEN CONV_TAC REAL_FIELD);;

let C1092IPFS_ID3 = prove
 (`forall x. &2725000 * (&1 + x pow 2) pow 2 *
       (c1092ipfs_A2 (c1092sps_cosH x) (c1092sps_sinH x) * (&60 / &109) -
        c1092ipfs_B2 (c1092sps_cosH x) (c1092sps_sinH x) * (&91 / &109)) =
       &1496169 * x pow 4 + &690380 * x pow 3 - &2618300 * x pow 2 + &197780 * x + &78131`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  REWRITE_TAC[c1092ipfs_A2; c1092ipfs_B2; c1092ipfs_L0; c1092ipfs_alpha; c1092ipfs_gamma;
              c1092sps_cosH; c1092sps_sinH] THEN CONV_TAC REAL_FIELD);;

let C1092IPFS_ID4 = prove
 (`forall x. &1362500 * (&1 + x pow 2) pow 2 *
       (c1092ipfs_gamma (c1092sps_cosH x) (c1092sps_sinH x) -
        c1092ipfs_A2 (c1092sps_cosH x) (c1092sps_sinH x) * (&91 / &109) -
        c1092ipfs_B2 (c1092sps_cosH x) (c1092sps_sinH x) * (&60 / &109)) =
       &516420 * x pow 4 - &1963519 * x pow 3 + &272700 * x pow 2 + &132781 * x + &2580`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  REWRITE_TAC[c1092ipfs_A2; c1092ipfs_B2; c1092ipfs_L0; c1092ipfs_alpha; c1092ipfs_gamma;
              c1092sps_cosH; c1092sps_sinH] THEN CONV_TAC REAL_FIELD);;

let C1092IPFS_POW_TAC =
  REWRITE_TAC[REAL_ARITH `x pow 4 = (x * x) * (x * x) /\ x pow 3 = x * x * x`; REAL_POW_2];;

(* the half-angle polynomial margins on [0, 1/5] *)
let C1092IPFS_TRANSVERSE_X = prove
 (`forall x c s. &0 <= x /\ x <= &1 / &5 /\ c = c1092sps_cosH x /\ s = c1092sps_sinH x
     ==> &0 < c1092ipfs_A1 c s * (&60 / &109) - c1092ipfs_B1 c s * (&91 / &109) /\
         &0 < &1 - c1092ipfs_A1 c s * (&91 / &109) - c1092ipfs_B1 c s * (&60 / &109)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092IPFS_ID2) THEN MP_TAC(SPEC `x:real` C1092IPFS_ID1) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `x * x <= &1 / &25` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 / &5 - x) * (&1 / &5 + x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < &60 * a - &91 * b ==> &0 < a * (&60 / &109) - b * (&91 / &109)`) THEN
    MATCH_MP_TAC C1092IPFS_POS_OF_ID THEN
    MAP_EVERY EXISTS_TAC [`&250`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (x * x) * (&56060 - &83587 * x - &500 * (x * x))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `x <= &1 / &5` THEN C1092IPFS_POW_TAC THEN REAL_ARITH_TAC;
    MATCH_MP_TAC C1092IPFS_POS_OF_ID THEN
    MAP_EVERY EXISTS_TAC [`&13625`; `x:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (x * x) * (&2879 - &3550 * x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `x <= &1 / &5` THEN C1092IPFS_POW_TAC THEN REAL_ARITH_TAC]);;

(* Lean: transverse_coefficients (private) *)
let C1092IPFS_TRANSVERSE_COEFFICIENTS = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &1 / &5
     ==> &0 <= c1092ipfs_A1 c s /\ &0 <= c1092ipfs_B1 c s /\
         &0 < c1092ipfs_A1 c s * (&60 / &109) - c1092ipfs_B1 c s * (&91 / &109) /\
         &0 < &1 - c1092ipfs_A1 c s * (&91 / &109) - c1092ipfs_B1 c s * (&60 / &109)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  SUBGOAL_THEN `&0 <= c * s /\ &0 <= s * (&1 - (&2 / &5) * s) /\ &0 <= s * s` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[c1092ipfs_A1; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[c1092ipfs_B1; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`C1092WPS_half c s`; `c:real`; `s:real`] C1092IPFS_TRANSVERSE_X) THEN
  (ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
       FIRST_ASSUM ACCEPT_TAC;
       MATCH_MP_TAC(GEN_ALL(DISCH_ALL(CONJUNCT1(UNDISCH(SPEC_ALL C1092IPNS_FORMS))))) THEN FIRST_ASSUM ACCEPT_TAC;
       MATCH_MP_TAC(GEN_ALL(DISCH_ALL(CONJUNCT2(UNDISCH(SPEC_ALL C1092IPNS_FORMS))))) THEN FIRST_ASSUM ACCEPT_TAC];
     SIMP_TAC[]]));;

(* Lean: transverse_target *)
let C1092IPFS_TRANSVERSE_TARGET = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ C1092WPS_half c s <= &1 / &5 /\ &60 / &109 <= t
     ==> &0 < &1 - d - t + c1092ipns_k c s d t * (&1 - c - (&2 / &5) * s) +
              c1092ipns_ell c s d t * (&1 - (&543 / &500) * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IPFS_TRANSVERSE_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  MP_TAC(SPECL [`&91 / &109`; `&60 / &109`; `d:real`; `t:real`; `c1092ipfs_A1 c s`; `c1092ipfs_B1 c s`]
    CCUCC_DECREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `&1 - d - t + c1092ipns_k c s d t * (&1 - c - (&2 / &5) * s) +
                c1092ipns_ell c s d t * (&1 - (&543 / &500) * s) =
                &1 - c1092ipfs_A1 c s * d - c1092ipfs_B1 c s * t` SUBST1_TAC THENL
   [REWRITE_TAC[c1092ipns_k; c1092ipns_ell; c1092ipfs_A1; c1092ipfs_B1] THEN
    UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RING;
    ASM_REAL_ARITH_TAC]);;

let C1092IPFS_OBLIQUE_X = prove
 (`forall x c s. &0 <= x /\ x <= &1 / &5 /\ c = c1092sps_cosH x /\ s = c1092sps_sinH x
     ==> &0 < c1092ipfs_A2 c s * (&60 / &109) - c1092ipfs_B2 c s * (&91 / &109) /\
         &0 < c1092ipfs_gamma c s - c1092ipfs_A2 c s * (&91 / &109) - c1092ipfs_B2 c s * (&60 / &109)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092IPFS_ID4) THEN MP_TAC(SPEC `x:real` C1092IPFS_ID3) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= x * (&1 / &5 - x) /\ &0 <= x * x * x /\ &0 <= (x * x) * (x * x) /\
                &0 <= x * (&1 / &25 - x * x) /\ &0 <= x * x`
    STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `x * x <= &1 / &25` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= (&1 / &5 - x) * (&1 / &5 + x)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC C1092IPFS_POS_OF_ID THENL
   [MAP_EVERY EXISTS_TAC [`&2725000`; `x:real`]; MAP_EVERY EXISTS_TAC [`&1362500`; `x:real`]] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      let t = concl th in is_binary "real_lt" t || is_binary "real_le" t)) THEN
  C1092IPFS_POW_TAC THEN REAL_ARITH_TAC);;

(* Lean: oblique_coefficients (private) *)
let C1092IPFS_OBLIQUE_COEFFICIENTS = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &1 / &5
     ==> &0 <= c1092ipfs_A2 c s /\ &0 <= c1092ipfs_B2 c s /\
         &0 < c1092ipfs_A2 c s * (&60 / &109) - c1092ipfs_B2 c s * (&91 / &109) /\
         &0 < c1092ipfs_gamma c s - c1092ipfs_A2 c s * (&91 / &109) - c1092ipfs_B2 c s * (&60 / &109)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092IPP_SINE_LE_TWICE_HALF) THEN
  SUBGOAL_THEN `s <= &2 / &5` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c1092ipfs_L0 c s <= &7 / &50` ASSUME_TAC THENL
   [REWRITE_TAC[c1092ipfs_L0; c1092ipfs_alpha; c1092ipfs_gamma] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s * (&7 / &50 - c1092ipfs_L0 c s) /\
                &0 < c * (&9209 / &25000 - (&173 / &500) * c) /\
                &0 <= s * (&13 / &50 - (&87 / &500) * c)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      let t = concl th in is_binary "real_lt" t || is_binary "real_le" t)) THEN
    REWRITE_TAC[c1092ipfs_A2; c1092ipfs_L0; c1092ipfs_alpha; c1092ipfs_gamma] THEN REAL_ARITH_TAC;
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      let t = concl th in is_binary "real_lt" t || is_binary "real_le" t)) THEN
    REWRITE_TAC[c1092ipfs_B2; c1092ipfs_L0; c1092ipfs_alpha; c1092ipfs_gamma] THEN REAL_ARITH_TAC;
    ALL_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`C1092WPS_half c s`; `c:real`; `s:real`] C1092IPFS_OBLIQUE_X) THEN
  (ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
       FIRST_ASSUM ACCEPT_TAC;
       MATCH_MP_TAC(GEN_ALL(DISCH_ALL(CONJUNCT1(UNDISCH(SPEC_ALL C1092IPNS_FORMS))))) THEN FIRST_ASSUM ACCEPT_TAC;
       MATCH_MP_TAC(GEN_ALL(DISCH_ALL(CONJUNCT2(UNDISCH(SPEC_ALL C1092IPNS_FORMS))))) THEN FIRST_ASSUM ACCEPT_TAC];
     SIMP_TAC[]]));;

(* Lean: oblique_target *)
let C1092IPFS_OBLIQUE_TARGET = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ C1092WPS_half c s <= &1 / &5 /\ &60 / &109 <= t
     ==> &0 < c1092ipfs_gamma c s * (&1 - d - t) + c1092ipns_ell c s d t * c1092ipfs_L0 c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IPFS_OBLIQUE_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  MP_TAC(SPECL [`&91 / &109`; `&60 / &109`; `d:real`; `t:real`; `c1092ipfs_A2 c s`; `c1092ipfs_B2 c s`]
    CCUCC_DECREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `c1092ipfs_gamma c s * (&1 - d - t) + c1092ipns_ell c s d t * c1092ipfs_L0 c s =
                c1092ipfs_gamma c s - c1092ipfs_A2 c s * d - c1092ipfs_B2 c s * t` SUBST1_TAC THENL
   [REWRITE_TAC[c1092ipns_ell; c1092ipfs_A2; c1092ipfs_B2] THEN CONV_TAC REAL_RING;
    ASM_REAL_ARITH_TAC]);;
