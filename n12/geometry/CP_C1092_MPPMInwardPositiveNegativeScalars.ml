(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveNegativeScalars.lean   *)
(* (N12Compact.C1092MPPMInwardPositive.NegativeScalars).  Shared positive-C/ *)
(* negative-E comparisons of POSITIVE-MISSING-INWARD-ORIGIN-ENDING.          *)
(* Normal: c977cc_normal; normal_bounds: C977CC_NORMAL_BOUNDS; half / cosH / *)
(* sinH: C1092WPS_half / c1092sps_cosH / c1092sps_sinH; quarter_data:        *)
(* C1092WPS_QUARTER_DATA; normal_sum: C1092MANS_NORMAL_SUM; dot_strict:      *)
(* C1092IFCS_DOT_STRICT; SuccessorScalars.A/B: c1092ipss_A / c1092ipss_B.    *)
(* Tag C1092IPNS_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveSuccessor.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryHalf.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveSuccessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinaryScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalCapScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C1092ShallowPositiveScalars.ml";;

(* Lean: k *)
let c1092ipns_k = new_definition
 `c1092ipns_k (c:real) (s:real) (d:real) (t:real) = c * d - s * t`;;

(* Lean: ell *)
let c1092ipns_ell = new_definition
 `c1092ipns_ell (c:real) (s:real) (d:real) (t:real) = c * t + s * d`;;

(* Lean: smallA *)
let c1092ipns_smallA = new_definition
 `c1092ipns_smallA (c:real) (s:real) = &2 - c - s + (&2 / &5) * c * s`;;

(* Lean: smallB *)
let c1092ipns_smallB = new_definition
 `c1092ipns_smallB (c:real) (s:real) = &1 - c + s - (&2 / &5) * s pow 2`;;

let C1092IPNS_NORMAL_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;

(* generalise k and ell (with every assumption mentioning them) to x and y *)
let C1092IPNS_GEN_KL_TAC =
  let k = `c1092ipns_k c s d t` and e = `c1092ipns_ell c s d t` in
  REPEAT(FIRST_X_ASSUM(fun th -> if free_in k (concl th) || free_in e (concl th)
                                 then MP_TAC th else NO_TAC)) THEN
  SPEC_TAC(e, `y:real`) THEN SPEC_TAC(k, `x:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC;;

(* Lean: tight_sum *)
let C1092IPNS_TIGHT_SUM = prove
 (`forall c s. c977cc_normal c s ==> c + s <= &99 / &70`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  C1092IPNS_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (c + s - &99 / &70) * (c + s + &99 / &70)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC [SQ_NONNEG `c - s:real`]);;

(* Lean: relative *)
let C1092IPNS_RELATIVE = prove
 (`forall c s d t. c977cc_normal c s /\ s < c /\ &0 < s /\ c977cc_normal d t
     ==> &0 < c1092ipns_k c s d t /\ &0 < c1092ipns_ell c s d t /\
         c1092ipns_k c s d t <= &1 /\ c1092ipns_ell c s d t <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  C1092IPNS_NORMAL_TAC THEN
  SUBGOAL_THEN `c1092ipns_k c s d t pow 2 + c1092ipns_ell c s d t pow 2 = &1` ASSUME_TAC THENL
   [REWRITE_TAC[c1092ipns_k; c1092ipns_ell] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c1092ipns_k c s d t /\ &0 < c1092ipns_ell c s d t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092ipns_k; c1092ipns_ell] THEN
    SUBGOAL_THEN `&0 < (c - s) * d /\ &0 <= s * (d - t) /\ &0 <= c * t /\ &0 < s * d`
      STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL;
        MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      let t = concl th in is_binary "real_lt" t || is_binary "real_le" t)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092IPNS_GEN_KL_TAC THEN CONJ_TAC THEN
  NLIN_TAC [SQ_NONNEG `x:real`; SQ_NONNEG `y:real`; SQ_NONNEG `x - &1`; SQ_NONNEG `y - &1`]);;

(* Lean: downward *)
let C1092IPNS_DOWNWARD = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
     &0 <= c1092ipns_k c s d t /\ c1092ipns_k c s d t <= &1 /\ c1092ipns_ell c s d t <= &1
     ==> &0 < &1 - (&7 / &20) * (c + s) + c1092ipns_k c s d t * (&1 - (&543 / &500) * d) +
              c1092ipns_ell c s d t * (&1 - d - t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092IPNS_TIGHT_SUM o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092IPNS_TIGHT_SUM o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092MANS_NORMAL_SUM o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  C1092IPNS_GEN_KL_TAC THEN
  SUBGOAL_THEN `&0 <= x * (&1 - d)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x * d <= &1` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN UNDISCH_TAC `x <= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - y) * (d + t - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      let t = concl th in is_binary "real_lt" t || is_binary "real_le" t)) THEN
  REAL_ARITH_TAC);;

(* Lean: transverse *)
let C1092IPNS_TRANSVERSE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
     &0 <= c1092ipns_k c s d t /\ &0 <= c1092ipns_ell c s d t /\ c1092ipns_ell c s d t <= &1
     ==> &0 < &1 + (c1092ipns_k c s d t + c1092ipns_ell c s d t) * (&1 - c) +
              (&2 / &5) * (c1092ipns_k c s d t - c1092ipns_ell c s d t) * s - t + (&2 / &5) * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal d t`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C1092IPNS_TIGHT_SUM o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  C1092IPNS_NORMAL_TAC THEN
  SUBGOAL_THEN `s < &71 / &100` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (c - s) * (c + s)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC [SQ_NONNEG `s - &71 / &100`];
    ALL_TAC] THEN
  C1092IPNS_GEN_KL_TAC THEN
  SUBGOAL_THEN `&0 <= (x + y) * (&1 - c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (x - y + &1) * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      let t = concl th in is_binary "real_lt" t || is_binary "real_le" t)) THEN
  REAL_ARITH_TAC);;

(* Lean: forms *)
let C1092IPNS_FORMS = prove
 (`forall c s. c977cc_normal c s
     ==> c = c1092sps_cosH (C1092WPS_half c s) /\ s = c1092sps_sinH (C1092WPS_half c s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  C1092IPNS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
  SIMP_TAC[REAL_EQ_RDIV_EQ; C1092SPS_HALF_DEN_POS] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let C1092IPNS_SMALL_IDENTITY = prove
 (`forall x. &25 * (&1 + x pow 2) pow 2 *
       (&1 - c1092ipns_smallA (c1092sps_cosH x) (c1092sps_sinH x) pow 2 -
             c1092ipns_smallB (c1092sps_cosH x) (c1092sps_sinH x) pow 2) =
       &4 * x * (&15 - &59 * x + &55 * x pow 2 - &75 * x pow 3)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  REWRITE_TAC[c1092ipns_smallA; c1092ipns_smallB; c1092sps_cosH; c1092sps_sinH] THEN
  CONV_TAC REAL_FIELD);;

let C1092IPNS_MARKER_IDENTITY = prove
 (`forall x. &400 * (&1 + x pow 2) pow 2 *
       (&1 - c1092ipss_A (c1092sps_cosH x) (c1092sps_sinH x) pow 2 -
             c1092ipss_B (c1092sps_cosH x) (c1092sps_sinH x) pow 2) =
       --(&5409 * x pow 4 - &2196 * x pow 3 - &366 * x pow 2 - &204 * x + &49)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  REWRITE_TAC[c1092ipss_A; c1092ipss_B; c1092sps_cosH; c1092sps_sinH] THEN
  CONV_TAC REAL_FIELD);;

let C1092IPNS_SCALED_POS = prove
 (`forall x z. &0 < &25 * (&1 + x pow 2) pow 2 * z ==> &0 < z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &25 * (&1 + x pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN SIMP_TAC[REAL_POW_LT; C1092SPS_HALF_DEN_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LT_MUL_EQ; REAL_MUL_ASSOC]);;

let C1092IPNS_SMALL_NORM = prove
 (`forall x c s. &0 < x /\ x <= &1 / &5 /\ c = c1092sps_cosH x /\ s = c1092sps_sinH x
     ==> c1092ipns_smallA c s pow 2 + c1092ipns_smallB c s pow 2 < &1 pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092IPNS_SMALL_IDENTITY) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &15 - &59 * x + &55 * x pow 2 - &75 * x pow 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= x pow 2 * (&55 - &75 * x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `x <= &1 / &5` THEN UNDISCH_TAC `&0 < x` THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH `x pow 3 = x * x * x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < &1 - p - q ==> p + q < &1 pow 2`) THEN
  MATCH_MP_TAC C1092IPNS_SCALED_POS THEN EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);;

(* Lean: small_target *)
let C1092IPNS_SMALL_TARGET = prove
 (`forall c s d t. c977cc_normal c s /\ &0 < s /\ c977cc_normal d t /\ C1092WPS_half c s <= &1 / &5
     ==> &0 < &1 - d - t + c1092ipns_k c s d t * (&1 - c - (&2 / &5) * s) +
              c1092ipns_ell c s d t * (&1 - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  SUBGOAL_THEN `c1092ipns_smallA c s pow 2 + c1092ipns_smallB c s pow 2 < &1 pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092IPNS_SMALL_NORM THEN EXISTS_TAC `C1092WPS_half c s` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC C1092IPNS_FORMS THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c1092ipns_smallA c s`; `c1092ipns_smallB c s`; `&1`]
    C1092IFCS_DOT_STRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01] THEN UNDISCH_TAC `c977cc_normal d t` THEN SIMP_TAC[c977cc_normal];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - d - t + c1092ipns_k c s d t * (&1 - c - (&2 / &5) * s) +
                c1092ipns_ell c s d t * (&1 - s) =
                &1 - c1092ipns_smallA c s * d - c1092ipns_smallB c s * t` SUBST1_TAC THENL
   [REWRITE_TAC[c1092ipns_k; c1092ipns_ell; c1092ipns_smallA; c1092ipns_smallB] THEN
    UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RING;
    REAL_ARITH_TAC]);;

let C1092IPNS_MARKER_NORM_X = prove
 (`forall x c s. &1 / &5 <= x /\ x <= &2 / &5 /\ c = c1092sps_cosH x /\ s = c1092sps_sinH x
     ==> c1092ipss_A c s pow 2 + c1092ipss_B c s pow 2 < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092IPNS_MARKER_IDENTITY) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&5409 * x pow 4 - &2196 * x pow 3 - &366 * x pow 2 - &204 * x + &49 < &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `x pow 3 * (&5409 * x - &2196) <= &0 /\ &0 <= (x - &1 / &5) * (x + &1 / &5) /\
                  &0 <= x pow 3`
      MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a * --b ==> a * b <= &0`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `&1 / &5 <= x` THEN UNDISCH_TAC `x <= &2 / &5` THEN
    REWRITE_TAC[REAL_ARITH `x pow 4 = x pow 3 * x`; REAL_POW_2] THEN
    SPEC_TAC(`x pow 3`, `z:real`) THEN REPEAT STRIP_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < &1 - p - q ==> p + q < &1`) THEN
  MATCH_MP_TAC C1092IPNS_SCALED_POS THEN EXISTS_TAC `x:real` THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < &16 * z ==> &0 < z`) THEN
  REWRITE_TAC[REAL_ARITH `&16 * &25 * y * z = &400 * y * z`] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: marker_norm *)
let C1092IPNS_MARKER_NORM = prove
 (`forall c s. c977cc_normal c s /\ &1 / &5 <= C1092WPS_half c s /\ C1092WPS_half c s <= &2 / &5
     ==> c1092ipss_A c s pow 2 + c1092ipss_B c s pow 2 < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092IPNS_MARKER_NORM_X THEN EXISTS_TAC `C1092WPS_half c s` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092IPNS_FORMS THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: marker_target *)
let C1092IPNS_MARKER_TARGET = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
     &1 / &5 <= C1092WPS_half c s /\ C1092WPS_half c s <= &2 / &5
     ==> &0 < &1 - d - t + c1092ipns_k c s d t * (&1 - c - (&2 / &5) * s) +
              c1092ipns_ell c s d t * (&1 - (&7 / &20) * (c + s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IPNS_MARKER_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c1092ipss_B c s`; `c1092ipss_A c s`; `&1`]
    C1092IFCS_DOT_STRICT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
     [UNDISCH_TAC `c977cc_normal d t` THEN SIMP_TAC[c977cc_normal];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 - d - t + c1092ipns_k c s d t * (&1 - c - (&2 / &5) * s) +
                c1092ipns_ell c s d t * (&1 - (&7 / &20) * (c + s)) =
                &1 - c1092ipss_B c s * d - c1092ipss_A c s * t` SUBST1_TAC THENL
   [REWRITE_TAC[c1092ipns_k; c1092ipns_ell; c1092ipss_A; c1092ipss_B] THEN
    UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RING;
    REAL_ARITH_TAC]);;
