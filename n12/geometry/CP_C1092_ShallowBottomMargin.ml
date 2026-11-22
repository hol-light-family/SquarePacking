(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShallowBottomMargin.lean                 *)
(* (N12Compact.C1092ShallowBottomMargin).  The northwest bottom support      *)
(* comparison with the central faces A and K in both relative-angle orders.  *)
(* cosH / sinH / scalarB / wallWeight / bottomMinus: c1092sps_*;             *)
(* C1092ShallowBottom.upper: c1092sb_upper; b: c1092scs_b; half /            *)
(* quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShallowCentralScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: gap (definition) *)
let c1092sbm_gap = new_definition
 `c1092sbm_gap a c s A K h t =
    --h * c1092scs_b a c s K - &2 * t + (a / &2) * (&1 + t pow 2 + h * t) -
    ((s * t - c * h) * A + (s * h + c * t) * (K - a) - a * max (s * t - c * h) (&0))`;;

let C1092SBM_LIN_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then RASM_ARITH_TAC g else NLIN_TAC ~deg2:false [] g));;

(* Lean: upper_endpoint (private) *)
let C1092SBM_UPPER_ENDPOINT = prove
 (`forall a x. &1 < a /\ &0 < x /\ x <= &1 / &4 ==> &0 < c1092sb_upper a x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1092sps_cosH (&1) = &0 /\ c1092sps_sinH (&1) = &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092sb_upper; c1092sps_wallWeight; c1092sps_scalarB] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_COS_POS) THEN
  ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_SIN_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPS_BOTTOM_FAR_ENDPOINT_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a - &1`; `&1 + c1092sps_cosH x + c1092sps_sinH x`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN
  MAP_EVERY ABBREV_TAC [`C = c1092sps_cosH x`; `S = c1092sps_sinH x`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_MUL_LZERO] THEN RASM_ARITH_TAC);;

(* Lean: margin *)
let C1092SBM_MARGIN = prove
 (`forall a c s A K h t x.
     &1 < a /\ &0 < x /\ x <= &1 / &4 /\ c = c1092sps_cosH x /\ s = c1092sps_sinH x /\
     &0 <= h /\ &0 <= t /\ h pow 2 + t pow 2 = &1 /\
     a - c - s <= A /\ A <= --s / &2 /\
     a + (&14 / &25) * s - c <= K /\ K <= s /\ a <= c + (&11 / &25) * s
     ==> &0 <= c1092sbm_gap a c s A K h t /\
         (h = &0 ==> &0 < c1092sbm_gap a c s A K h t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check ((=) `c = c1092sps_cosH x` o concl)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check ((=) `s = c1092sps_sinH x` o concl)) THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_COS_POS) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_SIN_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_UNIT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`h:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = C1092WPS_half h t` THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1092sps_cosH z = h /\ c1092sps_sinH z = t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN CONJ_TAC THEN C1092SBM_LIN_TAC;
    ALL_TAC] THEN
  (* the relative sine and its factorization (in x and z) *)
  SUBGOAL_THEN `(&1 + x pow 2) * (&1 + z pow 2) *
                (c1092sps_sinH x * c1092sps_sinH z - c1092sps_cosH x * c1092sps_cosH z) =
                (x * z + x + z - &1) * (&1 + x + z - x * z)` MP_TAC THENL
   [REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
    MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_NZ) THEN
    MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_NZ) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x + z - x * z` ASSUME_TAC THENL
   [MP_TAC(SPECL [`x:real`; `&1 - z`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN C1092SBM_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + x pow 2) * (&1 + z pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s = &0)` ASSUME_TAC THENL [C1092SBM_LIN_TAC; ALL_TAC] THEN
  (* the comparison functions, in terms of c, s, h, t *)
  SUBGOAL_THEN
   `c1092sb_upper a x z =
      --h * ((a * (&3 / &2 + (c * (c + s)) / &2) - s - &2 * c) / s) -
      &2 * t + (a * (&1 + t pow 2 + t * h)) / &2 -
      ((s * t - c * h) * (--s / &2) + (s * h + c * t) * (s - a) - a * (s * t - c * h)) /\
    c1092sps_bottomMinus a x z =
      (a * (&1 + t pow 2 + t * h)) / &2 +
      (a * ((c + s) / &2 - &1 / s) + c / s - (&11 / &25) * c pow 2) * h +
      (--a * s - &1 + (&11 / &25) * c * s) * t`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092sb_upper; c1092sps_bottomMinus; c1092sps_scalarB;
                    c1092sps_wallWeight] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092sbm_gap; c1092scs_b] THEN
  ASM_CASES_TAC `&0 <= s * t - c * h` THENL
   [SUBGOAL_THEN `max (s * t - c * h) (&0) = s * t - c * h` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`]; ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= x * z + x + z` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`(&1 + x pow 2) * (&1 + z pow 2)`; `s * t - c * h`] REAL_LE_MUL) THEN
      MP_TAC(SPECL [`&1 - (x * z + x + z)`; `&1 + x + z - x * z`] REAL_LT_MUL) THEN
      REPEAT(ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC]) THEN C1092SBM_LIN_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `x:real`; `z:real`] C1092SB_UPPER_NONNEG) THEN
    ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`s * t - c * h`; `--s / &2 - A`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`(c * (s * t - c * h)) / s`; `s - K`] REAL_LE_MUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN C1092SBM_LIN_TAC; C1092SBM_LIN_TAC];
        C1092SBM_LIN_TAC];
      DISCH_TAC] THEN
    SUBGOAL_THEN
     `--h * ((a * (&3 / &2 + c * (c + s) / &2) - K - &2 * c) / s) - &2 * t +
      (a / &2) * (&1 + t pow 2 + h * t) -
      ((s * t - c * h) * A + (s * h + c * t) * (K - a) - a * (s * t - c * h)) =
      c1092sb_upper a x z + (s * t - c * h) * (--s / &2 - A) +
      ((c * (s * t - c * h)) / s) * (s - K)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        lhs(concl th) = `c1092sb_upper a x z` then REWRITE_TAC[th] else NO_TAC) THEN
      UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `~(s = &0)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    CONJ_TAC THENL [C1092SBM_LIN_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `t = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `h pow 2 + t pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC [];
      ALL_TAC] THEN
    SUBGOAL_THEN `z = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `C1092WPS_half h t = z` THEN ASM_REWRITE_TAC[C1092WPS_half] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `x:real`] C1092SBM_UPPER_ENDPOINT) THEN
    ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN
    C1092SBM_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `max (s * t - c * h) (&0) = &0` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> max x (&0) = &0`]; ALL_TAC] THEN
  SUBGOAL_THEN `x * z + x + z <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`(&1 + x pow 2) * (&1 + z pow 2)`; `--(s * t - c * h)`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`(x * z + x + z) - &1`; `&1 + x + z - x * z`] REAL_LT_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC]) THEN C1092SBM_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `x:real`; `z:real`] C1092SB_LOWER_NONNEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SBM_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`--(s * t - c * h)`; `A - (a - c - s)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= --((c * (s * t - c * h)) / s)` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_ARITH `--((c * d) * i) = (c * --d) * i`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN C1092SBM_LIN_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN C1092SBM_LIN_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`--((c * (s * t - c * h)) / s)`; `K - (a + (&14 / &25) * s - c)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [C1092SBM_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `--h * ((a * (&3 / &2 + c * (c + s) / &2) - K - &2 * c) / s) - &2 * t +
    (a / &2) * (&1 + t pow 2 + h * t) -
    ((s * t - c * h) * A + (s * h + c * t) * (K - a) - a * &0) =
    c1092sps_bottomMinus a x z + --(s * t - c * h) * (A - (a - c - s)) +
    --((c * (s * t - c * h)) / s) * (K - (a + (&14 / &25) * s - c))` SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      lhs(concl th) = `c1092sps_bottomMinus a x z` then REWRITE_TAC[th] else NO_TAC) THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `~(s = &0)` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  CONJ_TAC THENL [C1092SBM_LIN_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `t = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `h pow 2 + t pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN UNDISCH_TAC `~(&0 <= s * t - c * h)` THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  ASM_REAL_ARITH_TAC);;
