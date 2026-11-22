(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShallowLeftMargin.lean                   *)
(* (N12Compact.C1092ShallowLeftMargin).  The coupled left-wall margin with   *)
(* the same A and K as the bottom envelope.  cosH / sinH / scalarB /         *)
(* relSin / relCos / wallWeight / leftPlus / leftMinus: c1092sps_*;          *)
(* b: c1092scs_b; Normal: c977cc_normal; half / quarter_data:                *)
(* C1092WPS_half / C1092WPS_QUARTER_DATA.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShallowCentralScalars.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: gamma (definition) *)
let c1092slm_gamma = new_definition
 `c1092slm_gamma a c s A r d =
    d / s * (a * (&3 / &2 + c * (c + s) / &2) - &2 * c -
             (r + (c * r - s * d) * A - a * max (c * r - s * d) (&0)) / (c * d + s * r)) -
    r + (a / &2) * (&1 + r pow 2 + r * d)`;;

let C1092SLM_LIN_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then RASM_ARITH_TAC g else NLIN_TAC ~deg2:false [] g));;

(* Lean: margin *)
let C1092SLM_MARGIN = prove
 (`forall a c s A K r d x.
     &1 < a /\ &0 < x /\ x <= &1 / &4 /\ c = c1092sps_cosH x /\ s = c1092sps_sinH x /\
     c977cc_normal c s /\ c977cc_normal d r /\
     a - c - s <= A /\ A <= --s / &2 /\
     --(c * r - s * d) * A + (c * d + s * r) * K + a * max (c * r - s * d) (&0) < r
     ==> &0 < (--(c * r - s * d) * A + (c * d + s * r) * K + a * max (c * r - s * d) (&0)) -
              (&2 * r - d * c1092scs_b a c s K - (a / &2) * (&1 + r pow 2 + r * d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check ((=) `c = c1092sps_cosH x` o concl)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check ((=) `s = c1092sps_sinH x` o concl)) THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_COS_POS) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_SIN_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real` C1092SCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN DISCH_TAC THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [C1092SLM_LIN_TAC; ALL_TAC] THEN
  ABBREV_TAC `z = C1092WPS_half d r` THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1092sps_cosH z = d /\ c1092sps_sinH z = r` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN CONJ_TAC THEN C1092SLM_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z < &1` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[C1092WPS_half] THEN
    SUBGOAL_THEN `&0 < &1 + d` ASSUME_TAC THENL [C1092SLM_LIN_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN C1092SLM_LIN_TAC;
    ALL_TAC] THEN
  (* tau factor *)
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SPS_RELATIVE_SIN_FACTOR) THEN
  REWRITE_TAC[c1092sps_relSin] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `tau = c * r - s * d` THEN ABBREV_TAC `k = c * d + s * r` THEN
  ABBREV_TAC `M = max tau (&0)` THEN
  SUBGOAL_THEN `&0 < (&1 + x pow 2) * (&1 + z pow 2) /\ &0 < &2 * (&1 + x * z)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`x:real`; `z:real`] REAL_LE_MUL) THEN
      ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC] THEN C1092SLM_LIN_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau * ((&1 + x pow 2) * (&1 + z pow 2)) = &2 * (z - x) * (&1 + x * z)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `tau:real`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `tau:real`)) THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MP_TAC(SPECL [`c:real`; `d:real`] REAL_LT_MUL) THEN
    MP_TAC(SPECL [`s:real`; `r:real`] REAL_LE_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC]) THEN C1092SLM_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k pow 2 + tau pow 2 = &1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["k"; "tau"] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `k <= &1` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `tau:real`];
    ALL_TAC] THEN
  SUBGOAL_THEN `k - d / s < &0` ASSUME_TAC THENL
   [SUBGOAL_THEN `k * s < d` MP_TAC THENL
     [MP_TAC(SPECL [`s:real`; `k:real`; `&1`] REAL_LE_LMUL) THEN
      ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC] THEN C1092SLM_LIN_TAC;
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `K < (r + tau * A - a * M) / k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN C1092SLM_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`--(k - d / s)`; `--(K - (r + tau * A - a * M) / k)`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `~(s = &0) /\ ~(k = &0)` STRIP_ASSUME_TAC THENL [C1092SLM_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `((--tau * A + k * K + a * M) - (&2 * r - d * c1092scs_b a c s K - (a / &2) * (&1 + r pow 2 + r * d))) -
    c1092slm_gamma a c s A r d =
    (k - d / s) * (K - (r + tau * A - a * M) / k)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092slm_gamma; c1092scs_b] THEN
    UNDISCH_TAC `~(s = &0)` THEN UNDISCH_TAC `~(k = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c1092slm_gamma a c s A r d` ASSUME_TAC THENL
   [ALL_TAC; C1092SLM_LIN_TAC] THEN
  SUBGOAL_THEN
   `forall A0. c1092slm_gamma a c s A r d =
         c1092slm_gamma a c s A0 r d + (--((d * tau) / (s * k))) * (A - A0)`
    ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[c1092slm_gamma] THEN
    UNDISCH_TAC `~(s = &0)` THEN UNDISCH_TAC `~(k = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= tau` THENL
   [SUBGOAL_THEN `x <= z` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`&2 * (&1 + x * z)`; `x - z`] REAL_LT_MUL) THEN
      MP_TAC(SPECL [`tau:real`; `(&1 + x pow 2) * (&1 + z pow 2)`] REAL_LE_MUL) THEN
      REPEAT(ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC]) THEN C1092SLM_LIN_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `x:real`; `z:real`] C1092SPS_LEFT_PLUS_POS) THEN
    ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `c1092slm_gamma a c s (--s / &2) r d = c1092sps_leftPlus a x z` ASSUME_TAC THENL
     [SUBGOAL_THEN `(M:real) = tau` ASSUME_TAC THENL
       [EXPAND_TAC "M" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> max x (&0) = x`) THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[c1092slm_gamma; c1092sps_leftPlus; c1092sps_scalarB; c1092sps_relSin;
        c1092sps_relCos; c1092sps_wallWeight] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (d * tau) / (s * k)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN C1092SLM_LIN_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN C1092SLM_LIN_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`(d * tau) / (s * k)`; `--s / &2 - A`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `c1092slm_gamma`)) (concl th)
      then ONCE_REWRITE_TAC[SPEC `--s / &2` th] else NO_TAC) THEN
    C1092SLM_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z <= x` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&2 * (&1 + x * z)`; `z - x`] REAL_LT_MUL) THEN
    MP_TAC(SPECL [`--tau`; `(&1 + x pow 2) * (&1 + z pow 2)`] REAL_LE_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC]) THEN C1092SLM_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `x:real`; `z:real`] C1092SPS_LEFT_MINUS_POS) THEN
  ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c1092slm_gamma a c s (a - c - s) r d = c1092sps_leftMinus a x z` ASSUME_TAC THENL
   [SUBGOAL_THEN `M = &0` ASSUME_TAC THENL
     [EXPAND_TAC "M" THEN MATCH_MP_TAC(REAL_ARITH `~(&0 <= x) ==> max x (&0) = &0`) THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[c1092slm_gamma; c1092sps_leftMinus; c1092sps_scalarB; c1092sps_relSin;
      c1092sps_relCos; c1092sps_wallWeight] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d * tau) / (s * k) <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= (d * --tau) * i ==> (d * tau) * i <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN C1092SLM_LIN_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN C1092SLM_LIN_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`--((d * tau) / (s * k))`; `A - (a - c - s)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [C1092SLM_LIN_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
    can (find_term ((=) `c1092slm_gamma`)) (concl th)
    then ONCE_REWRITE_TAC[SPEC `a - c - s` th] else NO_TAC) THEN
  C1092SLM_LIN_TAC);;
