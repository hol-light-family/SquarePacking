(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalSignScalars.lean          *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  Both full-angle scalar      *)
(* margins in NEGATIVE-INWARD-SUCCESSOR-SIGN.  Normal: c977cc_normal;        *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA; small_tenth:  *)
(* C1092MIFMG_SMALL_TENTH.                                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalMargins.ml";;

(* Lean: signFirst (definition) *)
let c1092mifsg_signFirst = new_definition
 `c1092mifsg_signFirst (c:real) (s:real) (d:real) (t:real) =
    &1 - c + (&13 / &50) * s + (c * d - s * t) * (&1 - d + (&2 / &5) * t) +
    (c * t + s * d) * (&1 - d - t)`;;

(* Lean: signLast (definition) *)
let c1092mifsg_signLast = new_definition
 `c1092mifsg_signLast (c:real) (s:real) (d:real) (t:real) =
    &1 - d - t + (c * t + s * d) * (&1 - c + (&13 / &50) * s) +
    (c * d - s * t) * (&1 - (&7 / &20) * (c - s))`;;

let C1092MIFSG_LIN_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then RASM_ARITH_TAC g else NLIN_TAC ~deg2:false [] g));;

let C1092MIFSG_MUL_TAC th x y =
  MP_TAC(SPECL [x; y] th) THEN ANTS_TAC THENL [C1092MIFSG_LIN_TAC; DISCH_TAC];;

(* Lean: sign_polynomial_negative (private) *)
let C1092MIFSG_SIGN_POLYNOMIAL_NEGATIVE = prove
 (`forall z. &1 / &10 <= z /\ z <= &5 / &12
       ==> &27569 * z pow 4 - &30600 * z pow 3 + &22458 * z pow 2 - &6600 * z + &169 < &0`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = &27569 * (z pow 2 + (&1 / &10 + &5 / &12) * z + (&1 / &10) pow 2 +
                  (&1 / &10) * (&5 / &12) + (&5 / &12) pow 2) -
                  &30600 * (z + &1 / &10 + &5 / &12) + &22458` THEN
  SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[REAL_POW_2] THEN
    NLIN_TAC [SQ_NONNEG `z - &16356 / &55138`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&5 / &12 - z) * (&27569 * (&1 / &10) pow 4 - &30600 * (&1 / &10) pow 3 +
                      &22458 * (&1 / &10) pow 2 - &6600 * (&1 / &10) + &169) +
    (z - &1 / &10) * (&27569 * (&5 / &12) pow 4 - &30600 * (&5 / &12) pow 3 +
                      &22458 * (&5 / &12) pow 2 - &6600 * (&5 / &12) + &169) -
    (&5 / &12 - &1 / &10) *
      (&27569 * z pow 4 - &30600 * z pow 3 + &22458 * z pow 2 - &6600 * z + &169) =
    (&5 / &12 - &1 / &10) * (z - &1 / &10) * (&5 / &12 - z) * Q` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  C1092MIFSG_MUL_TAC REAL_LE_MUL `z - &1 / &10` `&5 / &12 - z` THEN
  C1092MIFSG_MUL_TAC REAL_LE_MUL `(z - &1 / &10) * (&5 / &12 - z)` `Q:real` THEN
  C1092MIFSG_LIN_TAC);;

(* Lean: sign_first_positive *)
let C1092MIFSG_SIGN_FIRST_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &0 < t
     ==> &0 < c1092mifsg_signFirst c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  ABBREV_TAC `A = &13 / &50 + d - t - &1 + (&3 / &5) * t pow 2` THEN
  ABBREV_TAC `B = &2 - d - t + (&3 / &5) * d * t` THEN
  SUBGOAL_THEN `c1092mifsg_signFirst c s d t = &1 - B * c + A * s` SUBST1_TAC THENL
   [REWRITE_TAC[c1092mifsg_signFirst] THEN MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [C1092MIFSG_LIN_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `C1092WPS_half d t <= &1 / &10` THENL
   [STRIP_TAC THEN
    MP_TAC(SPECL [`d:real`; `t:real`] C1092MIFMG_SMALL_TENTH) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL
     [EXPAND_TAC "A" THEN NLIN_TAC [SQ_NONNEG `t:real`]; ALL_TAC] THEN
    C1092MIFSG_MUL_TAC REAL_LE_MUL `d:real` `t:real` THEN
    SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [EXPAND_TAC "B" THEN C1092MIFSG_LIN_TAC; ALL_TAC] THEN
    C1092MIFSG_MUL_TAC REAL_LE_MUL `&3 / &2 - d - t` `d + t - &1` THEN
    SUBGOAL_THEN `(&4 / &5) * d * t <= d + t - &1` ASSUME_TAC THENL
     [C1092MIFSG_LIN_TAC; ALL_TAC] THEN
    C1092MIFSG_MUL_TAC REAL_LT_MUL `d:real` `t:real` THEN
    SUBGOAL_THEN `B < &1` ASSUME_TAC THENL [EXPAND_TAC "B" THEN C1092MIFSG_LIN_TAC; ALL_TAC] THEN
    C1092MIFSG_MUL_TAC REAL_LE_MUL `B:real` `&1 - c` THEN
    C1092MIFSG_MUL_TAC REAL_LE_MUL `A:real` `s:real` THEN
    C1092MIFSG_LIN_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `z = C1092WPS_half d t` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d = (&1 - z pow 2) / (&1 + z pow 2) /\ t = (&2 * z) / (&1 + z pow 2)`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN CONJ_TAC THEN C1092MIFSG_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z <= &5 / &12` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MIFSG_MUL_TAC REAL_LE_MUL `&1 + z pow 2` `d - t` THEN
    C1092MIFSG_MUL_TAC REAL_LE_MUL `z - &5 / &12` `z + &5 / &12` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MIFSG_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `z:real` C1092MIFSG_SIGN_POLYNOMIAL_NEGATIVE) THEN
  ANTS_TAC THENL [C1092MIFSG_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&2500 * (&1 + z pow 2) pow 2 * (&1 - B pow 2 - A pow 2) =
                --(&27569 * z pow 4 - &30600 * z pow 3 + &22458 * z pow 2 - &6600 * z + &169)`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `d = (&1 - z pow 2) / (&1 + z pow 2)`
      then ONCE_REWRITE_TAC[th] else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if concl th = `t = (&2 * z) / (&1 + z pow 2)`
      then ONCE_REWRITE_TAC[th] else NO_TAC) THEN
    SUBGOAL_THEN `~(&1 + z pow 2 = &0)` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - B pow 2 - A pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&2500 * (&1 + z pow 2) pow 2`; `--(&1 - B pow 2 - A pow 2)`] REAL_LE_MUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
        C1092MIFSG_LIN_TAC];
      DISCH_TAC] THEN
    C1092MIFSG_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(B * c - A * s) pow 2 <= B pow 2 + A pow 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(B * c - A * s) pow 2 + (B * s + A * c) pow 2 = B pow 2 + A pow 2`
      MP_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MP_TAC(SPEC `B * s + A * c` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MIFSG_MUL_TAC REAL_LE_MUL `B * c - A * s - &1` `B * c - A * s + &1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MIFSG_LIN_TAC);;

(* Lean: sign_last_positive *)
let C1092MIFSG_SIGN_LAST_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < c1092mifsg_signLast c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  ABBREV_TAC `P = (&7 / &20) * c * c + (&13 / &20) * c * s - c - (&13 / &50) * s * s - s + &1` THEN
  ABBREV_TAC `Q = c * c - (&61 / &100) * c * s - c + (&7 / &20) * s * s + s + &1` THEN
  SUBGOAL_THEN `c1092mifsg_signLast c s d t = &1 - P * d - Q * t` SUBST1_TAC THENL
   [REWRITE_TAC[c1092mifsg_signLast] THEN MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092MIFSG_MUL_TAC REAL_LE_MUL `c - s` `(&13 / &20) * c - (&61 / &100) * s` THEN
  SUBGOAL_THEN `P <= Q` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN C1092MIFSG_LIN_TAC; ALL_TAC] THEN
  C1092MIFSG_MUL_TAC REAL_LE_MUL `c - &7 / &10` `&1 - c` THEN
  SUBGOAL_THEN `&1 - c <= (&10 / &17) * s * s` ASSUME_TAC THENL
   [C1092MIFSG_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * s <= &1 / &2` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `P + Q <= &137 / &100` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Q"] THEN NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  C1092MIFSG_MUL_TAC REAL_LE_MUL `Q - P` `d - t` THEN
  C1092MIFSG_MUL_TAC REAL_LE_MUL `&137 / &100 - (P + Q)` `d + t` THEN
  C1092MIFSG_LIN_TAC);;
