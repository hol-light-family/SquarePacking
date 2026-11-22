(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallRightMargin.lean                *)
(* (N12Compact.C1092ShortWallRightMargin).  The ordered narrow right-wall    *)
(* margin by a concave chord over 0 <= t <= s.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortWallScalars.ml";;

let C1092SWRM_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SWRM_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWRM_LIN_TAC; DISCH_TAC];;

(* Lean: X *)
let C1092SWRM_X = new_definition
 `C1092SWRM_X (c:real) (s:real) =
    &2 + s pow 2 / &2 - c * s - s * C1092SWS_allowance c s`;;

(* Lean: Y *)
let C1092SWRM_Y = new_definition
 `C1092SWRM_Y (c:real) (s:real) =
    &3 - s pow 2 - c * s / &2 + c * C1092SWS_allowance c s`;;

let C1092SWRM_Q = new_definition
 `C1092SWRM_Q (s:real) (z:real) =
    (&9 / &25) * s pow 3 + ((&12 / &25) * s - (&12 / &25) * s pow 2) * z -
    (&17 / &40) * z pow 2`;;

(* Lean: ordered *)
let C1092SWRM_ORDERED = prove
 (`forall c s r t. c977cc_normal c s /\ c977cc_normal r t /\ &4 * s <= c /\ t <= s
             ==> &0 <= r pow 2 * C1092SWRM_X c s + r * t * (C1092SWRM_Y c s - &2) +
                       r * ((c * r + s * t) - (c * t - s * r) + &1) +
                       (&1543 / &500) * t pow 2 - &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_NARROW_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_ALLOWANCE_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SWS_CUBIC_BASELINE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:real`; `t:real`] C1092SWS_NARROW_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SWRM_LIN_TAC; STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else failwith "no")) THEN
  ABBREV_TAC `A = C1092SWS_allowance c s` THEN
  SUBGOAL_THEN `&0 <= s pow 3 /\ &0 <= t pow 2 /\ &0 <= s pow 2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN C1092SWRM_LIN_TAC; ALL_TAC] THEN
  C1092SWRM_LE_MUL_TAC `r - &24 / &25` `r + &24 / &25` THEN
  SUBGOAL_THEN `&9 / &10 <= r pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN C1092SWRM_LIN_TAC; ALL_TAC] THEN
  ABBREV_TAC `M0 = s pow 2 / &2 - (&1 - c) * (&1 - s) - s * A` THEN
  ABBREV_TAC `B = &1 - c + s - s pow 2 - c * s / &2 + c * A` THEN
  C1092SWRM_LE_MUL_TAC `r pow 2` `M0 - (&2 / &5) * s pow 3` THEN
  C1092SWRM_LE_MUL_TAC `s pow 3` `(&2 / &5) * r pow 2 - &9 / &25` THEN
  SUBGOAL_THEN `B - (s / &2 - s pow 2 / &2) =
                (&1 - c) pow 2 / &2 + s * (&1 - c) / &2 + c * A` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - c) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]; ALL_TAC] THEN
  C1092SWRM_LE_MUL_TAC `s:real` `&1 - c` THEN
  C1092SWRM_LE_MUL_TAC `c:real` `A:real` THEN
  C1092SWRM_LE_MUL_TAC `s:real` `&1 - s` THEN
  C1092SWRM_LE_MUL_TAC `r:real` `B - (s / &2 - s pow 2 / &2)` THEN
  C1092SWRM_LE_MUL_TAC `r - &24 / &25` `s / &2 - s pow 2 / &2` THEN
  C1092SWRM_LE_MUL_TAC `t:real` `r * B - ((&12 / &25) * s - (&12 / &25) * s pow 2)` THEN
  SUBGOAL_THEN
   `r pow 2 * C1092SWRM_X c s + r * t * (C1092SWRM_Y c s - &2) +
    r * ((c * r + s * t) - (c * t - s * r) + &1) + (&1543 / &500) * t pow 2 - &4 =
    r pow 2 * M0 + r * t * B - (&1 - r) + (&43 / &500) * t pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[C1092SWRM_X; C1092SWRM_Y] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["M0"; "B"] THEN
    UNDISCH_TAC `r pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  (* Q t <= target and 0 <= Q t *)
  SUBGOAL_THEN `&0 <= C1092SWRM_Q s t` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= C1092SWRM_Q s (&0) /\ &0 <= C1092SWRM_Q s s` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[C1092SWRM_Q] THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_RZERO; REAL_POW_ZERO; ARITH] THEN C1092SWRM_LIN_TAC;
        C1092SWRM_LE_MUL_TAC `s pow 2` `&11 / &200 - (&3 / &25) * s` THEN
        C1092SWRM_LIN_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `s = &0` THENL
     [SUBGOAL_THEN `t = &0` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN C1092SWRM_LIN_TAC;
        FIRST_X_ASSUM(SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
     [UNDISCH_TAC `~(s = &0)` THEN UNDISCH_TAC `&0 <= s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092SWRM_LE_MUL_TAC `s - t` `C1092SWRM_Q s (&0)` THEN
    C1092SWRM_LE_MUL_TAC `t:real` `C1092SWRM_Q s s` THEN
    C1092SWRM_LE_MUL_TAC `s:real` `t:real` THEN
    C1092SWRM_LE_MUL_TAC `s * t` `s - t` THEN
    SUBGOAL_THEN `s * C1092SWRM_Q s t =
                  (s - t) * C1092SWRM_Q s (&0) + t * C1092SWRM_Q s s +
                  (&17 / &40) * (s * t) * (s - t)` ASSUME_TAC THENL
     [REWRITE_TAC[C1092SWRM_Q] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MP_TAC(SPECL [`&0`; `C1092SWRM_Q s t`; `s:real`] REAL_LE_LMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    C1092SWRM_LIN_TAC;
    ALL_TAC] THEN
  C1092SWRM_LE_MUL_TAC `t pow 2` `&17 / &40 - &25 / &49 + &43 / &500` THEN
  UNDISCH_TAC `&0 <= C1092SWRM_Q s t` THEN REWRITE_TAC[C1092SWRM_Q] THEN
  DISCH_TAC THEN C1092SWRM_LIN_TAC);;
