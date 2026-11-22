(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortWallPenalty.lean                    *)
(* (N12Compact.C1092ShortWallPenalty).  The sharp top-wall penalty over the  *)
(* full first-quadrant wall arc.                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092SWP_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092SWP_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092SWP_LIN_TAC; DISCH_TAC];;

(* Lean: lower_arc (private) *)
let C1092SWP_LOWER_ARC = prove
 (`forall c s r t A B L.
     &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
     &0 <= r /\ &0 <= t /\ r pow 2 + t pow 2 = &1 /\
     c * t - s * r <= &0 /\ &0 <= L /\
     L <= A /\ L <= A * c + B * s
     ==> L <= A * r + B * t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `c = &1` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN C1092SWP_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r = &1` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    C1092SWP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [UNDISCH_TAC `~(s = &0)` THEN UNDISCH_TAC `&0 <= s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092SWP_LE_MUL_TAC `s:real` `r:real` THEN C1092SWP_LE_MUL_TAC `c:real` `t:real` THEN
  C1092SWP_LE_MUL_TAC `s * r - c * t` `s * r + c * t` THEN
  SUBGOAL_THEN `(s * r) * (s * r) - (c * t) * (c * t) = s * s - t * t` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `r * r + t * t = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `t <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (t - s) * (t + s)`] THEN C1092SWP_LIN_TAC;
    ALL_TAC] THEN
  C1092SWP_LE_MUL_TAC `s:real` `t:real` THEN
  C1092SWP_LE_MUL_TAC `s * t` `s * (&1 + r) - t * (&1 + c)` THEN
  SUBGOAL_THEN `(&1 + c) * (&1 + r) * (s * (r - &1) + (&1 - c) * t) =
                s * t * (s * (&1 + r) - t * (&1 + c))` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `r * r + t * t = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s * (r - &1) + (&1 - c) * t` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `s * (r - &1) + (&1 - c) * t`; `(&1 + c) * (&1 + r)`]
      REAL_LE_LMUL_EQ) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C1092SWP_LIN_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
      C1092SWP_LIN_TAC];
    ALL_TAC] THEN
  C1092SWP_LE_MUL_TAC `s * r - c * t` `A - L` THEN
  C1092SWP_LE_MUL_TAC `t:real` `A * c + B * s - L` THEN
  C1092SWP_LE_MUL_TAC `L:real` `s * (r - &1) + (&1 - c) * t` THEN
  SUBGOAL_THEN `&0 <= s * (A * r + B * t - L)` ASSUME_TAC THENL
   [C1092SWP_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&0`; `A * r + B * t - L`; `s:real`] REAL_LE_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_TAC THEN C1092SWP_LIN_TAC);;

(* Lean: penalty *)
let C1092SWP_PENALTY = prove
 (`forall c s r t. c977cc_normal c s /\ &0 <= r /\ &0 <= t /\ r pow 2 + t pow 2 = &1
             ==> &1 + c pow 2 + c * s <=
                 &2 * c * r + c * t + s * t + abs(c * t - s * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C1092SWP_LE_MUL_TAC `c:real` `s:real` THEN
  C1092SWP_LE_MUL_TAC `&1 - c` `c + s - &1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `&0 <= &1 + c * c + c * s /\ &1 + c * c + c * s <= &2 * c + s`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  ASM_CASES_TAC `c * t - s * r <= &0` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `t:real`; `&2 * c + s`; `s:real`;
                  `&1 + c * c + c * s`] C1092SWP_LOWER_ARC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN
      TRY(FIRST_ASSUM ACCEPT_TAC) THEN C1092SWP_LIN_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN `abs(c * t - s * r) = --(c * t - s * r)` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; C1092SWP_LIN_TAC];
    MP_TAC(SPECL [`s:real`; `c:real`; `t:real`; `r:real`; `&2 * c + s`; `&2 * c - s`;
                  `&1 + c * c + c * s`] C1092SWP_LOWER_ARC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN
      TRY C1092SWP_LIN_TAC THEN
      UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `r * r + t * t = &1` THEN
      REAL_ARITH_TAC;
      DISCH_TAC] THEN
    SUBGOAL_THEN `abs(c * t - s * r) = c * t - s * r` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; C1092SWP_LIN_TAC]]);;
