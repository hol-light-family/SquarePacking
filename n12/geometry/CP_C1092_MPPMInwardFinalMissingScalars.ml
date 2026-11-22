(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalMissingScalars.lean        *)
(* (N12Compact.C1092MPPMInwardFinal).  The full missing-center predecessor  *)
(* scalar margin.  Normal is c977cc_normal; half / quarter_data are          *)
(* C1092WPS_half / C1092WPS_QUARTER_DATA; f, g, fg_bounds, g_lower are       *)
(* c1092mifs_f, c1092mifs_g, C1092MIFS_FG_BOUNDS, C1092MIFS_G_LOWER.  The    *)
(* local polynomial P (with G = 104/289) is written out.  Tag C1092MIFM_.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalFloor.ml";;

let C1092MIFM_POS_CANCEL = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

(* Lean: missing_predecessor_margin *)
let C1092MIFM_MISSING_PREDECESSOR_MARGIN = prove
 (`forall c s b r. c977cc_normal c s /\ c977cc_normal b r /\
     &17 / &20 < c /\ s < &13 / &25 /\ &1 / &10 <= C1092WPS_half c s /\ &8 / &17 <= r
     ==> c * (c * c1092mifs_f b r - s * c1092mifs_g b r) <
         c - &1 + s * (&1 - c + (&13 / &50) * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MIFS_FG_BOUNDS) THEN
  MP_TAC(SPECL [`b:real`; `r:real`] C1092MIFS_G_LOWER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if free_in `C1092WPS_half c s` (concl th) then MP_TAC th else NO_TAC)) THEN
  SPEC_TAC(`C1092WPS_half c s`,`x:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x <= &3 / &10` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (x - &3 / &10) * (&1 + c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s - (&2 / &11) * c` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (x - &1 / &10) * (&1 + c)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x pow 2 <= &9 / &100 /\ &0 <= x pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `&0 <= (&3 / &10 - x) * (&3 / &10 + x)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x pow 3 <= &27 / &1000` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&3 / &10 - x) * x pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `x pow 2 <= &9 / &100` THEN
    REWRITE_TAC[REAL_ARITH `x pow 3 = x * x pow 2`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `G = &104 / &289` THEN
  SUBGOAL_THEN `&0 < (--(&22) - &2 * G) * (x pow 3 + x pow 2 / &10 + x / &100 + &1 / &1000) +
      (&44 - &22 * G) * (x pow 2 + x / &10 + &1 / &100) +
      (--(&264) / &25 + &4 * G) * (x + &1 / &10) + &22 * G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (--(&22) - &2 * G) * x pow 4 + (&44 - &22 * G) * x pow 3 +
      (--(&264) / &25 + &4 * G) * x pow 2 + &22 * G * x - &2 * G` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (x - &1 / &10) *
      ((--(&22) - &2 * G) * (x pow 3 + x pow 2 / &10 + x / &100 + &1 / &1000) +
       (&44 - &22 * G) * (x pow 2 + x / &10 + &1 / &100) +
       (--(&264) / &25 + &4 * G) * (x + &1 / &10) + &22 * G)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "G" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&11 * (&1 + x pow 2) pow 2) *
      ((c - &1 + s * (&1 - c + (&13 / &50) * s)) + c * (s - (&2 / &11) * c) * G) =
      (--(&22) - &2 * G) * x pow 4 + (&44 - &22 * G) * x pow 3 +
      (--(&264) / &25 + &4 * G) * x pow 2 + &22 * G * x - &2 * G` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c - &1 + s * (&1 - c + (&13 / &50) * s)) + c * (s - (&2 / &11) * c) * G`
  ASSUME_TAC THENL
   [MATCH_MP_TAC C1092MIFM_POS_CANCEL THEN EXISTS_TAC `&11 * (&1 + x pow 2) pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * c1092mifs_f b r <= c * ((&2 / &11) * c1092mifs_g b r) /\
                &0 <= (s - (&2 / &11) * c) * (c1092mifs_g b r - G)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN EXPAND_TAC "G" THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * (--(s - (&2 / &11) * c) * G -
                          (c * c1092mifs_f b r - s * c1092mifs_g b r))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
