(* ========================================================================= *)
(* Port of Compact/Geometry/CentralWallParallelMargin.lean (Jatloe).          *)
(* Continuous scalar margin for the central square's longitudinal axis.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* helper: cancellation of a positive factor *)
let CWPM_NONNEG_OF_MUL = prove
 (`forall x y. &0 < y /\ &0 <= y * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&0`; `x:real`; `y:real`] REAL_LE_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

(* Lean: ordered_dot (private) *)
let CWPM_ORDERED_DOT = prove
 (`forall c s cc ss p q. c977cc_normal c s /\ c977cc_normal cc ss /\
                   &0 <= c * ss - s * cc /\ &0 <= p /\ p <= q
     ==> p * c + q * s <= p * cc + q * ss`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`cc:real`; `ss:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `c977cc_normal x y`) o concl))) THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (c * ss - s * cc) * (c * ss + s * cc)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c * ss - s * cc) * (c * ss + s * cc) = ss * ss - s * s`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `cc * cc + ss * ss = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s <= ss` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < (s - ss) * (s + ss)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c + cc) * (cc + ss - c - s)` ASSUME_TAC THENL
  [SUBGOAL_THEN `(c + cc) * (cc + ss - c - s) = (ss - s) * (c + cc - ss - s)`
   SUBST1_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `cc * cc + ss * ss = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cc + ss - c - s` ASSUME_TAC THENL
  [MATCH_MP_TAC CWPM_NONNEG_OF_MUL THEN EXISTS_TAC `c + cc:real` THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p * (cc + ss - c - s) /\ &0 <= (q - p) * (ss - s)`
  MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: quartic (private definition) *)
let cwpm_quartic = new_definition
 `cwpm_quartic (q:real) =
    -- &72 + (&6873 / &50) * q + (&1471151 / &10000) * q pow 2 -
    (&5027 / &50) * q pow 3 - (&208849 / &10000) * q pow 4`;;

(* Lean: quartic_nonneg (private) *)
let CWPM_QUARTIC_NONNEG = prove
 (`forall q. &5 / &12 <= q /\ q <= &1 ==> &0 <= cwpm_quartic q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= q - &5 / &12 /\ &0 <= &1 - q` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (i,j) ->
    MP_TAC(MATCH_MP REAL_LE_MUL
      (CONJ (SPEC (mk_small_numeral i) (MATCH_MP REAL_POW_LE
               (ASSUME `&0 <= q - &5 / &12`)))
            (SPEC (mk_small_numeral j) (MATCH_MP REAL_POW_LE
               (ASSUME `&0 <= &1 - q`))))))
    [0,4; 1,3; 2,2; 3,1; 4,0] THEN
  REWRITE_TAC[cwpm_quartic] THEN REAL_ARITH_TAC);;

(* Lean: wall_endpoint (private) *)
let CWPM_WALL_ENDPOINT = prove
 (`forall r t. c977cc_normal r t /\ &5 * r <= &12 * t
         ==> &0 <= &7 * r + &17 * t - &11 - (&457 / &100) * (t / r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal r t` THEN REWRITE_TAC[c977cc_normal] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= t - &5 / &12 * r /\ &0 <= r - t` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&11 * r + &457 / &100 * t) pow 2 * (r pow 2 + t pow 2) <=
    (r * (&7 * r + &17 * t)) pow 2` MP_TAC THENL
  [MAP_EVERY (fun (i,j) ->
     MP_TAC(MATCH_MP REAL_LE_MUL
       (CONJ (SPEC (mk_small_numeral i) (MATCH_MP REAL_POW_LE
                (ASSUME `&0 <= t - &5 / &12 * r`)))
             (SPEC (mk_small_numeral j) (MATCH_MP REAL_POW_LE
                (ASSUME `&0 <= r - t`))))))
     [0,4; 1,3; 2,2; 3,1; 4,0] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&11 * r + &457 / &100 * t <= r * (&7 * r + &17 * t)` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= &11 * r + &457 / &100 * t /\ &0 <= r * (&7 * r + &17 * t)`
   MP_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
   UNDISCH_TAC `(&11 * r + &457 / &100 * t) pow 2 <=
                (r * (&7 * r + &17 * t)) pow 2` THEN
   REWRITE_TAC[REAL_POW_2] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
   SPEC_TAC(`&11 * r + &457 / &100 * t`,`A:real`) THEN
   SPEC_TAC(`r * (&7 * r + &17 * t)`,`B:real`) THEN
   REPEAT STRIP_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&7 * r + &17 * t - &11 - (&457 / &100) * (t / r) =
                (r * (&7 * r + &17 * t) - (&11 * r + &457 / &100 * t)) / r`
  SUBST1_TAC THENL
  [UNDISCH_TAC `&7 / &10 <= r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

(* Lean: parallel_margin *)
let CWPM_PARALLEL_MARGIN = prove
 (`forall c s r t. c977cc_normal c s /\ c977cc_normal r t /\
             &12 * s <= &5 * c /\ &0 <= c * t - s * r
     ==> &0 <= &1 + (c - s) * r + (c + s) * t - &2 * c -
               (&457 / &500) * s * (t / r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal r t`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  SUBGOAL_THEN `exists k. t / r = k /\ k * r = t` STRIP_ASSUME_TAC THENL
  [EXISTS_TAC `t / r` THEN REWRITE_TAC[] THEN
   UNDISCH_TAC `&7 / &10 <= r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `r * r + t * t = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c977cc_normal r t` THEN SIMP_TAC[c977cc_normal; REAL_POW_2];
   ALL_TAC] THEN
  ABBREV_TAC `P = &2 - r - t` THEN
  ABBREV_TAC `Q = r - t + (&457 / &500) * k` THEN
  SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL [EXPAND_TAC "P" THEN ASM_REAL_ARITH_TAC;
                                           ALL_TAC] THEN
  SUBGOAL_THEN `r * Q = r * (r - t) + (&457 / &500) * t` ASSUME_TAC THENL
  [EXPAND_TAC "Q" THEN UNDISCH_TAC `k * r = t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `P <= Q` ASSUME_TAC THENL
  [SUBGOAL_THEN `&2 * r * t <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `r - t:real`]; ALL_TAC] THEN
   SUBGOAL_THEN `r * (&1 + r) * (Q - P) =
                 t * ((&457 / &500) * (&1 + r) - &2 * r * t)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN UNDISCH_TAC `r * Q = r * (r - t) + (&457 / &500) * t` THEN
    UNDISCH_TAC `r * r + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= Q - P ==> P <= Q`) THEN
   MATCH_MP_TAC CWPM_NONNEG_OF_MUL THEN EXISTS_TAC `r * (&1 + r)` THEN
   ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `P * c + Q * s <= &1` ASSUME_TAC THENL
  [ASM_CASES_TAC `&12 * t <= &5 * r` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `t:real`; `P:real`; `Q:real`]
      CWPM_ORDERED_DOT) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&12 / &13 <= r` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     SUBGOAL_THEN `&0 <= (&5 * r - &12 * t) * (&5 * r + &12 * t) /\
                   &0 < (&12 / &13 - r) * (&12 / &13 + r)` MP_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     UNDISCH_TAC `r * r + t * t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r * (&1 - P * r - Q * t) =
                  (&1 - r) * (&2 * r - (&457 / &500) * (&1 + r))` ASSUME_TAC THENL
    [EXPAND_TAC "P" THEN UNDISCH_TAC `r * Q = r * (r - t) + (&457 / &500) * t` THEN
     UNDISCH_TAC `r * r + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &1 - P * r - Q * t` MP_TAC THENL
    [MATCH_MP_TAC CWPM_NONNEG_OF_MUL THEN EXISTS_TAC `r:real` THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`c:real`; `s:real`; `&12 / &13`; `&5 / &13`; `P:real`; `Q:real`]
      CWPM_ORDERED_DOT) THEN
    ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`r:real`; `t:real`] CWPM_WALL_ENDPOINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "P" THEN EXPAND_TAC "Q" THEN
    REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `P * c + Q * s <= &1` THEN EXPAND_TAC "P" THEN EXPAND_TAC "Q" THEN
  REAL_ARITH_TAC);;
