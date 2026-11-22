(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/LeftFar.lean                        *)
(* (N12Compact.C1092MMMPLeftFar).  The actual left wall must own G1.         *)
(* Conventions of CP_C1092_MMMP_UpperPoints.ml / CP_C1092_RigidCharts.ml     *)
(* (forward toolkit c1092mo_).  The squares of the Lean proof are explicit   *)
(* tuples: for owners p 8 = (c, s, u, v, a),                                 *)
(*   W = (pullY (pullX q)).translated 2 2 = (c, s, 2c + 2s - u - a,          *)
(*       2c - 2s - v - a, a)                  (C1092MLF_INSIDE_W / CENTER_W), *)
(*   V = centered_frame W (C1092MWC_CENTERED_FRAME),                         *)
(*   B = translate (opposite V) (-1) 0 = (c, s, --u - a + c, --v - a - s, a)  *)
(*       for V = (c, s, u, v, a)                         (C1092MLF_INSIDE_B). *)
(* square_support_bound C1092MPWS_SQUARE_SUPPORT_BOUND (squareRadius is      *)
(* tss_support_radius); MixedWideWall.canonical_profile                      *)
(* C1092MWW_CANONICAL_PROFILE; left_g_cover C1092AC_LEFT_G_COVER;            *)
(* left_origin C1092MO_LEFT_ORIGIN; UpperPoints.northwest_point              *)
(* C1092MUP_NORTHWEST_POINT; p.side_le OO_SIDE_LE.  Tag C1092MLF_.           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_UpperPoints.ml";;
needs "n12/geometry/CP_C1092_MixedWideCrossing.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;
needs "n12/geometry/CP_C1092_MixedWideWall.ml";;

let C1092MLF_LIN = NLIN_TAC ~deg2:false [];;

(* Lean: wide_impossible *)
let C1092MLF_WIDE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s < &0 /\ --s < c /\ &5 / &4 < c - s /\
     linside c s u v a (--(&43 / &500)) (&0) /\ linside c s u v a (&0) (&0) /\
     linside c s u v a (&0) (&39 / &100) /\ ~linside c s u v a (&19 / &100) (&1 / &5) /\
     v + a <= (&2 / &5) * c /\
     (forall x y. linside c s u v a x y ==> --(&1) <= x)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--(&1)`; `&0`; `&1`]
    C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[tss_support_radius; lcx; lcy] THEN
  SUBGOAL_THEN `abs(--(&1) * c + &0 * s) = c /\ abs(-- --(&1) * s + &0 * c) = --s`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN RASM_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) then ALL_TAC else NO_TAC) THEN
  RULE_ASSUM_TAC(fun th -> let t = concl th in
    if is_comb t && fst (strip_comb t) = `linside` then REWRITE_RULE[linside] th else th) THEN
  SUBGOAL_THEN `u + a <= &19 / &100 * c + &1 / &5 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&19 / &100) (&1 / &5)` THEN
    REWRITE_TAC[linside; TAUT `~p ==> false <=> p`] THEN REPEAT CONJ_TAC THEN C1092MLF_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) <= c * u - s * v` ASSUME_TAC THENL [C1092MLF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `c * (u + a) <= c * (&19 / &100 * c + &1 / &5 * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s * (v + a) <= --s * ((&2 / &5) * c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (a - &1) * (c - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c - s < &1 + &19 / &100 * c * c - &1 / &5 * c * s` ASSUME_TAC THENL
   [C1092MLF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL [NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * (&1 - c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c - s < &109 / &100 + (c - s) * (c - s) / &10` ASSUME_TAC THENL
   [C1092MLF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `c - s <= &10 / &7` ASSUME_TAC THENL
   [MP_TAC(SPECL [`c:real`; `--s`] C977CC_NORMAL_BOUNDS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
      ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c - s - &5 / &4) * (&1 - (c - s + &5 / &4) / &10)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092MLF_LIN);;

let C1092MLF_INSIDE_W = prove
 (`forall c s u v a x y.
     linside c s (&2 * c + &2 * s - u - a) (&2 * c - &2 * s - v - a) a x y <=>
     linside c s u v a (&2 - x) (&2 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C1092MLF_CENTER_W = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcy c s (&2 * c + &2 * s - u - a) (&2 * c - &2 * s - v - a) a = &2 - lcy c s u v a`,
  REWRITE_TAC[lcy] THEN CONV_TAC REAL_RING);;
let C1092MLF_INSIDE_B = prove
 (`forall c s u v a x y.
     linside c s (--u - a + c) (--v - a - s) a x y <=> linside c s u v a (&1 - x) (--y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point *)
let C1092MLF_POINT = prove
 (c1092mmpe_stmt 8 "&1" "&12 / &5",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MUP_NORTHWEST_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MPC_CUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MPC_LEFT_TIP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let a8 x y = ASSUME (c1092mo_in 8 x y) in
  let nw = c1092mo_use C1092MMPE_NORTHWEST_PAIR in
  let lcov = CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V C1092AC_LEFT_G_COVER) (c1092mo_hh ())) in
  let o8 = c1092mo_own 8 in
  let insW = SPECL o8 C1092MLF_INSIDE_W and centerW = MATCH_MP (SPECL o8 C1092MLF_CENTER_W) (c1092mo_unit 8) in
  let tW = fst (chop_list 5 (snd (strip_comb (lhs (snd (strip_forall (concl insW))))))) in
  let box8 = REWRITE_RULE[lcont] (c1092mo_box 8) in
  SUBGOAL_THEN (c1092mo_in 8 `&1` `&8 / &5`) ASSUME_TAC THENL
   [MP_TAC lcov THEN ASM_REWRITE_TAC[c1092mo_excl 8 7 (CONJUNCT2 nw)]; ALL_TAC] THEN
  MP_TAC(SPECL tW C1092MWC_CENTERED_FRAME) THEN
  ANTS_TAC THENL [REWRITE_TAC[c1092mo_unit 8; c1092mo_pos ()]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  REWRITE_TAC[insW; centerW] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = l`)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `l:real`] C1092MWW_CANONICAL_PROFILE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092mo_pos (); c1092mo_side (); MP (SPECL C1092MMPE_V OO_SIDE_LE) (ASSUME C1092MO_NP)] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[c1092mo_seed 8 (`&457 / &500`, `&2`);
      c1092mo_excl 8 4 (c1092mo_seed 4 (`&33 / &20`, `&33 / &20`))] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box8) THEN REAL_ARITH_TAC;
      RASM_ARITH_TAC];
    STRIP_TAC] THEN
  MATCH_MP_TAC (SPECL [`c:real`; `s:real`; `--u - l + c`; `--v - l - s`; `l:real`] C1092MLF_WIDE_IMPOSSIBLE) THEN
  REWRITE_TAC[C1092MLF_INSIDE_B] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[c1092mo_seed 8 (`&457 / &500`, `&2`); c1092mo_use C1092MO_LEFT_ORIGIN;
    c1092mo_excl 8 7 (ASSUME (c1092mo_in 7 `&119 / &100` `&11 / &5`)); c1092mo_side (); c1092mo_pos ()] THEN
  CONJ_TAC THENL
   [RASM_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box8) THEN REAL_ARITH_TAC]);;
