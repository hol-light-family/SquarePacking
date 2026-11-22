(* ========================================================================= *)
(* Port of Compact/Geometry/C977CornerSectorBounds.lean (Jatloe, N12-jatloe) *)
(* (namespace N12Compact.C977CornerSectorBounds).                            *)
(* Early continuous angle comparisons in the corner coupling: exact chord    *)
(* identities in the sine coordinate, no trigonometry.                       *)
(* Note: Lean variable T is renamed TT (T is truth in HOL).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Adds the unfolded Normal facts and C977CC_NORMAL_BOUNDS for every         *)
(* c977cc_normal assumption (the assumptions themselves are kept).           *)
let C977CSB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C977CSB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let C977CSB_BOUNDARY_MUL = prove
 (`forall c t. ~(c = &0) ==> c * c977cc_boundary c t = c + c * t + t * (&1 - t)`,
  REWRITE_TAC[c977cc_boundary] THEN CONV_TAC REAL_FIELD);;

(* Lean: dot_le_one *)
let C977CSB_DOT_LE_ONE = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT ==> c * C + t * TT <= &1`,
  REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  NLIN_TAC [SQ_NONNEG `c - C:real`; SQ_NONNEG `t - TT:real`]);;

(* Lean: cosine_order *)
let C977CSB_COSINE_ORDER = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ TT <= t ==> c <= C`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN NLIN_TAC []);;

(* Lean: sine_order *)
let C977CSB_SINE_ORDER = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ c * TT - t * C <= &0
             ==> TT <= t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `C <= c` ASSUME_TAC THENL
  [MATCH_MP_TAC C977CSB_COSINE_ORDER THEN
   MAP_EVERY EXISTS_TAC [`TT:real`; `t:real`] THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C977CSB_NORMAL_TAC THEN NLIN_TAC []);;

(* Lean: linear_arc_max *)
let C977CSB_LINEAR_ARC_MAX = prove
 (`forall c t C TT a b. c977cc_normal c t /\ c977cc_normal C TT /\ TT <= t /\
                 &0 <= a /\ a * t <= b * c
                 ==> a * C + b * TT <= a * c + b * t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `TT:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * ((a * c + b * t) - (a * C + b * TT)) =
                a * (&1 - (c * C + t * TT)) + (b * c - a * t) * (t - TT)`
  SUBST1_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: boundary_parallel *)
let C977CSB_BOUNDARY_PARALLEL = prove
 (`forall c t. c977cc_normal c t ==> &2 * (c + t) - &1 <= c977cc_boundary c t`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C977CSB_BOUNDARY_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 - c`; `t - (&1 - c)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN NLIN_TAC []);;

(* Lean: boundary_horizontal *)
let C977CSB_BOUNDARY_HORIZONTAL = prove
 (`forall c t. c977cc_normal c t ==> c + (&87 / &50) * t <= c977cc_boundary c t`,
  REPEAT STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C977CSB_BOUNDARY_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c + t - &1`; `&10 / &7 - (c + t)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= c + t - &1 - (&37 / &50) * c * t`] THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN NLIN_TAC []);;

(* Lean: arc_chord *)
let C977CSB_ARC_CHORD = prove
 (`forall c t C TT k. c977cc_normal c t /\ c977cc_normal C TT /\ TT <= t /\ &0 <= k
     ==> (t - TT) * c + TT * (&1 - k * t) <= t * ((&1 - k * TT) * (c * C + t * TT))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `TT:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `TT:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= t * (C - &1) + TT * (&1 - c)` ASSUME_TAC THENL
  [MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `(&1 + c) * (&1 + C)` THEN
   CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `((&1 + c) * (&1 + C)) * ((t * (C - &1) + TT * (&1 - c)) - &0) =
                 (t * TT) * ((t - TT) * (&1 + C) + TT * (C - c))` SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN
    UNDISCH_TAC `C pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * ((&1 - k * TT) * (c * C + t * TT)) - ((t - TT) * c + TT * (&1 - k * t)) =
                c * (t * (C - &1) + TT * (&1 - c)) + ((k * t) * TT) * (&1 - (c * C + t * TT))`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * (t * (C - &1) + TT * (&1 - c)) +
                ((k * t) * TT) * (&1 - (c * C + t * TT))` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
   REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  UNDISCH_TAC `t * ((&1 - k * TT) * (c * C + t * TT)) - ((t - TT) * c + TT * (&1 - k * t)) =
                c * (t * (C - &1) + TT * (&1 - c)) + ((k * t) * TT) * (&1 - (c * C + t * TT))` THEN
  REAL_ARITH_TAC);;

(* Lean: o_axis_below *)
let C977CSB_O_AXIS_BELOW = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ TT <= t
     ==> c * (&2 + (&13 / &50) * C * TT - C) +
         t * (&87 / &50 + (&13 / &50) * TT pow 2 - TT) <= c977cc_boundary c t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `TT:real`; `&13 / &50`]
    C977CSB_ARC_CHORD) THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C977CSB_BOUNDARY_HORIZONTAL) THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C977CSB_BOUNDARY_PARALLEL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
  [SUBGOAL_THEN `TT = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN
   REWRITE_TAC[c977cc_boundary] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
   REWRITE_TAC[REAL_MUL_LZERO; real_div; REAL_ADD_RID] THEN NLIN_TAC [];
   ALL_TAC] THEN
  MP_TAC(SPECL [`t - TT`; `c977cc_boundary c t - (c + &87 / &50 * t)`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`TT:real`; `c977cc_boundary c t - (&2 * (c + t) - &1)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `t:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []);;

(* Lean: a_axis_below *)
let C977CSB_A_AXIS_BELOW = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ TT <= t
     ==> &2 * (C + TT) <= (TT / c) * (c - t) + (c * C + t * TT) * (&1 + t / c) + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `TT:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (((TT / c) * (c - t) + (c * C + t * TT) * (&1 + t / c) + &1) -
                     &2 * (C + TT)) =
                TT * (c - t) + (c * C + t * TT) * (c + t) + c - &2 * c * (C + TT)`
  SUBST1_TAC THENL
  [SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 - c`; `t - (&1 - c)`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`&2 - c - t`; `&1 - (c * C + t * TT)`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`c - t`; `t - TT`] REAL_LE_MUL) THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
  SUBGOAL_THEN `TT * (c - t) + (c * C + t * TT) * (c + t) + c - &2 * c * (C + TT) =
                (&1 - c) * (t - (&1 - c)) + (&2 - c - t) * (&1 - (c * C + t * TT)) +
                (c - t) * (t - TT)` SUBST1_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: a_axis_above *)
let C977CSB_A_AXIS_ABOVE = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ t <= TT
     ==> &2 * (C + TT) <= (TT / c) * (c - t + &1) + (c * C + t * TT) + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `TT:real`; `c:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (((TT / c) * (c - t + &1) + (c * C + t * TT) + &1) - &2 * (C + TT)) =
                TT * (c - t + &1) + c * (c * C + t * TT) + c - &2 * c * (C + TT)`
  SUBST1_TAC THENL
  [SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 - c`; `c * (&1 - C) + TT * (&1 - t)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_TAC []);;
