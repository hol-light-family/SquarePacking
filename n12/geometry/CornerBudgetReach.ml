(* ========================================================================= *)
(* Port of Compact/Geometry/CornerBudgetReach.lean (Jatloe N12).              *)
(* Two foreign auxiliary points force outward reach by a corner owner.       *)
(* positive_frame: CLF_POSITIVE_FRAME; positive_frame_wall_bounds:           *)
(* C977WC_POSITIVE_FRAME_WALL_BOUNDS; container_pullY: LCONT_PULLY;          *)
(* inside_pullY: LINSIDE_PULLY.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/C977WallChains.ml";;

let CBR_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* Lean: normal_margin (private) *)
let CBR_NORMAL_MARGIN = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> &1 + (&4 / &5) * c * s <= c + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c + s - &1`; SQ_NONNEG `c - s`; SQ_NONNEG `c + s - &3 / &2`]
   [`&1 <= c + s`; `c + s <= &3 / &2`] THEN
  SUBGOAL_THEN `&0 <= (c + s - &1) * ((&3 / &5) - (&2 / &5) * (c + s))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: positive (private) *)
let CBR_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y) /\
     linside c s u v a (&1) (&457 / &500) /\
     linside c s u v a (&457 / &500) (&1) /\
     ~linside c s u v a (&8 / &5) (&1) /\
     ~linside c s u v a (&1) (&8 / &5)
     ==> linside c s u v a (&4 / &5) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; lcy] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CBR_NORMAL_MARGIN) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_2] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c:real`; SQ_NONNEG `c - s`;
                  SQ_NONNEG `c + s - &3 / &2`]
   [`c <= &1`; `s <= &1`; `c + s <= &3 / &2`] THEN
  SUBGOAL_THEN `&0 < (a - &1) * (c + s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  REWRITE_TAC[linside] THEN
  ASM_CASES_TAC `u + a <= (&8 / &5) * c + s` THENL
   [ALL_TAC;
    SUBGOAL_THEN `c - (&8 / &5) * s <= v /\ u + a <= c + (&8 / &5) * s`
      STRIP_ASSUME_TAC THENL [CBR_ARITH_TAC; ALL_TAC] THEN
    CBR_ARITH_TAC] THEN
  SUBGOAL_THEN `u < (&4 / &5) * c + s` ASSUME_TAC THENL
   [CBR_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY CBR_ARITH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= s * (((&8 / &5) * c + s) - (u + a)) /\
                &0 <= c * (--s * &4 / &5 + c * &1 - (v + a))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: first_quadrant *)
let CBR_FIRST_QUADRANT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y) /\
     linside c s u v a (&1) (&457 / &500) /\
     linside c s u v a (&457 / &500) (&1) /\
     ~linside c s u v a (&8 / &5) (&1) /\
     ~linside c s u v a (&1) (&8 / &5)
     ==> linside c s u v a (&4 / &5) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a' (&4 / &5) (&1)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC CBR_POSITIVE THEN ASM_REWRITE_TAC[]);;

(* Lean: upper_left *)
let CBR_UPPER_LEFT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&1) (&1543 / &500) /\
     linside c s u v a (&457 / &500) (&3) /\
     ~linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&1) (&12 / &5)
     ==> linside c s u v a (&4 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&4 / &5`; `&1`]
    LINSIDE_PULLY) THEN
  CONV_TAC(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CBR_FIRST_QUADRANT THEN
  REWRITE_TAC[LINSIDE_PULLY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LCONT_PULLY) THEN
  REWRITE_TAC[lcont; LINSIDE_PULLY] THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
