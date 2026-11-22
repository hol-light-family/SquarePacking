(* ========================================================================= *)
(* Port of Compact/Geometry/CornerInwardPoint.lean                           *)
(*                                                                           *)
(* InsideContainer is lcont; pullY q = (c, --s, u - 4s, 4c - v - a, a).      *)
(* closed_pullY (private in Lean) is LCLOSED_PULLY of p2_base.               *)
(* S12.positive_frame_wall_bounds is C977WC_POSITIVE_FRAME_WALL_BOUNDS.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977WallChains.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: transverse_upper (private) *)
let CIP_TRANSVERSE_UPPER = prove
 (`forall a c s u v. &1 <= a /\ a <= &1001 / &1000 /\ &0 <= c /\ &0 <= s /\
     c pow 2 + s pow 2 = &1 /\ &0 <= s * u + c * v /\
     u <= (&457 / &500) * c + s /\ --(&457 / &500) * s + c <= v + a
     ==> a * (c - s) <= v + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `c / &20 <= s` THENL
   [NLIN_TAC []; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 < c`; `c <= &1`; `&0 <= a * c`; `&0 <= (a * c) * (&1 - c)`;
                     `&0 <= (a - &457 / &500) * c - s`;
                     `&0 <= s * ((a - &457 / &500) * c - s)`] THEN
  NLIN_TAC []);;

(* Lean: in_frame (private) *)
let CIP_IN_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 <= c /\ &0 <= s /\
     &1 <= a /\ a <= &1001 / &1000 /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y) /\
     lclosed c s u v a (&1) (&457 / &500) /\
     lclosed c s u v a (&457 / &500) (&1)
     ==> lclosed c s u v a a a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx; lcy] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c * u - s * (v + a) /\ &0 <= s * u + c * v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u * (c * c + s * s) = u` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed]) THEN REWRITE_TAC[lclosed] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c:real`; SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]
    [`c <= &1`; `s <= &1`; `a * c * s <= u`; `&0 <= (&1 - c) * (&1 - s)`;
     `c * a + s * a <= u + a`; `u <= c * a + s * a`] THEN
  MP_TAC(SPECL [`a:real`; `c:real`; `s:real`; `u:real`; `v:real`] CIP_TRANSVERSE_UPPER) THEN
  MP_TAC(SPECL [`a:real`; `s:real`; `c:real`; `u:real`; `--v - a:real`] CIP_TRANSVERSE_UPPER) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: first_quadrant *)
let CIP_FIRST_QUADRANT = prove
 (`forall c s u v a. c * c + s * s = &1 /\
     &1 <= a /\ a <= &1001 / &1000 /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ &0 <= y) /\
     lclosed c s u v a (&1) (&457 / &500) /\
     lclosed c s u v a (&457 / &500) (&1)
     ==> lclosed c s u v a a a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  MATCH_MP_TAC CIP_IN_FRAME THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: upper_left *)
let CIP_UPPER_LEFT = prove
 (`forall c s u v a. c * c + s * s = &1 /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     linside c s u v a (&1) (&1543 / &500) /\ linside c s u v a (&457 / &500) (&3)
     ==> lclosed c s u v a a (&4 - a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM LCLOSED_PULLY] THEN
  MATCH_MP_TAC CIP_FIRST_QUADRANT THEN
  REWRITE_TAC[LCLOSED_PULLY] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_SIMP_TAC[LINSIDE_CLOSED] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LCONT_PULLY o
    check (fun th -> is_comb(concl th) && fst(strip_comb(concl th)) = `lcont`)) THEN
  REWRITE_TAC[lcont] THEN MESON_TAC[]);;

(* Lean: outside_upper_left *)
let CIP_OUTSIDE_UPPER_LEFT = prove
 (`forall cB sB uB vB aB c s u v a.
     c * c + s * s = &1 /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     linside c s u v a (&1) (&1543 / &500) /\ linside c s u v a (&457 / &500) (&3) /\
     ldisj cB sB uB vB aB c s u v a
     ==> ~linside cB sB uB vB aB a (&4 - a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC OUTSIDE_OF_CLOSED THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC CIP_UPPER_LEFT THEN ASM_REWRITE_TAC[]]);;
