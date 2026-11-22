(* ========================================================================= *)
(* Port of Compact/Geometry/WallInwardCenter.lean (Jatloe, N12-jatloe).       *)
(* An inward auxiliary point constrains the actual centre of a wall owner.   *)
(* exists_positive_frame is WCB_EXISTS_POSITIVE_FRAME (WallCenterBarrier.ml)*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallLowerCenterBarrier.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let WIC_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: positive_box (private) *)
let WIC_POSITIVE_BOX = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\ &0 <= c /\ &0 <= s /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> &21 / &20 <= lcx c s u v a /\ lcx c s u v a <= &7 / &4 /\
         &9 / &4 <= lcy c s u v a /\ lcy c s u v a <= &59 / &20`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  WIC_UNFOLD_TAC `linside c s u v a (&457 / &500) (&2)` THEN
  WIC_UNFOLD_TAC `linside c s u v a (&1) (&12 / &5)` THEN
  WIC_UNFOLD_TAC `linside c s u v a (&87 / &50) (&2)` THEN
  SUBGOAL_THEN `u + a <= c * (&33 / &20) + s * (&47 / &20)` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&33 / &20) (&47 / &20)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &20`; `&61 / &100`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `--s + c * (&87 / &50) <= v` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&1) (&87 / &50)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&9 * c < &35 * s /\ &37 * s < &13 * c` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&15 / &16 <= c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= (&13 * c - &37 * s) * (&13 * c + &37 * s) /\
                 &0 <= (&15 / &16 - c) * (&15 / &16 + c)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&6 / &25 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c + s <= &13 / &10` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&13 * c - &37 * s) * (&37 * c - &13 * s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   DISCH_TAC THEN NLIN_TAC [SQ_NONNEG `c + s - &13 / &10`]; ALL_TAC] THEN
  SUBGOAL_THEN `a / &2 * (c + s) <= &69 / &100` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1001 / &1000 - a) * (c + s)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&9 / &4 <= lcy c s u v a` ASSUME_TAC THENL
  [REWRITE_TAC[lcy] THEN
   SUBGOAL_THEN
    `&0 <= s * ((u + a) - (c * &87 / &50 + s * &2)) /\
     &0 <= c * (v - (--s + c * (&87 / &50))) /\
     &0 < (a - &1) * (c - s) /\ &0 <= s * (c - &15 / &16) /\ &0 <= s * s`
   MP_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL;
     MATCH_MP_TAC REAL_LE_MUL; REWRITE_TAC[REAL_LE_SQUARE]] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&87 / &50`; `&2`;
                `&1`; `&0`] TSS_INSIDE_SUPPORT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1`; `&12 / &5`;
                `&1`; `&0`] TSS_INSIDE_SUPPORT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&457 / &500`; `&2`;
                `&0`; `&1`] TSS_INSIDE_SUPPORT) THEN
  ASM_REWRITE_TAC[tss_support_radius; REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID;
                  REAL_ADD_LID; REAL_MUL_LNEG; REAL_ABS_NEG; REAL_NEG_0] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: center_box *)
let WIC_CENTER_BOX = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> &21 / &20 <= lcx c s u v a /\ lcx c s u v a <= &7 / &4 /\
         &9 / &4 <= lcy c s u v a /\ lcy c s u v a <= &59 / &20`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && (rator(lhs(concl th)) = `lcx c' s' u' v'` ||
                        rator(lhs(concl th)) = `lcy c' s' u' v'`)))) THEN
  MATCH_MP_TAC WIC_POSITIVE_BOX THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;
