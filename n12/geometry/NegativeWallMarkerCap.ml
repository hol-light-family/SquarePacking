(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeWallMarkerCap.lean (Jatloe, N12-jatloe).  *)
(* The upper corner marker bounds the negative wall's upper face.            *)
(* short_projections is WFP_SHORT_PROJECTIONS.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/NegativeWallTopSeed.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let NWMC_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: upper_u *)
let NWMC_UPPER_U = prove
 (`forall c sW u v a t.
     c * c + sW * sW = &1 /\ &0 < a /\
     c977cc_normal c t /\ sW = --t /\ &1 < a /\
     linside c sW u v a (&457 / &500) (&2) /\
     (&19 / &25) * t + (&187 / &100) * c <= v /\
     ~linside c sW u v a (&33 / &20) (&47 / &20)
     ==> u + a <= (&33 / &20) * c - (&47 / &20) * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW:real = --t`)) THEN
  C977CSB_NORMAL_TAC THEN
  NWMC_UNFOLD_TAC `linside c (--t) u v a (&457 / &500) (&2)` THEN
  UNDISCH_TAC `~linside c (--t) u v a (&33 / &20) (&47 / &20)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: upper_face *)
let NWMC_UPPER_FACE = prove
 (`forall c sW u v a t.
     c * c + sW * sW = &1 /\ &0 < a /\
     c977cc_normal c t /\ sW = --t /\ &1 < a /\
     linside c sW u v a (&457 / &500) (&2) /\
     (&19 / &25) * t + (&187 / &100) * c <= v /\
     ~linside c sW u v a (&33 / &20) (&47 / &20) /\
     ~linside c sW u v a (&457 / &500) (&3)
     ==> v + a <= (&457 / &500) * t + &3 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `sW:real`; `&92 / &125`; `--(&13 / &20)`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW:real = --t`)) THEN
  C977CSB_NORMAL_TAC THEN
  NWMC_UNFOLD_TAC `linside c (--t) u v a (&457 / &500) (&2)` THEN
  SUBGOAL_THEN `u < (&457 / &500) * c - &3 * t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `v + a <= (&33 / &20) * t + (&47 / &20) * c` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c (--t) u v a (&33 / &20) (&47 / &20)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside c (--t) u v a (&457 / &500) (&3)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: sector *)
let NWMC_SECTOR = prove
 (`forall d t a lo hi. c977cc_normal d t /\ &1 < a /\ hi = lo + a /\
                 (&19 / &25) * t + (&187 / &100) * d <= lo /\
                 hi <= (&457 / &500) * t + &3 * d
                 ==> a <= (&77 / &500) * t + (&113 / &100) * d /\
                     t < &825 / &1387 /\ t < &3 / &5 /\ &4 / &5 < d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal d t` THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(&4 / &5) * d + (&3 / &5) * t <= &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `((&4 / &5) * d + (&3 / &5) * t) * ((&4 / &5) * d + (&3 / &5) * t) <= &1`
   MP_TAC THENL
   [MP_TAC(SPEC `&3 * d - &4 * t` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SPEC_TAC(`(&4 / &5) * d + (&3 / &5) * t`,`w:real`) THEN GEN_TAC THEN DISCH_TAC THEN
   NLIN_TAC [SQ_NONNEG `w - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `t < &825 / &1387` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&3 / &5 - t) * (&3 / &5 + t)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
   NLIN_TAC [SQ_NONNEG `d - &4 / &5`]]);;
