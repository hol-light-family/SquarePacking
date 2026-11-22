(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareRHigh.lean                             *)
(*                                                                           *)
(* Square q = (c,s,u,v,a) (the right square), square A = (cA,sA,uA,vA,aA).   *)
(* ClosedPointExclusion.outside_of_closed is OUTSIDE_OF_CLOSED (p2_base);    *)
(* S12.positive_frame_wall_bounds is C977WC_POSITIVE_FRAME_WALL_BOUNDS.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977WallChains.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: right_point *)
let FSRH_RIGHT_POINT = prove
 (`forall c s u v a cA sA uA vA aA.
     c * c + s * s = &1 /\ &1 < a /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     (forall x y. linside c s u v a x y ==> &0 <= x /\ x <= &4 /\ &0 <= y /\ y <= &4) /\
     lclosed c s u v a (&1543 / &500) (&2) /\
     lclosed c s u v a (&3) (&12 / &5) /\
     ~(linside c s u v a (&81 / &25) (&187 / &100)) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     ldisj c s u v a cA sA uA vA aA
     ==> linside c s u v a (&3) (&5 / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  (* hD *)
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `&113 / &50`; `&2`] OUTSIDE_OF_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* r = positive frame of pullX q *)
  MP_TAC(SPECL [`--c:real`; `s:real`; `u - &4 * c:real`; `--v - a - &4 * s:real`; `a:real`]
    CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LINSIDE_PULLX; LCLOSED_PULLX; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN
  (* hwall and hvertex *)
  SUBGOAL_THEN `forall x y. linside cr sr ur vr ar x y ==> &0 <= x /\ &0 <= y` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&4 - x:real`; `y:real`] o
      check (fun th -> is_imp(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= cr * ur - sr * (vr + ar)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the forced point *)
  MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
    WFP_LEFT_POSITIVE_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;
