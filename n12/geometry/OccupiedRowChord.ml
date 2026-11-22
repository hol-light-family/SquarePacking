(* ========================================================================= *)
(* Phase 2: Compact/Bridge/OccupiedRowChord.lean.                            *)
(* A blocked row forces an oriented chord cut from original point ownership. *)
(* Representation as in AngleSection.ml; the neighbours Fin 3 -> OpenSquare  *)
(* are five functions cN sN uN vN aN (indices < 3) with their OpenSquare     *)
(* invariants; ClosedInside is lclosed;                                       *)
(* CentralBarHeight.from_three_occupied_points is CBH_FROM_THREE_OCCUPIED_POINTS. *)
(* ========================================================================= *)

needs "n12/geometry/CentralBarHeight.ml";;
needs "n12/geometry/AngleSection.ml";;

(* Lean: above_radius *)
let ORC_ABOVE_RADIUS = prove
 (`forall leaf B r c s u v a (cN:num->real) sN uN vN aN h x y.
     c * c + s * s = &1 /\ &0 < a /\
     (forall i. i < 3 ==> cN i * cN i + sN i * sN i = &1 /\ &0 < aN i) /\
     ae_check (pl_angle leaf) /\ asec_radius_check B r (pl_angle leaf) /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\ angle_witness leaf c s u v a /\
     linside c s u v a x y /\ h + &51 / &100 <= y /\
     (forall i. i < 3 ==> lclosed (cN i) (sN i) (uN i) (vN i) (aN i) (&i + &1) h) /\
     (forall i x y. i < 3 ==> ~(linside c s u v a x y /\ linside (cN i) (sN i) (uN i) (vN i) (aN i) x y))
     ==> h + r < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `angle_witness leaf c s u v a` THEN
  REWRITE_TAC[angle_witness; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`; `t:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `a':real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ae_check] o
    check (fun th -> try fst(dest_const(rator(concl th))) = "ae_check" with Failure _ -> false)) THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_NONNEGATIVE) THEN
  (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THEN
  MP_TAC(SPECL [`B:real`; `r:real`; `pl_angle leaf`; `t:real`] ASEC_RADIUS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r <= lsec_radius c' s'` ASSUME_TAC THENL
   [REWRITE_TAC[lsec_radius; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[real_abs] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`;
                `cN:num->real`; `sN:num->real`; `uN:num->real`; `vN:num->real`; `aN:num->real`;
                `h:real`; `x:real`; `y:real`] CBH_FROM_THREE_OCCUPIED_POINTS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
           FIRST_ASSUM(fun th -> REWRITE_TAC[th] THEN NO_TAC);
           FIRST_ASSUM(fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC);
           SUBGOAL_THEN `linside c' s' u' v' a x y` MP_TAC THENL
            [FIRST_ASSUM(fun th -> REWRITE_TAC[th] THEN FIRST_ASSUM ACCEPT_TAC);
             REWRITE_TAC[linside; lclosed] THEN REAL_ARITH_TAC]];
    ASM_REAL_ARITH_TAC]);;

(* Lean: above_window *)
let ORC_ABOVE_WINDOW = prove
 (`forall leaf B r c s u v a (cN:num->real) sN uN vN aN h x y upper.
     c * c + s * s = &1 /\ &0 < a /\
     (forall i. i < 3 ==> cN i * cN i + sN i * sN i = &1 /\ &0 < aN i) /\
     ae_check (pl_angle leaf) /\ asec_radius_check B r (pl_angle leaf) /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\ angle_witness leaf c s u v a /\
     upper <= h /\ linside c s u v a x y /\ h + &51 / &100 <= y /\
     (forall i. i < 3 ==> lclosed (cN i) (sN i) (uN i) (vN i) (aN i) (&i + &1) h) /\
     (forall i x y. i < 3 ==> ~(linside c s u v a x y /\ linside (cN i) (sN i) (uN i) (vN i) (aN i) x y))
     ==> upper + r < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`leaf:pose_leaf`; `B:real`; `r:real`; `c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cN:num->real`; `sN:num->real`; `uN:num->real`; `vN:num->real`; `aN:num->real`;
                `h:real`; `x:real`; `y:real`] ORC_ABOVE_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
