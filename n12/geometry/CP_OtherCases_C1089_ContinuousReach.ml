(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ContinuousReach.lean          *)
(* (namespace N12Compact.Completion.OtherCases.C1089.ContinuousReach).      *)
(* exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME; affine_endpoint_       *)
(* nonnegative: SCAP_AFFINE_ENDPOINT_NONNEG; inside_iff_rotated_box:        *)
(* TSS_INSIDE_FACE.  The chart translate (pullX (pullSwap B)) 2 (-2) of     *)
(* bottom_points is the square (--sB, cB, uB + 2cB - 2sB, vB - 2cB - 2sB,   *)
(* aB) (C1089CR_CHART); inside_segment is a direct band computation.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* Lean: positive_point (private); the same statement as WallLowerReach's *)
let C1089CR_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     &0 <= c * u - s * (v + a) /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~(linside c s u v a (&1) (&87 / &50)) /\
     ~(linside c s u v a (&87 / &50) (&2))
     ==> linside c s u v a (&1) (&64 / &25)`,
  MATCH_ACCEPT_TAC WLR_POSITIVE_POINT);;

(* Lean: left_point *)
let C1089CR_LEFT_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> &0 <= x) /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\ ~linside c s u v a (&87 / &50) (&2)
     ==> linside c s u v a (&1) (&64 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `a1:real = a` o concl)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  SUBGOAL_THEN `&0 <= c1 * u1 - s1 * (v1 + a)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `c1 + s1:real`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c1 * (u1 + t) - s1 * (v1 + a - t)`;
                                  `s1 * (u1 + t) + c1 * (v1 + a - t)`] o
      check (fun th -> is_forall(concl th))) THEN
    ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC C1089CR_POSITIVE_POINT THEN ASM_REWRITE_TAC[]);;

(* the chart of bottom_points *)
let C1089CR_CHART = prove
 (`forall c s u v a x y.
     linside (--s) c (u + &2 * c - &2 * s) (v - &2 * c - &2 * s) a x y <=>
     linside c s u v a (y - &2) (&2 - x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: bottom_points *)
let C1089CR_BOTTOM_POINTS = prove
 (`forall cB sB uB vB aB cC sC uC vC aC.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cC * cC + sC * sC = &1 /\ &0 < aC /\
     &1 < aB /\
     (forall x y. linside cB sB uB vB aB x y ==> y <= &2) /\
     linside cB sB uB vB aB (&0) (&543 / &500) /\
     linside cB sB uB vB aB (&2 / &5) (&1) /\
     ~linside cB sB uB vB aB (--(&13 / &50)) (&1) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     ldisj cB sB uB vB aB cC sC uC vC aC
     ==> linside cB sB uB vB aB (&14 / &25) (&1) /\
         linside cB sB uB vB aB (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--sB:real`; `cB:real`; `uB + &2 * cB - &2 * sB`; `vB - &2 * cB - &2 * sB`;
                `aB:real`] C1089CR_LEFT_POINT) THEN
  REWRITE_TAC[C1089CR_CHART] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`y - &2`; `&2 - x`] o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `&2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_MESON_TAC[]];
    DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC [`linside cB sB uB vB aB (&14 / &25) (&1)`;
                         `linside cB sB uB vB aB (&2 / &5) (&1)`] THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
