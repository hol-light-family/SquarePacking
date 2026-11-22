(* ========================================================================= *)
(* Port of Compact/Geometry/CentralBarHeight.lean (Jatloe, N12-jatloe).       *)
(* A height bound from three occupied row points.                            *)
(* neighbors : Fin 3 -> OpenSquare is a num-indexed parameter family         *)
(* (cN i, sN i, uN i, vN i, aN i), i < 3.                                    *)
(* LongSection: scap_longsec; section_hits: SCAP_SECTION_HITS;               *)
(* sectionRadius: lsec_radius; horizontal_long_section:                      *)
(* LSEC_HORIZONTAL_LONG_SECTION; closed_support: TSS_CLOSED_SUPPORT;         *)
(* ClosedPointExclusion.outside_of_closed: OUTSIDE_OF_CLOSED.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/LongSection.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* Lean: blocked_section *)
let CBH_BLOCKED_SECTION = prove
 (`forall c s u v a (cN:num->real) sN uN vN aN h.
     c * c + s * s = &1 /\ &0 < a /\
     (forall i. i < 3 ==> cN i * cN i + sN i * sN i = &1 /\ &0 < aN i) /\
     lcont c s u v a /\
     (forall i. i < 3 ==> lclosed (cN i) (sN i) (uN i) (vN i) (aN i) (&i + &1) h) /\
     (forall i x y. i < 3 ==> ~(linside c s u v a x y /\
                         linside (cN i) (sN i) (uN i) (vN i) (aN i) x y))
     ==> ~scap_longsec c s u v a h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`]
    SCAP_SECTION_HITS) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `(cN:num->real) i`; `(sN:num->real) i`; `(uN:num->real) i`;
                `(vN:num->real) i`; `(aN:num->real) i`; `&i + &1`; `h:real`]
    OUTSIDE_OF_CLOSED) THEN
  ASM_SIMP_TAC[]);;

(* Lean: center_above_blocked *)
let CBH_CENTER_ABOVE_BLOCKED = prove
 (`forall c s u v a h x y.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\
     lclosed c s u v a x y /\ h + &51 / &100 <= y /\
     ~scap_longsec c s u v a h
     ==> h + lsec_radius c s < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs c * abs c + abs s * abs s = &1` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ARITH `abs x * abs x = x * x`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs c /\ &0 <= abs s` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs c + abs s <= &3 / &2 /\ abs c * abs s <= &1 / &2`
  STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `abs c * abs c + abs s * abs s = &1` THEN
   UNDISCH_TAC `&0 <= abs c` THEN UNDISCH_TAC `&0 <= abs s` THEN
   SPEC_TAC(`abs c`,`A:real`) THEN SPEC_TAC(`abs s`,`B:real`) THEN
   REPEAT STRIP_TAC THEN NLIN_TAC [SQ_NONNEG `A - B:real`]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`;
                `&0`; `&1`] TSS_CLOSED_SUPPORT) THEN
  ASM_REWRITE_TAC[tss_support_radius] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID; REAL_NEG_0] THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a * (abs s + abs c) <= &1001 / &1000 * (abs s + abs c)`
  ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lsec_radius c s = (abs c + abs s - &2 * abs c * abs s) / &2`
  ASSUME_TAC THENL
  [REWRITE_TAC[lsec_radius; REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `h - lsec_radius c s <= lcy c s u v a` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `~scap_longsec c s u v a h` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LSEC_HORIZONTAL_LONG_SECTION THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN ASM_REAL_ARITH_TAC);;

(* Lean: from_three_occupied_points *)
let CBH_FROM_THREE_OCCUPIED_POINTS = prove
 (`forall c s u v a (cN:num->real) sN uN vN aN h x y.
     c * c + s * s = &1 /\ &0 < a /\
     (forall i. i < 3 ==> cN i * cN i + sN i * sN i = &1 /\ &0 < aN i) /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     lclosed c s u v a x y /\ h + &51 / &100 <= y /\
     (forall i. i < 3 ==> lclosed (cN i) (sN i) (uN i) (vN i) (aN i) (&i + &1) h) /\
     (forall i x y. i < 3 ==> ~(linside c s u v a x y /\
                         linside (cN i) (sN i) (uN i) (vN i) (aN i) x y))
     ==> h + lsec_radius c s < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CBH_CENTER_ABOVE_BLOCKED THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CBH_BLOCKED_SECTION THEN
  MAP_EVERY EXISTS_TAC [`cN:num->real`; `sN:num->real`; `uN:num->real`;
                        `vN:num->real`; `aN:num->real`] THEN
  ASM_REWRITE_TAC[]);;
