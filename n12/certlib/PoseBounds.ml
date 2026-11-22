(* ========================================================================= *)
(* Port of source/S12/PoseBounds.lean (Jatloe, N12-jatloe).                  *)
(* Imported geometry: positive_frame_wall_bounds is                          *)
(* TSS_POSITIVE_FRAME_WALL_BOUNDS (geometry/ThreeSquareSupport.ml),                *)
(* affine_endpoint_nonnegative is SCAP_AFFINE_ENDPOINT_NONNEG                *)
(* (geometry/SectionCapacity.ml), inside_iff_rotated_box is TSS_INSIDE_FACE.       *)
(* The marker non-avoidance of MarkerCoverGeometry (imported by the Lean     *)
(* file, unused here) is Phase-1 MARKER_NONAVOID (n12/phase1/markers.ml).      *)
(* InsideContainer q is lcont c s u v a.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/certlib/AngleReference.ml";;

(* Lean: positive_frame_all_walls *)
let PB_POSITIVE_FRAME_ALL_WALLS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\ lcont c s u v a
     ==> a * (c + s) / &2 <= lcx c s u v a /\ lcx c s u v a <= &4 - a * (c + s) / &2 /\
         a * (c + s) / &2 <= lcy c s u v a /\ lcy c s u v a <= &4 - a * (c + s) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `lcont c s u v a` THEN
    REWRITE_TAC[lcont] THEN MESON_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= &4 - (c * (u + a) - s * v)` ASSUME_TAC THENL
  [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + a - t) - s * (v + t)`;
                                 `s * (u + a - t) + c * (v + t)`]) THEN
   ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 - (s * (u + a) + c * (v + a))` ASSUME_TAC THENL
  [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + a - t) - s * (v + a - t)`;
                                 `s * (u + a - t) + c * (v + a - t)`]) THEN
   ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[lcx; lcy] THEN ASM_REAL_ARITH_TAC);;

(* drop the hypotheses c = normalC t, s = normalS t once used *)
let PB_DROP_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th)) &&
    (try fst(dest_const(rator(rhs(concl th)))) = "normalC" ||
         fst(dest_const(rator(rhs(concl th)))) = "normalS" with Failure _ -> false))));;

(* turn the hypotheses c = normalC t, s = normalS t into normalC t = c, ...  *)
(* so that ASM_REWRITE_TAC does not substitute the square's c and s          *)
let PB_FLIP_NORMAL_TAC =
  RULE_ASSUM_TAC(fun th ->
    let tm = concl th in
    if is_eq tm && is_var(lhs tm) &&
       (try mem (fst(dest_const(rator(rhs tm)))) ["normalC"; "normalS"] with Failure _ -> false)
    then SYM th else th);;

(* Lean: AngleEnclosure.outer_sound *)
let PB_OUTER_SOUND = prove
 (`forall w upperSide c s u v a t x y.
     c * c + s * s = &1 /\ &0 < a /\
     ae_check w /\ c = normalC t /\ s = normalS t /\
     ae_lower w <= t /\ t <= ae_upper w /\ a <= upperSide /\ linside c s u v a x y
     ==> abs(ae_c w * (x - lcx c s u v a) + ae_s w * (y - lcy c s u v a)) <
           (upperSide * ae_outer w) / &2 /\
         abs(--(ae_s w) * (x - lcx c s u v a) + ae_c w * (y - lcy c s u v a)) <
           (upperSide * ae_outer w) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(ae_c w * c + ae_s w * s) + abs(--(ae_s w) * c + ae_c w * s) <= ae_outer w`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AE_SUPPORT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PB_DROP_NORMAL_TAC THEN
  UNDISCH_TAC `ae_check w` THEN REWRITE_TAC[ae_check] THEN STRIP_TAC THEN
  MATCH_MP_TAC RG_NORMAL_CHANGE_INNER THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `a:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[REAL_POW_2];
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH
      `abs(--(ae_c w) * s + ae_s w * c) = abs(--(ae_s w) * c + ae_c w * s)`] THEN
    UNDISCH_TAC `abs(ae_c w * c + ae_s w * s) + abs(--(ae_s w) * c + ae_c w * s) <= ae_outer w` THEN
    SPEC_TAC(`abs(ae_c w * c + ae_s w * s) + abs(--(ae_s w) * c + ae_c w * s)`,`B:real`) THEN
    GEN_TAC THEN DISCH_TAC THEN NLIN_TAC [];
    ALL_TAC; ALL_TAC] THEN
  UNDISCH_TAC `linside c s u v a x y` THEN REWRITE_TAC[linside] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: AngleEnclosure.wall_sound *)
let PB_WALL_SOUND = prove
 (`forall w lowerSide c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     ae_check w /\ &0 < lowerSide /\ c = normalC t /\ s = normalS t /\
     ae_lower w <= t /\ t <= ae_upper w /\ lowerSide <= a /\ lcont c s u v a
     ==> (lowerSide * ae_wall w) / &2 <= lcx c s u v a /\
         lcx c s u v a <= &4 - (lowerSide * ae_wall w) / &2 /\
         (lowerSide * ae_wall w) / &2 <= lcy c s u v a /\
         lcy c s u v a <= &4 - (lowerSide * ae_wall w) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ae_wall w <= c + s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AE_WALL_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c /\ &0 <= s` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC AE_NORMAL_NONNEGATIVE THEN
    UNDISCH_TAC `ae_check w` THEN REWRITE_TAC[ae_check] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  PB_DROP_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] PB_POSITIVE_FRAME_ALL_WALLS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lowerSide * ae_wall w <= a * (c + s)` MP_TAC THENL
   [NLIN_TAC []; ASM_REAL_ARITH_TAC]);;
