(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/WallProfile/BoundaryCapGeometry     *)
(* (namespace N12Compact.Completion.OtherCases.WallProfile).  The strict    *)
(* boundary-square support cap.  lower: ABT_lower; lower_wall_vertex:       *)
(* OCWPVG_LOWER_WALL_VERTEX; half / profile / quarter_data / boundary_cap:  *)
(* C1092WPS_half / C1092WPS_profile / C1092WPS_QUARTER_DATA /               *)
(* C1092WPS_BOUNDARY_CAP.  Square B is cB sB uB vB aB.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: lower_in_bands (private) *)
let OCWPBCG_LOWER_IN_BANDS = prove
 (`forall c s u v a nx ny.
      ABT_lower c s u v a nx ny =
      (nx * c + ny * s) * (u + a / &2) + (--nx * s + ny * c) * (v + a / &2) -
      a / &2 * (abs(nx * c + ny * s) + abs(--nx * s + ny * c))`,
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN REAL_ARITH_TAC);;

(* Lean: negative_lower_vertex *)
let OCWPBCG_NEGATIVE_LOWER_VERTEX = prove
 (`forall cB sB uB vB aB t c s.
      sB = --t /\ &0 <= cB /\ &0 <= t /\ &0 <= c /\ &0 <= s
      ==> ABT_lower cB sB uB vB aB c (--s) =
          c * (cB * uB + t * vB) - s * (--t * uB + cB * vB) +
          aB * min (c * t - s * cB) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[OCWPBCG_LOWER_IN_BANDS] THEN
  SUBGOAL_THEN `c * cB + --s * --t = c * cB + s * t /\
                --c * --t + --s * cB = c * t - s * cB` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(c * cB + s * t) = c * cB + s * t` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c * t - s * cB` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x /\ min x (&0) = &0`];
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> abs x = --x /\ min x (&0) = x`]] THEN
  REAL_ARITH_TAC);;

(* Lean: negative_boundary_cap *)
let OCWPBCG_NEGATIVE_BOUNDARY_CAP = prove
 (`forall cB sB uB vB aB t c s.
      cB * cB + sB * sB = &1 /\ &0 < aB /\
      sB = --t /\ &0 < cB /\ &0 < t /\ &1 < aB /\
      (forall x y. linside cB sB uB vB aB x y ==> &0 <= y) /\
      vB + aB <= &2 * t + cB /\
      &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
      ==> ABT_lower cB sB uB vB aB c (--s) < aB * C1092WPS_profile c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    OCWPVG_LOWER_WALL_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `t:real`; `c:real`; `s:real`] OCWPBCG_NEGATIVE_LOWER_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  SUBGOAL_THEN `cB pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cB * cB + --t * --t = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `cB:real`; `t:real`] C1092WPS_BOUNDARY_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `t * C1092WPS_half cB t = &1 - cB` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN
    SUBGOAL_THEN `~(&1 + cB = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ABBREV_TAC `m = min (c * t - s * cB) (&0)` THEN
  ABBREV_TAC `P = C1092WPS_profile c s` THEN
  ABBREV_TAC `h = C1092WPS_half cB t` THEN
  ABBREV_TAC `X = cB * uB + t * vB` THEN
  ABBREV_TAC `Y = --t * uB + cB * vB` THEN
  SUBGOAL_THEN `t * X + cB * Y = vB` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    UNDISCH_TAC `cB * cB + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `aB * t <= Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN UNDISCH_TAC `&0 <= --t * (uB + aB) + cB * vB` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= c * (&2 * t + cB - aB - (t * X + cB * Y)) /\
    &0 <= (c * cB + s * t) * (Y - aB * t) /\
    &0 <= (aB * t) * (P - (c * (&2 - cB - h) - s * t + m)) /\
    &0 < ((aB - &1) * c) * (&2 * t + cB) /\
    aB * c * (t * h) = aB * c * (&1 - cB)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= t * ((c * X - s * Y + aB * m) - aB * P)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN RASM_ARITH_TAC);;
