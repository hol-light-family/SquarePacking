(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1090/MergedLeftSeed.lean           *)
(* (namespace N12Compact.Completion.OtherCases.C1090.MergedLeftSeed).        *)
(* The merged-left seed is the wall-bridge consequence of markers 1 and 12  *)
(* in one square.  S12.wall_bridge_forces (source/S12/WallBridge.lean) is   *)
(* ported here for linside with only the left-wall hypothesis (the existing *)
(* n12/phase1/localq_geom.ml version assumes all four walls, owalls).        *)
(* S12.ExactMarkers / Owns are c1090mls_exact_markers, with the marker      *)
(* table `marker` of n12/phase1/markers.ml (Marker = Fin 16 <-> i < 16).      *)
(* The family q : Fin 12 -> OpenSquare enters only through q 0 and q 8,    *)
(* written c0 s0 u0 v0 a0 and c8 s8 u8 v8 a8.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* helper: localq_geom.ml WB_UPPER *)
let C1090MLS_WB_UPPER = prove
 (`forall X Y c s l t.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= X /\
        vector[&457 / &500; &1] IN osq X Y c s l /\ vector[&457 / &500; &2] IN osq X Y c s l /\
        &5 / &4 <= t /\ t <= &7 / &4
        ==> (&1 - X) * c + (t - Y) * s < l / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN STRIP_TAC THEN
  FRAME_FACTS_TAC THEN REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
  NLIN_FACTS_TAC [] [`s * (&2 - t) < (&43 / &500) * c`; `s <= (&43 / &125) * c`; `s <= c`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`] [`&2 / &3 <= c`] THEN
  NLIN_FACTS_TAC [] [`l * c <= c * c + (&457 / &500) * s * s - (&2 - t) * c * s`;
    `(&457 / &500 - &2 / &5) * s <= (&2 - t) * c`; `&0 <= (&1 - c) * (c - &2 / &3)`;
    `&0 < (l - &1) * c`; `c <= &1`] THEN
  NLIN_TAC []);;

(* helper: localq_geom.ml WALL_BRIDGE_FRAME *)
let C1090MLS_WALL_BRIDGE_FRAME = prove
 (`forall X Y c s l t.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= X /\
        vector[&457 / &500; &1] IN osq X Y c s l /\ vector[&457 / &500; &2] IN osq X Y c s l /\
        &5 / &4 <= t /\ t <= &7 / &4
        ==> vector[&1; t] IN osq X Y c s l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`X:real`; `Y:real`; `c:real`; `s:real`; `l:real`; `t:real`] C1090MLS_WB_UPPER) THEN
  MP_TAC(SPECL [`X:real`; `&3 - Y`; `s:real`; `c:real`; `l:real`; `&3 - t`] C1090MLS_WB_UPPER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `forall x y. vector[x; y] IN osq X (&3 - Y) s c l <=> vector[x; &3 - y] IN osq X Y c s l`
   (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[IN_OSQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `vector[&457 / &500; &1] IN osq X Y c s l` THEN
  UNDISCH_TAC `vector[&457 / &500; &2] IN osq X Y c s l` THEN
  REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN REPEAT STRIP_TAC THEN FRAME_FACTS_TAC THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC THEN NO_TAC) THEN
  NLIN_TAC [SQ_NONNEG `c - s`]);;

(* helper: left half of S12.positive_frame_wall_bounds (only the wall x >= 0) *)
let C1090MLS_POSITIVE_LEFT_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\
               (forall x y. linside c s u v a x y ==> &0 <= x)
     ==> a * (c + s) / &2 <= lcx c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c * u - s * (v + a)` ASSUME_TAC THENL
  [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + t) - s * (v + a - t)`;
                                 `s * (u + t) + c * (v + a - t)`]) THEN
   ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN ASM_REAL_ARITH_TAC);;

(* helper: linside as osq about the centre *)
let C1090MLS_LINSIDE_OSQ = prove
 (`forall c s u v a x y. c * c + s * s = &1
     ==> (linside c s u v a x y <=>
          vector[x; y] IN osq (lcx c s u v a) (lcy c s u v a) c s a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OSQ_LSQ] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[linside] THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REAL_ARITH_TAC);;

(* Lean: S12.wall_bridge_forces (source/S12/WallBridge.lean) *)
let C1090MLS_WALL_BRIDGE_FORCES = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> &0 <= x) /\
     linside c s u v a (&457 / &500) (&1) /\ linside c s u v a (&457 / &500) (&2) /\
     &5 / &4 <= t /\ t <= &7 / &4
     ==> linside c s u v a (&1) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> try REWRITE_RULE[MATCH_MP C1090MLS_LINSIDE_OSQ
    (ASSUME `c * c + s * s = &1`)] th with Failure _ -> th) THEN
  ASM_SIMP_TAC[C1090MLS_LINSIDE_OSQ] THEN
  MAP_EVERY ABBREV_TAC [`X = lcx c s u v a`; `Y = lcy c s u v a`] THEN
  MP_TAC(MP (SPECL [`X:real`; `Y:real`; `c:real`; `s:real`; `a:real`] OSQ_POS_FRAME)
    (ASSUME `c * c + s * s = &1`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(fun th -> if concl th = `osq X Y c s a = osq X Y c' s' a`
    then SUBST_ALL_TAC th else NO_TAC) THEN
  MATCH_MP_TAC C1090MLS_WALL_BRIDGE_FRAME THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `c' * X + s' * Y - a / &2`;
                `--s' * X + c' * Y - a / &2`; `a:real`] C1090MLS_POSITIVE_LEFT_WALL) THEN
  ASM_REWRITE_TAC[GSYM OSQ_LSQ] THEN
  SUBGOAL_THEN `lcx c' s' (c' * X + s' * Y - a / &2) (--s' * X + c' * Y - a / &2) a = X`
    SUBST1_TAC THENL
   [REWRITE_TAC[lcx] THEN UNDISCH_TAC `c' * c' + s' * s' = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: S12.ExactMarkers with S12.Owns (source/S12/TransformFacts.lean) *)
let c1090mls_exact_markers = new_definition
 `c1090mls_exact_markers c s u v a (g:num->bool) <=>
    forall i. i < 16 ==> (linside c s u v a (marker i$1) (marker i$2) <=> i IN g)`;;

(* Lean: segment *)
let C1090MLS_SEGMENT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> &0 <= x) /\
     linside c s u v a (&457 / &500) (&1) /\ linside c s u v a (&457 / &500) (&2)
     ==> forall y. &5 / &4 <= y ==> y <= &7 / &4 ==> linside c s u v a (&1) y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C1090MLS_WALL_BRIDGE_FORCES THEN
  ASM_REWRITE_TAC[]);;

(* Lean: of_exact_markers *)
let C1090MLS_OF_EXACT_MARKERS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ lcont c s u v a /\
     c1090mls_exact_markers c s u v a {1, 12}
     ==> forall y. &5 / &4 <= y ==> y <= &7 / &4 ==> linside c s u v a (&1) y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1090mls_exact_markers] THEN STRIP_TAC THEN
  MATCH_MP_TAC C1090MLS_SEGMENT THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[lcont];
    FIRST_X_ASSUM(MP_TAC o SPEC `1`);
    FIRST_X_ASSUM(MP_TAC o SPEC `12`)] THEN
  CONV_TAC(ONCE_DEPTH_CONV MARKER_CONV) THEN
  REWRITE_TAC[VECTOR_2; IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: marker1_foreign_to_singleton *)
let C1090MLS_MARKER1_FOREIGN_TO_SINGLETON = prove
 (`forall c0 s0 u0 v0 a0 c8 s8 u8 v8 a8.
     c0 * c0 + s0 * s0 = &1 /\ &0 < a0 /\ c8 * c8 + s8 * s8 = &1 /\ &0 < a8 /\
     linside c8 s8 u8 v8 a8 (&457 / &500) (&1) /\
     ldisj c0 s0 u0 v0 a0 c8 s8 u8 v8 a8
     ==> ~linside c0 s0 u0 v0 a0 (&457 / &500) (&1)`,
  REWRITE_TAC[ldisj] THEN MESON_TAC[]);;

(* Lean: actual_segment *)
let C1090MLS_ACTUAL_SEGMENT = prove
 (`forall c8 s8 u8 v8 a8. c8 * c8 + s8 * s8 = &1 /\ &0 < a8 /\ &1 < a8 /\
     lcont c8 s8 u8 v8 a8 /\
     linside c8 s8 u8 v8 a8 (&457 / &500) (&1) /\ linside c8 s8 u8 v8 a8 (&457 / &500) (&2)
     ==> forall y. &5 / &4 <= y ==> y <= &7 / &4 ==> linside c8 s8 u8 v8 a8 (&1) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1090MLS_SEGMENT THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[lcont]);;
