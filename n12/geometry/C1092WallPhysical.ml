(* ========================================================================= *)
(* Port of Compact/Geometry/C1092WallPhysical.lean (Jatloe, N12-jatloe).      *)
(* Physical adapter for the C1092 wall polygon: original marker12 owners     *)
(* contain all twelve targets (reflected when the centre is above y = 2).    *)
(* S12.first_quadrant_rational: ARC_PARAM (shared/tools/bernstein.ml);                *)
(* exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME;                         *)
(* positive_frame_wall_bounds: C977WC_POSITIVE_FRAME_WALL_BOUNDS;            *)
(* short_projections: WFP_SHORT_PROJECTIONS; pullY: LINSIDE_PULLY etc.       *)
(* Owns q j (Marker = Fin 16) is c1092wphy_owns with the Phase-1 marker.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "shared/tools/bernstein.ml";;
needs "n12/geometry/C1092WallCenterCover.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

(* Lean: S12.Owns (definition) *)
let c1092wphy_owns = new_definition
 `c1092wphy_owns c s u v a (j:num) <=>
    linside c s u v a (marker j$1) (marker j$2)`;;

let C1092WPHY_ARC_TAC =
  MP_TAC(SPECL [`s:real`; `c:real`] ARC_PARAM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (&1 + t * t) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN
   MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC; ALL_TAC];;

(* Lean: target_quadratic_support *)
let C1092WPHY_TARGET_QUADRATIC_SUPPORT = prove
 (`forall i c s. i < 12 /\ &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> c1092wp_targetX i * c pow 2 + (&457 / &500) * s pow 2 +
         (c1092wp_targetY i - &1) * c * s <= c + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092WPHY_ARC_TAC THEN
  MP_TAC(SPECL [`c1092wp_targetX i`; `&2 - c1092wp_targetY i`; `t:real`]
    C1092WP_REGION_MARGIN) THEN
  ASM_SIMP_TAC[C1092WP_TARGET_REGION] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(c + s - (c1092wp_targetX i * c pow 2 + (&457 / &500) * s pow 2 +
              (c1092wp_targetY i - &1) * c * s)) * (&1 + t * t) pow 2 =
    c1092wp_margin (c1092wp_targetX i) (&2 - c1092wp_targetY i) t`
  ASSUME_TAC THENL
  [SUBGOAL_THEN
    `(c + s - (c1092wp_targetX i * c pow 2 + (&457 / &500) * s pow 2 +
               (c1092wp_targetY i - &1) * c * s)) * (&1 + t * t) pow 2 =
     (c * (&1 + t * t) + s * (&1 + t * t)) * (&1 + t * t) -
     (c1092wp_targetX i * (c * (&1 + t * t)) pow 2 +
      (&457 / &500) * (s * (&1 + t * t)) pow 2 +
      (c1092wp_targetY i - &1) * (c * (&1 + t * t)) * (s * (&1 + t * t)))`
   SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[c1092wp_margin] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c + s - (c1092wp_targetX i * c pow 2 + (&457 / &500) * s pow 2 +
                                (c1092wp_targetY i - &1) * c * s)` MP_TAC THENL
  [MATCH_MP_TAC C1092WP_NONNEG_OF_MUL THEN EXISTS_TAC `(&1 + t * t) pow 2` THEN
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* Lean: rectangle_support *)
let C1092WPHY_RECTANGLE_SUPPORT = prove
 (`forall x h c s. x <= &1 /\ h <= &197 / &500 /\ &0 <= c /\ &0 <= s /\
             c pow 2 + s pow 2 = &1
             ==> &2 * (x * s + h * c) <= &1 + s * (c + s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092WPHY_ARC_TAC THEN
  SUBGOAL_THEN `&0 <= (&2 * (&1 - t)) *
     (&53 / &500 - (&447 / &500) * t + (&1053 / &500) * t pow 2 -
      (&447 / &500) * t pow 3)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[C1092WP_PFACE2_CUBIC_NONNEG] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + s * (c + s) - &2 * (s + (&197 / &500) * c)) * (&1 + t * t) pow 2 =
     (&2 * (&1 - t)) *
     (&53 / &500 - (&447 / &500) * t + (&1053 / &500) * t pow 2 -
      (&447 / &500) * t pow 3)` ASSUME_TAC THENL
  [SUBGOAL_THEN
    `(&1 + s * (c + s) - &2 * (s + (&197 / &500) * c)) * (&1 + t * t) pow 2 =
     (&1 + t * t) pow 2 + (s * (&1 + t * t)) * (c * (&1 + t * t) + s * (&1 + t * t)) -
     &2 * (s * (&1 + t * t) + (&197 / &500) * (c * (&1 + t * t))) * (&1 + t * t)`
   SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + s * (c + s) - &2 * (s + (&197 / &500) * c)` ASSUME_TAC THENL
  [MATCH_MP_TAC C1092WP_NONNEG_OF_MUL THEN EXISTS_TAC `(&1 + t * t) pow 2` THEN
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - x) * s /\ &0 <= (&197 / &500 - h) * c` MP_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= &1 + s * (c + s) - &2 * (s + (&197 / &500) * c)` THEN
  REAL_ARITH_TAC);;

(* Lean: positive_frame_left_point *)
let C1092WPHY_POSITIVE_FRAME_LEFT_POINT = prove
 (`forall c s u v a i.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 <= c /\ &0 <= s /\
     a * (c + s) / &2 <= lcx c s u v a /\
     lcx c s u v a <= &1 /\ lcy c s u v a <= &2 /\
     linside c s u v a (&457 / &500) (&2) /\
     ~linside c s u v a (&457 / &500) (&1) /\ i < 12
     ==> linside c s u v a (c1092wp_targetX i) (c1092wp_targetY i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `i:num` C1092WCC_TARGET_COVER_ARITHMETIC) THEN
  MP_TAC(SPEC `i:num` C1092WP_TARGET_HALF_DISTANCE) THEN
  MP_TAC(SPEC `i:num` C1092WP_TARGET_RECTANGLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `c:real`; `s:real`] C1092WPHY_TARGET_QUADRATIC_SUPPORT) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1092wp_targetX i`; `&2 - c1092wp_targetY i`; `c:real`; `s:real`]
    C1092WPHY_RECTANGLE_SUPPORT) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&2 * (&1 - c1092wp_targetX i)`;
                `&2 * (&2 - c1092wp_targetY i)`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `c1092wp_targetX i - &457 / &500`;
                `c1092wp_targetY i - &1`] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `X = lcx c s u v a` THEN ABBREV_TAC `Y = lcy c s u v a` THEN
  ABBREV_TAC `x = c1092wp_targetX i` THEN ABBREV_TAC `y = c1092wp_targetY i` THEN
  UNDISCH_TAC `linside c s u v a (&457 / &500) (&2)` THEN
  UNDISCH_TAC `~linside c s u v a (&457 / &500) (&1)` THEN
  REWRITE_TAC[linside] THEN DISCH_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  let prod tm = SUBGOAL_THEN tm ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] in
  prod `&0 <= c * (&1 - X)` THEN prod `&0 <= s * (&2 - Y)` THEN
  prod `&0 <= c * (&2 - Y)` THEN prod `&0 <= s * (x - &457 / &500)` THEN
  prod `&0 <= c * (&2 - y)` THEN
  SUBGOAL_THEN `&0 < c + s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `c = &0 /\ s = &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  prod `&0 < (a - &1) * (c + s)` THEN
  prod `&0 <= s * (c + s)` THEN
  prod `&0 < (a - &1) * (&1 + s * (c + s))` THEN
  SUBGOAL_THEN `s * (a * (c + s) / &2) <= s * X` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c * c * X + s * s * X = X` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c * &457 / &500 + s * &1 <= u \/ --s * &457 / &500 + c * &1 <= v`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
  [RASM_ARITH_TAC;
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [RASM_ARITH_TAC;
    prod `&0 <= c * ((c * x + s * y) - (c * X + s * Y + a / &2))` THEN
    prod `&0 <= s * ((--s * X + c * Y - a / &2) - (--s * &457 / &500 + c * &1))` THEN
    RASM_ARITH_TAC];
   RASM_ARITH_TAC;
   RASM_ARITH_TAC]);;

(* Lean: original_wall_point *)
let C1092WPHY_ORIGINAL_WALL_POINT = prove
 (`forall c s u v a i.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     ~linside c s u v a (&1) (&457 / &500) /\
     ~linside c s u v a (&457 / &500) (&1) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     lcy c s u v a <= &2 /\ i < 12
     ==> linside c s u v a (c1092wp_targetX i) (c1092wp_targetY i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `lcx c s u v a <= &1` THENL
  [ALL_TAC;
   MATCH_MP_TAC C1092WCC_ORIGINAL_RIGHT_BRANCH_POINT THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) then REWRITE_TAC[GSYM th]
                        else NO_TAC) THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
   DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_MESON_TAC[];
   STRIP_TAC] THEN
  MATCH_MP_TAC C1092WPHY_POSITIVE_FRAME_LEFT_POINT THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[]);;

(* Lean: singleton_wall_point_cover *)
let C1092WPHY_SINGLETON_WALL_POINT_COVER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\ lcont c s u v a /\
     c1092wphy_owns c s u v a 12 /\
     (forall j. j < 16 /\ ~(j = 12) ==> ~c1092wphy_owns c s u v a j)
     ==> (lcy c s u v a <= &2 /\
          forall i. i < 12 ==> linside c s u v a (c1092wp_targetX i) (c1092wp_targetY i)) \/
         (&2 <= lcy c s u v a /\
          forall i. i < 12 ==> linside c s u v a (c1092wp_targetX i)
                                           (&4 - c1092wp_targetY i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let miss k = FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o
                 check (fun th -> is_forall(concl th))) THEN
               REWRITE_TAC[c1092wphy_owns; MARKER_EXPLICIT; VECTOR_2; ARITH] THEN
               DISCH_TAC in
  miss 0 THEN miss 1 THEN miss 6 THEN miss 7 THEN miss 8 THEN miss 11 THEN
  UNDISCH_TAC `c1092wphy_owns c s u v a 12` THEN
  REWRITE_TAC[c1092wphy_owns; MARKER_EXPLICIT; VECTOR_2] THEN DISCH_TAC THEN
  ASM_CASES_TAC `lcy c s u v a <= &2` THENL
  [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC C1092WPHY_ORIGINAL_WALL_POINT THEN ASM_REWRITE_TAC[];
   DISJ2_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LINSIDE_PULLY] THEN
   MATCH_MP_TAC C1092WPHY_ORIGINAL_WALL_POINT THEN
   ASM_SIMP_TAC[LCONT_PULLY] THEN
   REWRITE_TAC[LINSIDE_PULLY] THEN
   CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN
   FIRST [FIRST_ASSUM ACCEPT_TAC;
          ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `~(lcy c s u v a <= &2)` THEN
          UNDISCH_TAC `c * c + s * s = &1` THEN
          REWRITE_TAC[lcy] THEN REAL_ARITH_TAC]]);;
