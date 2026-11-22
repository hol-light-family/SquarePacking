(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/MissingCornerBounds.lean.                  *)
(* Conventions of MissingCornerPoints.ml.  CornerBandAlternative r is        *)
(* c977mcb_cba r, CanonicalCornerBounds q is c977mcb_ccb q (the witness r is *)
(* an OpenSquare: unit normal and positive side are part of the existential).*)
(* S12.exists_positive_frame is WCB_EXISTS_POSITIVE_FRAME,                   *)
(* S12.positive_frame_wall_bounds is C977WC_POSITIVE_FRAME_WALL_BOUNDS.      *)
(* Tag C977MCB_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/MissingCornerPoints.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/geometry/C977WallChains.ml";;

(* Lean: high_normal_wall_bound *)
let C977MCB_HIGH_NORMAL_WALL_BOUND = prove
 (`forall c s. &0 <= c /\ c <= &12 / &25 /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> c pow 2 + (&457 / &500) * s pow 2 + c * s <= c + s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c * (&12 / &25 - c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * c <= (&12 / &25) * (&12 / &25)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `s <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&87 / &100 <= s` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(s < x) ==> x <= s`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s * (&87 / &100 - s)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - s) * ((&27 / &50) * (&1 + s) - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s - (&1 - (&27 / &50) * c * c)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * (s - (&1 - (&27 / &50) * c * c))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&313 / &500) * (c + &12 / &25) -
      (&27 / &50) * (c * c + (&12 / &25) * c + (&12 / &25) * (&12 / &25))` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&12 / &25 - c) * ((&313 / &500) * (c + &12 / &25) -
      (&27 / &50) * (c * c + (&12 / &25) * c + (&12 / &25) * (&12 / &25)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lower_face_cos_bound *)
let C977MCB_LOWER_FACE_COS_BOUND = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &1 < s + (&43 / &500) * c
     ==> c < &43000 / &251849`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (s + (&43 / &500) * c - &1) * (s + &1 - (&43 / &500) * c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * (&43000 / &251849 - c)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `~(x <= c) ==> c < x`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `c * (&43000 / &251849 - c) <= &0` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= c * (c - x) ==> c * (x - c) <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Lean: CornerBandAlternative *)
let c977mcb_cba = new_definition
 `c977mcb_cba (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    (&12 / &25 < c /\ u + a <= &2 * c + (&457 / &500) * s) \/
    (c < &43000 / &251849 /\ (&457 / &500) * c - &2 * s <= v)`;;

(* Lean: CornerBandAlternative.cosine_gap *)
let C977MCB_COSINE_GAP = prove
 (`forall c s u v a. c977mcb_cba c s u v a ==> ~(&43000 / &251849 <= c /\ c <= &12 / &25)`,
  REWRITE_TAC[c977mcb_cba] THEN REAL_ARITH_TAC);;

(* Lean: CanonicalCornerBounds *)
let c977mcb_ccb = new_definition
 `c977mcb_ccb (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
      a' = a /\ lcx c' s' u' v' a' = lcx c s u v a /\ lcy c' s' u' v' a' = lcy c s u v a /\
      (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
      &0 < c' /\ &0 < s' /\ v' + a' <= c' - s' /\ c977mcb_cba c' s' u' v' a'`;;

(* the positive-frame part of canonical_corner_bounds_of_anchors *)
let C977MCB_POSITIVE_FRAME_CORE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 <= s /\
     &0 <= s * u + c * v /\
     linside c s u v a (&1) (&457 / &500) /\ linside c s u v a (&28 / &25) (&1) /\
     ~linside c s u v a (&1) (&1) /\ ~linside c s u v a (&2) (&457 / &500)
     ==> &0 < c /\ &0 < s /\ v + a <= c - s /\ c977mcb_cba c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977mcb_cba] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `linside c s u v a (&1) (&457 / &500)`) THEN
  MP_TAC(ASSUME `linside c s u v a (&28 / &25) (&1)`) THEN
  REWRITE_TAC[linside] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v + a <= c - s` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(c - s < v + a) ==> v + a <= c - s`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `linside c s u v a (&1) (&1)` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&2 * c + (&457 / &500) * s < u + a` THENL
   [DISJ2_TAC THEN
    SUBGOAL_THEN `(&457 / &500) * c - &2 * s <= v` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(v < x) ==> x <= v`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `linside c s u v a (&2) (&457 / &500)` (fun th -> ASM_MESON_TAC[th]) THEN
      REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C977MCB_LOWER_FACE_COS_BOUND THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[REAL_POW_2] THEN NLIN_TAC ~deg2:false [];
    DISJ1_TAC THEN
    SUBGOAL_THEN `u + a <= &2 * c + (&457 / &500) * s` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `~(c <= x) ==> x < c`) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`] C977MCB_HIGH_NORMAL_WALL_BOUND) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s * ((&2 * c + (&457 / &500) * s) - (u + a))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= c * ((c - s) - (v + a))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (a - &1) * (c + s)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: canonical_corner_bounds_of_anchors *)
let C977MCB_CANONICAL_CORNER_BOUNDS_OF_ANCHORS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ lcont c s u v a /\ linside c s u v a (&1) (&457 / &500) /\
     c977mcg_anchors c s u v a /\ ~linside c s u v a (&1) (&1) /\
     ~linside c s u v a (&2) (&457 / &500)
     ==> c977mcb_ccb c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977mcg_anchors] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN `u':real`
    (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real` STRIP_ASSUME_TAC))))) THEN
  UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[c977mcb_ccb] THEN
  MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C977MCB_POSITIVE_FRAME_CORE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_SIMP_TAC[];
    REWRITE_TAC[lcy] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN REAL_ARITH_TAC]);;

(* Lean: canonical_corner_bounds *)
let C977MCB_CANONICAL_CORNER_BOUNDS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     c977mcp_strengthened c s u v a /\ ~linside c s u v a (&2) (&457 / &500)
     ==> c977mcb_ccb c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977mcp_strengthened; c977cr_mce] THEN STRIP_TAC THEN
  MATCH_MP_TAC C977MCB_CANONICAL_CORNER_BOUNDS_OF_ANCHORS THEN ASM_REWRITE_TAC[]);;

let C977MCB_SQ_TAC =
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: code_one_missing_corner_bounds *)
let C977MCB_CODE_ONE_MISSING_CORNER_BOUNDS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
     c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                          (--b i * c1 i + a i * c2 i - l / &2) l
     ==> c977mcb_ccb (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                     (--b i * c1 i + a i * c2 i - l / &2) l`,
  REPEAT STRIP_TAC THEN C977MCB_SQ_TAC THEN
  MATCH_MP_TAC C977MCB_CANONICAL_CORNER_BOUNDS THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_CODE_ONE_EXACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `13`) THEN
  REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2; IN_SING] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* Lean: code_two_missing_corner_bounds *)
let C977MCB_CODE_TWO_MISSING_CORNER_BOUNDS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 2 /\
     c977mcp_strengthened (b i) (a i) (a i * c1 i + b i * c2 i - l / &2)
                          (--(--b i * c1 i + a i * c2 i - l / &2) - l) l
     ==> c977mcb_ccb (b i) (a i) (a i * c1 i + b i * c2 i - l / &2)
                     (--(--b i * c1 i + a i * c2 i - l / &2) - l) l`,
  REPEAT STRIP_TAC THEN C977MCB_SQ_TAC THEN
  MATCH_MP_TAC C977MCB_CANONICAL_CORNER_BOUNDS THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[LINSIDE_PULLSW]] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_CODE_TWO_EXACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `12`) THEN
  REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2; IN_SING] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

(* Lean: bounded_missing_corner_cover *)
let C977MCB_BOUNDED_MISSING_CORNER_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
               ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               ((c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                                      (--b i * c1 i + a i * c2 i - l / &2) l /\
                 c977mcb_ccb (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                             (--b i * c1 i + a i * c2 i - l / &2) l) \/
                (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                         (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
                 c977mcp_strengthened (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                                      (--(--b j * c1 j + a j * c2 j - l / &2) - l) l /\
                 c977mcb_ccb (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                             (--(--b j * c1 j + a j * c2 j - l / &2) - l) l))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977MCP_MISSING_CORNER_STRENGTHENING_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN MATCH_MP_TAC C977MCB_CODE_ONE_MISSING_CORNER_BOUNDS;
    DISJ2_TAC THEN MATCH_MP_TAC C977MCB_CODE_TWO_MISSING_CORNER_BOUNDS] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: retained_bounded_missing_corner_cover *)
let C977MCB_RETAINED_BOUNDED_MISSING_CORNER_COVER = prove
 (`forall r. r < 577 /\ MEM (EL r COVER_IDS) EXPECTED_IDS /\ EL r COVER_IDS = 977
     ==> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL r ROWS)
     ==> exists i j. i < 12 /\ j < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 1 /\
               ownmask (c1 j) (c2 j) (a j) (b j) l = 2 /\ ~(i = j) /\
               ((c977mcp_strengthened (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                                      (--b i * c1 i + a i * c2 i - l / &2) l /\
                 c977mcb_ccb (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                             (--b i * c1 i + a i * c2 i - l / &2) l) \/
                (linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                         (--b i * c1 i + a i * c2 i - l / &2) l (&1) (&1) /\
                 c977mcp_strengthened (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                                      (--(--b j * c1 j + a j * c2 j - l / &2) - l) l /\
                 c977mcb_ccb (b j) (a j) (a j * c1 j + b j * c2 j - l / &2)
                             (--(--b j * c1 j + a j * c2 j - l / &2) - l) l))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977MCB_BOUNDED_MISSING_CORNER_COVER THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `set_of_list (EL r ROWS)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CCC977RI_ROW_FAMILY THEN ASM_REWRITE_TAC[]);;
