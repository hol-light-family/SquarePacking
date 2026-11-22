(* ========================================================================= *)
(* Port of Compact/Geometry/MidpointSection.lean (Jatloe, N12-jatloe).        *)
(* A unit vertical span forces a closed unit horizontal segment of strict    *)
(* interior points at its midpoint height.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/SectionCapacity.ml";;

(* Lean: UnitSection (definition) *)
let mps_unit_section = new_definition
 `mps_unit_section (c:real) s u v a h <=>
    exists z. forall d. abs d <= &1 / &2 ==> linside c s u v a (z + d) h`;;

(* Lean: positive_height_bounds (private) *)
let MPS_POSITIVE_HEIGHT_BOUNDS = prove
 (`forall c s u v a x y. c * c + s * s = &1 /\ &0 < c /\ &0 <= s /\
                   linside c s u v a x y
     ==> --a * (c + s) / &2 < y - lcy c s u v a /\
         y - lcy c s u v a < a * (c + s) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    LCENTRE_COORDS) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `linside c s u v a x y` THEN REWRITE_TAC[linside] THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `--(a / &2) < c * (x - X) + s * (y - Y) /\
                c * (x - X) + s * (y - Y) < a / &2 /\
                --(a / &2) < --s * (x - X) + c * (y - Y) /\
                --s * (x - X) + c * (y - Y) < a / &2` MP_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `y - Y = s * (c * (x - X) + s * (y - Y)) +
                        c * (--s * (x - X) + c * (y - Y))` MP_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SPEC_TAC(`c * (x - X) + s * (y - Y)`,`U:real`) THEN
  SPEC_TAC(`--s * (x - X) + c * (y - Y)`,`V:real`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  CONJ_TAC THEN NLIN_TAC []);;

(* Lean: scalar_unit_section  (InBands lo lo a p q written out) *)
let MPS_SCALAR_UNIT_SECTION = prove
 (`forall a c s t. &1 < a /\ &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
             &2 * abs t < a * (c + s) - &2 * c * s
     ==> exists z. forall d. abs d <= &1 / &2
           ==> --a / &2 < c * (z + d) + s * t /\
               c * (z + d) + s * t < --a / &2 + a /\
               --a / &2 < --s * (z + d) + c * t /\
               --s * (z + d) + c * t < --a / &2 + a`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a * (c + s) - &2 * c * s` ASSUME_TAC THENL
  [MP_TAC(SPEC `t:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists lam. lam * (a * (c + s) - &2 * c * s) = t` STRIP_ASSUME_TAC THENL
  [EXISTS_TAC `t / (a * (c + s) - &2 * c * s)` THEN
   ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  UNDISCH_TAC `&2 * abs t < a * (c + s) - &2 * c * s` THEN
  REWRITE_TAC[REAL_ARITH `&2 * abs t < D <=> --D < &2 * t /\ &2 * t < D`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `--(&1 / &2) < lam /\ lam < &1 / &2` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  EXISTS_TAC `c * (a - c) * lam - s * (a - s) * lam` THEN
  X_GEN_TAC `d:real` THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c * ((c * (a - c) * lam - s * (a - s) * lam) + d) + s * t =
      (a - c) * lam + c * d /\
    --s * ((c * (a - c) * lam - s * (a - s) * lam) + d) + c * t =
      (a - s) * lam - s * d`
  (fun th -> REWRITE_TAC[th]) THENL
  [UNDISCH_TAC `lam * (a * (c + s) - &2 * c * s) = t` THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < a - c /\ &0 < a - s` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: positive_span *)
let MPS_POSITIVE_SPAN = prove
 (`forall c s u v a x0 x1 h d.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\
     linside c s u v a x0 (h - d / &2) /\ linside c s u v a x1 (h + d / &2) /\
     &2 * c * s <= d
     ==> mps_unit_section c s u v a h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `x0:real`; `h - d / &2`] MPS_POSITIVE_HEIGHT_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `x1:real`; `h + d / &2`] MPS_POSITIVE_HEIGHT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `c:real`; `s:real`; `h - lcy c s u v a`]
    MPS_SCALAR_UNIT_SECTION) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN ANTS_TAC THENL
  [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_ARITH `&2 * abs t < D <=> --D < &2 * t /\ &2 * t < D`] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real`) THEN
  REWRITE_TAC[mps_unit_section] THEN EXISTS_TAC `lcx c s u v a + z` THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[linside] THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REAL_ARITH_TAC);;

(* Lean: of_unit_span *)
let MPS_OF_UNIT_SPAN = prove
 (`forall c s u v a x0 x1 h.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a x0 (h - &1 / &2) /\ linside c s u v a x1 (h + &1 / &2)
     ==> mps_unit_section c s u v a h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`;
                `x0:real`; `x1:real`; `h:real`; `&1`] MPS_POSITIVE_SPAN) THEN
  ASM_REWRITE_TAC[mps_unit_section] THEN ANTS_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c' - s':real`]; ALL_TAC] THEN
  REWRITE_TAC[]);;

(* Lean: grid_hit *)
let MPS_GRID_HIT = prove
 (`forall c s u v a h. lcont c s u v a /\ mps_unit_section c s u v a h
     ==> exists j. j < 3 /\ linside c s u v a (&j + &1) h`,
  REWRITE_TAC[lcont; mps_unit_section] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `forall k. z - &1 / &2 <= k /\ k <= z + &1 / &2
                    ==> linside c s u v a k h` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `k - z:real`) THEN
   REWRITE_TAC[REAL_ARITH `z + (k - z) = k:real`] THEN
   DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z - &1 / &2 /\ z + &1 / &2 <= &4` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [SUBGOAL_THEN `linside c s u v a (z - &1 / &2) h` MP_TAC;
    SUBGOAL_THEN `linside c s u v a (z + &1 / &2) h` MP_TAC] THEN
   (ANTS_TAC THENL [ALL_TAC; ALL_TAC] ORELSE ALL_TAC) THEN
   (CONJ_TAC ORELSE ALL_TAC) THEN
   TRY(FIRST_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC) THEN
   DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  let tac n = EXISTS_TAC n THEN
    CONV_TAC(NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC in
  ASM_CASES_TAC `z - &1 / &2 <= &1` THENL [tac `0`; ALL_TAC] THEN
  ASM_CASES_TAC `z - &1 / &2 <= &2` THENL [tac `1`; tac `2`]);;
