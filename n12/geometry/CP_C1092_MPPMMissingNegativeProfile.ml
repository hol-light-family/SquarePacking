(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeProfile.lean           *)
(* (N12Compact.C1092MPPMMissingNegativeProfile).  MISSING-NEGATIVE-WALL-     *)
(* ORDER Lemma 1 and MISSING-NEGATIVE-BOUNDARIES Lemma 1.  Square C is      *)
(* c s u v a; the structures Core, Faces, WeakFaces, StrongFaces are the    *)
(* predicates c1092mnpg_core / _faces / _weak_faces / _strong_faces         *)
(* (WeakFaces/StrongFaces extend Faces as a conjunction).  Normal is        *)
(* c977cc_normal; half is C1092WPS_half; arc_gap / half_width are           *)
(* C1092MNP_ARC_GAP / C1092MNP_HALF_WIDTH.  Tag C1092MNPG_.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeProfileScalars.ml";;

(* Lean: Core (structure) *)
let c1092mnpg_core = new_definition
 `c1092mnpg_core c s u v a <=>
    linside c s u v a (--(&7) / &20) (--(&7) / &20) /\
    linside c s u v a (--(&1)) (--(&13) / &50) /\
    linside c s u v a (--(&1)) (--(&2) / &5) /\
    linside c s u v a (--(&1)) (--(&1) / &2) /\
    ~linside c s u v a (--(&1)) (--(&1)) /\
    ~linside c s u v a (--(&13) / &50) (&0) /\
    (forall x. --(&14 / &25) <= x ==> x <= --(&13 / &50) ==> ~linside c s u v a x (--(&1)))`;;

(* Lean: Faces (structure) *)
let c1092mnpg_faces = new_definition
 `c1092mnpg_faces c s u v a <=>
    s - c <= v /\
    u + a <= --s - (&14 / &25) * c /\
    v + a <= (&13 / &50) * s /\
    s < &0 /\
    C1092WPS_half c (--s) < &1`;;

(* Lean: WeakFaces (structure extending Faces) *)
let c1092mnpg_weak_faces = new_definition
 `c1092mnpg_weak_faces c s u v a <=>
    c1092mnpg_faces c s u v a /\
    --(&543 / &500) * c <= u /\
    a <= (&263 / &500) * c - s /\
    &237 / &763 < C1092WPS_half c (--s)`;;

(* Lean: StrongFaces (structure extending Faces) *)
let c1092mnpg_strong_faces = new_definition
 `c1092mnpg_strong_faces c s u v a <=>
    c1092mnpg_faces c s u v a /\
    --c <= u /\
    a <= (&11 / &25) * c - s /\
    &7 / &18 < C1092WPS_half c (--s)`;;

let C1092MNPG_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC]) tms;;

let C1092MNPG_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let C1092MNPG_UNFOLD_TAC tms =
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC) tms;;

let C1092MNPG_CORE_TAC =
  MP_TAC(ASSUME `c1092mnpg_core c s u v a`) THEN REWRITE_TAC[c1092mnpg_core] THEN STRIP_TAC THEN
  C1092MNPG_UNFOLD_TAC
   [`linside c s u v a (--(&7) / &20) (--(&7) / &20)`;
    `linside c s u v a (--(&1)) (--(&13) / &50)`;
    `linside c s u v a (--(&1)) (--(&2) / &5)`;
    `linside c s u v a (--(&1)) (--(&1) / &2)`] THEN
  PCT_NORMAL_TAC;;

let C1092MNPG_BAR_TAC x =
  FIRST_ASSUM(MP_TAC o SPEC x o check (fun th -> is_forall(concl th) &&
     length(fst(strip_forall(concl th))) = 1)) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC;;

(* Lean: bar_bands (private) *)
let C1092MNPG_BAR_BANDS = prove
 (`forall c s u v a x.
     c977cc_normal c (--s) /\ c1092mnpg_core c s u v a /\
     --(&14 / &25) <= x /\ x <= --(&13 / &50)
     ==> u < c * x - s /\ --s * x - c < v + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNPG_CORE_TAC THEN
  C1092MNPG_PROD_TAC [`&0 <= c * (x + &14 / &25)`; `&0 <= --s * (--(&13 / &50) - x)`] THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: point_caps (private) *)
let C1092MNPG_POINT_CAPS = prove
 (`forall c s u v a w.
     &1 < a /\ c977cc_normal c (--s) /\ c1092mnpg_core c s u v a /\
     &1 <= w /\ w <= &543 / &500 /\ ~linside c s u v a (--w) (&0)
     ==> s - c <= v /\ --w * c <= u /\ v + a <= (&13 / &50) * s /\
         u + a <= --s - (&13 / &50) * c /\ s < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--(&13 / &50)`]
    C1092MNPG_BAR_BANDS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MNPG_CORE_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s - c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNPG_MISS_TAC `~linside c s u v a (--(&1)) (--(&1))`; ALL_TAC] THEN
  C1092MNPG_PROD_TAC [`&0 <= (w - &1) * c`; `&0 <= (&543 / &500 - w) * --s`;
                      `&0 <= (w - &1) * --s`; `&0 <= c * (&543 / &500 - w)`] THEN
  SUBGOAL_THEN `--w * c <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v + a <= w * s` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MNPG_MISS_TAC `~linside c s u v a (--w) (&0)`; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&13 / &50) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u + a <= --(&13 / &50) * c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MNPG_MISS_TAC `~linside c s u v a (--(&13) / &50) (&0)`; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= --s - (&13 / &50) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNPG_BAR_TAC `--(&13 / &50)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

let C1092MNPG_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let C1092MNPG_POS_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

(* Lean: vertex (private) *)
let C1092MNPG_VERTEX = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     c977cc_normal c (--s) /\ c1092mnpg_core c s u v a /\ s < &0 /\
     u + a <= --s - (&13 / &50) * c /\ --s - (&14 / &25) * c < u + a
     ==> --(&1) <= c * v + s * (u + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--(&14 / &25)`]
    C1092MNPG_BAR_BANDS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MNPG_CORE_TAC THEN
  SUBGOAL_THEN `&0 < c /\ &0 < --s` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&14 / &25) * s - c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNPG_BAR_TAC `--(&14 / &25)`; ALL_TAC] THEN
  SUBGOAL_THEN `--s * ((v + c) / --s) = v + c /\ c * ((u + a + s) / c) = u + a + s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_DIV_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `f = (v + c) / --s` THEN ABBREV_TAC `uu = (u + a + s) / c` THEN
  SUBGOAL_THEN `--(&14 / &25) <= f` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= f + &14 / &25 ==> --(&14 / &25) <= f`) THEN
    MATCH_MP_TAC C1092MNPG_NONNEG_OF_MUL THEN EXISTS_TAC `--s` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uu <= --(&13 / &50)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= --(&13 / &50) - uu ==> uu <= --(&13 / &50)`) THEN
    MATCH_MP_TAC C1092MNPG_NONNEG_OF_MUL THEN EXISTS_TAC `c:real` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c * --s * (uu - f) = --s * (u + a) - c * v - &1` ASSUME_TAC THENL
   [UNDISCH_TAC `--s * f = v + c` THEN UNDISCH_TAC `c * uu = u + a + s` THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `f < uu` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < uu - f ==> f < uu`) THEN
    MATCH_MP_TAC C1092MNPG_POS_OF_MUL THEN EXISTS_TAC `c * --s` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `(f + uu) / &2`]
    C1092MNPG_BAR_BANDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  C1092MNPG_PROD_TAC [`&0 < --s * ((f + uu) / &2 - f)`; `&0 < c * (uu - (f + uu) / &2)`] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(f + uu) / &2` o check (fun th -> is_forall(concl th) &&
     length(fst(strip_forall(concl th))) = 1)) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: profile_aux (private) *)
let C1092MNPG_PROFILE_AUX = prove
 (`forall c s u v a w.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c (--s) /\ c1092mnpg_core c s u v a /\
     &1 <= w /\ w <= &543 / &500 /\ ~linside c s u v a (--w) (&0)
     ==> c1092mnpg_faces c s u v a /\ --w * c <= u /\ a <= (w - &14 / &25) * c - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `w:real`]
    C1092MNPG_POINT_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c /\ &0 < --s` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= --s - (&14 / &25) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MNPG_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `--s`] C1092MNP_ARC_GAP) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    C1092MNPG_PROD_TAC
     [`&0 <= c * ((&13 / &50) * s - (v + a))`;
      `&0 <= --s * (u - --w * c)`;
      `&0 <= c * --s`;
      `&0 <= (c * --s) * (&543 / &500 - w)`;
      `&0 < (a - &1) * (c - s)`] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `a <= (w - &14 / &25) * c - s` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s`; `w - &14 / &25`] C1092MNP_HALF_WIDTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[c1092mnpg_faces]);;

(* Lean: weak_profile *)
let C1092MNPG_WEAK_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c (--s) /\ c1092mnpg_core c s u v a /\
     ~linside c s u v a (--(&543 / &500)) (&0)
     ==> c1092mnpg_weak_faces c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&543 / &500`]
    C1092MNPG_PROFILE_AUX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s`; `&263 / &500`] C1092MNP_HALF_WIDTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[c1092mnpg_weak_faces] THEN RASM_ARITH_TAC);;

(* Lean: strong_profile *)
let C1092MNPG_STRONG_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c (--s) /\ c1092mnpg_core c s u v a /\
     ~linside c s u v a (--(&1)) (&0)
     ==> c1092mnpg_strong_faces c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1`]
    C1092MNPG_PROFILE_AUX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s`; `&11 / &25`] C1092MNP_HALF_WIDTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[c1092mnpg_strong_faces] THEN RASM_ARITH_TAC);;
