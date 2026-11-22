(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShallowBoundarySupport.lean              *)
(* (N12Compact.C1092ShallowBoundarySupport).  Actual-square boundary         *)
(* support bounds for the shallow wall order.                                *)
(* The square Q is (cq, sq, uq, vq, aq).  supportRadius / squareRadius are   *)
(* tss_support_radius; lower / upper are ABT_lower / ABT_upper;              *)
(* S12.square_support_bound is C1092MPWS_SQUARE_SUPPORT_BOUND; Normal is     *)
(* c977cc_normal; ShallowWidths.signed_widths is C1092SW_SIGNED_WIDTHS.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShallowWidths.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_C1092_MMMP_PhysicalWallSupport.ml";;

(* Lean: width0 (definition) *)
let c1092sbs_width0 = new_definition
 `c1092sbs_width0 (cq:real) (sq:real) = abs cq + abs sq`;;

(* Lean: FaceNormal (definition) *)
let c1092sbs_FaceNormal = new_definition
 `c1092sbs_FaceNormal (cq:real) (sq:real) (nx:real) (ny:real) <=>
    (nx = cq /\ ny = sq) \/ (nx = --cq /\ ny = --sq) \/
    (nx = --sq /\ ny = cq) \/ (nx = sq /\ ny = --cq)`;;

(* Lean: bottom_center *)
let C1092SBS_BOTTOM_CENTER = prove
 (`forall cq sq uq vq aq.
     cq * cq + sq * sq = &1 /\ &0 < aq /\
     (forall x y. linside cq sq uq vq aq x y ==> -- &2 <= y)
     ==> -- &2 + aq * c1092sbs_width0 cq sq / &2 <= lcy cq sq uq vq aq`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                `&0`; `-- &1`; `&2`] C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[tss_support_radius; c1092sbs_width0] THEN
  REWRITE_TAC[REAL_ARITH `abs(&0 * c + -- &1 * s) = abs s /\
                          abs(--(&0) * s + -- &1 * c) = abs c`] THEN
  REAL_ARITH_TAC);;

(* Lean: left_center *)
let C1092SBS_LEFT_CENTER = prove
 (`forall cq sq uq vq aq.
     cq * cq + sq * sq = &1 /\ &0 < aq /\
     (forall x y. linside cq sq uq vq aq x y ==> -- &2 <= x)
     ==> -- &2 + aq * c1092sbs_width0 cq sq / &2 <= lcx cq sq uq vq aq`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`;
                `-- &1`; `&0`; `&2`] C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[tss_support_radius; c1092sbs_width0] THEN
  REWRITE_TAC[REAL_ARITH `abs(-- &1 * c + &0 * s) = abs c /\
                          abs(--(-- &1) * s + &0 * c) = abs s`] THEN
  REAL_ARITH_TAC);;

(* Lean: width_bounds *)
let C1092SBS_WIDTH_BOUNDS = prove
 (`forall cq sq (uq:real) (vq:real) aq c s.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ c977cc_normal c s
     ==> aq * (&1 + c * (c + s)) / &2 <=
           c * (aq * c1092sbs_width0 cq sq / &2) + tss_support_radius cq sq aq (--s) c /\
         aq * (&1 + s * (c + s)) / &2 <=
           s * (aq * c1092sbs_width0 cq sq / &2) + tss_support_radius cq sq aq (--s) c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `cq:real`; `sq:real`] C1092SW_SIGNED_WIDTHS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  REWRITE_TAC[tss_support_radius; c1092sbs_width0] THEN
  REWRITE_TAC[REAL_ARITH `abs(--s * cq + c * sq) = abs(c * sq - s * cq) /\
                          abs(-- --s * sq + c * cq) = abs(c * cq + s * sq)`] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`aq / &2`; `&1 + c * (c + s)`;
      `c * (abs cq + abs sq) + abs(c * sq - s * cq) + abs(c * cq + s * sq)`] REAL_LE_LMUL);
    MP_TAC(SPECL [`aq / &2`; `&1 + s * (c + s)`;
      `s * (abs cq + abs sq) + abs(c * sq - s * cq) + abs(c * cq + s * sq)`] REAL_LE_LMUL)] THEN
  (ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]));;

(* Lean: face_width *)
let C1092SBS_FACE_WIDTH = prove
 (`forall cq sq nx ny. c1092sbs_FaceNormal cq sq nx ny
     ==> c1092sbs_width0 cq sq = abs nx + abs ny`,
  REWRITE_TAC[c1092sbs_FaceNormal; c1092sbs_width0] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG] THEN REAL_ARITH_TAC);;

(* Lean: radius_neg (private) *)
let C1092SBS_RADIUS_NEG = prove
 (`forall cq sq aq nx ny.
     tss_support_radius cq sq aq (--nx) (--ny) = tss_support_radius cq sq aq nx ny`,
  REWRITE_TAC[tss_support_radius] THEN
  REWRITE_TAC[REAL_ARITH `--nx * c + --ny * s = --(nx * c + ny * s) /\
                          -- --nx * s + --ny * c = --(--nx * s + ny * c)`; REAL_ABS_NEG]);;

(* Lean: face_radius *)
let C1092SBS_FACE_RADIUS = prove
 (`forall cq sq aq nx ny.
     cq * cq + sq * sq = &1 /\ c1092sbs_FaceNormal cq sq nx ny
     ==> tss_support_radius cq sq aq nx ny = aq / &2`,
  REWRITE_TAC[c1092sbs_FaceNormal] THEN REPEAT STRIP_TAC THEN
  (SUBGOAL_THEN `sq * sq + cq * cq = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[tss_support_radius] THEN
  REWRITE_TAC[REAL_ARITH `--cq * cq + --sq * sq = --(cq * cq + sq * sq) /\
                          -- --cq * sq + --sq * cq = &0 /\
                          --cq * sq + sq * cq = &0 /\
                          --sq * cq + cq * sq = &0 /\
                          -- --sq * sq + cq * cq = cq * cq + sq * sq /\
                          sq * cq + --cq * sq = &0 /\
                          --sq * sq + --cq * cq = --(cq * cq + sq * sq)`] THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

(* Lean: bottom_face *)
let C1092SBS_BOTTOM_FACE = prove
 (`forall cq sq uq vq aq h t.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ &0 <= h /\ &0 <= t /\
     (forall x y. linside cq sq uq vq aq x y ==> -- &2 <= y) /\
     c1092sbs_FaceNormal cq sq (--h) t
     ==> --h * lcx cq sq uq vq aq - &2 * t + (aq / &2) * (&1 + t pow 2 + h * t) <=
         ABT_upper cq sq uq vq aq (--h) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `--h`; `t:real`] C1092SBS_FACE_WIDTH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_NEG; REAL_ARITH `&0 <= x ==> abs x = x`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `aq:real`; `--h`; `t:real`] C1092SBS_FACE_RADIUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] C1092SBS_BOTTOM_CENTER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[ABT_upper] THEN
  MP_TAC(SPECL [`t:real`; `lcy cq sq uq vq aq - (-- &2 + aq * (h + t) / &2)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: left_face *)
let C1092SBS_LEFT_FACE = prove
 (`forall cq sq uq vq aq r d.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ &0 <= r /\ &0 <= d /\
     (forall x y. linside cq sq uq vq aq x y ==> -- &2 <= x) /\
     c1092sbs_FaceNormal cq sq (--r) d
     ==> ABT_lower cq sq uq vq aq (--r) d <=
         &2 * r + d * lcy cq sq uq vq aq - (aq / &2) * (&1 + r pow 2 + r * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `--r`; `d:real`] C1092SBS_FACE_WIDTH) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_NEG; REAL_ARITH `&0 <= x ==> abs x = x`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `aq:real`; `--r`; `d:real`] C1092SBS_FACE_RADIUS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] C1092SBS_LEFT_CENTER) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[ABT_lower] THEN
  MP_TAC(SPECL [`r:real`; `lcx cq sq uq vq aq - (-- &2 + aq * (r + d) / &2)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;
