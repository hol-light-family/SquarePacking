(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/BorderPoints.lean.                         *)
(* Sound local rules for the conditional border-point deduction.            *)
(* center_coordinates is LCENTRE_COORDS; short_projections is               *)
(* WFP_SHORT_PROJECTIONS (WallForcedPoint.ml).  The packing square           *)
(* p.square i is the 5-tuple (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)  *)
(* (--b i * c1 i + a i * c2 i - l / &2) l (as in NPACK_LDISJ).               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/fs_bridge.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: border_missing_positive_face *)
let C977BP_BORDER_MISSING_POSITIVE_FACE = prove
 (`forall c s u v a t x y.
     c * c + s * s = &1 /\ &0 < a /\
     &0 <= c /\ &0 <= s /\ t <= x /\ y <= &1 /\
     linside c s u v a t y /\ linside c s u v a x (&1) /\ ~linside c s u v a t (&1)
     ==> v + a <= --s * t + c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `&1 - y`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`c:real`; `x - t:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`s:real`; `x - t:real`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_SUB_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: border_missing_negative_face *)
let C977BP_BORDER_MISSING_NEGATIVE_FACE = prove
 (`forall c s u v a t x y.
     c * c + s * s = &1 /\ &0 < a /\
     &0 <= c /\ s <= &0 /\ t <= x /\ y <= &1 /\
     linside c s u v a t y /\ linside c s u v a x (&1) /\ ~linside c s u v a t (&1)
     ==> c * t + s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--s:real`; `&1 - y`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`c:real`; `&1 - y`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`--s:real`; `x - t:real`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_SUB_LE; REAL_NEG_GE0] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: border_axial_forcing *)
let C977BP_BORDER_AXIAL_FORCING = prove
 (`forall c s u v a t x y.
     c * c + s * s = &1 /\ &0 < a /\
     &0 <= c /\ s = &0 /\ t <= x /\ y <= &1 /\
     linside c s u v a t y /\ linside c s u v a x (&1)
     ==> linside c s u v a t (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`; `x:real`; `y:real`]
    C977BP_BORDER_MISSING_POSITIVE_FACE) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  UNDISCH_TAC `linside c s u v a x (&1)` THEN ASM_REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: border_positive_center_bound *)
let C977BP_BORDER_POSITIVE_CENTER_BOUND = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ v + a <= --s * t + c
     ==> &1 / &2 < s * (lcx c s u v a - t) - c * (lcy c s u v a - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&1 < a` THEN UNDISCH_TAC `v + a <= --s * t + c` THEN
  REAL_ARITH_TAC);;

(* Lean: border_negative_center_bound *)
let C977BP_BORDER_NEGATIVE_CENTER_BOUND = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c * t + s <= u
     ==> &1 / &2 < c * (lcx c s u v a - t) + s * (lcy c s u v a - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&1 < a` THEN UNDISCH_TAC `c * t + s <= u` THEN
  REAL_ARITH_TAC);;

(* Lean: border_center_disk_inside *)
let C977BP_BORDER_CENTER_DISK_INSIDE = prove
 (`forall c s u v a x y.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ (x - lcx c s u v a) pow 2 + (y - lcy c s u v a) pow 2 <= &1 / &4
     ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&2 * (x - lcx c s u v a)`; `&2 * (y - lcy c s u v a)`]
    WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x - lcx c s u v a) pow 2 + (y - lcy c s u v a) pow 2 <= &1 / &4` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[linside] THEN UNDISCH_TAC `&1 < a` THEN REAL_ARITH_TAC);;

(* Lean: border_close_centers_overlap *)
let C977BP_BORDER_CLOSE_CENTERS_OVERLAP = prove
 (`forall cq sq uq vq aq cr sr ur vr ar.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     &1 < aq /\ &1 < ar /\
     (lcx cr sr ur vr ar - lcx cq sq uq vq aq) pow 2 +
     (lcy cr sr ur vr ar - lcy cq sq uq vq aq) pow 2 <= &1
     ==> exists x y. linside cq sq uq vq aq x y /\ linside cr sr ur vr ar x y`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(lcx cq sq uq vq aq + lcx cr sr ur vr ar) / &2` THEN
  EXISTS_TAC `(lcy cq sq uq vq aq + lcy cr sr ur vr ar) / &2` THEN
  CONJ_TAC THEN MATCH_MP_TAC C977BP_BORDER_CENTER_DISK_INSIDE THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* Lean: border_packing_center_distance *)
let C977BP_BORDER_PACKING_CENTER_DISTANCE = prove
 (`forall c1 c2 a b l i j.
     NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> &1 < (lcx (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l -
               lcx (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l) pow 2 +
              (lcy (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l -
               lcy (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `i:num`; `j:num`] NPACK_LDISJ) THEN
  ASM_REWRITE_TAC[ldisj] THEN REWRITE_TAC[GSYM NOT_EXISTS_THM; TAUT `~p ==> false <=> p`] THEN
  MATCH_MP_TAC C977BP_BORDER_CLOSE_CENTERS_OVERLAP THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] NPACK_SQ) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `j:num`] NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;
