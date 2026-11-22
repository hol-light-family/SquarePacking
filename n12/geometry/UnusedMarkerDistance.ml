(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/UnusedMarkerDistance.lean.                 *)
(* Conventions of WallBranches.ml: p.square i is the 5-tuple                 *)
(*   (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)                          *)
(*   (--b i * c1 i + a i * c2 i - l / &2) l,                                 *)
(* p.commonSide (= its side by p.congruent) is l, centerX / centerY are      *)
(* lcx / lcy.  Tag C977UMD_.                                                 *)
(* ========================================================================= *)

needs "n12/geometry/WallBranches.ml";;

let C977UMD_ROT = prove
 (`forall c s dx dy. c * c + s * s = &1
     ==> (c * dx + s * dy) pow 2 + (--s * dx + c * dy) pow 2 = dx pow 2 + dy pow 2`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

let C977UMD_BAND = prove
 (`forall p q u v a. &0 < a /\ ~(u < p /\ p < u + a /\ v < q /\ q < v + a)
     ==> a pow 2 / &4 <= (p - (u + a / &2)) pow 2 + (q - (v + a / &2)) pow 2`,
  REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)) THEN
  NLIN_TAC [SQ_NONNEG `p - (u + a / &2)`; SQ_NONNEG `q - (v + a / &2)`]);;

(* Lean: outside_center_distance *)
let C977UMD_OUTSIDE_CENTER_DISTANCE = prove
 (`forall c s u v a x y.
     c * c + s * s = &1 /\ &0 < a /\ ~linside c s u v a x y
     ==> a pow 2 / &4 <= (x - lcx c s u v a) pow 2 + (y - lcy c s u v a) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `x - lcx c s u v a`; `y - lcy c s u v a`] C977UMD_ROT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH `c * (x - X) + s * (y - Y) = (c * x + s * y) - (c * X + s * Y)`;
              REAL_ARITH `--s * (x - X) + c * (y - Y) = (--s * x + c * y) - (--s * X + c * Y)`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC C977UMD_BAND THEN ASM_REWRITE_TAC[GSYM linside]);;

let C977UMD_MARKER10 = prove
 (`marker 10$1 = &47 / &20 /\ marker 10$2 = &47 / &20`,
  REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2]);;

(* Lean: unused_marker_center_distance *)
let C977UMD_UNUSED_MARKER_CENTER_DISTANCE = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12
     ==> l pow 2 / &4 <=
         (&47 / &20 - lcx (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                          (--b i * c1 i + a i * c2 i - l / &2) l) pow 2 +
         (&47 / &20 - lcy (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                          (--b i * c1 i + a i * c2 i - l / &2) l) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977UMD_OUTSIDE_CENTER_DISTANCE THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977WB_UNUSED_MARKER_TEN) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    NPACK_SQ) THEN
  ASM_REWRITE_TAC[C977UMD_MARKER10] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: unused_marker_center_distance_strict *)
let C977UMD_UNUSED_MARKER_CENTER_DISTANCE_STRICT = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12
     ==> &1 / &4 <
         (&47 / &20 - lcx (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                          (--b i * c1 i + a i * c2 i - l / &2) l) pow 2 +
         (&47 / &20 - lcy (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                          (--b i * c1 i + a i * c2 i - l / &2) l) pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977UMD_UNUSED_MARKER_CENTER_DISTANCE) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`(&47 / &20 - lcx (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                          (--b i * c1 i + a i * c2 i - l / &2) l) pow 2 +
         (&47 / &20 - lcy (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                          (--b i * c1 i + a i * c2 i - l / &2) l) pow 2`, `d:real`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 < l pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT_1 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ASM_REAL_ARITH_TAC]);;
