(* ========================================================================= *)
(* Port of Compact/Completion/C981/OppositeOffset.lean                        *)
(* (N12Compact.C981CompletionOppositeOffset).  The inward owner's small      *)
(* lower-face offset in the final C981 pair.  OpenSquare A is (c,s,u,v,a)     *)
(* with c*c+s*s = 1 and 0 < a; inside_segment is CES_INSIDE_SEGMENT,         *)
(* short_projections is WFP_SHORT_PROJECTIONS, affine_endpoint_nonnegative is *)
(* SCAP_AFFINE_ENDPOINT_NONNEG and inside_iff_rotated_box is TSS_INSIDE_FACE.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

let C981OO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

let C981OO_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  STRIP_TAC;;

let C981OO_POS_OF_MUL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: components (private) *)
let C981OO_COMPONENTS = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &50 / &37 < c + s
     ==> &23 / &50 < c /\ &23 / &50 < s`,
  SUBGOAL_THEN `forall x y. &0 <= x /\ &0 <= y /\ x pow 2 + y pow 2 = &1 /\ &50 / &37 < x + y
                ==> &23 / &50 < x` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C981OO_PROD `&0 < (y - (&27 / &20 - x)) * (y + (&27 / &20 - x))` THEN
   C981OO_PROD `&0 <= (&23 / &50 - x) * (&27 / &10 - &2 * (x + &23 / &50))` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
  [EXISTS_TAC `s:real`; EXISTS_TAC `c:real`] THEN ASM_REAL_ARITH_TAC);;

(* Lean: vertex_margin (private) *)
let C981OO_VERTEX_MARGIN = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &50 / &37 < c + s
     ==> &0 < (&17 / &500) * c + (&13 / &50) * s pow 2 - (&1 - c) * (&1 - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981OO_COMPONENTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  MATCH_MP_TAC C981OO_POS_OF_MUL THEN EXISTS_TAC `&1 + c` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s <= &3 / &5` THENL
  [SUBGOAL_THEN `(&1 + c) * ((&17 / &500) * c + (&13 / &50) * s * s - (&1 - c) * (&1 - s)) =
                 (&1 + c) * ((&17 / &500) * c - (&1 / &25) * s * s) +
                 (s * s) * ((&3 / &10) * (&1 + c) - (&1 - s))` SUBST1_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   C981OO_PROD `&0 <= (&3 / &5 - s) * (&3 / &5 + s)` THEN
   SUBGOAL_THEN `&4 / &5 <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C981OO_PROD `&0 < (&4 / &5 - c) * (&4 / &5 + c)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C981OO_PROD `&0 < (&1 + c) * ((&17 / &500) * c - (&1 / &25) * s * s)` THEN
   C981OO_PROD `&0 <= (s * s) * ((&3 / &10) * (&1 + c) - (&1 - s))` THEN
   ASM_REAL_ARITH_TAC;
   SUBGOAL_THEN `&0 <= s + (&13 / &50) * c - &37 / &50` ASSUME_TAC THENL
   [ASM_CASES_TAC `&37 / &50 <= s` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    C981OO_PROD `&0 <= (&37 / &50 - s) * (&37 / &50 + s)` THEN
    SUBGOAL_THEN `&67 / &100 <= c` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C981OO_PROD `&0 < (&67 / &100 - c) * (&67 / &100 + c)` THEN ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 + c) * ((&17 / &500) * c + (&13 / &50) * s * s - (&1 - c) * (&1 - s)) =
                 (&17 / &500) * c * (&1 + c) + (s * s) * (s + (&13 / &50) * c - &37 / &50)`
   SUBST1_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   C981OO_PROD `&0 < c * (&1 + c)` THEN
   C981OO_PROD `&0 <= (s * s) * (s + (&13 / &50) * c - &37 / &50)` THEN
   ASM_REAL_ARITH_TAC]);;

let C981OO_PROJECTION = prove
 (`forall X Y. X * X + Y * Y = &2669 / &2500 ==> X < &517 / &500`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&517 / &500 * &517 / &500 <= X * X` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `Y:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC);;

(* Lean: bounds *)
let C981OO_BOUNDS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\
     linside c s u v a (&0) (&13 / &50) /\ linside c s u v a (&13 / &50) (&0) /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&13 / &50) (&1) /\
     (forall y. &13 / &50 <= y /\ y <= &4 / &5 ==> ~linside c s u v a (&1) y)
     ==> &0 < s /\ &0 <= u /\ u < &17 / &500`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C981OO_UNFOLD_TAC `linside c s u v a (&0) (&13 / &50)` THEN
  C981OO_UNFOLD_TAC `linside c s u v a (&13 / &50) (&0)` THEN
  C981OO_UNFOLD_TAC `linside c s u v a (&7 / &20) (&7 / &20)` THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (&0) (&0)` THEN REWRITE_TAC[linside] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&13 / &50 * c + s`; `c - &13 / &50 * s`] C981OO_PROJECTION) THEN
  MP_TAC(SPECL [`c + &13 / &50 * s`; `&13 / &50 * c - s`] C981OO_PROJECTION) THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; DISCH_TAC] THEN
  ANTS_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; DISCH_TAC] THEN
  SUBGOAL_THEN `v + a <= c - &13 / &50 * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (&13 / &50) (&1)` THEN REWRITE_TAC[linside] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s + &13 / &50 * c <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `&13 / &50`) THEN REWRITE_TAC[linside] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&50 / &37 < c + s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981OO_COMPONENTS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981OO_VERTEX_MARGIN) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C981OO_PROD `&0 <= s * ((c - &13 / &50 * s) - (v + a))` THEN
  C981OO_PROD `&0 <= c * (u - &17 / &500)` THEN
  C981OO_PROD `&0 < (a - &1) * (c + s)` THEN
  SUBGOAL_THEN `&1 < c * (u + a) - s * v` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `--(&37 / &50)`; `&11 / &25`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `u + a <= c + &14 / &25 * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `&14 / &25`) THEN REWRITE_TAC[linside] THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall y. ~linside c s u v a (&1) y` ASSUME_TAC THENL
  [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
   C981OO_UNFOLD_TAC `linside c s u v a (&1) y` THEN
   SUBGOAL_THEN `&13 / &50 < y` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < y - &13 / &50 ==> &13 / &50 < y`) THEN
    MATCH_MP_TAC C981OO_POS_OF_MUL THEN EXISTS_TAC `c:real` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `y < &14 / &25` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < &14 / &25 - y ==> y < &14 / &25`) THEN
    MATCH_MP_TAC C981OO_POS_OF_MUL THEN EXISTS_TAC `s:real` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (is_forall o concl)) THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall x y. linside c s u v a x y ==> x <= &1` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&0`; `&13 / &50`;
                 `x:real`; `y:real`; `&1 / x`] CES_INSIDE_SEGMENT) THEN
   SUBGOAL_THEN `(&1 - &1 / x) * &0 + &1 / x * x = &1` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 < x ==> &0 < x`] THEN
    ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - (c * (u + a) - s * v)` MP_TAC THENL
  [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
   MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
   X_GEN_TAC `e:real` THEN STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + a - e) - s * (v + e)`;
                                 `s * (u + a - e) + c * (v + e)`]) THEN
   ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
