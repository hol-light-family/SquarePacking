(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C896MergedInward.lean             *)
(* (namespace N12Compact.FiniteCases.C896Ending; Lean header: "Source       *)
(* only").  A genuine inward point (G6) of the merged lower C896 owner 768.  *)
(* owner p m is the 5-tuple (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l.   *)
(* seed_point / aux_point / foreign are the producers c896mi_seed_point      *)
(* (= oo_seed), c896mi_aux_point (= c896wb_aux at compulsory points,         *)
(* OO_AUX_EXACT in general) and C896MI_FOREIGN_TAC (OO_APART at a point).    *)
(* q.translated tx ty is (c, s, u - (c tx + s ty), v - (--s tx + c ty), a)   *)
(* (C896MI_TRANSLATED); S12 inside_segment: C896MI_INSIDE_SEGMENT.           *)
(* ShortCornerAdvance.point: OCSCA_POINT; TwoChordHull.points: OCTCH_POINTS; *)
(* ShorterCornerWall.impossible: OCSCW_IMPOSSIBLE; C896CentralPoints.fixed:  *)
(* the C896CP_* facts; C896WallBars.bottom_right: C896WB_BOTTOM_RIGHT.       *)
(* Tag C896MI_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C896CentralPoints.ml";;
needs "n12/geometry/CP_OtherCases_TwoChordHull.ml";;
needs "n12/geometry/CP_OtherCases_ShortCornerAdvance.ml";;
needs "n12/geometry/CP_OtherCases_ShorterCornerWall.ml";;

let C896MI_TRANSLATED = prove
 (`forall c s u v a tx ty x y.
     linside c s (u - (c * tx + s * ty)) (v - (--s * tx + c * ty)) a x y <=>
     linside c s u v a (tx + x) (ty + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: S12.inside_segment *)
let C896MI_INSIDE_SEGMENT = prove
 (`forall c s u v a x y x' y' t.
     linside c s u v a x y /\ linside c s u v a x' y' /\ &0 <= t /\ t <= &1
     ==> linside c s u v a ((&1 - t) * x + t * x') ((&1 - t) * y + t * y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c * ((&1 - t) * x + t * x') + s * ((&1 - t) * y + t * y') =
      (&1 - t) * (c * x + s * y) + t * (c * x' + s * y') /\
    --s * ((&1 - t) * x + t * x') + c * ((&1 - t) * y + t * y') =
      (&1 - t) * (--s * x + c * y) + t * (--s * x' + c * y')`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC REAL_CONVEX_BOUND_LT ORELSE MATCH_MP_TAC REAL_CONVEX_BOUND_GT) THEN
  ASM_REAL_ARITH_TAC);;

let c896mi_tr (tx, ty) [c; s; u; v; a] =
  [c; s; mk_binop `(-):real->real->real` u
           (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c tx)
                                            (mk_binop `( * ):real->real->real` s ty));
   mk_binop `(-):real->real->real` v
           (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (mk_comb(`(--):real->real`, s)) tx)
                                            (mk_binop `( * ):real->real->real` c ty)); a];;

(* Lean: seed_point *)
let c896mi_seed_point m p = c896wb_seed m p;;
(* Lean: aux_point (at a compulsory point of C896Entrance.compulsory) *)
let c896mi_aux_point m j = c896wb_aux m j;;

(* Lean: foreign: goal ~linside (owner m) x y from |- .. ==> linside (owner n) x y *)
let C896MI_FOREIGN_TAC n th (asl, w) =
  let args = snd (strip_comb (dest_neg w)) in
  let m = dest_small_numeral (el 5 (snd (strip_comb (hd args)))) in
  (MP_TAC (SPEC_ALL (oo_apart C896D_F m n)) THEN ASM_REWRITE_TAC[ldisj] THEN
   DISCH_THEN (MP_TAC o SPECL [el 5 args; el 6 args]) THEN
   ASM_SIMP_TAC[th] THEN NO_TAC) (asl, w);;

let C896MI_CONV =
  REWRITE_CONV[C896MI_TRANSLATED; LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
  REAL_RAT_REDUCE_CONV;;

(* a wall of a charted owner: !x y. linside K x y ==> R, from OO_BOX *)
let C896MI_WALL_TAC m =
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP (REWRITE_RULE[lcont]
    (UNDISCH (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                     mk_small_numeral m] OO_BOX)))) THEN
  REAL_ARITH_TAC;;

let C896MI_SIDE_TAC ths fors extra =
  FIRST ([FIRST_ASSUM ACCEPT_TAC;
          ASM_SIMP_TAC ths THEN NO_TAC;
          REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
          FIRST [ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC;
                 ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC];
          MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC] @
         map (fun (n, th) -> C896MI_FOREIGN_TAC n th) fors @ extra);;

(* the antecedent of th at the tuple tp (rewritten through the charts), proved by the side tactic;
   leaves  concl ==> goal  (concl rewritten) *)
let C896MI_USE_TAC th tp ths fors extra =
  let th1 = SPECL tp th in
  let eq = C896MI_CONV (lhand (concl th1)) in
  let ceq = C896MI_CONV (rand (concl th1)) in
  SUBGOAL_THEN (rhs (concl eq)) MP_TAC THENL
   [REPEAT CONJ_TAC THEN C896MI_SIDE_TAC ths fors extra; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o EQ_MP ceq o MP th1 o EQ_MP (SYM eq));;

let c896mi_stmt hyps concl =
  list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(list_mk_conj([`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = c896d_family`] @ hyps),
           concl));;

(* Lean: bottom_marker *)
let C896MI_BOTTOM_MARKER = c896mi_seed_point 8192 (`&2`, `&457 / &500`);;

(* Lean: bottom_g5 *)
let C896MI_BOTTOM_G5 = c896mi_aux_point 8192 15;;

let C896MI_CORNER_ORIGIN = c896mi_seed_point 12 (`&3`, `&1`);;
let C896MI_RIGHT_G8 = c896mi_aux_point 16384 18;;

(* Lean: southeast_corner_advance *)
let C896MI_SOUTHEAST_CORNER_ADVANCE = prove
 (c896mi_stmt [] (c896wb_own 12 `&3` `&39 / &50`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C896MI_USE_TAC OCSCA_POINT (c896mi_tr (`&3`, `&3`) (c896wb_pullx (c896wb_pullsw (c896wb_q 12))))
    [C896MI_CORNER_ORIGIN] [16384, C896MI_RIGHT_G8; 8192, C896WB_BOTTOM_RIGHT]
    [C896MI_WALL_TAC 12] THEN
  DISCH_THEN ACCEPT_TAC);;

let C896MI_SINGLETON = c896mi_seed_point 1 (`&87 / &50`, `&1`);;

(* the bottom segment from the marker to G5 (Lean: segment in merged_lower_hull) *)
let C896MI_BOTTOM_SEGMENT = prove
 (c896mi_stmt [`&0 <= z`; `z <= &1`]
   (c896wb_own 8192 `(&1 - z) * &2 + z * &113 / &50` `(&1 - z) * &457 / &500 + z * &1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C896MI_INSIDE_SEGMENT THEN
  ASM_SIMP_TAC[C896MI_BOTTOM_MARKER; C896MI_BOTTOM_G5]);;

(* the excluded slant of TwoChordHull: a point of the bottom segment *)
let C896MI_SLANT_TAC (asl, w) =
  let args = snd (strip_comb (dest_neg w)) in
  let x = el 5 args and y = el 6 args in
  let x' = `(&1 - z) * &2 + z * &113 / &50` and y' = `(&1 - z) * &457 / &500 + z * &1` in
  (SUBGOAL_THEN (mk_conj(mk_eq(x, x'), mk_eq(y, y'))) (fun th -> REWRITE_TAC[th]) THENL
    [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   C896MI_FOREIGN_TAC 8192 C896MI_BOTTOM_SEGMENT) (asl, w);;

(* Lean: merged_lower_hull *)
let C896MI_MERGED_LOWER_HULL = prove
 (c896mi_stmt [mk_neg (c896wb_own 768 `&113 / &50` `&2`)]
   (list_mk_conj [c896wb_own 768 `&2` `&49 / &50`; c896wb_own 768 `&101 / &50` `&49 / &50`;
                  c896wb_own 768 `&211 / &100` `&26 / &25`]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C896MI_USE_TAC OCTCH_POINTS (c896mi_tr (`&2`, `&2`) (c896wb_pullx (c896wb_pullsw (c896wb_q 768))))
    [C896CP_SW_MARKER; C896CP_SE_MARKER]
    [2048, C896CP_NW_G3; 1, C896MI_SINGLETON; 8192, C896MI_BOTTOM_G5]
    [X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN C896MI_SLANT_TAC] THEN
  DISCH_THEN ACCEPT_TAC);;

(* Lean: merged_g6_point *)
let C896MI_MERGED_G6_POINT = prove
 (c896mi_stmt [] (c896wb_own 768 `&113 / &50` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (c896wb_own 768 `&113 / &50` `&2`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC (SPEC_ALL C896MI_MERGED_LOWER_HULL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C896MI_USE_TAC OCSCW_IMPOSSIBLE (c896mi_tr (`&3`, `&2`) (c896wb_pullx (c896wb_pullsw (c896wb_q 8192))))
    [C896MI_BOTTOM_MARKER; C896MI_BOTTOM_G5; C896WB_BOTTOM_RIGHT]
    [12, C896MI_SOUTHEAST_CORNER_ADVANCE]
    [C896MI_WALL_TAC 8192;
     C896MI_FOREIGN_TAC 768 (ASSUME (c896wb_own 768 `&2` `&49 / &50`));
     C896MI_FOREIGN_TAC 768 (ASSUME (c896wb_own 768 `&101 / &50` `&49 / &50`));
     C896MI_FOREIGN_TAC 768 (ASSUME (c896wb_own 768 `&211 / &100` `&26 / &25`))] THEN
  REWRITE_TAC[]);;

(* Lean: merged_g6 *)
let C896MI_MERGED_G6 = prove
 (c896mi_stmt [] `16 IN ooaux c1 c2 a b l 768`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM (oo_aux_point 16)] THEN
  ASM_SIMP_TAC[C896MI_MERGED_G6_POINT]);;
