(* ========================================================================= *)
(* Port of Compact/Completion/C981/WallOrigin.lean                            *)
(* (N12Compact.C981CompletionWallOrigin).  Actual wall-origin completion     *)
(* from a perpendicular whole foreign corner segment.  ClosedInside is       *)
(* lclosed; canonical_frame is CLF_CANONICAL_FRAME.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C981WO_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C981WO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

let C981WO_NONNEG_OF_MUL = prove
 (`forall x k. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&0`; `x:real`; `k:real`] REAL_LE_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

(* Lean: vertex (private) *)
let C981WO_VERTEX = prove
 (`forall c s u v a U V. c * c + s * s = &1 /\
     (u <= U /\ U <= u + a) /\ (v <= V /\ V <= v + a)
     ==> lclosed c s u v a (c * U - s * V) (s * U + c * V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lclosed] THEN
  SUBGOAL_THEN `c * (c * U - s * V) + s * (s * U + c * V) = U /\
                --s * (c * U - s * V) + c * (s * U + c * V) = V` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: mixed (private) *)
let C981WO_MIXED = prove
 (`forall c s u v a x y t.
     lclosed c s u v a x y /\ linside c s u v a (&2 / &5) (&0) /\ &0 < t /\ t < &1
     ==> linside c s u v a ((&1 - t) * (&2 / &5) + t * x) (t * y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside] THEN STRIP_TAC THEN
  C981WO_PROD `&0 <= t * ((c * x + s * y) - u)` THEN
  C981WO_PROD `&0 <= t * ((u + a) - (c * x + s * y))` THEN
  C981WO_PROD `&0 <= t * ((--s * x + c * y) - v)` THEN
  C981WO_PROD `&0 <= t * ((v + a) - (--s * x + c * y))` THEN
  C981WO_PROD `&0 < (&1 - t) * ((c * &2 / &5 + s * &0) - u)` THEN
  C981WO_PROD `&0 < (&1 - t) * ((u + a) - (c * &2 / &5 + s * &0))` THEN
  C981WO_PROD `&0 < (&1 - t) * ((--s * &2 / &5 + c * &0) - v)` THEN
  C981WO_PROD `&0 < (&1 - t) * ((v + a) - (--s * &2 / &5 + c * &0))` THEN
  RASM_ARITH_TAC);;

(* Lean: crossing (private) *)
let C981WO_CROSSING = prove
 (`forall c s u v a x y.
     lclosed c s u v a x y /\ &1 < x /\ &0 < y /\ y < &3 / &5 /\
     linside c s u v a (&2 / &5) (&0) /\
     (forall z. &0 <= z /\ z <= &3 / &5 ==> ~linside c s u v a (&1) z)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exists t. t * (x - &2 / &5) = &3 / &5` STRIP_ASSUME_TAC THENL
  [EXISTS_TAC `(&3 / &5) / (x - &2 / &5)` THEN UNDISCH_TAC `&1 < x` THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t < &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`;
                `t:real`] C981WO_MIXED) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 - t) * (&2 / &5) + t * x = &1` SUBST1_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `t * y`) THEN ASM_REWRITE_TAC[] THEN
  C981WO_PROD `&0 < t * y` THEN C981WO_PROD `&0 <= (&1 - t) * y` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_origin (private) *)
let C981WO_POSITIVE_ORIGIN = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     (forall z. &0 <= z /\ z <= &3 / &5 ==> ~linside c s u v a (&1) z)
     ==> linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981CA_UPPER_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; STRIP_TAC] THEN
  C981WO_UNFOLD_TAC `linside c s u v a (&0) (&43 / &500)` THEN
  C981WO_UNFOLD_TAC `linside c s u v a (&2 / &5) (&0)` THEN
  SUBGOAL_THEN `u < &0` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `--s <= v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&3 / &5`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                 `c * (u + a) - s * v`; `s * (u + a) + c * v`] C981WO_CROSSING) THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u + a`; `v:real`]
     C981WO_VERTEX) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `c * (c * (u + a) - s * v) = u + a - s * (s * (u + a) + c * v)` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   C981WO_PROD `&0 <= c * s` THEN
   C981WO_PROD `&0 < (a - &1) * (&1 + c * s)` THEN
   C981WO_PROD `&0 <= (&1 - c) * (&1 - s)` THEN
   C981WO_PROD `&0 <= s * (&1 - (s * (u + a) + c * v) - c * a)` THEN
   C981WO_PROD `&0 <= s * u` THEN C981WO_PROD `&0 <= c * (v + s)` THEN
   C981WO_PROD `&0 < s * (a - c)` THEN C981WO_PROD `&0 < c * (a - &1)` THEN
   C981WO_PROD `&0 <= c * s` THEN
   REWRITE_TAC[DE_MORGAN_THM] THEN REWRITE_TAC[REAL_NOT_LT] THEN
   ASM_CASES_TAC `c * (u + a) - s * v <= &1` THENL
   [C981WO_PROD `&0 <= c * (&1 - (c * (u + a) - s * v))` THEN RASM_ARITH_TAC;
    RASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: negative_origin (private) *)
let C981WO_NEGATIVE_ORIGIN = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     (forall z. &0 <= z /\ z <= &3 / &5 ==> ~linside c s u v a (&1) z)
     ==> linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`] C981CA_UPPER_WALL) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
     is_forall(concl th) && can (find_term ((=) `&1`)) (concl th) &&
     not (can (find_term ((=) `&3 / &5`)) (concl th)))) THEN
   EXISTS_TAC `x:real` THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
   DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C977CC_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
                              REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C981WO_UNFOLD_TAC `linside c s u v a (&0) (&43 / &500)` THEN
  C981WO_UNFOLD_TAC `linside c s u v a (&2 / &5) (&0)` THEN
  SUBGOAL_THEN `v < &0` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < --s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `u + a <= c` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&3 / &5`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= c + --s - &1 - c * --s + (--s) * (--s) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC C981WO_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + c` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + c) * (c + --s - &1 - c * --s + (--s) * (--s) / &2) =
                  ((--s) * (--s) / &2) * (c + &2 * --s - &1)` SUBST1_TAC THENL
    [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [MP_TAC(SPEC `--s:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
     ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `c + (&3 / &5) * s < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C981WO_PROD `&0 <= --s * ((c + (&3 / &5) * s) - (u + a))` THEN
    C981WO_PROD `&0 <= c * v` THEN
    C981WO_PROD `&0 < (a - &1) * (c + --s)` THEN
    MP_TAC(SPEC `s:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `v + a <= --s + (&3 / &5) * c` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&3 / &5` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&3 / &5`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                 `c * (u + a) - s * (v + a)`; `s * (u + a) + c * (v + a)`] C981WO_CROSSING) THEN
   ASM_REWRITE_TAC[] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u + a`; `v + a`]
     C981WO_VERTEX) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `--s * (c * (u + a) - s * (v + a)) = v + a - c * (s * (u + a) + c * (v + a))`
   ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   C981WO_PROD `&0 <= c * --s` THEN
   C981WO_PROD `&0 < (a - &1) * (&1 + c * --s)` THEN
   C981WO_PROD `&0 <= (&1 - c) * (&1 - --s)` THEN
   C981WO_PROD `&0 <= c * (&1 - (s * (u + a) + c * (v + a)) - --s * a)` THEN
   C981WO_PROD `&0 <= --s * (c - (u + a))` THEN C981WO_PROD `&0 <= c * v` THEN
   C981WO_PROD `&0 < c * (a - --s)` THEN C981WO_PROD `&0 < --s * (a - &1)` THEN
   C981WO_PROD `&0 <= c * --s` THEN
   REWRITE_TAC[DE_MORGAN_THM] THEN REWRITE_TAC[REAL_NOT_LT] THEN
   ASM_CASES_TAC `c * (u + a) - s * (v + a) <= &1` THENL
   [C981WO_PROD `&0 <= --s * (&1 - (c * (u + a) - s * (v + a)))` THEN RASM_ARITH_TAC;
    RASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: point *)
let C981WO_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     (forall z. &0 <= z /\ z <= &3 / &5 ==> ~linside c s u v a (&1) z)
     ==> linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real` (X_CHOOSE_THEN `s':real` (X_CHOOSE_THEN
    `u':real` (X_CHOOSE_THEN `v':real` (X_CHOOSE_THEN `a':real`
    STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) &&
     is_iff(snd(strip_forall(concl th))) then
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
     else NO_TAC) THEN
  UNDISCH_TAC `abs s' <= c'` THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= s'` THENL
  [MATCH_MP_TAC C981WO_POSITIVE_ORIGIN; MATCH_MP_TAC C981WO_NEGATIVE_ORIGIN] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
