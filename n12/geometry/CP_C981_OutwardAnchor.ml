(* ========================================================================= *)
(* Port of Compact/Completion/C981/OutwardAnchor.lean                         *)
(* (N12Compact.C981CompletionOutwardAnchor).  A central square with the true *)
(* inward and outward anchors must cross the whole foreign bottom segment.  *)
(* ClosedInside is lclosed; canonical_frame is CLF_CANONICAL_FRAME.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_WallScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C981OA_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C981OA_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL ORELSE
           MATCH_MP_TAC REAL_LE_ADD) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: strict_closed_segment (private) *)
let C981OA_STRICT_CLOSED_SEGMENT = prove
 (`forall c s u v a x y x' y' t.
     lclosed c s u v a x y /\ linside c s u v a x' y' /\ &0 < t /\ t < &1
     ==> linside c s u v a ((&1 - t) * x + t * x') ((&1 - t) * y + t * y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside] THEN STRIP_TAC THEN
  C981OA_PROD `&0 <= (&1 - t) * ((c * x + s * y) - u)` THEN
  C981OA_PROD `&0 <= (&1 - t) * ((u + a) - (c * x + s * y))` THEN
  C981OA_PROD `&0 <= (&1 - t) * ((--s * x + c * y) - v)` THEN
  C981OA_PROD `&0 <= (&1 - t) * ((v + a) - (--s * x + c * y))` THEN
  C981OA_PROD `&0 < t * ((c * x' + s * y') - u)` THEN
  C981OA_PROD `&0 < t * ((u + a) - (c * x' + s * y'))` THEN
  C981OA_PROD `&0 < t * ((--s * x' + c * y') - v)` THEN
  C981OA_PROD `&0 < t * ((v + a) - (--s * x' + c * y'))` THEN
  RASM_ARITH_TAC);;

(* Lean: crossing (private) *)
let C981OA_CROSSING = prove
 (`forall c s u v a x y.
     lclosed c s u v a x y /\ &113 / &50 < x /\ x < &14 / &5 /\ y < &1 /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     (forall z. &113 / &50 <= z /\ z <= &14 / &5 ==> ~linside c s u v a z (&1))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exists t. t * (&33 / &20 - y) = &1 - y` STRIP_ASSUME_TAC THENL
  [EXISTS_TAC `(&1 - y) / (&33 / &20 - y)` THEN UNDISCH_TAC `y < &1` THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t < &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`;
                `&47 / &20`; `&33 / &20`; `t:real`] C981OA_STRICT_CLOSED_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 - t) * y + t * &33 / &20 = &1` SUBST1_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - t) * x + t * &47 / &20`) THEN
  ASM_REWRITE_TAC[] THEN
  C981OA_PROD `&0 <= (&1 - t) * (x - &113 / &50)` THEN
  C981OA_PROD `&0 <= (&1 - t) * (&14 / &5 - x)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_impossible (private) / nonnegative_impossible *)
let C981OA_NONNEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&3) (&1) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     (forall z. &113 / &50 <= z /\ z <= &14 / &5 ==> ~linside c s u v a z (&1))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981WS_CANONICAL_PROJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C981OA_UNFOLD_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
  C981OA_UNFOLD_TAC `linside c s u v a (&3) (&8 / &5)` THEN
  SUBGOAL_THEN `--(&3) * s + c <= v` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&3) (&1)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&1543 / &500) * c + &2 * s` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&1543 / &500) (&2)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --(&113 / &50) * s + &2 * c` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&113 / &50) (&2)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&113 / &50) * c + s <= u` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o SPEC `&113 / &50` o check (is_forall o concl)) THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `--(&14 / &5) * s + c <= v` ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o SPEC `&14 / &5` o check (is_forall o concl)) THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c * u - s * v`; `s * u + c * v`] C981OA_CROSSING) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lclosed c s u v a (c * u - s * v) (s * u + c * v)` ASSUME_TAC THENL
  [REWRITE_TAC[lclosed] THEN
   SUBGOAL_THEN `c * (c * u - s * v) + s * (s * u + c * v) = u /\
                 --s * (c * u - s * v) + c * (s * u + c * v) = v` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[NOT_IMP] THEN
  C981OA_PROD `&0 <= c * (u - ((&113 / &50) * c + s))` THEN
  C981OA_PROD `&0 <= s * ((--(&113 / &50) * s + &2 * c) - (v + a))` THEN
  C981OA_PROD `&0 < s * (a - c)` THEN
  C981OA_PROD `&0 <= c * (((&1543 / &500) * c + &2 * s) - (u + a))` THEN
  C981OA_PROD `&0 <= s * (v - (--(&14 / &5) * s + c))` THEN
  C981OA_PROD `&0 < c * (a - &1)` THEN
  C981OA_PROD `&0 < c * (&1 - ((&143 / &500) * c + s))` THEN
  C981OA_PROD `&0 <= s * (((&1543 / &500) * c + &2 * s) - (u + a))` THEN
  C981OA_PROD `&0 <= c * ((--(&113 / &50) * s + &2 * c) - (v + a))` THEN
  C981OA_PROD `&0 < c * s` THEN
  SUBGOAL_THEN `&1 <= c + s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c + s <= &99 / &70` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  C981OA_PROD `&0 <= (&99 / &70 - (c + s)) * ((c + s) - &1)` THEN
  C981OA_PROD `&0 < (a - &1) * (c + s)` THEN
  RASM_ARITH_TAC);;

(* Lean: nonpositive_impossible (private) *)
let C981OA_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     (forall z. &113 / &50 <= z /\ z <= &14 / &5 ==> ~linside c s u v a z (&1))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  C981OA_UNFOLD_TAC `linside c s u v a (&2) (&87 / &50)` THEN
  C981OA_UNFOLD_TAC `linside c s u v a (&3) (&8 / &5)` THEN
  SUBGOAL_THEN `v + a <= --(&113 / &50) * s + &2 * c` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&113 / &50) (&2)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `&113 / &50` o check (is_forall o concl)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: impossible *)
let C981OA_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&3) (&1) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     (forall z. &113 / &50 <= z /\ z <= &14 / &5 ==> ~linside c s u v a z (&1))
     ==> false`,
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
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s'` THENL
  [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
     C981OA_NONNEGATIVE_IMPOSSIBLE);
   MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
     C981OA_NONPOSITIVE_IMPOSSIBLE)] THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[];
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;
