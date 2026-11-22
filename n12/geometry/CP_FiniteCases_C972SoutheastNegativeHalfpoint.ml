(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972SoutheastNegativeHalfpoint.lean*)
(* (namespace N12Compact.FiniteCases.C972Local).  Normal is c977cc_normal;   *)
(* q.translated dx dy is (c, s, u - (c dx + s dy), v - (--s dx + c dy), a).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let FC972SNH_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let FC972SNH_NEG_TAC t = MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: negative_point *)
let FC972SNH_NEGATIVE_POINT = prove
 (`forall c s u v a t.
     s = --t /\ c977cc_normal c t /\ &1 < a /\
     linside c s u v a (&13 / &50) (&0) /\ linside c s u v a (&1) (--(&13 / &50)) /\
     linside c s u v a (&1) (--(&2 / &5)) /\
     ~linside c s u v a (&1) (&0) /\
     ~linside c s u v a (&0) (--(&13 / &50)) /\
     ~linside c s u v a (&0) (--(&1 / &2))
     ==> linside c s u v a (&1) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c (--t) u v a (&13 / &50) (&0)`; `linside c (--t) u v a (&1) (--(&13 / &50))`;
    `linside c (--t) u v a (&1) (--(&2 / &5))`] THEN
  SUBGOAL_THEN `v + a <= t` ASSUME_TAC THENL
   [FC972SNH_NEG_TAC `~linside c (--t) u v a (&1) (&0)`; ALL_TAC] THEN
  ASM_CASES_TAC `linside c (--t) u v a (&1) (--(&1 / &2))` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `u + a <= c + t / &2` ASSUME_TAC THENL
   [FC972SNH_NEG_TAC `~linside c (--t) u v a (&1) (--(&1 / &2))`; ALL_TAC] THEN
  SUBGOAL_THEN `--c / &2 <= v` ASSUME_TAC THENL
   [FC972SNH_NEG_TAC `~linside c (--t) u v a (&0) (--(&1 / &2))`; ALL_TAC] THEN
  SUBGOAL_THEN `(&13 / &50) * t <= u` ASSUME_TAC THENL
   [FC972SNH_NEG_TAC `~linside c (--t) u v a (&0) (--(&13 / &50))`; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: negative_point_original *)
let FC972SNH_NEGATIVE_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c977cc_normal c (--s) /\ &1 < a /\
     linside c s u v a (&113 / &50) (&2) /\ linside c s u v a (&3) (&87 / &50) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&3) (&2) /\
     ~linside c s u v a (&2) (&87 / &50) /\
     ~linside c s u v a (&2) (&3 / &2)
     ==> linside c s u v a (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`; `--s:real`] FC972SNH_NEGATIVE_POINT) THEN
  REWRITE_TAC[FC972SNH_TRANSLATED; REAL_NEG_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;
