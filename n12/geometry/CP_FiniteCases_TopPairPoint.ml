(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/TopPairPoint.lean                  *)
(* q.translated 2 3 is (c, s, u - (2c + 3s), v - (3c - 2s), a)               *)
(* (FCTPP_TRANSLATED); short_projections is WFP_SHORT_PROJECTIONS / WFP_SP.  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* S12 translation of a square (inside_translated_iff) *)
let FCTPP_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive (private) *)
let FCTPP_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (--(&7 / &20)) (--(&13 / &20)) /\ linside c s u v a (&2 / &5) (&0) /\
     ~linside c s u v a (&7 / &20) (--(&13 / &20)) /\
     ~linside c s u v a (&0) (--(&1 / &2))
     ==> linside c s u v a (--(&2 / &5)) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (--(&7 / &20)) (--(&13 / &20))`; `linside c s u v a (&2 / &5) (&0)`] THEN
  MP_TAC(WFP_SP `--(&3 / &4)` `&13 / &20`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--s * (&7 / &20) + c * --(&13 / &20) <= v` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&7 / &20) (--(&13 / &20))`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u < c * --(&2 / &5)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ASSUME `~linside c s u v a (&0) (--(&1 / &2))`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: nonpositive (private) *)
let FCTPP_NONPOSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (--(&7 / &20)) (--(&13 / &20)) /\ linside c s u v a (&2 / &5) (&0) /\
     ~linside c s u v a (&7 / &20) (--(&13 / &20))
     ==> linside c s u v a (--(&2 / &5)) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (--(&7 / &20)) (--(&13 / &20))`; `linside c s u v a (&2 / &5) (&0)`] THEN
  MP_TAC(WFP_SP `&3 / &4` `--(&13 / &20)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `u + a <= c * (&7 / &20) + s * --(&13 / &20)` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&7 / &20) (--(&13 / &20))`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: point *)
let FCTPP_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\ linside c s u v a (&12 / &5) (&3) /\
     ~linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&2) (&5 / &2)
     ==> linside c s u v a (&8 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u0 = u - (c * &2 + s * &3)` THEN
  ABBREV_TAC `v0 = v - (--s * &2 + c * &3)` THEN
  SUBGOAL_THEN `forall x y. linside c s u0 v0 a x y <=> linside c s u v a (x + &2) (y + &3)`
    ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u0"; "v0"] THEN REWRITE_TAC[FCTPP_TRANSLATED]; ALL_TAC] THEN
  SUBGOAL_THEN `linside c s u0 v0 a (--(&2 / &5)) (&0)` MP_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u0:real`; `v0:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ar:real = a` o concl)) THEN
  SUBGOAL_THEN `linside cr sr ur vr a (--(&7 / &20)) (--(&13 / &20)) /\
                linside cr sr ur vr a (&2 / &5) (&0) /\
                ~linside cr sr ur vr a (&7 / &20) (--(&13 / &20)) /\
                ~linside cr sr ur vr a (&0) (--(&1 / &2))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th))) &&
      can (find_term ((=) `cr:real`)) (concl th) &&
      fst(strip_comb(lhs(snd(strip_forall(concl th))))) = `linside`
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC FCTPP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FCTPP_NONPOSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
