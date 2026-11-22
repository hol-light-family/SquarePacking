(* ========================================================================= *)
(* Port of Compact/Completion/C981/UpperPoint.lean                            *)
(* (N12Compact.C981CompletionUpperPoint).  C981-COMMON-CYCLE Theorem 1 and   *)
(* Corollary 4.  canonical_frame is CLF_CANONICAL_FRAME.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let C981UP_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C981UP_FACE t face =
  SUBGOAL_THEN face ASSUME_TAC THENL
  [UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

(* Lean: positive_faces (private) *)
let C981UP_POSITIVE_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&3) (&12 / &5) /\ ~linside c s u v a (&3) (&3)
     ==> &2 * c + (&12 / &5) * s <= u /\ u + a <= &3 * c + &3 * s /\
         --(&3) * s + (&12 / &5) * c <= v /\ v + a <= --(&2) * s + &3 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  C981UP_UNFOLD_TAC `linside c s u v a (&47 / &20) (&47 / &20)` THEN
  C981UP_UNFOLD_TAC `linside c s u v a (&113 / &50) (&3)` THEN
  C981UP_FACE `~linside c s u v a (&2) (&12 / &5)` `&2 * c + (&12 / &5) * s <= u` THEN
  C981UP_FACE `~linside c s u v a (&3) (&3)` `u + a <= &3 * c + &3 * s` THEN
  C981UP_FACE `~linside c s u v a (&2) (&3)` `v + a <= --(&2) * s + &3 * c` THEN
  C981UP_FACE `~linside c s u v a (&3) (&12 / &5)` `--(&3) * s + (&12 / &5) * c <= v` THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive *)
let C981UP_POSITIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&3) (&12 / &5) /\ ~linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&3) (&64 / &25)
     ==> &7 / &18 < c981ha_half c s /\ linside c s u v a (&2) (&131 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981UP_POSITIVE_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_QUARTER_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `s = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `&1 / &4 < c981ha_half c (&0)` THEN
   REWRITE_TAC[c981ha_half; real_div; REAL_MUL_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&4 / &25`] C981HA_SHORT_OF_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C981UP_UNFOLD_TAC `linside c s u v a (&47 / &20) (&47 / &20)` THEN
  C981UP_UNFOLD_TAC `linside c s u v a (&113 / &50) (&3)` THEN
  C981UP_FACE `~linside c s u v a (&3) (&64 / &25)` `--(&3) * s + (&64 / &25) * c <= v` THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_STEEP_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&19 / &50`] C981HA_SHORT_OF_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_SINE38_SHORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: negative_faces (private) *)
let C981UP_NEGATIVE_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&3) (&12 / &5) /\ ~linside c s u v a (&3) (&3)
     ==> &2 * c + &3 * s <= u /\ u + a <= &3 * c + (&12 / &5) * s /\
         --(&2) * s + (&12 / &5) * c <= v /\ v + a <= --(&3) * s + &3 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  C981UP_UNFOLD_TAC `linside c s u v a (&47 / &20) (&47 / &20)` THEN
  C981UP_UNFOLD_TAC `linside c s u v a (&113 / &50) (&3)` THEN
  C981UP_FACE `~linside c s u v a (&2) (&3)` `&2 * c + &3 * s <= u` THEN
  C981UP_FACE `~linside c s u v a (&3) (&12 / &5)`
    `u + a <= &3 * c + (&12 / &5) * s \/ v + a <= --(&3) * s + (&12 / &5) * c` THEN
  SUBGOAL_THEN `u < &2 * c + (&12 / &5) * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  C981UP_FACE `~linside c s u v a (&2) (&12 / &5)` `--(&2) * s + (&12 / &5) * c <= v` THEN
  SUBGOAL_THEN `u + a <= &3 * c + (&12 / &5) * s` ASSUME_TAC THENL
  [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  C981UP_FACE `~linside c s u v a (&3) (&3)` `v + a <= --(&3) * s + &3 * c` THEN
  ASM_REWRITE_TAC[]);;

(* Lean: nonpositive *)
let C981UP_NONPOSITIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&3) (&12 / &5) /\ ~linside c s u v a (&3) (&3)
     ==> linside c s u v a (&2) (&131 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981UP_NEGATIVE_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + (--s) pow 2 = &1` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C981HA_QUARTER_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < --s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `--s = &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `&1 / &4 < c981ha_half c (--s)` THEN
   ASM_REWRITE_TAC[c981ha_half; real_div; REAL_MUL_LZERO] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`; `&11 / &50`] C981HA_SHORT_OF_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C981HA_SINE38_SHORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  C981UP_UNFOLD_TAC `linside c s u v a (&47 / &20) (&47 / &20)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: point *)
let C981UP_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&2) (&12 / &5) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&3) (&12 / &5) /\ ~linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&3) (&64 / &25)
     ==> linside c s u v a (&2) (&131 / &50)`,
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
  [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`] C981UP_POSITIVE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; MESON_TAC[]];
   MATCH_MP_TAC C981UP_NONPOSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
