(* ========================================================================= *)
(* Port of Compact/Completion/C981/TopReach.lean                              *)
(* (N12Compact.C981CompletionTopReach).  Three actual-support lemmas,        *)
(* coordinates translated by (-2,-3).  canonical_frame is                    *)
(* CLF_CANONICAL_FRAME; short_projections is WFP_SHORT_PROJECTIONS.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/CP_C981_WallScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C981TR_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C981TR_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* derive a weak face from a negated point: `face` follows from the negation *)
let C981TR_FACE t face =
  SUBGOAL_THEN face ASSUME_TAC THENL
  [UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

let C981TR_SHORT x y =
  MP_TAC(SPECL [`c:real`; `s:real`; x; y] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC;;

(* Lean: arc (private) *)
let C981TR_ARC = prove
 (`forall c s. c977cc_normal c s ==> &1 + (&4 / &5) * c * s <= c + s`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal c s` THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  STRIP_TAC THEN
  C981TR_PROD `&0 <= ((c + s) - &1) * (&10 / &7 - (c + s))` THEN
  C981TR_PROD `&0 <= c * s` THEN ASM_REAL_ARITH_TAC);;

(* Lean: negative_wall (private) *)
let C981TR_NEGATIVE_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
               (forall x y. linside c s u v a x y ==> y <= &1)
     ==> s * u + c * (v + a) <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`] C981CA_UPPER_WALL) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:real` THEN
   POP_ASSUM MP_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
   REAL_ARITH_TAC]);;

(* Lean: origin_positive (private) *)
let C981TR_ORIGIN_POSITIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     ~linside c s u v a (&0) (&0)
     ==> linside c s u v a (&4 / &5) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981CA_UPPER_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981TR_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; STRIP_TAC] THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&0) (&43 / &500)` THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&2 / &5) (&0)` THEN
  C981TR_FACE `~linside c s u v a (&0) (&0)` `&0 <= u` THEN
  SUBGOAL_THEN `v < --(&4 / &5) * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C981TR_PROD `&0 <= s * u` THEN C981TR_PROD `&0 <= c * (v + (&4 / &5) * s)` THEN
   C981TR_PROD `&0 < (a - &1) * (c + s)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: origin_negative (private) *)
let C981TR_ORIGIN_NEGATIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     ~linside c s u v a (&0) (&0)
     ==> linside c s u v a (&4 / &5) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981TR_NEGATIVE_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C981TR_ARC) THEN
  ANTS_TAC THENL [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
                              REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C977CC_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
                              REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&0) (&43 / &500)` THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&2 / &5) (&0)` THEN
  C981TR_FACE `~linside c s u v a (&0) (&0)` `&0 <= v` THEN
  SUBGOAL_THEN `(&4 / &5) * c < u + a` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C981TR_PROD `&0 <= --s * ((&4 / &5) * c - u - a)` THEN C981TR_PROD `&0 <= c * v` THEN
   C981TR_PROD `&0 < (a - &1) * (c - s)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* canonical-frame wrapper used by the three public statements *)
let C981TR_FRAME_TAC =
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
  UNDISCH_TAC `abs s' <= c'` THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC;;

(* Lean: origin_alternative *)
let C981TR_ORIGIN_ALTERNATIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     ~linside c s u v a (&0) (&0)
     ==> linside c s u v a (&4 / &5) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C981TR_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s'` THENL
  [MATCH_MP_TAC C981TR_ORIGIN_POSITIVE; MATCH_MP_TAC C981TR_ORIGIN_NEGATIVE] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: tip_negative_impossible (private) *)
let C981TR_TIP_NEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (--(&13 / &50)) (&0) /\ linside c s u v a (&0) (--(&37 / &50)) /\
     linside c s u v a (--(&7 / &20)) (--(&13 / &20)) /\
     ~linside c s u v a (--(&2 / &5)) (&0) /\
     ~linside c s u v a (&7 / &20) (--(&13 / &20))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981TR_SHORT `&3 / &4` `--(&13 / &20)` THEN
  C981TR_UNFOLD_TAC `linside c s u v a (--(&13 / &50)) (&0)` THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&0) (--(&37 / &50))` THEN
  C981TR_UNFOLD_TAC `linside c s u v a (--(&7 / &20)) (--(&13 / &20))` THEN
  C981TR_FACE `~linside c s u v a (--(&2 / &5)) (&0)` `--(&2 / &5) * c <= u` THEN
  C981TR_FACE `~linside c s u v a (&7 / &20) (--(&13 / &20))`
    `u + a <= (&7 / &20) * c - (&13 / &20) * s` THEN
  RASM_ARITH_TAC);;

(* Lean: tip_positive (private) *)
let C981TR_TIP_POSITIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (--(&13 / &50)) (&0) /\ linside c s u v a (&0) (--(&37 / &50)) /\
     linside c s u v a (--(&7 / &20)) (--(&13 / &20)) /\
     ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (--(&2 / &5)) (&0) /\
     ~linside c s u v a (--(&13 / &50)) (--(&1)) /\
     ~linside c s u v a (--(&1)) (--(&1 / &5))
     ==> linside c s u v a (--(&3 / &100)) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981TR_SHORT `&19 / &20` `&29 / &100` THEN C981TR_SHORT `&97 / &100` `&1 / &5` THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981WS_CANONICAL_PROJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  C981TR_UNFOLD_TAC `linside c s u v a (--(&13 / &50)) (&0)` THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&0) (--(&37 / &50))` THEN
  C981TR_FACE `~linside c s u v a (&0) (&0)` `u + a <= &0` THEN
  C981TR_FACE `~linside c s u v a (--(&2 / &5)) (&0)` `v + a <= (&2 / &5) * s` THEN
  C981TR_FACE `~linside c s u v a (--(&13 / &50)) (--(&1))` `(&13 / &50) * s - c <= v` THEN
  C981TR_FACE `~linside c s u v a (--(&1)) (--(&1 / &5))` `--c - (&1 / &5) * s <= u` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: central_tip *)
let C981TR_CENTRAL_TIP = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&13 / &50)) (&0) /\ linside c s u v a (&0) (--(&37 / &50)) /\
     linside c s u v a (--(&7 / &20)) (--(&13 / &20)) /\
     ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (--(&2 / &5)) (&0) /\
     ~linside c s u v a (--(&13 / &50)) (--(&1)) /\
     ~linside c s u v a (&7 / &20) (--(&13 / &20)) /\
     ~linside c s u v a (--(&1)) (--(&1 / &5))
     ==> linside c s u v a (--(&3 / &100)) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C981TR_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s'` THENL
  [MATCH_MP_TAC C981TR_TIP_POSITIVE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
   MATCH_MP_TAC(TAUT `false ==> p`) THEN MATCH_MP_TAC C981TR_TIP_NEGATIVE_IMPOSSIBLE THEN
   MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`] THEN
   ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: foreign_positive (private) *)
let C981TR_FOREIGN_POSITIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     ~linside c s u v a (--(&3 / &100)) (&0)
     ==> linside c s u v a (&73 / &100) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981CA_UPPER_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981TR_ARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; STRIP_TAC] THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&0) (&43 / &500)` THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&2 / &5) (&0)` THEN
  C981TR_FACE `~linside c s u v a (--(&3 / &100)) (&0)` `--(&3 / &100) * c <= u` THEN
  SUBGOAL_THEN `v < --(&73 / &100) * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C981TR_PROD `&0 <= s * (u + (&3 / &100) * c)` THEN
   C981TR_PROD `&0 <= c * (v + (&73 / &100) * s)` THEN
   C981TR_PROD `&0 < (a - &1) * (c + s)` THEN C981TR_PROD `&0 <= c * s` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: foreign_negative (private) *)
let C981TR_FOREIGN_NEGATIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     ~linside c s u v a (--(&3 / &100)) (&0) /\
     ~linside c s u v a (&0) (--(&37 / &50))
     ==> linside c s u v a (&73 / &100) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981TR_NEGATIVE_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C981TR_ARC) THEN
  ANTS_TAC THENL [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
                              REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C977CC_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
                              REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&0) (&43 / &500)` THEN
  C981TR_UNFOLD_TAC `linside c s u v a (&2 / &5) (&0)` THEN
  SUBGOAL_THEN `--(&3 / &100) * c <= u \/ (&3 / &100) * s <= v` MP_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (--(&3 / &100)) (&0)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
  [C981TR_FACE `~linside c s u v a (&0) (--(&37 / &50))` `--(&37 / &50) * c <= v` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
   SUBGOAL_THEN `(&73 / &100) * c < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C981TR_PROD `&0 <= --s * ((&73 / &100) * c - u - a)` THEN
    C981TR_PROD `&0 <= c * (v - (&3 / &100) * s)` THEN
    C981TR_PROD `&0 < (a - &1) * (c - s)` THEN C981TR_PROD `&0 <= c * --s` THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC]);;

(* Lean: foreign_tip *)
let C981TR_FOREIGN_TIP = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     (forall x y. linside c s u v a x y ==> y <= &1) /\
     linside c s u v a (&0) (&43 / &500) /\ linside c s u v a (&2 / &5) (&0) /\
     ~linside c s u v a (--(&3 / &100)) (&0) /\
     ~linside c s u v a (&0) (--(&37 / &50))
     ==> linside c s u v a (&73 / &100) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C981TR_FRAME_TAC THEN
  ASM_CASES_TAC `&0 <= s'` THENL
  [MATCH_MP_TAC C981TR_FOREIGN_POSITIVE; MATCH_MP_TAC C981TR_FOREIGN_NEGATIVE] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
