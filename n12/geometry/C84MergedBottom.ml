(* ========================================================================= *)
(* Port of Compact/Geometry/C84MergedBottom.lean                             *)
(* (namespace N12Compact.C84MergedBottom).                                   *)
(* short_projections: WFP_SHORT_PROJECTIONS (instantiated by WFP_SP);        *)
(* ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Move all linside/lclosed facts and the goal to the canonical frame given  *)
(* by CLF_CANONICAL_FRAME (variables c' s' u' v', side a).                   *)
let C84MB_FRAME_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th)
           then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
           else NO_TAC));;

(* Lean: zero (private) *)
let C84MB_ZERO = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 < c /\ abs s <= c /\
     a <= &1001 / &1000 /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&1) (&8 / &5) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--c <= s /\ s <= c` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s <= &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c <= &13 * s` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= (c - &13 * s) * (c + &13 * s)`; `&99 / &100 <= c`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_corner (private) *)
let C84MB_NEGATIVE_CORNER = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ s <= &0 /\ --c <= s /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     u + a <= c * &113 / &50 + s /\
     ~linside c s u v a (&33 / &20) (&33 / &20) ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  MP_TAC(WFP_SP `&61 / &100` `--(&13 / &20)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: two (private) *)
let C84MB_TWO = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ abs s <= c /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&87 / &50) (&1) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&113 / &50) (&1) ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `--c <= s /\ s <= c` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [UNDISCH_TAC `~linside c s u v a (&33 / &20) (&33 / &20)` THEN
    UNDISCH_TAC `~linside c s u v a (&113 / &50) (&1)` THEN
    UNDISCH_TAC `linside c s u v a (&2) (&457 / &500)` THEN
    UNDISCH_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
    UNDISCH_TAC `linside c s u v a (&87 / &50) (&1)` THEN
    REWRITE_TAC[linside] THEN REPEAT DISCH_TAC THEN
    MP_TAC(WFP_SP `--(&61 / &100)` `&13 / &20`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `--s * &113 / &50 + c * &1 <= v` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `u + a <= c * &113 / &50 + s` ASSUME_TAC THENL
     [UNDISCH_TAC `~linside c s u v a (&113 / &50) (&1)` THEN
      UNDISCH_TAC `linside c s u v a (&2) (&457 / &500)` THEN
      UNDISCH_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
      UNDISCH_TAC `linside c s u v a (&87 / &50) (&1)` THEN
      REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC C84MB_NEGATIVE_CORNER THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: three (private) *)
let C84MB_THREE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ abs s <= c /\
     a <= &1001 / &1000 /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&113 / &50) (&1) ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `--c <= s /\ s <= c` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [UNDISCH_TAC `~linside c s u v a (&33 / &20) (&33 / &20)` THEN
    UNDISCH_TAC `~linside c s u v a (&113 / &50) (&1)` THEN
    UNDISCH_TAC `linside c s u v a (&2) (&457 / &500)` THEN
    UNDISCH_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
    UNDISCH_TAC `linside c s u v a (&87 / &50) (&2)` THEN
    REWRITE_TAC[linside] THEN REPEAT DISCH_TAC THEN
    NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`] [`c <= &1`; `s <= &1`] THEN
    SUBGOAL_THEN `c < &2 * s` ASSUME_TAC THENL
     [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
      NLIN_FACTS_TAC [] [`&0 <= s * (c - &2 * s)`; `&0 <= s * (&1 - c)`] THEN
      SUBGOAL_THEN `&1 - c <= s / &4` ASSUME_TAC THENL
       [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
        NLIN_FACTS_TAC [] [`&0 < ((&1 - c) - s / &4) * (&1 + c)`] THEN
        NLIN_TAC ~deg2:false [];
        ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `u + a <= c * &113 / &50 + s` ASSUME_TAC THENL
     [UNDISCH_TAC `~linside c s u v a (&113 / &50) (&1)` THEN
      UNDISCH_TAC `linside c s u v a (&2) (&457 / &500)` THEN
      UNDISCH_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
      UNDISCH_TAC `linside c s u v a (&87 / &50) (&2)` THEN
      REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC C84MB_NEGATIVE_CORNER THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: forbidden *)
let C84MB_FORBIDDEN = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ a <= &1001 / &1000 /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&113 / &50) (&1)
     ==> ~linside c s u v a (&1) (&8 / &5) /\ ~linside c s u v a (&87 / &50) (&1) /\
         ~linside c s u v a (&87 / &50) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C84MB_FRAME_TAC THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC C84MB_ZERO; MATCH_MP_TAC C84MB_TWO; MATCH_MP_TAC C84MB_THREE] THEN
  MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: canonical_positive *)
let C84MB_CANONICAL_POSITIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ abs s <= c /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&12 / &5) (&1) ==> &0 < s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
  SUBGOAL_THEN `--c <= s /\ s <= c` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * &33 / &20 + s * &33 / &20 <= u` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(WFP_SP `&3 / &4` `--(&13 / &20)`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: inward *)
let C84MB_INWARD = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&12 / &5) (&1)
     ==> linside c s u v a (&2) (&87 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C84MB_FRAME_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
    C84MB_CANONICAL_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `--c' <= s' /\ s' <= c'` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `linside c' s' u' v' a (&2) (&457 / &500)` THEN
  UNDISCH_TAC `linside c' s' u' v' a (&47 / &20) (&33 / &20)` THEN
  UNDISCH_TAC `linside c' s' u' v' a (&113 / &50) (&2)` THEN
  REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC);;
