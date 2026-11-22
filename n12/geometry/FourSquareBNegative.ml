(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareBNegative.lean                         *)
(* (N12Compact.FourSquareBNegative).  In the negative canonical B branch B   *)
(* contains M=(1.3,2.4) and N=(1,2.68); the left square contains one.       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;

(* Lean: left_cover *)
let FSBN_LEFT_COVER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ abs s <= c /\ &1 < a /\ lcont c s u v a /\
     lclosed c s u v a (&457 / &500) (&2) /\
     lclosed c s u v a (&1) (&12 / &5) /\
     --s * (&19 / &25) + c * (&187 / &100) <= v
     ==> linside c s u v a (&13 / &10) (&12 / &5) \/
         linside c s u v a (&1) (&67 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FSBC_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; lcx; REAL_ABS_BOUNDS]) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
   [`c <= &1`; `&0 <= (c - s) * (c + s)`; `&7 / &10 <= c`;
    `&0 <= (&1 - c) * (c - &2 / &3)`; `&1 - c <= (&3 / &5) * s * s`] THEN
  FSBL_SP_TAC `&6 / &25` `&81 / &100` THEN
  SUBGOAL_THEN `c + s * (&67 / &25) < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= c * (c + s * (&67 / &25) - (u + a))`; `&0 < (a - &1) * c`] THEN
    ASM_CASES_TAC `&0 <= s` THENL
     [FSBL_SP_TAC `&81 / &100` `&9 / &25` THEN
      UNDISCH_TAC `a * (c + abs s) / &2 <= c * (u + a / &2) - s * (v + a / &2)` THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`] THEN DISCH_TAC THEN
      NLIN_FACTS_TAC []
       [`s * (--s * (&19 / &25) + c * (&187 / &100)) <= s * v`;
        `&0 <= s * (&1 - (&81 / &100) * c - (&9 / &25) * s)`;
        `&0 <= s * (a - &1)`] THEN
      FSBC_ARITH_TAC;
      UNDISCH_TAC `a * (c + abs s) / &2 <= c * (u + a / &2) - s * (v + a / &2)` THEN
      ASM_SIMP_TAC[REAL_ARITH `~(&0 <= s) ==> abs s = --s`] THEN DISCH_TAC THEN
      NLIN_FACTS_TAC []
       [`s * (--s * (&457 / &500) + c * &2) <= s * v`;
        `&0 <= --s * (c + s)`; `c * s <= &0`] THEN
      FSBC_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [DISJ2_TAC THEN REWRITE_TAC[linside] THEN FSBC_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `linside c s u v a (&13 / &10) (&12 / &5)` THEN ASM_REWRITE_TAC[] THEN
  FSBL_SP_TAC `&27 / &50` `&53 / &100` THEN
  FSBL_SP_TAC `&3 / &10` `--(&7 / &25)` THEN
  SUBGOAL_THEN `u + a <= c * (&13 / &10) + s * (&12 / &5)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&13 / &10) (&12 / &5)` THEN
    REWRITE_TAC[linside] THEN FSBC_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN FSBC_ARITH_TAC);;

(* Lean: forced_faces *)
let FSBN_FORCED_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ s <= &0 /\ --s <= c /\ &1 < a /\
     lclosed c s u v a (&33 / &20) (&47 / &20) /\
     lclosed c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&2) (&5 / &2) /\
     v + a <= -- &2 * s + (&1543 / &500) * c
     ==> u + a <= &2 * c + (&5 / &2) * s /\
         --s + (&12 / &5) * c <= v /\ a <= --s + (&343 / &500) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside]) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  SUBGOAL_THEN `u + a <= &2 * c + s * (&5 / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FSBC_MISS_TAC [`c * &2`; `&5 / &2`]; ALL_TAC] THEN
  SUBGOAL_THEN `--s + c * (&12 / &5) <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FSBC_MISS_TAC [`c * &1`; `&12 / &5`]; ALL_TAC] THEN
  FSBC_ARITH_TAC);;

(* Lean: right_points *)
let FSBN_RIGHT_POINTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ s <= &0 /\ --s <= c /\ &1 < a /\
     lclosed c s u v a (&33 / &20) (&47 / &20) /\
     lclosed c s u v a (&8 / &5) (&3) /\
     u + a <= &2 * c + (&5 / &2) * s /\
     v + a <= -- &2 * s + (&1543 / &500) * c /\
     a <= --s + (&343 / &500) * c
     ==> linside c s u v a (&13 / &10) (&12 / &5) /\
         linside c s u v a (&1) (&67 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed]) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c:real`] [`c <= &1`; `--s <= &1`] THEN
  FSBL_SP_TAC `&7 / &10` `&343 / &500` THEN
  FSBL_SP_TAC `&25 / &27` `--(&10 / &27)` THEN
  SUBGOAL_THEN `&7 / &20 < --s` ASSUME_TAC THENL [FSBC_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c - (&9 / &50) * s < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= (c - (&1 + (&9 / &50) * s)) * (c + (&1 + (&9 / &50) * s))`;
      `&0 < --s * (--(&2581 / &2500) * s - &9 / &25)`] THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c + s`] [`c - s <= &283 / &200`] THEN
  REWRITE_TAC[linside] THEN FSBC_ARITH_TAC);;
