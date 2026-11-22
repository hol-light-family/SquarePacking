(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/ShortOutwardPoint.lean             *)
(* (N12Compact.CommonCases.ShortOutwardPoint).  The shorter actual top       *)
(* endpoint 2.73 forces the stronger outward strict point (2.54,1.99).       *)
(* q.translated dx dy is (c, s, u - (c dx + s dy), v - (--s dx + c dy), a).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let CCSOP_TRANSLATED = prove
 (`forall c s u v a x y dx dy.
     linside c s (u - (c * dx + s * dy)) (v - (--s * dx + c * dy)) a x y <=>
     linside c s u v a (x + dx) (y + dy)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let CCSOP_UNFOLD_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> try fst(strip_comb(concl th)) = `linside` with _ -> false) ths));;

(* linear arithmetic with one missing-point hypothesis `~linside ...` *)
let CCSOP_NFACT_TAC n t =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [MP_TAC(ASSUME n) THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

(* Lean: positive_point *)
let CCSOP_POSITIVE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&1) (&13 / &50) /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&543 / &500) (&0) /\
     ~linside c s u v a (&13 / &50) (&1) /\
     ~linside c s u v a (&73 / &100) (&1) /\
     ~linside c s u v a (&1) (&1) /\
     ~linside c s u v a (&543 / &500) (&1)
     ==> linside c s u v a (&27 / &50) (-- &1 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CCSOP_UNFOLD_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  SUBGOAL_THEN `v < --s * (&13 / &50)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCSOP_NFACT_TAC `~linside c s u v a (&13 / &50) (&1)` `c * (&13 / &50) + s * &1 <= u` THEN
    CCSOP_NFACT_TAC `~linside c s u v a (&73 / &100) (&1)` `u + a <= c * (&73 / &100) + s * &1` THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  CCSOP_NFACT_TAC `~linside c s u v a (&13 / &50) (&0)` `c * (&13 / &50) <= u` THEN
  CCSOP_NFACT_TAC `~linside c s u v a (&543 / &500) (&0)` `--s * (&543 / &500) <= v` THEN
  CCSOP_NFACT_TAC `~linside c s u v a (&543 / &500) (&1)`
    `u + a <= c * (&543 / &500) + s` THEN
  SUBGOAL_THEN `&87 / &500 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &1`]
   [`c <= &1 - s * s / &2`; `&0 < s * (s - &43 / &250)`; `c + (&43 / &500) * s < &1`] THEN
  CCSOP_NFACT_TAC `~linside c s u v a (&1) (&1)` `u + a <= c + s` THEN
  SUBGOAL_THEN `u < c * (&27 / &50) + s * (-- &1 / &100)` ASSUME_TAC THENL
   [ASM_CASES_TAC `u + a <= c * (&73 / &100) + s` THENL
     [MP_TAC(SPECL [`c:real`; `s:real`; `&19 / &100`; `&101 / &100`]
        CCOS_INCREASING_PROJECTION) THEN
      ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      RASM_ARITH_TAC;
      CCSOP_NFACT_TAC `~linside c s u v a (&73 / &100) (&1)` `v + a <= --s * (&73 / &100) + c` THEN
      MP_TAC(SPECL [`c:real`; `s:real`] CCOS_SHORT_STRONG_PROJECTION) THEN
      ASM_REWRITE_TAC[REAL_POW_2] THEN
      ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `v < --s * (&27 / &50) + c * (-- &1 / &100)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&27 * c <= &46 * s` THENL
     [RASM_ARITH_TAC;
      SUBGOAL_THEN `s < &51 / &100` ASSUME_TAC THENL
       [NLIN_FACTS_TAC [] [`&0 <= (&27 * c - &46 * s) * (&27 * c + &46 * s)`] THEN NLIN_TAC [];
        ALL_TAC] THEN
      CCSOP_NFACT_TAC `~linside c s u v a (&73 / &100) (&1)` `v + a <= --s * (&73 / &100) + c` THEN
      RASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: positive_point_original *)
let CCSOP_POSITIVE_POINT_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&273 / &100) (&3) /\
     ~linside c s u v a (&3) (&3) /\
     ~linside c s u v a (&1543 / &500) (&3)
     ==> linside c s u v a (&127 / &50) (&199 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] CCSOP_POSITIVE_POINT) THEN
  REWRITE_TAC[CCSOP_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;

