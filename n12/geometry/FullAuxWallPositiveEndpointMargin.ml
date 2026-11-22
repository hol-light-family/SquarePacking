(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveEndpointMargin.lean (Jatloe,  *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveEndpointMargin).      *)
(* Endpoint comparison for the positive outer square: a monotone arc and a   *)
(* single rational disk.  The Lean local abbreviations P, R are written out. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let FAWPEM_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPEM_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

let FAWPEM_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: shallow_margin *)
let FAWPEM_SHALLOW_MARGIN = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t /\ C * t <= S * b
     ==> &0 <= &1 - b * (&1 - C + C pow 2 - (&2 / &5) * C * S) +
               t * (S * (&1 - C) - (&2 / &5) * C pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPEM_NORMAL_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &1 - b * (&1 - C + C pow 2 - (&2 / &5) * C * S) - t * ((&2 / &5) * C pow 2 - S * (&1 - C))
     ==> &0 <= &1 - b * (&1 - C + C pow 2 - (&2 / &5) * C * S) +
               t * (S * (&1 - C) - (&2 / &5) * C pow 2)`) THEN
  ASM_CASES_TAC `S <= (&2 / &5) * C` THENL
  [FAWPEM_PROD_TAC `C:real` `C - (&2 / &5) * S` THEN
   SUBGOAL_THEN `&0 <= (&1 - C + C pow 2 - (&2 / &5) * C * S)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   SUBGOAL_THEN `((&2 / &5) * C pow 2 - S * (&1 - C)) * C - (&1 - C + C pow 2 - (&2 / &5) * C * S) * S = (&2 / &5) * C - S` ASSUME_TAC THENL
   [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 - C + C pow 2 - (&2 / &5) * C * S) * S <= ((&2 / &5) * C pow 2 - S * (&1 - C)) * C` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   FAWPEM_USE C977CSB_SINE_ORDER [`C:real`; `S:real`; `b:real`; `t:real`] THEN
   FAWPEM_USE C977CSB_LINEAR_ARC_MAX [`C:real`; `S:real`; `b:real`; `t:real`; `(&1 - C + C pow 2 - (&2 / &5) * C * S)`; `((&2 / &5) * C pow 2 - S * (&1 - C))`] THEN
   SUBGOAL_THEN `(&1 - C + C pow 2 - (&2 / &5) * C * S) * C + ((&2 / &5) * C pow 2 - S * (&1 - C)) * S = &2 * C - &1` ASSUME_TAC THENL
   [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  FAWPEM_PROD_TAC `&5 * S - &2 * C` `&5 * S + &2 * C` THEN
  SUBGOAL_THEN `C <= &19 / &20` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`C - &19 / &20`; `C + &19 / &20`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPEM_PROD_TAC `C:real` `&1 - C - &1 / &20` THEN
  FAWPEM_PROD_TAC `C:real` `S - &7 / &25` THEN
  SUBGOAL_THEN `(&1 - C + C pow 2 - (&2 / &5) * C * S) <= &9 / &10` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPEM_PROD_TAC `S:real` `&1 - C` THEN
  SUBGOAL_THEN `((&2 / &5) * C pow 2 - S * (&1 - C)) <= &2 / &5` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `S:real`]; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `b - &9 / &10`; SQ_NONNEG `t - &2 / &5`]
    [`(&9 / &10) * b + (&2 / &5) * t < &1`] THEN
  FAWPEM_PROD_TAC `b:real` `&9 / &10 - (&1 - C + C pow 2 - (&2 / &5) * C * S)` THEN
  FAWPEM_PROD_TAC `t:real` `&2 / &5 - ((&2 / &5) * C pow 2 - S * (&1 - C))` THEN
  NLIN_TAC ~deg2:false []);;
