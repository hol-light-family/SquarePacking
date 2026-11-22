(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveTopMargins.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveTopMargins).          *)
(* Support margins for the actual top endpoint, both relative-angle signs.   *)
(* The Lean local abbreviations f, g, F, G are written out.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/FullAuxWallPositiveEndpointMargin.ml";;

let FAWPTM_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPTM_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

let FAWPTM_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: defect (private) *)
let FAWPTM_DEFECT = prove
 (`forall b t. c977cc_normal b t ==> &1 - b <= (&3 / &5) * t pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FAWPTM_NORMAL_TAC THEN
  FAWPTM_PROD_TAC `&1 - b` `&3 * b - &2` THEN NLIN_TAC ~deg2:false []);;

(* Lean: c_axis_below *)
let FAWPTM_C_AXIS_BELOW = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t /\ C * t <= S * b
     ==> C * (&2 - b - (&13 / &20) * t pow 2 + (&1 / &20) * b * t) + S * (--(&1 / &20) + (&1 / &20) * t pow 2 + (&13 / &20) * b * t - t) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPTM_NORMAL_TAC THEN
  FAWPTM_PROD_TAC `b:real` `t:real` THEN
  SUBGOAL_THEN `&0 <= (&2 - b - (&13 / &20) * t pow 2 + (&1 / &20) * b * t)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `b:real`]; ALL_TAC] THEN
  FAWPTM_PROD_TAC `t:real` `&1 - b` THEN
  SUBGOAL_THEN `(--(&1 / &20) + (&1 / &20) * t pow 2 + (&13 / &20) * b * t - t) <= &0` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `b:real`]; ALL_TAC] THEN
  FAWPTM_USE C977CSB_SINE_ORDER [`C:real`; `S:real`; `b:real`; `t:real`] THEN
  FAWPTM_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `b:real`; `t:real`] THEN
  FAWPTM_PROD_TAC `(&2 - b - (&13 / &20) * t pow 2 + (&1 / &20) * b * t)` `b - C` THEN
  FAWPTM_PROD_TAC `S - t` `--(--(&1 / &20) + (&1 / &20) * t pow 2 + (&13 / &20) * b * t - t)` THEN
  SUBGOAL_THEN `b * (&2 - b - (&13 / &20) * t pow 2 + (&1 / &20) * b * t) + t * (--(&1 / &20) + (&1 / &20) * t pow 2 + (&13 / &20) * b * t - t) = &2 * b - &1` ASSUME_TAC THENL
  [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: c_axis_above *)
let FAWPTM_C_AXIS_ABOVE = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t /\ S * b <= C * t
     ==> C * (&2 - b - (&37 / &50) * t pow 2 - (&3 / &5) * b * t) + S * ((&3 / &5) - (&3 / &5) * t pow 2 + (&37 / &50) * b * t - t) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FAWPTM_USE FAWPTM_DEFECT [`b:real`; `t:real`] THEN FAWPTM_NORMAL_TAC THEN
  FAWPTM_PROD_TAC `b - t` `b + t` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `b - t:real`] [`t pow 2 <= &1 / &2`; `b * t <= &1 / &2`] THEN
  SUBGOAL_THEN `&0 <= (&2 - b - (&37 / &50) * t pow 2 - (&3 / &5) * b * t)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `&21 * t <= &10 * b` THENL
  [SUBGOAL_THEN `((&3 / &5) - (&3 / &5) * t pow 2 + (&37 / &50) * b * t - t) * b - (&2 - b - (&37 / &50) * t pow 2 - (&3 / &5) * b * t) * t = (&3 / &5) * b - (&63 / &50) * t` ASSUME_TAC THENL
   [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `(&2 - b - (&37 / &50) * t pow 2 - (&3 / &5) * b * t) * t <= ((&3 / &5) - (&3 / &5) * t pow 2 + (&37 / &50) * b * t - t) * b` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   FAWPTM_USE C977CSB_SINE_ORDER [`b:real`; `t:real`; `C:real`; `S:real`] THEN
   FAWPTM_USE C977CSB_LINEAR_ARC_MAX [`b:real`; `t:real`; `C:real`; `S:real`; `(&2 - b - (&37 / &50) * t pow 2 - (&3 / &5) * b * t)`; `((&3 / &5) - (&3 / &5) * t pow 2 + (&37 / &50) * b * t - t)`] THEN
   SUBGOAL_THEN `b * (&2 - b - (&37 / &50) * t pow 2 - (&3 / &5) * b * t) + t * ((&3 / &5) - (&3 / &5) * t pow 2 + (&37 / &50) * b * t - t) = &2 * b - &1` ASSUME_TAC THENL
   [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  FAWPTM_PROD_TAC `&21 * t - &10 * b` `&21 * t + &10 * b` THEN
  SUBGOAL_THEN `&2 / &5 <= t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`&2 / &5 - t`; `&2 / &5 + t`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPTM_PROD_TAC `t - &2 / &5` `t + &2 / &5` THEN
  FAWPTM_PROD_TAC `t:real` `b - &7 / &10` THEN
  SUBGOAL_THEN `(&2 - b - (&37 / &50) * t pow 2 - (&3 / &5) * b * t) <= &81 / &100` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPTM_PROD_TAC `t:real` `&1 - b` THEN
  SUBGOAL_THEN `((&3 / &5) - (&3 / &5) * t pow 2 + (&37 / &50) * b * t - t) <= &1 / &2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `t:real`]; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C - &81 / &100`; SQ_NONNEG `S - &1 / &2`]
    [`(&81 / &100) * C + (&1 / &2) * S < &1`] THEN
  FAWPTM_PROD_TAC `C:real` `&81 / &100 - (&2 - b - (&37 / &50) * t pow 2 - (&3 / &5) * b * t)` THEN
  FAWPTM_PROD_TAC `S:real` `&1 / &2 - ((&3 / &5) - (&3 / &5) * t pow 2 + (&37 / &50) * b * t - t)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: b_axis_above *)
let FAWPTM_B_AXIS_ABOVE = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t /\ S * b <= C * t
     ==> &0 <= &1 + b * (C - &2 + S pow 2 + (&2 / &5) * C * S - (&9 / &10) * S) +
               t * (S - C * S - (&2 / &5) * C pow 2 + (&9 / &10) * C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPTM_NORMAL_TAC THEN
  FAWPTM_PROD_TAC `S:real` `&9 / &10 - (&2 / &5) * C` THEN
  SUBGOAL_THEN `&0 <= (&1 - C + C pow 2 - (&2 / &5) * C * S + (&9 / &10) * S)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `C:real`]; ALL_TAC] THEN
  FAWPTM_PROD_TAC `S:real` `&1 - C` THEN
  FAWPTM_PROD_TAC `C:real` `&9 / &10 - (&2 / &5) * C` THEN
  SUBGOAL_THEN `&0 <= (S * (&1 - C) + C * ((&9 / &10) - (&2 / &5) * C))` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FAWPTM_USE C977CSB_SINE_ORDER [`b:real`; `t:real`; `C:real`; `S:real`] THEN
  FAWPTM_USE C977CSB_COSINE_ORDER [`b:real`; `t:real`; `C:real`; `S:real`] THEN
  FAWPTM_PROD_TAC `(&1 - C + C pow 2 - (&2 / &5) * C * S + (&9 / &10) * S)` `C - b` THEN
  FAWPTM_PROD_TAC `(S * (&1 - C) + C * ((&9 / &10) - (&2 / &5) * C))` `t - S` THEN
  SUBGOAL_THEN `&1 - C * (&1 - C + C pow 2 - (&2 / &5) * C * S + (&9 / &10) * S) + S * (S * (&1 - C) + C * ((&9 / &10) - (&2 / &5) * C)) = &2 * (&1 - C)` ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 + b * (C - &2 + S pow 2 + (&2 / &5) * C * S - (&9 / &10) * S) +
    t * (S - C * S - (&2 / &5) * C pow 2 + (&9 / &10) * C) = &1 - b * (&1 - C + C pow 2 - (&2 / &5) * C * S + (&9 / &10) * S) + t * (S * (&1 - C) + C * ((&9 / &10) - (&2 / &5) * C))`
  SUBST1_TAC THENL
  [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;
