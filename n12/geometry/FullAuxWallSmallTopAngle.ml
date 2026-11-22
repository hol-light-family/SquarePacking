(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallSmallTopAngle.lean (Jatloe, N12-jatloe)*)
(* (namespace N12Compact.FullAuxWallSmallTopAngle).                          *)
(* Continuous bound for the surviving outer-central angle.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let FAWSTA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWSTA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let FAWSTA_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: small_top_angle *)
let FAWSTA_SMALL_TOP_ANGLE = prove
 (`forall a c s C S b t u v.
     c977cc_normal c s /\ c977cc_normal C S /\ c977cc_normal b t /\
     &1 < a /\ &0 < s /\ &4 * s <= c /\ &4 * S <= C /\ &0 < u /\ &0 < v /\
     (c * C - s * S) * u + (c * S + s * C) * v < (&13 / &50) * s /\
     a * (&1 + (t * C + b * S)) + (b * C - t * S) * v <= b + t + (t * C + b * S) * u
     ==> t < &3 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWSTA_NORMAL_TAC THEN
  (* cosine *)
  FAWSTA_PROD_TAC `C - &4 * S` `C + &4 * S` THEN
  SUBGOAL_THEN `&9 / &10 <= C` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FAWSTA_PRODLT_TAC `&9 / &10 - C` `&9 / &10 + C` THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  (* alpha *)
  FAWSTA_PROD_TAC `S:real` `c - &4 * s` THEN
  FAWSTA_PROD_TAC `c:real` `C - &4 * S` THEN
  NLIN_FACTS_TAC [] [`(&15 / &16) * c * C <= c * C - s * S`] THEN
  FAWSTA_PROD_TAC `c:real` `C - &9 / &10` THEN
  SUBGOAL_THEN `(&27 / &32) * c <= c * C - s * S` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * S + s * C` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  (* u small *)
  SUBGOAL_THEN `u < &2 / &25` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FAWSTA_PROD_TAC `c * C - s * S` `u - &2 / &25` THEN
   FAWSTA_PROD_TAC `c * S + s * C` `v:real` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  (* k = t*C + b*S *)
  SUBGOAL_THEN `&0 <= t * C + b * S` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  FAWSTA_PROD_TAC `t:real` `C + S - &1` THEN
  FAWSTA_PROD_TAC `S:real` `b - t` THEN
  SUBGOAL_THEN `t <= t * C + b * S` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSTA_PROD_TAC `t:real` `&1 - C` THEN
  FAWSTA_PROD_TAC `S:real` `&1 - b` THEN
  SUBGOAL_THEN `t * C + b * S <= t + &1 / &4` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSTA_PROD_TAC `C:real` `b - t` THEN
  FAWSTA_PROD_TAC `t:real` `C - S` THEN
  SUBGOAL_THEN `&0 <= b * C - t * S` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  (* deficit *)
  FAWSTA_PRODLT_TAC `a - &1` `&1 + (t * C + b * S)` THEN
  FAWSTA_PROD_TAC `b * C - t * S` `v:real` THEN
  SUBGOAL_THEN `&1 - b < (t * C + b * S) * u` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSTA_PROD_TAC `(t + &1 / &4) - (t * C + b * S)` `u:real` THEN
  FAWSTA_PRODLT_TAC `t + &1 / &4` `&2 / &25 - u` THEN
  SUBGOAL_THEN `&1 - b < (&2 / &25) * (t + &1 / &4)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&1 - b`] [`t pow 2 / &2 <= &1 - b`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FAWSTA_PROD_TAC `t:real` `t - &3 / &10` THEN
  NLIN_TAC ~deg2:false []);;
