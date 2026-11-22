(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCornerSmallBottom.lean (Jatloe,          *)
(* N12-jatloe; namespace N12Compact.PositiveCornerSmallBottom).              *)
(* The central escape confines a negative bottom singleton to a small angle. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/PositiveWallUpperVImpossible.ml";;

let PCSB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCSB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PCSB_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: tilt *)
let PCSB_TILT = prove
 (`forall c t C S. c977cc_normal c t /\ c977cc_normal C S /\
     (C + S) * (&1 - (&7 / &20) * C) < &1 /\
     c977cc_boundary c t < c * (&2 + C * S - C - S) + t * (&2 - S pow 2 - C + S)
     ==> t < &1 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] PWUVI_COSINE_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN PCSB_NORMAL_TAC THEN
  PCSB_PROD_TAC `C - &81 / &100` `C + &81 / &100` THEN
  SUBGOAL_THEN `S <= &59 / &100` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCSB_PRODLT_TAC `S - &59 / &100` `S + &59 / &100` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCSB_PROD_TAC `C - S - &11 / &50` `C - S + &11 / &50` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C + S - &7 / &5`] [`C + S <= &7 / &5`] THEN
  PCSB_PROD_TAC `&7 / &5 - (C + S)` `C + S - &3 / &5` THEN
  PCSB_PROD_TAC `C - S` `&1 - (C + S) / &2` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &1`]
    [`&2 + C * S - C - S <= &27 / &25`; `&2 - S pow 2 - C + S <= &3 / &2`;
     `c <= &1 - t pow 2 / &2`] THEN
  PCSB_PROD_TAC `c - t` `c + t` THEN
  SUBGOAL_THEN `t <= &3 / &4` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCSB_PRODLT_TAC `t - &3 / &4` `t + &3 / &4` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCSB_PROD_TAC `t:real` `&1 - t` THEN
  PCSB_PROD_TAC `t * (&1 - t)` `&1 - c` THEN
  SUBGOAL_THEN `c * c977cc_boundary c t = c + c * t + t * (&1 - t)` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_boundary] THEN
   (SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &2 * t - t pow 2 <= c977cc_boundary c t` ASSUME_TAC THENL
  [MATCH_MP_TAC C977CSB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
   CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCSB_PROD_TAC `c:real` `&27 / &25 - (&2 + C * S - C - S)` THEN
  PCSB_PROD_TAC `t:real` `&3 / &2 - (&2 - S pow 2 - C + S)` THEN
  SUBGOAL_THEN `--(&2 / &25) + (&1 / &2) * t - (&23 / &50) * t pow 2 < &0` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  PCSB_PROD_TAC `t - &1 / &5` `&1 / &2 - (&23 / &50) * (t + &1 / &5)` THEN
  NLIN_TAC ~deg2:false []);;
