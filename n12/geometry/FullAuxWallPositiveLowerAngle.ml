(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveLowerAngle.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveLowerAngle).          *)
(* Both transverse central-square separators exclude a very small opposite   *)
(* angle.  The Lean local abbreviations P, Q, G, H are written out.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let FAWPLA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPLA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

(* Lean: c_axis *)
let FAWPLA_C_AXIS = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t /\ S <= &1 / &20 /\ &3 / &10 < t
     ==> C * (&2 - b - t + (&3 / &5) * b * t) + S * (b - t + (&3 / &5) * t pow 2) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPLA_NORMAL_TAC THEN
  FAWPLA_PROD_TAC `b + t - &1` `&3 / &2 - (b + t)` THEN
  NLIN_FACTS_TAC [] [`(&4 / &5) * b * t <= b + t - &1`] THEN
  FAWPLA_PROD_TAC `t:real` `b - &7 / &10` THEN
  NLIN_FACTS_TAC [] [`&21 / &100 < b * t`] THEN
  FAWPLA_PROD_TAC `t:real` `&5 / &7 - t` THEN
  FAWPLA_PROD_TAC `b:real` `t:real` THEN
  NLIN_FACTS_TAC [] [`&0 <= (&2 - b - t + (&3 / &5) * b * t)`; `(&2 - b - t + (&3 / &5) * b * t) < &479 / &500`; `(b - t + (&3 / &5) * t pow 2) <= &29 / &35`] THEN
  FAWPLA_PROD_TAC `&1 - C` `(&2 - b - t + (&3 / &5) * b * t)` THEN
  FAWPLA_PROD_TAC `S:real` `&29 / &35 - (b - t + (&3 / &5) * t pow 2)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: b_axis *)
let FAWPLA_B_AXIS = prove
 (`forall C S b t u. c977cc_normal C S /\ c977cc_normal b t /\ S <= &1 / &20 /\
               &3 / &10 < t /\ u <= &1 / &112 /\ &0 <= C * t - S * b
     ==> &0 <= &1 + b * (C - S + S pow 2 + (&2 / &5) * C * S - &2) + t * (C + S + (&2 / &5) * S pow 2 - C * S - &1) - (C * t - S * b) * u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPLA_NORMAL_TAC THEN
  FAWPLA_PROD_TAC `C:real` `&1 - C` THEN
  NLIN_FACTS_TAC [] [`&1 - C <= S pow 2`] THEN
  FAWPLA_PROD_TAC `S:real` `C - &7 / &10` THEN
  SUBGOAL_THEN `--(&1) - (&18 / &25) * S <= (C - S + S pow 2 + (&2 / &5) * C * S - &2)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPLA_PROD_TAC `S:real` `&1 - C` THEN
  SUBGOAL_THEN `--(&3 / &5) * S pow 2 <= (C + S + (&2 / &5) * S pow 2 - C * S - &1)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPLA_PROD_TAC `b:real` `(C - S + S pow 2 + (&2 / &5) * C * S - &2) - (--(&1) - (&18 / &25) * S)` THEN
  FAWPLA_PROD_TAC `S:real` `&1 - b` THEN
  FAWPLA_PROD_TAC `t:real` `(C + S + (&2 / &5) * S pow 2 - C * S - &1) - --(&3 / &5) * S pow 2` THEN
  FAWPLA_PROD_TAC `&1 / &20 - S` `&1 / &20 + S` THEN
  FAWPLA_PROD_TAC `t:real` `&1 / &400 - S pow 2` THEN
  FAWPLA_PROD_TAC `t:real` `&1 - C` THEN
  FAWPLA_PROD_TAC `S:real` `b:real` THEN
  SUBGOAL_THEN `C * t - S * b <= t` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPLA_PROD_TAC `C * t - S * b` `&1 / &100 - u` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&1 - b`] [`t pow 2 / &2 <= &1 - b`] THEN
  FAWPLA_PROD_TAC `t:real` `t - &3 / &10` THEN
  NLIN_TAC ~deg2:false []);;
