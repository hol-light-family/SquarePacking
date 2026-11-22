(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveUpperAngle.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveUpperAngle).          *)
(* Uniform upper-angle obstruction for the two positive C/B support modes.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let FAWPUA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPUA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

(* Lean: outer_bounds (private) *)
let FAWPUA_OUTER_BOUNDS = prove
 (`forall b t. c977cc_normal b t /\ &23 / &50 <= t
         ==> b <= &89 / &100 /\ &67 / &50 <= b + t /\ t <= &5 / &7`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPUA_NORMAL_TAC THEN
  SUBGOAL_THEN `t <= &5 / &7` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FAWPUA_PROD_TAC `t - &23 / &50` `t + &23 / &50` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `b - &89 / &100`] [`b <= &89 / &100`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FAWPUA_PROD_TAC `b - &23 / &50` `t - &23 / &50` THEN
  FAWPUA_PROD_TAC `&67 / &50 - (b + t)` `b + t + &21 / &50` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: c_axis *)
let FAWPUA_C_AXIS = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t /\
             S <= &11 / &50 /\ &23 / &50 <= t
             ==> C * (&2 - b - t + (&3 / &5) * b * t) +
                 S * (b - t + (&3 / &5) * t pow 2) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] FAWPUA_OUTER_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FAWPUA_NORMAL_TAC THEN
  FAWPUA_PROD_TAC `&89 / &100 - b` `&1 - (&3 / &10) * (b + t + &67 / &50)` THEN
  NLIN_FACTS_TAC [] [`&2 - b - t + (&3 / &5) * b * t <= &22467 / &25000`] THEN
  FAWPUA_PROD_TAC `t - &23 / &50` `&1 - (&3 / &5) * (t + &23 / &50)` THEN
  NLIN_FACTS_TAC [] [`b - t + (&3 / &5) * t pow 2 <= &3481 / &6250`] THEN
  FAWPUA_PROD_TAC `C:real` `&22467 / &25000 - (&2 - b - t + (&3 / &5) * b * t)` THEN
  FAWPUA_PROD_TAC `S:real` `&3481 / &6250 - (b - t + (&3 / &5) * t pow 2)` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C - &1`] [`C <= &1 - S pow 2 / &2`] THEN
  FAWPUA_PROD_TAC `&11 / &50 - S`
    `(&3481 / &6250) - (&22467 / &50000) * (S + &11 / &50)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: b_axis *)
let FAWPUA_B_AXIS = prove
 (`forall C S b t u. c977cc_normal C S /\ c977cc_normal b t /\
               S <= &11 / &50 /\ &23 / &50 <= t /\ u <= &1 / &1000 /\
               S * b <= C * t
               ==> &0 <= &1 + b * (C - S + S pow 2 + (&2 / &5) * C * S - &2) +
                         t * (C + S + (&2 / &5) * S pow 2 - C * S - &1) -
                         (C * t - S * b) * u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] FAWPUA_OUTER_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FAWPUA_NORMAL_TAC THEN
  FAWPUA_PROD_TAC `&11 / &50 - S` `&11 / &50 + S` THEN
  SUBGOAL_THEN `&97 / &100 <= C` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FAWPUA_PROD_TAC `&97 / &100 - C` `&97 / &100 + C` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPUA_PROD_TAC `&1 - C` `(&51 / &100) * C - &49 / &100` THEN
  NLIN_FACTS_TAC [] [`&1 - C <= (&51 / &100) * S pow 2`] THEN
  FAWPUA_PROD_TAC `(&51 / &100) * S pow 2 - (&1 - C)` `&1 + (&2 / &5) * S` THEN
  FAWPUA_PROD_TAC `S pow 2` `&49 / &100 - (&51 / &250) * S - &89 / &200` THEN
  NLIN_FACTS_TAC []
    [`--(&1) - (&3 / &5) * S + (&89 / &200) * S pow 2 <=
      C - S + S pow 2 + (&2 / &5) * C * S - &2`] THEN
  FAWPUA_PROD_TAC `(&51 / &100) * S pow 2 - (&1 - C)` `&1 - S` THEN
  FAWPUA_PROD_TAC `S:real` `S pow 2` THEN
  NLIN_FACTS_TAC []
    [`--(&11 / &100) * S pow 2 <= C + S + (&2 / &5) * S pow 2 - C * S - &1`] THEN
  FAWPUA_PROD_TAC `b:real`
    `(C - S + S pow 2 + (&2 / &5) * C * S - &2) -
     (--(&1) - (&3 / &5) * S + (&89 / &200) * S pow 2)` THEN
  FAWPUA_PROD_TAC `t:real`
    `(C + S + (&2 / &5) * S pow 2 - C * S - &1) - --(&11 / &100) * S pow 2` THEN
  FAWPUA_PROD_TAC `S pow 2` `(&89 / &200) * b - (&11 / &100) * t - &23 / &100` THEN
  FAWPUA_PROD_TAC `&89 / &100 - b` `&1 + (&3 / &5) * S` THEN
  FAWPUA_PROD_TAC `t:real` `&1 - C` THEN
  FAWPUA_PROD_TAC `S:real` `b:real` THEN
  SUBGOAL_THEN `C * t - S * b <= t` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPUA_PROD_TAC `C * t - S * b` `&1 / &1000 - u` THEN
  FAWPUA_PROD_TAC `&11 / &50 - S` `(&267 / &500) - (&23 / &100) * (S + &11 / &50)` THEN
  NLIN_TAC ~deg2:false []);;
