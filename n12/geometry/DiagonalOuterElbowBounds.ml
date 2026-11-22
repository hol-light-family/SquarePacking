(* ========================================================================= *)
(* Port of Compact/Geometry/DiagonalOuterElbowBounds.lean (Jatloe,           *)
(* N12-jatloe; namespace N12Compact.DiagonalOuterElbowBounds).               *)
(* Continuous margins for an elbow owning the outer top auxiliary.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let DOEB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let DOEB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let DOEB_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: shallow_u *)
let DOEB_SHALLOW_U = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < d * (c - &2 / &5 + (&7 / &20) * s pow 2 - (&7 / &20) * c * s) +
              t * (&13 / &20 - s + (&7 / &20) * s pow 2 + (&7 / &20) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DOEB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s:real`] [`c * s <= &1 / &2`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
    [`&0 < c - &2 / &5 + (&7 / &20) * s pow 2 - (&7 / &20) * c * s`] THEN
  DOEB_PROD_TAC `s:real` `c + s - &1` THEN
  NLIN_FACTS_TAC []
    [`&0 <= &13 / &20 - s + (&7 / &20) * s pow 2 + (&7 / &20) * c * s`] THEN
  DOEB_PRODLT_TAC `d:real` `c - &2 / &5 + (&7 / &20) * s pow 2 - (&7 / &20) * c * s` THEN
  DOEB_PROD_TAC `t:real` `&13 / &20 - s + (&7 / &20) * s pow 2 + (&7 / &20) * c * s` THEN
  RASM_ARITH_TAC);;

(* Lean: shallow_v *)
let DOEB_SHALLOW_V = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 < d * (c - &3 / &4 + (&7 / &10) * s pow 2) +
              t * (&13 / &20 - s + (&7 / &10) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DOEB_NORMAL_TAC THEN
  DOEB_PROD_TAC `&1 - c` `(&7 / &10) * c - &3 / &10` THEN
  NLIN_FACTS_TAC [] [`&0 < c - &3 / &4 + (&7 / &10) * s pow 2`] THEN
  DOEB_PROD_TAC `s:real` `c - &7 / &10` THEN
  NLIN_FACTS_TAC [] [`&0 <= &13 / &20 - s + (&7 / &10) * c * s`] THEN
  DOEB_PRODLT_TAC `d:real` `c - &3 / &4 + (&7 / &10) * s pow 2` THEN
  DOEB_PROD_TAC `t:real` `&13 / &20 - s + (&7 / &10) * c * s` THEN
  RASM_ARITH_TAC);;

(* Lean: wall_coefficients *)
let DOEB_WALL_COEFFICIENTS = prove
 (`forall d t. c977cc_normal d t /\ &2 * t <= d
         ==> &2 / &5 + (&343 / &500) * t pow 2 - d * t <= &2 / &5 /\
             t pow 2 + (&343 / &500) * d * t <= &3 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DOEB_NORMAL_TAC THEN
  DOEB_PROD_TAC `t:real` `d - &2 * t` THEN
  DOEB_PROD_TAC `d - &2 * t` `d + &2 * t` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d - t:real`] [`t pow 2 <= &1 / &5`; `d * t <= &1 / &2`] THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `t:real`]);;

(* Lean: shallow_incoming *)
let DOEB_SHALLOW_INCOMING = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &2 * t <= d
     ==> c * (&2 / &5 + (&343 / &500) * t pow 2 - d * t) +
         s * (t pow 2 + (&343 / &500) * d * t) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] DOEB_WALL_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DOEB_NORMAL_TAC THEN
  DOEB_PROD_TAC `c:real` `&2 / &5 - (&2 / &5 + (&343 / &500) * t pow 2 - d * t)` THEN
  DOEB_PROD_TAC `s:real` `&3 / &5 - (t pow 2 + (&343 / &500) * d * t)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: steep *)
let DOEB_STEEP = prove
 (`forall c s d t. c977cc_normal s c /\ c977cc_normal d t
     ==> &0 < d * (s - (&13 / &25) * s pow 2 - &7 / &50) +
              t * c * (&1 - (&13 / &25) * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DOEB_NORMAL_TAC THEN
  DOEB_PROD_TAC `s:real` `&1 - s` THEN
  NLIN_FACTS_TAC [] [`&0 < s - (&13 / &25) * s pow 2 - &7 / &50`] THEN
  SUBGOAL_THEN `&0 <= t * c` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  DOEB_PROD_TAC `t * c` `&1 - (&13 / &25) * s` THEN
  DOEB_PRODLT_TAC `d:real` `s - (&13 / &25) * s pow 2 - &7 / &50` THEN
  RASM_ARITH_TAC);;
