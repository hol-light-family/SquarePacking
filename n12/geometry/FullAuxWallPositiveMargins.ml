(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveMargins.lean (Jatloe,         *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveMargins).             *)
(* Continuous support coefficients for the positive opposite central square. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let FAWPM_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPM_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: F (definition) *)
let fawpm_f = new_definition
 `fawpm_f (c:real) s = &2 / &5 + s - (&37 / &50) * c * s + (&2 / &5) * s pow 2`;;

(* Lean: G (definition) *)
let fawpm_g = new_definition
 `fawpm_g (c:real) s = &2 - c - (&37 / &50) * s pow 2 - (&2 / &5) * c * s`;;

(* Lean: coefficients *)
let FAWPM_COEFFICIENTS = prove
 (`forall c s. c977cc_normal c s /\ &4 * s <= c
         ==> &0 <= fawpm_f c s /\ fawpm_f c s <= fawpm_g c s /\
             fawpm_f c s + fawpm_g c s <= &7 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPM_NORMAL_TAC THEN
  REWRITE_TAC[fawpm_f; fawpm_g] THEN
  FAWPM_PROD_TAC `c - &4 * s` `c + &4 * s` THEN
  SUBGOAL_THEN `&24 / &25 <= c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`&24 / &25 - c`; `&24 / &25 + c`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWPM_PROD_TAC `&1 - c` `c - &1 / &2` THEN
  NLIN_FACTS_TAC [] [`&1 - c <= (&2 / &3) * s pow 2`] THEN
  FAWPM_PROD_TAC `s:real` `&1 - (&37 / &50) * c` THEN
  FAWPM_PROD_TAC `s:real` `&1 / &4 - s` THEN
  FAWPM_PROD_TAC `c:real` `s:real` THEN
  FAWPM_PROD_TAC `s:real` `c - &4 * s` THEN
  FAWPM_PROD_TAC `s:real` `c - &24 / &25` THEN
  REPEAT CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`]);;

(* Lean: margin *)
let FAWPM_MARGIN = prove
 (`forall c s C S. c977cc_normal c s /\ c977cc_normal C S /\ &4 * s <= c
             ==> C * fawpm_f c s + S * fawpm_g c s <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FAWPM_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `c977cc_normal C S` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  FAWPM_PROD_TAC `fawpm_g c s - fawpm_f c s` `C - S` THEN
  FAWPM_PROD_TAC `fawpm_f c s + fawpm_g c s` `&10 / &7 - (C + S)` THEN
  NLIN_TAC ~deg2:false []);;
