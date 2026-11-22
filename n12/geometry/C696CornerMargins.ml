(* ========================================================================= *)
(* Port of Compact/Geometry/C696CornerMargins.lean (Jatloe, N12-jatloe)      *)
(* (namespace N12Compact.C696CornerMargins).                                 *)
(* Continuous margins for a positive bottom singleton and a negative        *)
(* central square.                                                           *)
(* Note: Lean variable T is renamed TT (T is truth in HOL).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let C696CM_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C696CM_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let C696CM_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let C696CM_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: boundary (definition) *)
let c696cm_boundary = new_definition
 `c696cm_boundary (c:real) s = &1 + s / c - &2 * s - (&457 / &500) * s pow 2 / c`;;

(* Lean: sum_margin (private) *)
let C696CM_SUM_MARGIN = prove
 (`forall c s. c977cc_normal c s ==> (&4 / &5) * c * s <= c + s - &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C696CM_NORMAL_TAC THEN
  C696CM_PROD_TAC `c + s - &1` `&3 / &2 - (c + s)` THEN NLIN_TAC ~deg2:false []);;

(* Lean: longitudinal *)
let C696CM_LONGITUDINAL = prove
 (`forall c s C TT. c977cc_normal c s /\ c977cc_normal C TT
     ==> c * (&3 / &2 + (&1 / &2) * TT pow 2 - TT) + s * (&2 + (&1 / &2) * C * TT - C)
         < (&187 / &100) * c + (&19 / &25) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C696CM_USE C696CM_SUM_MARGIN [`C:real`; `TT:real`] THEN C696CM_NORMAL_TAC THEN
  C696CM_PROD_TAC `TT:real` `C - TT` THEN
  C696CM_PROD_TAC `C - TT` `C + TT` THEN
  NLIN_FACTS_TAC [] [`TT pow 2 <= &1 / &2`] THEN
  NLIN_FACTS_TAC [] [`&9 / &10 <= (C + TT) * (&1 - TT / &2)`] THEN
  C696CM_PROD_TAC `C:real` `TT:real` THEN
  SUBGOAL_THEN `C - &31 / &25 - C * TT / &2 <= &0` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  C696CM_PROD_TAC `c - s` `--(C - &31 / &25 - C * TT / &2)` THEN
  C696CM_PROD_TAC `c:real` `(C + TT) * (&1 - TT / &2) - &9 / &10` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: comparison *)
let C696CM_COMPARISON = prove
 (`forall c s f g. c977cc_normal c s /\ f <= &1 /\ &33 / &20 <= g
             ==> c * f - s * g <= c696cm_boundary c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C696CM_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &7 / &20`; SQ_NONNEG `s - &457 / &500`]
    [`(&7 / &20) * c + (&457 / &500) * s <= &1`] THEN
  C696CM_PROD_TAC `c:real` `&1 - c` THEN
  C696CM_PROD_TAC `s:real` `&1 - ((&7 / &20) * c + (&457 / &500) * s)` THEN
  SUBGOAL_THEN `c * c696cm_boundary c s = c + s - &2 * c * s - (&457 / &500) * s pow 2`
  ASSUME_TAC THENL
  [REWRITE_TAC[c696cm_boundary] THEN
   (SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `c - (&33 / &20) * s <= c696cm_boundary c s` ASSUME_TAC THENL
  [MATCH_MP_TAC C696CM_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
   CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  C696CM_PROD_TAC `c:real` `&1 - f` THEN
  C696CM_PROD_TAC `s:real` `g - &33 / &20` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: left_comparison *)
let C696CM_LEFT_COMPARISON = prove
 (`forall c s C TT. c977cc_normal c s /\ c977cc_normal C TT
     ==> c * (&2 + (TT - &1) / C - TT) - s * (&1 + C) <= c696cm_boundary c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C696CM_COMPARISON THEN
  ASM_REWRITE_TAC[] THEN C696CM_NORMAL_TAC THEN
  CONJ_TAC THENL [ALL_TAC; RASM_ARITH_TAC] THEN
  MATCH_MP_TAC C696CM_LE_BY_POS THEN EXISTS_TAC `C:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * (&1 - (&2 + (TT - &1) / C - TT)) = (&1 - C) * (&1 - TT)`
  SUBST1_TAC THENL
  [(SUBGOAL_THEN `~(C = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: near_comparison *)
let C696CM_NEAR_COMPARISON = prove
 (`forall c s C TT. c977cc_normal c s /\ c977cc_normal C TT
     ==> c * (&2 - (&22 / &25) * TT pow 2 + C * TT - C - TT) -
         s * (&1 + TT pow 2 + (&22 / &25) * C * TT + C - TT) <= c696cm_boundary c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C696CM_COMPARISON THEN
  ASM_SIMP_TAC[C977CC_LOW_COEFFICIENT] THEN C696CM_NORMAL_TAC THEN
  C696CM_PROD_TAC `TT:real` `C - &7 / &10` THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `TT - &24 / &125`]);;

(* Lean: central_axis *)
let C696CM_CENTRAL_AXIS = prove
 (`forall c s C TT. c977cc_normal c s /\ c977cc_normal C TT /\ &0 < s
     ==> &2 * (C + TT) <= (TT / s) * (&1 - c + s) + (c * TT + s * C) +
                          (c * C - s * TT) + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C696CM_USE C696CM_SUM_MARGIN [`c:real`; `s:real`] THEN C696CM_NORMAL_TAC THEN
  C696CM_PROD_TAC `s:real` `c - s` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`(&2 - c - s) pow 2 + s pow 2 <= &1`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&2 - c - s - C`; SQ_NONNEG `s - TT:real`]
    [`(&2 - c - s) * C + s * TT <= &1`] THEN
  MATCH_MP_TAC C696CM_LE_BY_POS THEN EXISTS_TAC `s:real` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s * (((TT / s) * (&1 - c + s) + (c * TT + s * C) + (c * C - s * TT) + &1) -
                     &2 * (C + TT)) =
                s * (&1 - ((&2 - c - s) * C + s * TT)) + TT * ((&1 - c) * (&1 - s))`
  SUBST1_TAC THENL
  [(SUBGOAL_THEN `~(s = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN RASM_ARITH_TAC);;
