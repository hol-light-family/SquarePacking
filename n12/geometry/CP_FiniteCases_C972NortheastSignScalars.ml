(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972NortheastSignScalars.lean      *)
(* (namespace N12Compact.FiniteCases.C972Local.NortheastScalars).            *)
(* Normal is c977cc_normal.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: north_transverse *)
let FC972NS_NORTH_TRANSVERSE = prove
 (`forall c s d r. c977cc_normal c s /\ c977cc_normal d r /\ &4 / &5 < c /\ s < &1 / &2
     ==> &0 < d * (c - &61 / &100 - (&6 / &25) * c pow 2) +
              r * (&13 / &20 - s + (&6 / &25) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c - &4 / &5) * (&1 - (&6 / &25) * (c + &4 / &5))`;
    `&0 < c - &61 / &100 - (&6 / &25) * c pow 2`; `&0 <= c * s`;
    `&0 < &13 / &20 - s + (&6 / &25) * c * s`;
    `&0 < d * (c - &61 / &100 - (&6 / &25) * c pow 2)`;
    `&0 <= r * (&13 / &20 - s + (&6 / &25) * c * s)`] THEN
  RASM_ARITH_TAC);;

(* Lean: A (definition) *)
let fc972ns_A = new_definition
 `fc972ns_A (d:real) (r:real) = &17 / &20 - r + (&92 / &125) * r pow 2 + (&7 / &20) * d * r`;;

(* Lean: B (definition) *)
let fc972ns_B = new_definition
 `fc972ns_B (d:real) (r:real) = &1 - d - (&7 / &20) * r pow 2 + (&92 / &125) * d * r`;;

(* Lean: source_transverse *)
let FC972NS_SOURCE_TRANSVERSE = prove
 (`forall c s d r. c977cc_normal c s /\ c977cc_normal d r
     ==> &0 < &1 - c * fc972ns_A d r - s * fc972ns_B d r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  REWRITE_TAC[fc972ns_A; fc972ns_B] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d - r:real`; SQ_NONNEG `(&1 / &2) * c - (&17 / &20) * s`;
                  SQ_NONNEG `(&17 / &20) * c + (&1 / &2) * s - &1`]
   [`r <= &5 / &7`; `(&92 / &125) * r + (&7 / &20) * d <= &1`;
    `&0 <= r * (&1 - ((&92 / &125) * r + (&7 / &20) * d))`;
    `&17 / &20 - r + (&92 / &125) * r pow 2 + (&7 / &20) * d * r <= &17 / &20`;
    `&0 <= (&1 - d) * (d - &7 / &10)`; `&1 - d <= (&10 / &17) * r pow 2`;
    `&0 <= (d - r) * (d + r)`; `r pow 2 <= &1 / &2`; `d * r <= &1 / &2`;
    `&1 - d - (&7 / &20) * r pow 2 + (&92 / &125) * d * r < &1 / &2`;
    `(&17 / &20) * c + (&1 / &2) * s < &1`;
    `&0 <= c * (&17 / &20 - (&17 / &20 - r + (&92 / &125) * r pow 2 + (&7 / &20) * d * r))`;
    `&0 <= s * (&1 / &2 - (&1 - d - (&7 / &20) * r pow 2 + (&92 / &125) * d * r))`] THEN
  RASM_ARITH_TAC);;
