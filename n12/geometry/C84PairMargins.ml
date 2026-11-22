(* ========================================================================= *)
(* Port of Compact/Geometry/C84PairMargins.lean                              *)
(* (namespace N12Compact.C84PairMargins).                                    *)
(* Normal c s is c977cc_normal c s (C977CornerCubic).                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: A (def) *)
let C84PM_A_DEF = new_definition
 `c84pm_a (c:real) (s:real) =
    &13 / &50 + (&13 / &50) * s pow 2 - (&43 / &500) * c * s - s`;;

(* Lean: D (def) *)
let C84PM_D_DEF = new_definition
 `c84pm_d (c:real) (s:real) =
    -- &1 - (&43 / &500) * s pow 2 - (&13 / &50) * c * s + c`;;

(* Lean: arc (private) *)
let C84PM_ARC = prove
 (`forall c s. c977cc_normal c s ==> &1 + (&4 / &5) * c * s <= c + s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  NLIN_FACTS_TAC [] [`&0 <= (c + s - &1) * (&1 - (&2 / &5) * (c + s + &1))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: margins *)
let C84PM_MARGINS = prove
 (`forall c s. c977cc_normal c s /\ &3 / &10 <= s
         ==> c84pm_a c s < &0 /\ c84pm_d c s <= &0 /\
             &35 * c84pm_a c s - &9 * c84pm_d c s < &0 /\
             c84pm_a c s - c84pm_d c s - &13 / &50 < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C84PM_ARC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REWRITE_TAC[C84PM_A_DEF; C84PM_D_DEF] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s - &71 / &100`]
   [`&0 <= (c - s) * (c + s)`; `s pow 2 <= &1 / &2`; `s <= &71 / &100`;
    `&0 <= (s - &3 / &10) * (&71 / &100 - s)`; `&0 <= s * (c - s)`; `&0 < c * s`;
    `&0 <= (&1 - c) * ((&3 / &5) * c - &2 / &5)`; `&1 - c <= (&3 / &5) * s pow 2`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [SQ_NONNEG `s:real`]);;

(* Lean: diagonal *)
let C84PM_DIAGONAL = prove
 (`forall c s. c977cc_normal c s /\ &3 / &10 <= s
         ==> &0 < c + s - &1 - (&87 / &500) * c * s - (&173 / &500) * s pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o MATCH_MP C84PM_MARGINS) THEN
  REWRITE_TAC[C84PM_A_DEF; C84PM_D_DEF] THEN REAL_ARITH_TAC);;

(* Lean: parallel *)
let C84PM_PARALLEL = prove
 (`forall c s. c977cc_normal c s ==> &0 < &1 - (&13 / &20) * c - (&61 / &100) * s`,
  REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&61 / &100) * c - (&13 / &20) * s`]
   [`((&13 / &20) * c + (&61 / &100) * s) pow 2 <= &3973 / &5000`] THEN
  NLIN_TAC [SQ_NONNEG `(&13 / &20) * c + (&61 / &100) * s - &1`]);;
