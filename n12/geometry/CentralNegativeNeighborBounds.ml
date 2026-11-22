(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeNeighborBounds.lean               *)
(* (namespace N12Compact.CentralNegativeNeighborBounds).                     *)
(* A negative southeast neighbour sharpens the positive central owner's      *)
(* upper support.  Normal c s is c977cc_normal c s; cosine_defect is         *)
(* URNPLB_COSINE_DEFECT, disk_margin is URCLB_DISK_MARGIN.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightNegativePairLongitudinalBounds.ml";;

let CNNB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let CNNB_DISK tm a b =
  MP_TAC(SPECL [fst tm; snd tm; a; b] URCLB_DISK_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC];;

(* Lean: excess (def) *)
let CNNB_EXCESS_DEF = new_definition
 `cnnb_excess (C:real) (S:real) (c:real) (t:real) =
    c - &1 + (&7 / &20) * t + t * (&1 - C) +
    S * (--c + (&7 / &20) * (c + t) * C + (&7 / &20) * (c - t) * S)`;;

(* Lean: small_of_positive *)
let CNNB_SMALL_OF_POSITIVE = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t /\ &0 < cnnb_excess C S c t
             ==> S < &2 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] URNPLB_COSINE_DEFECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CNNB_DISK (`c:real`,`t:real`) `&4 / &5` `&263 / &500` THEN
  C977CSB_NORMAL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[CNNB_EXCESS_DEF]) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C / &4 - (&7 / &20) * S`;
                  SQ_NONNEG `(&7 / &20) * C + S / &4 - &11 / &25`]
   [`&0 <= t * ((&3 / &5) * S pow 2 - (&1 - C))`;
    `(&7 / &20) * (C + S) <= &1 / &2`;
    `((&7 / &20) * C + S / &4) pow 2 <= &37 / &200`;
    `(&7 / &20) * C + S / &4 <= &11 / &25`;
    `&0 <= c * (&1 / &2 - (&7 / &20) * (C + S))`;
    `&0 <= t * (&11 / &25 - ((&7 / &20) * C + S / &4))`;
    `(&7 / &20) * (c + t) * C + ((&7 / &20) * c + t / &4) * S <= c / &2 + (&11 / &25) * t`;
    `&0 <= S * ((c / &2 + (&11 / &25) * t) -
                ((&7 / &20) * (c + t) * C + ((&7 / &20) * c + t / &4) * S))`] THEN
  REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
  NLIN_FACTS_TAC [] [`&0 <= c / &2 - (&11 / &25) * t`;
                     `&0 <= (S - &2 / &5) * (c / &2 - (&11 / &25) * t)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: upper_bound *)
let CNNB_UPPER_BOUND = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t /\ S <= &2 / &5
             ==> cnnb_excess C S c t <= (&9 / &100) * C * (C * c - S * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] URNPLB_COSINE_DEFECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CNNB_EXCESS_DEF] THEN
  NLIN_FACTS_TAC []
   [`&0 <= t * ((&3 / &5) * S pow 2 - (&1 - C))`;
    `&0 <= (&7 / &20) * c + (&11 / &25) * t`; `&0 <= (&11 / &25) * c + t / &4`;
    `&0 <= ((&7 / &20) * c + (&11 / &25) * t) * (&1 - C)`;
    `&0 <= ((&11 / &25) * c + t / &4) * (&2 / &5 - S)`;
    `--c + ((&7 / &20) * c + (&11 / &25) * t) * C + ((&11 / &25) * c + t / &4) * S <=
     --(&237 / &500) * c + (&27 / &50) * t`;
    `&0 <= S * ((--(&237 / &500) * c + (&27 / &50) * t) -
          (--c + ((&7 / &20) * c + (&11 / &25) * t) * C + ((&11 / &25) * c + t / &4) * S))`] THEN
  ASM_CASES_TAC `--(&237 / &500) * c + (&27 / &50) * t <= &0` THENL
   [CNNB_DISK (`c:real`,`t:real`) `&91 / &100` `&7 / &20` THEN
    NLIN_FACTS_TAC [] [`&0 <= S * --(--(&237 / &500) * c + (&27 / &50) * t)`] THEN
    NLIN_TAC ~deg2:false [CNNB_EQ_HINT `(&9 / &100) * c` (ASSUME `C pow 2 + S pow 2 = &1`)];
    CNNB_DISK (`c:real`,`t:real`) `&1801 / &2500` `&283 / &500` THEN
    NLIN_FACTS_TAC []
     [`&0 <= (&2 / &5 - S) * (--(&237 / &500) * c + (&27 / &50) * t)`] THEN
    NLIN_TAC ~deg2:false [CNNB_EQ_HINT `(&9 / &100) * c` (ASSUME `C pow 2 + S pow 2 = &1`)]]);;

(* Lean: own_coefficients *)
let CNNB_OWN_COEFFICIENTS = prove
 (`forall c t. c977cc_normal c t
         ==> (&1 - c) * (&1 - t) <= &4 / &45 /\ &1 / &2 <= c - t + t pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] URNPLB_COSINE_DEFECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t - &2 / &3`]
   [`&0 <= (&1 - t) * ((&3 / &5) * t pow 2 - (&1 - c))`;
    `&0 <= (t - &2 / &3) pow 2 * (t + &1 / &3)`;
    `&0 <= (c - t) * (&1 - (c + t) / &2)`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;
