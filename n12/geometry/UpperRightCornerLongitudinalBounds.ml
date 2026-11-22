(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightCornerLongitudinalBounds.lean          *)
(* (Jatloe, N12-jatloe; namespace                                            *)
(*  N12Compact.UpperRightCornerLongitudinalBounds).                          *)
(* Continuous scalar margins for the top-wall/corner support chain.          *)
(* The Lean local abbreviations A, B are written out in full.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/UpperRightCornerLongitudinalNorm.ml";;

let URCLB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let URCLB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

let URCLB_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* A unit vector has dot product at least -1 with a vector of norm <= 1. *)
let URCLB_UNIT_DOT = prove
 (`forall e f A B. e pow 2 + f pow 2 = &1 /\ A pow 2 + B pow 2 <= &1
             ==> &0 <= &1 + e * A + f * B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e * A + f * B) pow 2 + (e * B - f * A) pow 2 = A pow 2 + B pow 2`
  ASSUME_TAC THENL
  [UNDISCH_TAC `e pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  UNDISCH_TAC `(e * A + f * B) pow 2 + (e * B - f * A) pow 2 = A pow 2 + B pow 2` THEN
  UNDISCH_TAC `A pow 2 + B pow 2 <= &1` THEN
  MP_TAC(SPEC `e * B - f * A` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `e * A + f * B + &1` REAL_LE_POW_2) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`e * B - f * A`,`Y:real`) THEN SPEC_TAC(`e * A + f * B`,`X:real`) THEN
  SPEC_TAC(`A pow 2 + B pow 2`,`N:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN NLIN_TAC []);;

let URCLB_NONNEG_BY_POS = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: disk_margin *)
let URCLB_DISK_MARGIN = prove
 (`forall e f a b. c977cc_normal e f /\ a pow 2 + b pow 2 < &1
             ==> &0 < &1 - a * e - b * f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `&1 - a * e - b * f = &1 - (a * e + b * f)`] THEN
  SUBGOAL_THEN `(a * e + b * f) pow 2 + (a * f - b * e) pow 2 = a pow 2 + b pow 2`
  ASSUME_TAC THENL
  [UNDISCH_TAC `e pow 2 + f pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  UNDISCH_TAC `(a * e + b * f) pow 2 + (a * f - b * e) pow 2 = a pow 2 + b pow 2` THEN
  UNDISCH_TAC `a pow 2 + b pow 2 < &1` THEN
  MP_TAC(SPEC `a * f - b * e` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `a * e + b * f - &1` REAL_LE_POW_2) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`a * f - b * e`,`Y:real`) THEN SPEC_TAC(`a * e + b * f`,`X:real`) THEN
  SPEC_TAC(`a pow 2 + b pow 2`,`N:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN NLIN_TAC []);;

(* Lean: marker_margin *)
let URCLB_MARKER_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= &1 + e * (c - &44 / &25 + (&13 / &50) * s pow 2 - (&43 / &500) * c * s) + f * ((&43 / &500) * c pow 2 + s - (&13 / &50) * c * s - &3 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URCLB_USE URCLN_RESIDUAL_NONPOS [`c:real`; `s:real`] THEN
  URCLB_NORMAL_TAC THEN MATCH_MP_TAC URCLB_UNIT_DOT THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c - &44 / &25 + (&13 / &50) * s pow 2 - (&43 / &500) * c * s) pow 2 + ((&43 / &500) * c pow 2 + s - (&13 / &50) * c * s - &3 / &5) pow 2 - &1 =
     &261 / &100 - (&88 / &25) * c - (&6 / &5) * s +
     (&187949 / &250000) * c pow 2 + (&57 / &100) * c * s` MP_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: products (private) *)
let URCLB_PRODUCTS = prove
 (`forall c s. c977cc_normal c s ==> s pow 2 <= &1 / &2 /\ c * s <= &1 / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN URCLB_NORMAL_TAC THEN
  URCLB_PROD_TAC `c - s` `c + s` THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - s:real`]);;

(* Lean: arc_margin (private) *)
let URCLB_ARC_MARGIN = prove
 (`forall c s. c977cc_normal c s ==> &1 + (&4 / &5) * c * s <= c + s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN URCLB_NORMAL_TAC THEN
  URCLB_PROD_TAC `c + s - &1` `&3 / &2 - (c + s)` THEN NLIN_TAC ~deg2:false []);;

(* Lean: lower_pair_margin *)
let URCLB_LOWER_PAIR_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ &0 <= f * c - e * s
     ==> &0 <= &1 + e * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) + f * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URCLB_USE C977CSB_SINE_ORDER [`e:real`; `f:real`; `c:real`; `s:real`] THEN
  URCLB_USE URCLB_PRODUCTS [`c:real`; `s:real`] THEN
  URCLB_USE C977CSB_DOT_LE_ONE [`c:real`; `s:real`; `e:real`; `f:real`] THEN
  URCLB_NORMAL_TAC THEN
  ASM_CASES_TAC `s <= &2 / &5` THENL
  [URCLB_PROD_TAC `s:real` `&2 / &5 - s` THEN
   NLIN_FACTS_TAC [SQ_NONNEG `c - &9 / &10`] [`&9 / &10 <= c`] THEN
   URCLB_PROD_TAC `s:real` `c - &9 / &10` THEN
   NLIN_FACTS_TAC [SQ_NONNEG `s - &7 / &20`] [`--(&47 / &50) <= (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s)`] THEN
   URCLB_PROD_TAC `c - &9 / &10` `&1 - c` THEN
   NLIN_FACTS_TAC [] [`&1 - c <= (&10 / &19) * s pow 2`] THEN
   URCLB_PROD_TAC `s:real` `&1 - c` THEN
   NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`--(&1 / &4) <= (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s)`] THEN
   URCLB_PROD_TAC `e:real` `(c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) - --(&47 / &50)` THEN
   URCLB_PROD_TAC `f:real` `(c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s) - --(&1 / &4)` THEN
   MP_TAC(SPECL [`e:real`; `f:real`; `&47 / &50`; `&1 / &4`] URCLB_DISK_MARGIN) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `(c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) <= &0` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `c * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s) - s * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) = &1 + (&23 / &20) * s - (&5 / &4) * c` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s) - s * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + c * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) + s * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s) = &2 - (&44 / &25) * c - (&3 / &5) * s`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&22 / &25`; `&3 / &10`] URCLB_DISK_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  URCLB_PROD_TAC `--(c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s)` `&1 - (c * e + s * f)` THEN
  URCLB_PROD_TAC `f - s` `c * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s) - s * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s)` THEN
  SUBGOAL_THEN `&0 <= c * ((&1 + e * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) + f * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s)) - (&1 + c * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) + s * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s)))`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `c * ((&1 + e * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) + f * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s)) - (&1 + c * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) + s * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s))) =
                 --(c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) * (&1 - (c * e + s * f)) + (f - s) * (c * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s) - s * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s))`
   SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + e * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) + f * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s)) - (&1 + c * (c - s - &44 / &25 + (&61 / &100) * s pow 2 + (&13 / &20) * c * s) + s * (c + s - &5 / &4 + (&13 / &20) * s pow 2 - (&61 / &100) * c * s))` ASSUME_TAC THENL
  [MATCH_MP_TAC URCLB_NONNEG_BY_POS THEN EXISTS_TAC `c:real` THEN
   CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: upper_pair_margin *)
let URCLB_UPPER_PAIR_MARGIN = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ f * c - e * s <= &0 /\
             (&3 / &10) * c <= s
     ==> &0 <= &1 + e * (c + s - &23 / &20 - (&61 / &100) * s pow 2 - (&13 / &20) * c * s) +
                f * (s - c + (&61 / &100) * c * s - (&13 / &20) * s pow 2 - &3 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URCLB_USE C977CSB_SINE_ORDER [`c:real`; `s:real`; `e:real`; `f:real`] THEN
  URCLB_USE URCLB_PRODUCTS [`c:real`; `s:real`] THEN
  URCLB_USE URCLB_ARC_MARGIN [`c:real`; `s:real`] THEN
  URCLB_NORMAL_TAC THEN
  REWRITE_TAC[REAL_ARITH
   `f * (s - c + (&61 / &100) * c * s - (&13 / &20) * s pow 2 - &3 / &5) =
    f * ((s - c + (&61 / &100) * c * s - (&13 / &20) * s pow 2) - &3 / &5)`] THEN
  URCLB_PROD_TAC `c:real` `s:real` THEN
  SUBGOAL_THEN `--(&91 / &200) <= (c + s - &23 / &20 - (&61 / &100) * s pow 2 - (&13 / &20) * c * s)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  URCLB_PROD_TAC `c - s` `&1 - (&61 / &100) * s` THEN
  SUBGOAL_THEN `(s - c + (&61 / &100) * c * s - (&13 / &20) * s pow 2) = --(c - s) * (&1 - (&61 / &100) * s) - (&1 / &25) * s pow 2`
  ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c - s <= &7 / &10` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  URCLB_PROD_TAC `c - s` `s:real` THEN
  SUBGOAL_THEN `--(&18 / &25) <= (s - c + (&61 / &100) * c * s - (&13 / &20) * s pow 2)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `s <= &1 / &2` THENL
  [URCLB_PROD_TAC `s:real` `&1 / &2 - s` THEN
   SUBGOAL_THEN `--(&121 / &400) <= (c + s - &23 / &20 - (&61 / &100) * s pow 2 - (&13 / &20) * c * s)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   URCLB_PROD_TAC `e:real` `(c + s - &23 / &20 - (&61 / &100) * s pow 2 - (&13 / &20) * c * s) - --(&121 / &400)` THEN
   URCLB_PROD_TAC `f:real` `(s - c + (&61 / &100) * c * s - (&13 / &20) * s pow 2) - --(&18 / &25)` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  URCLB_PROD_TAC `s - &1 / &2` `s:real` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &87 / &100`] [`c <= &87 / &100`] THEN
  URCLB_PROD_TAC `&1 - (&61 / &100) * s` `&37 / &100 - (c - s)` THEN
  SUBGOAL_THEN `--(&7 / &25) <= (s - c + (&61 / &100) * c * s - (&13 / &20) * s pow 2)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  URCLB_PROD_TAC `e:real` `(c + s - &23 / &20 - (&61 / &100) * s pow 2 - (&13 / &20) * c * s) - --(&91 / &200)` THEN
  URCLB_PROD_TAC `f:real` `(s - c + (&61 / &100) * c * s - (&13 / &20) * s pow 2) - --(&7 / &25)` THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `&91 / &200`; `&22 / &25`] URCLB_DISK_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  NLIN_TAC ~deg2:false []);;
