(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveWallUpperVImpossible.lean (Jatloe,       *)
(* N12-jatloe; namespace N12Compact.PositiveWallUpperVImpossible).           *)
(* Completion of the positive-wall upper-V branch.  IncreasingSegment-       *)
(* Avoidance.dichotomy is ISA_DICHOTOMY; FourSquareBLBridge.left_wall is     *)
(* FSBL_LEFT_WALL.  The OpenSquare invariants of W used by the dichotomy     *)
(* (cW * cW + sW * sW = &1, &0 < aW) are explicit hypotheses.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/PositiveCentralNegativeFloor.ml";;
needs "n12/geometry/PositiveWallEscapeFaces.ml";;
needs "n12/geometry/IncreasingSegmentAvoidance.ml";;

let PWUVI_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PWUVI_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PWUVI_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PWUVI_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PWUVI_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: cosine_bound *)
let PWUVI_COSINE_BOUND = prove
 (`forall C S. c977cc_normal C S /\ (C + S) * (&1 - (&7 / &20) * C) < &1 ==> &81 / &100 < C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWUVI_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `Q = &1031 / &400 - (&7 / &5) * (C + &81 / &100) +
                  (&49 / &200) * (C pow 2 + (&81 / &100) * C + (&81 / &100) pow 2)` THEN
  SUBGOAL_THEN `&0 <= Q` ASSUME_TAC THENL
  [EXPAND_TAC "Q" THEN NLIN_TAC [SQ_NONNEG `C:real`]; ALL_TAC] THEN
  PWUVI_PROD_TAC `&81 / &100 - C` `Q:real` THEN
  SUBGOAL_THEN `&0 < &13 / &10 - (&1031 / &400) * C + (&7 / &5) * C pow 2 -
                     (&49 / &200) * C pow 3` ASSUME_TAC THENL
  [SUBGOAL_THEN `&13 / &10 - (&1031 / &400) * C + (&7 / &5) * C pow 2 -
                 (&49 / &200) * C pow 3 = &112391 / &200000000 + (&81 / &100 - C) * Q`
   SUBST1_TAC THENL [EXPAND_TAC "Q" THEN REAL_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
  PWUVI_PRODLT_TAC `C:real` `&13 / &10 - (&1031 / &400) * C + (&7 / &5) * C pow 2 -
                     (&49 / &200) * C pow 3` THEN
  PWUVI_PROD_TAC `&1 - (&7 / &20) * C` `S:real` THEN
  SUBGOAL_THEN `&0 < &1 - C + (&7 / &20) * C pow 2 - (&1 - (&7 / &20) * C) * S /\
                &0 < &1 - C + (&7 / &20) * C pow 2 + (&1 - (&7 / &20) * C) * S`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWUVI_PRODLT_TAC `&1 - C + (&7 / &20) * C pow 2 - (&1 - (&7 / &20) * C) * S`
                   `&1 - C + (&7 / &20) * C pow 2 + (&1 - (&7 / &20) * C) * S` THEN
  SUBGOAL_THEN
   `((&1 - (&7 / &20) * C) * S) pow 2 - (&1 - C + (&7 / &20) * C pow 2) pow 2 =
    C * (&13 / &10 - (&1031 / &400) * C + (&7 / &5) * C pow 2 - (&49 / &200) * C pow 3)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: height_margin (private) *)
let PWUVI_HEIGHT_MARGIN = prove
 (`forall C S. c977cc_normal C S /\ (C + S) * (&1 - (&7 / &20) * C) < &1
     ==> &0 < C + S - &1 - C * S + (&3 / &25) * C pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PWUVI_USE PWUVI_COSINE_BOUND [`C:real`; `S:real`] THEN PWUVI_NORMAL_TAC THEN
  PWUVI_PROD_TAC `C - &81 / &100` `C + &81 / &100` THEN
  PWUVI_PROD_TAC `C pow 2 - &6561 / &10000` `C pow 2 - &3439 / &10000` THEN
  SUBGOAL_THEN `(C * S) pow 2 = C pow 2 - C pow 2 * C pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`(C * S) pow 2 <= (&119 / &250) pow 2`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C * S - &119 / &250`] [`C * S <= &119 / &250`] THEN
  NLIN_FACTS_TAC [] [`(C + S) pow 2 <= &244 / &125`;
                     `C + S - &1 < (&7 / &20) * C * (C + S)`] THEN
  PWUVI_PRODLT_TAC `(&7 / &20) * C * (C + S) - (C + S - &1)`
                   `(&7 / &20) * C * (C + S) + (C + S - &1)` THEN
  PWUVI_PROD_TAC `C pow 2` `&244 / &125 - (C + S) pow 2` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: central_height *)
let PWUVI_CENTRAL_HEIGHT = prove
 (`forall c s u v a. c977cc_normal c s /\ &1 < a /\ u + a <= &2 * (c + s) /\
     &1 < s * u + c * v /\ v + a <= (&47 / &20) * c - (&33 / &20) * s
     ==> (&47 / &25) * c - s < v + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWUVI_NORMAL_TAC THEN
  PWUVI_PROD_TAC `s:real` `&2 * (c + s) - (u + a)` THEN
  PWUVI_PROD_TAC `c:real` `((&47 / &20) * c - (&33 / &20) * s) - (v + a)` THEN
  PWUVI_PRODLT_TAC `c + s` `a - &1` THEN
  SUBGOAL_THEN `(c + s) * (&1 - (&7 / &20) * c) < &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWUVI_USE PWUVI_HEIGHT_MARGIN [`c:real`; `s:real`] THEN
  SUBGOAL_THEN
   `c * (v + a - ((&47 / &25) * c - s)) =
    (s * u + c * v - &1) + s * (&2 * (c + s) - a - u) + (c + s) * (a - &1) +
    (c + s - &1 - c * s + (&3 / &25) * c pow 2)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PWUVI_POS_OF_MUL THEN
  EXISTS_TAC `c:real` THEN CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: wall_point *)
let PWUVI_WALL_POINT = prove
 (`forall c s u v a. c977cc_normal c s /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     (&187 / &100) * c - (&19 / &25) * s <= v /\ v + a <= (&72 / &25) * c - s /\
     s < &1 / &24
     ==> linside c s u v a (&1) (&47 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWUVI_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcx]) THEN
  SUBGOAL_THEN `abs s = s` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `s * (v + a) <= c * u` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PWUVI_PROD_TAC `s:real` `v - ((&187 / &100) * c - (&19 / &25) * s)` THEN
  PWUVI_PRODLT_TAC `a - &1` `c + s` THEN
  PWUVI_PROD_TAC `c:real` `&1 - c` THEN
  PWUVI_PROD_TAC `s:real` `&1 - (&1 / &100) * c - (&19 / &25) * s` THEN
  SUBGOAL_THEN `&0 < c * ((u + a) - (c + (&47 / &25) * s))` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (u + a) - (c + (&47 / &25) * s)` ASSUME_TAC THENL
  [MATCH_MP_TAC PWUVI_POS_OF_MUL THEN EXISTS_TAC `c:real` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME `linside c s u v a (&457 / &500) (&2)`) THEN
  MP_TAC(ASSUME `linside c s u v a (&1) (&12 / &5)`) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: segment_impossible *)
let PWUVI_SEGMENT_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cW sW uW vW aW.
     c977cc_normal cA sA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aA /\ uA + aA <= &2 * (cA + sA) /\
     cA * uA - sA * (vA + aA) < &1 /\ (&47 / &25) * cA - sA < vA + aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cW sW uW vW aW (&1) (&47 / &25) /\ linside cW sW uW vW aW (&1) (&12 / &5) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWUVI_NORMAL_TAC THEN
  SUBGOAL_THEN `cA * cA + sA * sA = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cA sA uA vA aA (&33 / &20) (&33 / &20)`) THEN
  MP_TAC(ASSUME `linside cA sA uA vA aA (&3 / &2) (&2)`) THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `sA = &0` THENL
  [UNDISCH_TAC `ldisj cA sA uA vA aA cW sW uW vW aW` THEN
   REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&1`; `&47 / &25`]) THEN
   ASM_REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `&1`; `&47 / &25`; `&1`; `&12 / &5`] ISA_DICHOTOMY) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
  SUBGOAL_THEN
   `(--sA * (&1 - &1) + cA * (&12 / &5 - &47 / &25)) * (cA * &1 + sA * &47 / &25) -
    (cA * (&1 - &1) + sA * (&12 / &5 - &47 / &25)) * (--sA * &1 + cA * &47 / &25) = &13 / &25`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: impossible *)
let PWUVI_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cW sW uW vW aW.
     c977cc_normal cA sA /\ c977cc_normal cW sW /\ &1 < aA /\ &1 < aW /\
     lcont cW sW uW vW aW /\ uA + aA <= &2 * (cA + sA) /\
     &1 < sA * uA + cA * vA /\ vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\ linside cW sW uW vW aW (&1) (&12 / &5) /\
     (&187 / &100) * cW - (&19 / &25) * sW <= vW /\ vW + aW <= (&72 / &25) * cW - sW /\
     sW < &1 / &24 /\ ldisj cA sA uA vA aA cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PWUVI_USE PCNF_LEFT_SUPPORT [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PWUVI_USE PWUVI_CENTRAL_HEIGHT [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PWUVI_USE PWUVI_WALL_POINT [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  PWUVI_NORMAL_TAC THEN
  MATCH_MP_TAC PWUVI_SEGMENT_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                        `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  UNDISCH_TAC `cW pow 2 + sW pow 2 = &1` THEN CONV_TAC REAL_RING);;
