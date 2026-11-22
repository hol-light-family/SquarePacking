(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralTransverse.lean (Jatloe,          *)
(* N12-jatloe; namespace N12Compact.PositiveCentralTransverse).              *)
(* A positive canonical central square missing (2,2) can only lie above its  *)
(* bottom singleton on one of their transverse axes.  Lean upper/lower are   *)
(* ABT_upper/ABT_lower; the SAT step is ABT_FOUR_AXES.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let PCT_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCT_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PCT_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCT_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Support values with known coefficient signs (helpers). *)
let PCT_LOWER_PN = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ --nx * s + ny * c <= &0
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * u + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

let PCT_LOWER_PP = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny = (nx * c + ny * s) * u + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

let PCT_POS_BY_POS = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: central_margin *)
let PCT_CENTRAL_MARGIN = prove
 (`forall C S. c977cc_normal C S ==> (&13 / &100) * C + (&31 / &25) * S < &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCT_NORMAL_TAC THEN RASM_ARITH_TAC);;

(* Lean: product_margin (private) *)
let PCT_PRODUCT_MARGIN = prove
 (`forall C S. c977cc_normal C S ==> &9 / &10 <= (C + S) * (&1 - S / &2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCT_NORMAL_TAC THEN
  PCT_PROD_TAC `C + S - &1` `&3 / &2 - (C + S)` THEN
  NLIN_FACTS_TAC [] [`(&4 / &5) * C * S <= C + S - &1`] THEN
  PCT_PROD_TAC `S:real` `C - S` THEN
  PCT_PROD_TAC `C - S` `C + S` THEN
  NLIN_FACTS_TAC [] [`S pow 2 <= &1 / &2`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: smaller_angle *)
let PCT_SMALLER_ANGLE = prove
 (`forall c s C S. &0 < c /\ c977cc_normal C S /\ &0 <= c * S - s * C
     ==> c * (&2 - S pow 2 / &2 - C) + s * (&2 + C * S / &2 - S) <
         (&187 / &100) * c + (&19 / &25) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCT_USE PCT_CENTRAL_MARGIN [`C:real`; `S:real`] THEN PCT_NORMAL_TAC THEN
  PCT_PROD_TAC `C:real` `S:real` THEN
  SUBGOAL_THEN `&0 <= &31 / &25 - S + C * S / &2` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PRODLT_TAC `c:real` `&1 - (&13 / &100) * C - (&31 / &25) * S` THEN
  PCT_PROD_TAC `c * S - s * C` `&31 / &25 - S + C * S / &2` THEN
  SUBGOAL_THEN
   `C * (((&187 / &100) * c + (&19 / &25) * s) -
         (c * (&2 - S pow 2 / &2 - C) + s * (&2 + C * S / &2 - S))) =
    c * (&1 - (&13 / &100) * C - (&31 / &25) * S) +
    (c * S - s * C) * (&31 / &25 - S + C * S / &2)` ASSUME_TAC THENL
  [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  MATCH_MP_TAC PCT_POS_BY_POS THEN EXISTS_TAC `C:real` THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: larger_angle *)
let PCT_LARGER_ANGLE = prove
 (`forall c s C S. &0 < c /\ s <= c /\ c977cc_normal C S
     ==> c * (&2 + C * S / &2 - C) + s * (&3 / &2 + S pow 2 / &2 - S) <
         (&187 / &100) * c + (&19 / &25) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCT_USE PCT_PRODUCT_MARGIN [`C:real`; `S:real`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `S - &1`] [`S - S pow 2 / &2 - &37 / &50 <= &0`] THEN
  PCT_PROD_TAC `c - s` `--(S - S pow 2 / &2 - &37 / &50)` THEN
  PCT_PROD_TAC `c:real` `(C + S) * (&1 - S / &2) - &9 / &10` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: alternatives *)
let PCT_ALTERNATIVES = prove
 (`forall cO sO uO vO aO cA sA uA vA aA.
     cO * cO + sO * sO = &1 /\ &0 < cO /\ abs sO <= cO /\ c977cc_normal cA sA /\
     aO = aA /\ &1 < aA /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     uA + aA <= &2 * (cA + sA) /\
     ldisj cO sO uO vO aO cA sA uA vA aA
     ==> vO + aO <= ABT_lower cA sA uA vA aA (--sO) cO \/
         ABT_upper cO sO uO vO aO (--sA) cA <= vA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  PCT_NORMAL_TAC THEN
  SUBGOAL_THEN `cA * cA + sA * sA = &1 /\ &0 < aA /\ --cO <= sO /\ sO <= cO`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING;
    RASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
   UNDISCH_TAC `abs sO <= cO` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  let sqO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aA:real`]
  and sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] in
  MP_TAC(SPECL sqA ABT_OWNU) THEN MP_TAC(SPECL sqA ABT_OWNV) THEN
  MP_TAC(SPECL sqO ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y),(nx,ny)) -> ABT_SB_TAC sq x y nx ny)
   [sqO,(`&187 / &100`,`&19 / &25`),(`cO:real`,`sO:real`);
    sqO,(`&28 / &25`,`&1`),(`cO:real`,`sO:real`);
    sqA,(`&2`,`&87 / &50`),(`cO:real`,`sO:real`);
    sqO,(`&187 / &100`,`&19 / &25`),(`cA:real`,`sA:real`);
    sqO,(`&28 / &25`,`&1`),(`cA:real`,`sA:real`);
    sqA,(`&2`,`&87 / &50`),(`cA:real`,`sA:real`);
    sqA,(`&33 / &20`,`&33 / &20`),(`--sO`,`cO:real`);
    sqO,(`&28 / &25`,`&1`),(`--sO`,`cO:real`);
    sqA,(`&33 / &20`,`&33 / &20`),(`--sA`,`cA:real`);
    sqO,(`&28 / &25`,`&1`),(`--sA`,`cA:real`)] THEN
  MP_TAC(ASSUME `linside cA sA uA vA aA (&3 / &2) (&2)`) THEN
  MP_TAC(ASSUME `linside cA sA uA vA aA (&2) (&3 / &2)`) THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  PCT_USE PCT_CENTRAL_MARGIN [`cA:real`; `sA:real`] THEN
  PCT_PROD_TAC `cO:real` `cA - sA` THEN
  PCT_PROD_TAC `sA:real` `cO + sO` THEN
  SUBGOAL_THEN `&0 <= cO * cA + sO * sA` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCT_PROD_TAC `cO * cA + sO * sA` `&2 * (cA + sA) - (uA + aA)` THEN
  PCT_PROD_TAC `cO * cA + sO * sA` `aA - &1` THEN
  MP_TAC(SPECL (sqO @ sqA) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `--cO * sA + sO * cA <= &0` THENL
  [PCT_USE PCT_LOWER_PN (sqA @ [`cO:real`; `sO:real`]) THEN
   PCT_PROD_TAC `--(--cO * sA + sO * cA)` `(vA + aA) - (--sA * &3 / &2 + cA * &2)` THEN
   PCT_USE PCT_SMALLER_ANGLE [`cO:real`; `sO:real`; `cA:real`; `sA:real`] THEN
   SUBGOAL_THEN
    `(cO * cA + sO * sA) * (&2 * (cA + sA) - &1) +
     (--cO * sA + sO * cA) * (--sA * (&3 / &2) + cA * &2) =
     cO * (&2 - sA pow 2 / &2 - cA) + sO * (&2 + cA * sA / &2 - sA)` ASSUME_TAC THENL
   [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN RASM_ARITH_TAC;
   PCT_USE PCT_LOWER_PP (sqA @ [`cO:real`; `sO:real`]) THEN
   PCT_PROD_TAC `--cO * sA + sO * cA` `(--sA * &2 + cA * &3 / &2) - vA` THEN
   PCT_USE PCT_LARGER_ANGLE [`cO:real`; `sO:real`; `cA:real`; `sA:real`] THEN
   SUBGOAL_THEN
    `(cO * cA + sO * sA) * (&2 * (cA + sA) - &1) +
     (--cO * sA + sO * cA) * (--sA * &2 + cA * (&3 / &2)) =
     cO * (&2 + cA * sA / &2 - cA) + sO * (&3 / &2 + sA pow 2 / &2 - sA)` ASSUME_TAC THENL
   [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN RASM_ARITH_TAC]);;
