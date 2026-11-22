(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralPositiveBottom.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.PositiveCentralPositiveBottom, plus the  *)
(* theorem PositiveCentralTransverse.only_bottom_axis defined in that file). *)
(* Positive-bottom counterpart of the left-point support reduction.  Lean    *)
(* upper/lower are ABT_upper/ABT_lower.                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerHalfAngle.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/PositiveCentralNegativeBottom.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;
needs "n12/geometry/PositiveCentralLeftBand.ml";;

let PCPB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCPB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PCPB_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCPB_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PCPB_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ k * x < k * y ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let PCPB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: endpoint (private) *)
let PCPB_ENDPOINT = prove
 (`forall c s. c977cc_normal c s ==> &0 <= (&1 - c) * ((&543 / &500) * c + s - &457 / &500)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCPB_NORMAL_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC);;

(* Lean: central_above (private) *)
let PCPB_CENTRAL_ABOVE = prove
 (`forall c s C S. c977cc_normal c s /\ c977cc_normal C S /\ s * C - c * S <= &0
     ==> &0 <= c - c * (&2 - c) * C + (&1 - c + (c - &457 / &500) * s) * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPB_USE PCPB_ENDPOINT [`c:real`; `s:real`] THEN
  PCPB_USE C977CHA_ORDERED_NORMALS [`c:real`; `s:real`; `C:real`; `S:real`] THEN
  PCPB_NORMAL_TAC THEN
  PCPB_PROD_TAC `c:real` `&2 - c` THEN
  PCPB_PROD_TAC `&1 - c` `&1 - s` THEN
  SUBGOAL_THEN `&0 <= &1 - c + (c - &457 / &500) * s` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPB_PROD_TAC `c * (&2 - c)` `c - C` THEN
  PCPB_PROD_TAC `&1 - c + (c - &457 / &500) * s` `S - s` THEN
  SUBGOAL_THEN `c - c * (&2 - c) * c + (&1 - c + (c - &457 / &500) * s) * s =
                (&1 - c) * ((&543 / &500) * c + s - &457 / &500)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: central_below (private) *)
let PCPB_CENTRAL_BELOW = prove
 (`forall c s C S. c977cc_normal c s /\ c977cc_normal C S /\ &0 <= s * C - c * S
     ==> &0 <= c - c * (&2 - c - s) * C - (c - s * (c + s - &457 / &500)) * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPB_USE PCPB_ENDPOINT [`c:real`; `s:real`] THEN PCPB_NORMAL_TAC THEN
  SUBGOAL_THEN `c - (c * (&2 - c - s)) * c - (c - s * (c + s - &457 / &500)) * s =
                (&1 - c) * ((&543 / &500) * c + s - &457 / &500)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `(&543 / &500) * s <= c` THENL
  [PCPB_USE C977CSB_SINE_ORDER [`c:real`; `s:real`; `C:real`; `S:real`] THEN
   PCPB_PROD_TAC `c:real` `&2 - c - s` THEN
   PCPB_PROD_TAC `c:real` `c - (&543 / &500) * s` THEN
   SUBGOAL_THEN `(c * (&2 - c - s)) * s <= (c - s * (c + s - &457 / &500)) * c`
   ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PCPB_USE C977CSB_LINEAR_ARC_MAX
     [`c:real`; `s:real`; `C:real`; `S:real`; `c * (&2 - c - s)`;
      `c - s * (c + s - &457 / &500)`] THEN
   RASM_ARITH_TAC;
   ALL_TAC] THEN
  PCPB_PROD_TAC `c:real` `c + s - &4 / &3` THEN
  PCPB_PROD_TAC `s:real` `c + s - &457 / &500 - &2 / &5` THEN
  SUBGOAL_THEN `c * (&2 - c - s) <= (&2 / &3) * c /\
                c - s * (c + s - &457 / &500) <= (&2 / &3) * c` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPB_PROD_TAC `C:real` `(&2 / &3) * c - c * (&2 - c - s)` THEN
  PCPB_PROD_TAC `S:real` `(&2 / &3) * c - (c - s * (c + s - &457 / &500))` THEN
  PCPB_PROD_TAC `c:real` `&1 - (&2 / &3) * (C + S)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: upper_axis *)
let PCPB_UPPER_AXIS = prove
 (`forall cO sO uO vO aO C S.
     c977cc_normal cO sO /\ c977cc_normal C S /\ &1 < aO /\ lcont cO sO uO vO aO /\
     uO + aO <= &2 * cO + (&457 / &500) * sO
     ==> &2 * C - S < ABT_upper cO sO uO vO aO (--S) C + aO`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCPB_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + sO * sO = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  SUBGOAL_THEN `abs sO = sO` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cO * vO + sO * uO` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCPB_PROD_TAC `cO:real` `C:real` THEN PCPB_PROD_TAC `sO:real` `S:real` THEN
  PCPB_PROD_TAC `(cO * C + sO * S)` `cO * vO + sO * uO` THEN
  PCPB_PROD_TAC `S:real` `(&2 * cO + (&457 / &500) * sO) - (uO + aO)` THEN
  ASM_CASES_TAC `(sO * C - cO * S) <= &0` THENL
  [PCPB_USE C977NCO_UPPER_NEGATIVE_NONPOS
     [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `--sO`; `--S`; `C:real`] THEN
   FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
   PCPB_USE PCPB_CENTRAL_ABOVE [`cO:real`; `sO:real`; `C:real`; `S:real`] THEN
   PCPB_PROD_TAC `cO:real` `(cO * C + sO * S) + &0` THEN
   PCPB_PRODLT_TAC `(cO * ((cO * C + sO * S) + &0) + S + cO)` `aO - &1` THEN
   SUBGOAL_THEN `cO * ((((--S * cO - C * --sO) * uO + (--S * --sO + C * cO) * (vO + aO)) + aO) - (&2 * C - S)) = (cO * C + sO * S) * (cO * vO + sO * uO) + S * (&2 * cO + (&457 / &500) * sO - (uO + aO)) + (cO * ((cO * C + sO * S) + &0) + S + cO) * (aO - &1) + (cO * ((cO * C + sO * S) + &0) + S + cO - cO * S - (&457 / &500) * sO * S - &2 * cO * C)` ASSUME_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC PCPB_LT_BY_POS THEN EXISTS_TAC `cO:real` THEN
   CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  PCPB_USE C977NCO_UPPER_NEGATIVE_POS
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `--sO`; `--S`; `C:real`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match [] `ABT_upper c s u v a nx ny = e`) o concl)) THEN
  PCPB_USE PCPB_CENTRAL_BELOW [`cO:real`; `sO:real`; `C:real`; `S:real`] THEN
  SUBGOAL_THEN `(cO * ((cO * C + sO * S) + (sO * C - cO * S)) + S + cO - cO * S - (&457 / &500) * sO * S - &2 * cO * C) = cO - cO * (&2 - cO - sO) * C - (cO - sO * (cO + sO - &457 / &500)) * S`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCPB_PROD_TAC `cO:real` `(cO * C + sO * S) + (sO * C - cO * S)` THEN
  PCPB_PRODLT_TAC `(cO * ((cO * C + sO * S) + (sO * C - cO * S)) + S + cO)` `aO - &1` THEN
  SUBGOAL_THEN `cO * ((((--S * cO - C * --sO) * (uO + aO) + (--S * --sO + C * cO) * (vO + aO)) + aO) - (&2 * C - S)) = (cO * C + sO * S) * (cO * vO + sO * uO) + S * (&2 * cO + (&457 / &500) * sO - (uO + aO)) + (cO * ((cO * C + sO * S) + (sO * C - cO * S)) + S + cO) * (aO - &1) + (cO * ((cO * C + sO * S) + (sO * C - cO * S)) + S + cO - cO * S - (&457 / &500) * sO * S - &2 * cO * C)` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC PCPB_LT_BY_POS THEN EXISTS_TAC `cO:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []);;

let PCPB_LOWER_NP = prove
 (`forall c s u v a nx ny. nx * c + ny * s <= &0 /\ &0 <= --nx * s + ny * c
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

(* Lean: central_axis_impossible *)
let PCPB_CENTRAL_AXIS_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cA sA (uA:real) vA aA.
     c977cc_normal cO sO /\ c977cc_normal cA sA /\ aO = aA /\ &1 < aA /\
     lcont cO sO uO vO aO /\ uO + aO <= &2 * cO + (&457 / &500) * sO /\
     vA + aA <= &2 * cA - sA
     ==> ~(ABT_upper cO sO uO vO aO (--sA) cA <= vA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPB_USE PCPB_UPPER_AXIS
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cA:real`; `sA:real`] THEN
  RASM_ARITH_TAC);;

(* Lean: own_axis_margin *)
let PCPB_OWN_AXIS_MARGIN = prove
 (`forall c s C S. c977cc_normal c s /\ c977cc_normal C S /\ &0 < s /\ S <= s
     ==> c * (&2 + (&1 / &2) * C * S - C) + s * (--(&3 / &2) + (&1 / &2) * S pow 2 - S)
         <= c696cm_boundary c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPB_USE PCPB_ENDPOINT [`c:real`; `s:real`] THEN
  PCPB_USE C977CSB_ARC_CHORD [`c:real`; `s:real`; `C:real`; `S:real`; `&1 / &2`] THEN
  PCPB_NORMAL_TAC THEN
  PCPB_PROD_TAC `&1 - c` `(&3 / &5) * c - &2 / &5` THEN
  NLIN_FACTS_TAC [] [`&1 - c <= (&3 / &5) * s pow 2`] THEN
  PCPB_PROD_TAC `s:real` `&5 / &7 - s` THEN
  PCPB_PROD_TAC `s:real` `&1 - c` THEN
  SUBGOAL_THEN `&0 <= (c + s - (&1 / &2) * c * s - (&457 / &500) * s pow 2 - &2 * c pow 2) + c pow 2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `(c + s - (&1 / &2) * c * s - (&457 / &500) * s pow 2 - &2 * c pow 2) + c * (&1 - s / &2) = (&1 - c) * ((&543 / &500) * c + s - &457 / &500)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCPB_PROD_TAC `c:real` `(s * ((&1 - &1 / &2 * S) * (c * C + s * S)) - ((s - S) * c + S * (&1 - &1 / &2 * s)))` THEN
  PCPB_PROD_TAC `s - S` `(c + s - (&1 / &2) * c * s - (&457 / &500) * s pow 2 - &2 * c pow 2) + c pow 2` THEN
  PCPB_PROD_TAC `S:real` `(c + s - (&1 / &2) * c * s - (&457 / &500) * s pow 2 - &2 * c pow 2) + c * (&1 - s / &2)` THEN
  SUBGOAL_THEN `&0 <= (c + s - (&1 / &2) * c * s - (&457 / &500) * s pow 2 - &2 * c pow 2) + c * (c * C + s * S) * (&1 - S / &2)` ASSUME_TAC THENL
  [MATCH_MP_TAC PCPB_LE_BY_POS THEN EXISTS_TAC `s:real` THEN
   CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `s * (((c + s - (&1 / &2) * c * s - (&457 / &500) * s pow 2 - &2 * c pow 2) + c * (c * C + s * S) * (&1 - S / &2)) - &0) =
                 (s - S) * ((c + s - (&1 / &2) * c * s - (&457 / &500) * s pow 2 - &2 * c pow 2) + c pow 2) + S * ((c + s - (&1 / &2) * c * s - (&457 / &500) * s pow 2 - &2 * c pow 2) + c * (&1 - s / &2)) + c * (s * ((&1 - &1 / &2 * S) * (c * C + s * S)) - ((s - S) * c + S * (&1 - &1 / &2 * s)))`
   SUBST1_TAC THENL [REAL_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `c * c696cm_boundary c s = c + s - &2 * c * s - (&457 / &500) * s pow 2`
  ASSUME_TAC THENL
  [REWRITE_TAC[c696cm_boundary] THEN
   (SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC PCPB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN NLIN_TAC ~deg2:false []);;

(* Lean: own_axis_angle *)
let PCPB_OWN_AXIS_ANGLE = prove
 (`forall cO sO uO vO aO cA sA uA vA aA.
     c977cc_normal cO sO /\ c977cc_normal cA sA /\ aO = aA /\ &1 < aA /\
     lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     ~linside cO sO uO vO aO (&1) (&1) /\ ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\ vA + aA <= &2 * cA - sA /\
     vO + aO <= ABT_lower cA sA uA vA aA (--sO) cO
     ==> sO < sA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPB_USE C696PC_CORNER_FACES [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  PCPB_USE C977CSB_COSINE_ORDER [`cO:real`; `sO:real`; `cA:real`; `sA:real`] THEN
  PCPB_NORMAL_TAC THEN
  PCPB_PROD_TAC `sO:real` `cA - cO` THEN PCPB_PROD_TAC `cO:real` `sO - sA` THEN
  SUBGOAL_THEN `&0 <= sO * cA - cO * sA` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPB_PROD_TAC `cO:real` `cA:real` THEN PCPB_PROD_TAC `sO:real` `sA:real` THEN
  PCPB_USE PCPB_LOWER_NP
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `--sO`; `cO:real`] THEN
  MP_TAC(ASSUME `linside cA sA uA vA aA (&3 / &2) (&2)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  PCPB_PROD_TAC `sO * cA - cO * sA` `(uA + aA) - ((&3 / &2) * cA + &2 * sA)` THEN
  PCPB_PROD_TAC `cO * cA + sO * sA` `(&2 * cA - sA) - (vA + aA)` THEN
  PCPB_PROD_TAC `cO * cA + sO * sA` `aA - &1` THEN
  SUBGOAL_THEN
   `--(sO * cA - cO * sA) * ((&3 / &2) * cA + &2 * sA) +
    (cO * cA + sO * sA) * (&2 * cA - sA - &1) =
    cO * (&2 + (&1 / &2) * cA * sA - cA) + sO * (--(&3 / &2) + (&1 / &2) * sA pow 2 - sA)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCPB_USE PCPB_OWN_AXIS_MARGIN [`cO:real`; `sO:real`; `cA:real`; `sA:real`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: PositiveCentralTransverse.only_bottom_axis *)
let PCPB_ONLY_BOTTOM_AXIS = prove
 (`forall cO sO uO vO aO cA sA uA vA aA.
     cO * cO + sO * sO = &1 /\ &0 < cO /\ abs sO <= cO /\ c977cc_normal cA sA /\
     aO = aA /\ &1 < aA /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\ ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     uA + aA <= &2 * (cA + sA) /\ ~linside cA sA uA vA aA (&1) (&2) /\
     ldisj cO sO uO vO aO cA sA uA vA aA
     ==> vO + aO <= ABT_lower cA sA uA vA aA (--sO) cO`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCPB_NORMAL_TAC THEN
  SUBGOAL_THEN `cA * cA + sA * sA = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCPB_USE PCLB_UPPER_FACE [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] PCT_ALTERNATIVES) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `--cO <= sO /\ sO <= cO` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `abs sO <= cO` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sO` THENL
  [SUBGOAL_THEN `c977cc_normal cO sO` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    UNDISCH_TAC `cO * cO + sO * sO = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   PCPB_USE C696PC_CORNER_FACES [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] THEN
   PCPB_USE PCPB_CENTRAL_AXIS_IMPOSSIBLE
     [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
      `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
   ASM_MESON_TAC[];
   SUBGOAL_THEN `c977cc_normal cO (--sO)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
    UNDISCH_TAC `cO * cO + sO * sO = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   PCPB_USE PCNB_CENTRAL_AXIS_IMPOSSIBLE
     [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
      `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `--sO`] THEN
   ASM_MESON_TAC[]]);;
