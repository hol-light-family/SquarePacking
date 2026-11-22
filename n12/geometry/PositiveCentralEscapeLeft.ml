(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralEscapeLeft.lean (Jatloe,          *)
(* N12-jatloe; namespace N12Compact.PositiveCentralEscapeLeft).              *)
(* Left-singleton restrictions in the missing-west-point sector.  Lean       *)
(* upper/lower are ABT_upper/ABT_lower; B is pceo_b.  L's side_pos is the    *)
(* explicit hypothesis &0 < aL.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/PositiveCentralEscapeOrder.ml";;
needs "n12/geometry/CornerSingletonPair.ml";;

let PCEL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCEL_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PCEL_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCEL_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PCEL_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let PCEL_LOWER_PN = prove
 (`forall c s u v a nx ny. &0 <= nx * c + ny * s /\ --nx * s + ny * c <= &0
     ==> ABT_lower c s u v a nx ny =
         (nx * c + ny * s) * u + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> abs x = --x`; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REAL_ARITH_TAC);;

(* Lean: bottom_cosine *)
let PCEL_BOTTOM_COSINE = prove
 (`forall p q C S v. c977cc_normal p q /\ c977cc_normal C S /\ q <= S /\
     pceo_b p q < (p * S - q * C) * (&2 * (C + S) - &1) + (p * C + q * S) * (v - &1) /\
     v <= (&47 / &20) * C - (&33 / &20) * S
     ==> &9 / &10 < p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCEL_USE PCEO_STRONG_BASE_BOUND [`p:real`; `q:real`; `C:real`; `S:real`; `v:real`] THEN
  PCEL_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `p:real`; `q:real`] THEN
  PCEL_NORMAL_TAC THEN
  PCEL_PROD_TAC `C:real` `((&47 / &20) * C - (&33 / &20) * S) - v` THEN
  SUBGOAL_THEN `C * (&1 - p) < &1 + (&7 / &20) * C * (C + S) - (C + S)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  PCEL_PROD_TAC `&9 / &10 - C` `&9 / &10 + C` THEN
  SUBGOAL_THEN `&13 / &30 <= S` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCEL_PROD_TAC `&13 / &30 - S` `&13 / &30 + S` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCEL_PROD_TAC `&7 / &15 - (C - S)` `&7 / &15 + (C - S)` THEN
  SUBGOAL_THEN `&4 / &3 <= C + S` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCEL_PROD_TAC `&4 / &3 - (C + S)` `&4 / &3 + C + S` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCEL_PROD_TAC `C:real` `&9 / &10 - p` THEN
  PCEL_PROD_TAC `(C + S) - &4 / &3` `&1 - (&7 / &20) * C` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: corner_margin (private) *)
let PCEL_CORNER_MARGIN = prove
 (`forall p q. c977cc_normal p q /\ &9 / &10 <= p ==> &0 <= (&1 - p) pow 2 + q * (p - &457 / &500)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCEL_NORMAL_TAC THEN
  ASM_CASES_TAC `&457 / &500 <= p` THENL
  [PCEL_PROD_TAC `q:real` `p - &457 / &500` THEN NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - p`];
   ALL_TAC] THEN
  PCEL_PROD_TAC `p - &9 / &10` `p + &9 / &10` THEN
  SUBGOAL_THEN `q <= &11 / &25` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCEL_PRODLT_TAC `q - &11 / &25` `q + &11 / &25` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCEL_PROD_TAC `&11 / &25 - q` `&457 / &500 - p` THEN
  PCEL_PROD_TAC `p - &9 / &10` `p - &33 / &50` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_left_axis_impossible *)
let PCEL_NEGATIVE_LEFT_AXIS_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cL sL uL vL aL r.
     c977cc_normal cO sO /\ c977cc_normal cL r /\ sL = --r /\ &0 < aL /\
     &9 / &10 <= cO /\ &1 < aO /\ lcont cO sO uO vO aO /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     linside cL sL uL vL aL (&1) (&1)
     ==> ~(ABT_upper cL sL uL vL aL cL sL <= ABT_lower cO sO uO vO aO cL sL)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  PCEL_USE PCEL_CORNER_MARGIN [`cO:real`; `sO:real`] THEN PCEL_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + sO * sO = &1 /\ cL * cL + --r * --r = &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1`; UNDISCH_TAC `cL pow 2 + r pow 2 = &1`] THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  PCEL_PROD_TAC `cO:real` `cL - r` THEN PCEL_PROD_TAC `r:real` `cO - sO` THEN
  SUBGOAL_THEN `&0 <= (cO * cL - sO * r)` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCEL_PROD_TAC `sO:real` `cL:real` THEN PCEL_PROD_TAC `cO:real` `r:real` THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] TSS_BOTTOM_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  SUBGOAL_THEN `abs sO = sO` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cO * vO + sO * uO` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCEL_USE PCEL_LOWER_PN
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cL:real`; `--r`] THEN
  PCEL_PROD_TAC `cO:real` `(sO * cL + cO * r)` THEN
  PCEL_PRODLT_TAC `aO - &1` `cL + cO * (sO * cL + cO * r)` THEN
  PCEL_PROD_TAC `cL:real` `(&2 * cO + (&457 / &500) * sO) - (uO + aO)` THEN
  PCEL_PROD_TAC `(sO * cL + cO * r)` `cO * vO + sO * uO` THEN
  PCEL_PROD_TAC `cL:real` `(&1 - cO) pow 2 + sO * (cO - &457 / &500)` THEN
  PCEL_PROD_TAC `cO:real` `cL - r` THEN
  PCEL_PROD_TAC `cO * (cL - r)` `&1 - cO` THEN
  SUBGOAL_THEN
   `cO * ((cL - r) - ((cO * cL - sO * r) * uO - (sO * cL + cO * r) * (vO + aO))) =
    cL * (&2 * cO + (&457 / &500) * sO - (uO + aO)) + (sO * cL + cO * r) * (cO * vO + sO * uO) +
    (aO - &1) * (cL + cO * (sO * cL + cO * r)) + cL * ((&1 - cO) pow 2 + sO * (cO - &457 / &500)) +
    cO * (cL - r) * (&1 - cO)` ASSUME_TAC THENL
  [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (cL - r) - ((cO * cL - sO * r) * uO - (sO * cL + cO * r) * (vO + aO))` ASSUME_TAC THENL
  [MATCH_MP_TAC PCEL_POS_OF_MUL THEN EXISTS_TAC `cO:real` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABT_SB_TAC [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`] `&1` `&1` `cL:real` `--r` THEN
  RASM_ARITH_TAC);;
