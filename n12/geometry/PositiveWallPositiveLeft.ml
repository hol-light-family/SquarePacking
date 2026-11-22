(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveWallPositiveLeft.lean (Jatloe,           *)
(* N12-jatloe; namespace N12Compact.PositiveWallPositiveLeft).               *)
(* Original-point entrance for the negative-bottom / positive-left /         *)
(* positive-wall sector when the central square misses (1,2).                *)
(* Normal is c977cc_normal; lower is ABT_lower; boundary is c977cc_boundary; *)
(* O.s = -t is sO = --t.  The structure Cuts is the predicate pwpl_cuts.     *)
(* corner_face: C977NCO_CORNER_FACE; only_bottom_axis: PCPB_ONLY_BOTTOM_AXIS;*)
(* PositiveCentralNegativeFloor.of_separation / inner_left_point:            *)
(* PCNF_OF_SEPARATION / PCNF_INNER_LEFT_POINT; PositiveCentralLeftBand.      *)
(* northwest_cap / upper_face: PCLB_NORTHWEST_CAP / PCLB_UPPER_FACE;         *)
(* PositiveCornerSmallBottom.tilt: PCSB_TILT; negative_bands:                *)
(* C977NCO_NEG_BANDS; PositiveWallEscapeFaces.faces: PWEF_FACES;             *)
(* PositiveWallUpperUPositiveLeft.impossible: PWUUPL_IMPOSSIBLE;             *)
(* PositiveWallUpperVImpossible.impossible: PWUVI_IMPOSSIBLE.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/PositiveCentralLeftBand.ml";;
needs "n12/geometry/PositiveCentralNegativeFloor.ml";;
needs "n12/geometry/PositiveCentralPositiveBottom.ml";;
needs "n12/geometry/PositiveCornerSmallBottom.ml";;
needs "n12/geometry/PositiveWallEscapeFaces.ml";;
needs "n12/geometry/PositiveWallUpperVImpossible.ml";;
needs "n12/geometry/PositiveWallUpperUPositiveLeft.ml";;

let PWPL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PWPL_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PWPL_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PWPL_DISCHARGE_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC];;

let PWPL_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [PWPL_DISCHARGE_TAC; DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])];;

(* lower_in_bands with both face coefficients nonnegative *)
let PWPL_LOWER_PP = prove
 (`forall c s u v a nx ny k h.
     nx * c + ny * s = k /\ --nx * s + ny * c = h /\ &0 <= k /\ &0 <= h
     ==> ABT_lower c s u v a nx ny = k * u + h * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  UNDISCH_TAC `nx * c + ny * s = k` THEN UNDISCH_TAC `--nx * s + ny * c = h` THEN
  CONV_TAC REAL_RING);;

(* Lean: Cuts (structure) *)
let pwpl_cuts = new_definition
 `pwpl_cuts cO (sO:real) uO vO aO cA sA uA vA aA t <=>
    &0 < t /\ t < &1 / &5 /\ t * (uO + aO) <= cO * vO /\
    uO + aO <= &2 * cO - (&457 / &500) * t /\
    &1 < sA * uA + cA * vA /\
    vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA`;;

(* Lean: cuts *)
let PWPL_CUTS = prove
 (`forall cO sO uO vO aO cA sA uA vA aA t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cA sA /\
     aO = aA /\ &1 < aA /\ lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\ ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     uA + aA <= &2 * (cA + sA) /\
     ~linside cA sA uA vA aA (&1) (&2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ldisj cO sO uO vO aO cA sA uA vA aA
     ==> pwpl_cuts cO sO uO vO aO cA sA uA vA aA t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  PWPL_NORMAL_TAC THEN
  let sqO = [`cO:real`; `--t`; `uO:real`; `vO:real`; `aA:real`]
  and sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] in
  PWPL_USE C977NCO_CORNER_FACE (sqO @ [`t:real`]) THEN
  PWPL_USE PCPB_ONLY_BOTTOM_AXIS (sqO @ sqA) THEN
  PWPL_USE PCNF_OF_SEPARATION (sqO @ sqA @ [`t:real`]) THEN
  PWPL_USE PWPL_LOWER_PP (sqA @ [`&0`; `&1`; `sA:real`; `cA:real`]) THEN
  PWPL_USE PCLB_NORTHWEST_CAP sqA THEN
  PWPL_USE PCLB_UPPER_FACE sqA THEN
  SUBGOAL_THEN `&1 < sA * uA + cA * vA` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PWPL_PROD_TAC `sA:real` `&2 * (cA + sA) - (uA + aA)` THEN
  PWPL_PROD_TAC `cA:real` `(&47 / &20) * cA - (&33 / &20) * sA - (vA + aA)` THEN
  PWPL_PRODLT_TAC `cA + sA` `aA - &1` THEN
  SUBGOAL_THEN `(cA + sA) * (&1 - (&7 / &20) * cA) < &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWPL_PROD_TAC `cO:real` `cA - sA` THEN PWPL_PROD_TAC `sA:real` `cO - t` THEN
  PWPL_PROD_TAC `t:real` `cA:real` THEN PWPL_PROD_TAC `cO:real` `sA:real` THEN
  SUBGOAL_THEN `&0 <= cO * cA - t * sA` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWPL_USE PWPL_LOWER_PP (sqA @ [`t:real`; `cO:real`; `t * cA + cO * sA`; `cO * cA - t * sA`]) THEN
  PWPL_PROD_TAC `t * cA + cO * sA` `&2 * (cA + sA) - &1 - uA` THEN
  PWPL_PROD_TAC `cO * cA - t * sA` `&2 * cA - sA - &1 - vA` THEN
  SUBGOAL_THEN
   `(t * cA + cO * sA) * (&2 * (cA + sA) - &1) + (cO * cA - t * sA) * (&2 * cA - sA - &1) =
    cO * (&2 + cA * sA - cA - sA) + t * (&2 - sA pow 2 - cA + sA)` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_boundary cO t <
                cO * (&2 + cA * sA - cA - sA) + t * (&2 - sA pow 2 - cA + sA)`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWPL_USE PCSB_TILT [`cO:real`; `t:real`; `cA:real`; `sA:real`] THEN
  PWPL_PROD_TAC `t:real` `&1 / &5 - t` THEN
  SUBGOAL_THEN `&1 + &2 * t - t pow 2 <= c977cc_boundary cO t` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_boundary] THEN
   SUBGOAL_THEN `&1 - t <= (&1 - t) / cO` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&7 / &10 <= c ==> &0 < c`] THEN
    PWPL_PROD_TAC `&1 - t` `&1 - cO` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   PWPL_PROD_TAC `t:real` `(&1 - t) / cO - (&1 - t)` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * t + (&457 / &500) * cO < vO + aA` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cO (--t) uO vO aA (&1) (&457 / &500)`) THEN
  REWRITE_TAC[C977NCO_NEG_BANDS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `uO + aA <= &2 * cO - (&457 / &500) * t` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cO (--t) uO vO aA (&2) (&457 / &500)` THEN
   REWRITE_TAC[C977NCO_NEG_BANDS] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pwpl_cuts] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: missing_left_impossible *)
let PWPL_MISSING_LEFT_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cA sA uA vA aA cW sW uW vW aW t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     sO = --t /\ c977cc_normal cO t /\ c977cc_normal cL sL /\
     c977cc_normal cA sA /\ c977cc_normal cW sW /\
     aO = aA /\ aL = aA /\ aW = aA /\ &1 < aA /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\ ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cL sL uL vL aL (&457 / &500) (&1) /\
     linside cL sL uL vL aL (&1) (&1) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cL sL uL vL aL (&1) (&8 / &5) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     uA + aA <= &2 * (cA + sA) /\
     ~linside cA sA uA vA aA (&1) (&2) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&12 / &5) /\
     ~linside cW sW uW vW aW (&1) (&72 / &25) /\
     ldisj cO sO uO vO aO cA sA uA vA aA /\
     ldisj cO sO uO vO aO cL sL uL vL aL /\
     ldisj cL sL uL vL aL cA sA uA vA aA /\
     ldisj cL sL uL vL aL cW sW uW vW aW /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&1) (&8 / &5)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cL sL uL vL aL cA sA uA vA aA` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&1`; `&8 / &5`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cW sW uW vW aW (&19 / &25) (&187 / &100)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cL sL uL vL aL cW sW uW vW aW` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&19 / &25`; `&187 / &100`]) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  let sqO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`]
  and sqL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
  and sqA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
  and sqW = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] in
  MP_TAC(SPECL (sqO @ sqA @ [`t:real`]) PWPL_CUTS) THEN
  ANTS_TAC THENL [PWPL_DISCHARGE_TAC; REWRITE_TAC[pwpl_cuts] THEN STRIP_TAC] THEN
  PWPL_USE PCNF_INNER_LEFT_POINT sqA THEN
  PWPL_USE PWEF_FACES (sqA @ sqW) THENL
  [MATCH_MP_TAC(SPECL (sqO @ sqL @ sqW @ [`t:real`]) PWUUPL_IMPOSSIBLE) THEN
   PWPL_DISCHARGE_TAC;
   MATCH_MP_TAC(SPECL (sqA @ sqW) PWUVI_IMPOSSIBLE) THEN
   PWPL_DISCHARGE_TAC]);;
