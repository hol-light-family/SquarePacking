(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralPositiveLeft.lean (Jatloe,        *)
(* N12-jatloe; namespace N12Compact.PositiveCentralPositiveLeft).            *)
(* Original positive-left supports in the missing-west sector.  Normal is    *)
(* c977cc_normal; upper/lower are ABT_upper/ABT_lower; B is pceo_b;          *)
(* vertexDefect is pcplb_vertexdefect; the four-axis split is ABT_FOUR_AXES; *)
(* CornerWallPositiveLongitudinal.incoming: CWPL_INCOMING;                   *)
(* FourSquareBLBridge.left_wall: FSBL_LEFT_WALL; own_axis_margin:            *)
(* PCPLB_OWN_AXIS_MARGIN; central_axis_margin: PCPLA_CENTRAL_AXIS_MARGIN.    *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/PositiveCentralEscapeOrder.ml";;
needs "n12/geometry/PositiveCentralPositiveLeftBounds.ml";;
needs "n12/geometry/PositiveCentralPositiveLeftArc.ml";;
needs "n12/geometry/CornerWallPositiveLongitudinal.ml";;

let PCPL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCPL_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PCPL_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCPL_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
         CONV_TAC REAL_RING];;

let PCPL_USE th tms =
  MP_TAC(SPECL tms th) THEN ANTS_TAC THENL [PCPL_ANTS_TAC; DISCH_THEN STRIP_ASSUME_TAC];;

let PCPL_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: left_alternatives *)
let PCPL_LEFT_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cA sA uA vA aA.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cL sL /\ c977cc_normal cA sA /\ aL = aA /\
     linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     ldisj cL sL uL vL aL cA sA uA vA aA
     ==> uL + aL <= ABT_lower cA sA uA vA aA cL sL \/
         ABT_upper cL sL uL vL aL cA sA <= uA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aA`)) THEN
  PCPL_NORMAL_TAC THEN
  let qL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aA:real`]
  and qA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] in
  let sb sq (x,y) (nx,ny) =
    MP_TAC(REWRITE_RULE[REAL_POW_2] (SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS)) THEN
    ANTS_TAC THENL [PCPL_ANTS_TAC; STRIP_TAC] in
  let d1 = (`cL:real`,`sL:real`) and d2 = (`--sL`,`cL:real`)
  and d3 = (`cA:real`,`sA:real`) and d4 = (`--sA`,`cA:real`) in
  let ln = (`&1`,`&28 / &25`) and lf = (`&19 / &25`,`&187 / &100`)
  and am = (`&33 / &20`,`&33 / &20`) and ae = (`&87 / &50`,`&2`)
  and al = (`&2`,`&3 / &2`) in
  MAP_EVERY (fun (sq,p,d) -> sb sq p d)
   [qL,ln,d1; qA,am,d1; qL,ln,d3; qA,am,d3;
    qL,lf,d2; qA,al,d2; qA,ae,d2; qL,ln,d2;
    qL,lf,d4; qA,al,d4; qA,ae,d4; qL,ln,d4] THEN
  MP_TAC(SPECL (qL @ qA) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [PCPL_ANTS_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL qL ABT_OWNU) THEN ANTS_TAC THENL [PCPL_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL qA ABT_OWNU) THEN ANTS_TAC THENL [PCPL_ANTS_TAC; STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RASM_ARITH_TAC);;

(* Lean: vertex_bounds *)
let PCPL_VERTEX_BOUNDS = prove
 (`forall c s u v a p.
     c977cc_normal c s /\ &1 < a /\ u + a <= &2 * (c + s) /\ v + a <= &2 * c - s /\
     &1 + (c + s) * (&1 - &2 * s) + c * (&1 - p) < c * (v + a)
     ==> c * u - s * (v + a) < &1 - (pcplb_vertexdefect c s + s * (&1 - p)) /\
         s * u + c * (v + a) <= &2 - s * (&1 - c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCPL_NORMAL_TAC THEN
  SUBGOAL_THEN `c * pcplb_vertexdefect c s = (&1 - c) * (&1 - s)` ASSUME_TAC THENL
  [REWRITE_TAC[pcplb_vertexdefect] THEN
   SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  PCPL_PRODLT_TAC `c:real` `c:real` THEN
  PCPL_PRODLT_TAC `c * c` `&2 * (c + s) - &1 - u` THEN
  PCPL_PROD_TAC `s:real` `c * (v + a) - (&1 + (c + s) * (&1 - &2 * s) + c * (&1 - p))` THEN
  SUBGOAL_THEN `c - c pow 2 * (&2 * (c + s) - &1) + s * (&1 + (c + s) * (&1 - &2 * s)) =
                (&1 - c) * (&1 - s)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  CONJ_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PCPL_POS_OF_MUL THEN
   EXISTS_TAC `c:real` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   NLIN_TAC ~deg2:false [];
   PCPL_PROD_TAC `s:real` `&2 * (c + s) - &1 - u` THEN
   PCPL_PROD_TAC `c:real` `&2 * c - s - (v + a)` THEN
   NLIN_TAC ~deg2:false []]);;

(* Lean: vertex_closed (private) *)
let PCPL_VERTEX_CLOSED = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> lclosed c s u v a (c * u - s * (v + a)) (s * u + c * (v + a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lclosed] THEN
  SUBGOAL_THEN `c * (c * u - s * (v + a)) + s * (s * u + c * (v + a)) = u /\
                --s * (c * u - s * (v + a)) + c * (s * u + c * (v + a)) = v + a`
  (fun th -> REWRITE_TAC[th]) THENL
  [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: own_axis_impossible *)
let PCPL_OWN_AXIS_IMPOSSIBLE = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cA sA uA vA aA.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cA sA /\
     &1 < aL /\ &1 < aA /\ lcont cL sL uL vL aL /\
     sO <= sA /\ &9 / &10 <= cO /\ &4 / &5 <= cA /\ sA <= &3 / &5 /\
     pceo_b cO sO < vO + aO /\
     uA + aA <= &2 * (cA + sA) /\ vA + aA <= &2 * cA - sA /\
     &1 + (cA + sA) * (&1 - &2 * sA) + cA * (&1 - cO) < cA * (vA + aA) /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     uL + aL <= ABT_lower cA sA uA vA aA cL sL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPL_USE CWPL_INCOMING [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
    `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
  PCPL_USE PCPL_VERTEX_BOUNDS [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `cO:real`] THEN
  PCPL_USE PCPLB_OWN_AXIS_MARGIN [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `cL:real`; `sL:real`] THEN
  PCPL_USE PCPL_VERTEX_CLOSED [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCPL_USE ABT_CLOSED_BOUNDS [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
    `cA * uA - sA * (vA + aA)`; `sA * uA + cA * (vA + aA)`; `cL:real`; `sL:real`] THEN
  PCPL_NORMAL_TAC THEN
  ABBREV_TAC `Q = (pceo_b cO sO + sO * sL) / cO` THEN
  SUBGOAL_THEN `cO * (sL * Q) = sL * (pceo_b cO sO + sO * sL)` ASSUME_TAC THENL
  [EXPAND_TAC "Q" THEN SUBGOAL_THEN `~(cO = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  PCPL_PROD_TAC `cO:real` `cL:real` THEN PCPL_PROD_TAC `sO:real` `sL:real` THEN
  PCPL_PROD_TAC `sL:real` `cO * cL + sO * sL` THEN
  PCPL_PRODLT_TAC `aL - &1` `cO + sL * (cO * cL + sO * sL)` THEN
  PCPL_PROD_TAC `sL:real` `vO + aO - pceo_b cO sO` THEN
  SUBGOAL_THEN `&1 + sL * cL + sL * Q < uL + aL` ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC PCPL_POS_OF_MUL THEN
   EXISTS_TAC `cO:real` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPL_PRODLT_TAC `cL:real`
    `(&1 - (pcplb_vertexdefect cA sA + sA * (&1 - cO))) - (cA * uA - sA * (vA + aA))` THEN
  PCPL_PROD_TAC `sL:real` `(&2 - sA * (&1 - cA)) - (sA * uA + cA * (vA + aA))` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: central_axis_impossible *)
let PCPL_CENTRAL_AXIS_IMPOSSIBLE = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cA sA uA (vA:real) aA.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cA sA /\
     &1 <= aL /\ &1 < aA /\ lcont cL sL uL vL aL /\
     sO <= sA /\ &4 / &5 <= cA /\ sA <= &3 / &5 /\
     pceo_b cO sO < vO + aO /\
     uA + aA <= &2 * (cA + sA) /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     ABT_upper cL sL uL vL aL cA sA <= uA
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `cL:real`; `sL:real`]
    PCPLA_CENTRAL_AXIS_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  PCPL_NORMAL_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs sL = sL` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= cL * uL - sL * (vL + aL)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCPL_PROD_TAC `cO:real` `cL:real` THEN PCPL_PROD_TAC `sO:real` `sL:real` THEN
  PCPL_PROD_TAC `cA:real` `cL:real` THEN PCPL_PROD_TAC `sA:real` `sL:real` THEN
  PCPL_PROD_TAC `cO:real` `cA:real` THEN PCPL_PROD_TAC `sO:real` `sA:real` THEN
  SUBGOAL_THEN
   `ABT_lower cL sL uL vL aL (--sO) cO =
    (cO * sL - sO * cL) * (uL + aL / &2) + (cO * cL + sO * sL) * (vL + aL / &2) -
    aL * (abs(cO * sL - sO * cL) + (cO * cL + sO * sL)) / &2` ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   SUBGOAL_THEN `--(--sO) * sL + cO * cL = cO * cL + sO * sL /\
                 --sO * cL + cO * sL = cO * sL - sO * cL` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(cO * cL + sO * sL) = cO * cL + sO * sL` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `ABT_upper cL sL uL vL aL cA sA =
    (cA * cL + sA * sL) * (uL + aL / &2) + (sA * cL - cA * sL) * (vL + aL / &2) +
    aL * ((cA * cL + sA * sL) + abs(sA * cL - cA * sL)) / &2` ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
   SUBGOAL_THEN `--cA * sL + sA * cL = sA * cL - cA * sL` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(cA * cL + sA * sL) = cA * cL + sA * sL` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `TT = ((cO * cA + sO * sA) * (cL + sL) +
                   cO * (cA * cL + sA * sL + abs(sA * cL - cA * sL)) +
                   sA * (abs(cO * sL - sO * cL) + cO * cL + sO * sL)) / &2` THEN
  SUBGOAL_THEN `&0 <= TT` ASSUME_TAC THENL
  [EXPAND_TAC "TT" THEN
   PCPL_PROD_TAC `cO * cA + sO * sA` `cL + sL` THEN
   PCPL_PROD_TAC `cO:real` `cA * cL + sA * sL + abs(sA * cL - cA * sL)` THEN
   PCPL_PROD_TAC `sA:real` `abs(cO * sL - sO * cL) + cO * cL + sO * sL` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `cO * ABT_upper cL sL uL vL aL cA sA - sA * ABT_lower cL sL uL vL aL (--sO) cO - aL * TT =
    (cO * cA + sO * sA) * (cL * uL - sL * (vL + aL))` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN EXPAND_TAC "TT" THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PCPL_PROD_TAC `cO * cA + sO * sA` `cL * uL - sL * (vL + aL)` THEN
  PCPL_PROD_TAC `sA:real` `vO + aO - pceo_b cO sO` THEN
  PCPL_PROD_TAC `sA:real` `ABT_lower cL sL uL vL aL (--sO) cO - (vO + aO)` THEN
  PCPL_PROD_TAC `cO:real` `uA - ABT_upper cL sL uL vL aL cA sA` THEN
  PCPL_PROD_TAC `TT:real` `aL - &1` THEN
  PCPL_PRODLT_TAC `cO:real` `&2 * (cA + sA) - &1 - uA` THEN
  SUBGOAL_THEN `cO * (&2 * (cA + sA) - &1) <= sA * pceo_b cO sO + TT` ASSUME_TAC THENL
  [EXPAND_TAC "TT" THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;
