(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralPositiveLeftWest.lean (Jatloe,    *)
(* N12-jatloe; namespace N12Compact.PositiveCentralPositiveLeftWest).        *)
(* The whole positive-left missing-west entrance.  Normal is c977cc_normal;  *)
(* B is pceo_b; C696CornerMargins.boundary is c696cm_boundary; lower is      *)
(* ABT_lower.  PositiveCentralTransverse.only_bottom_axis:                   *)
(* PCPB_ONLY_BOTTOM_AXIS; PositiveCentralLeftBand.upper_face / northwest_cap:*)
(* PCLB_UPPER_FACE / PCLB_NORTHWEST_CAP; PositiveCentralPositiveBottom.      *)
(* own_axis_angle: PCPB_OWN_AXIS_ANGLE; C696PositiveCorner.corner_faces:     *)
(* C696PC_CORNER_FACES; bottom_cosine: PCEL_BOTTOM_COSINE; strong_base_bound *)
(* / base_bound / northwest_threshold: PCEO_..; CornerSingletonPair.         *)
(* positive_alternatives: CSP_POSITIVE_ALTERNATIVES; the four closing        *)
(* theorems are PCPL_OWN/CENTRAL_AXIS_IMPOSSIBLE and PLOV_OWN/CENTRAL_AXIS_  *)
(* IMPOSSIBLE.  The OpenSquare invariants are explicit hypotheses.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C696CornerMargins.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/PositiveCentralEscapeOrder.ml";;
needs "n12/geometry/PositiveCentralEscapeLeft.ml";;
needs "n12/geometry/PositiveCentralLeftBand.ml";;
needs "n12/geometry/PositiveCentralPositiveBottom.ml";;
needs "n12/geometry/CornerSingletonPair.ml";;
needs "n12/geometry/PositiveCentralPositiveLeft.ml";;
needs "n12/geometry/PositiveLeftOwnV.ml";;

let PCPLW_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCPLW_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCPLW_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
         CONV_TAC REAL_RING];;

let PCPLW_USE th tms =
  MP_TAC(SPECL tms th) THEN ANTS_TAC THENL [PCPLW_ANTS_TAC; DISCH_TAC];;

(* Lean: west *)
let PCPLW_WEST = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cA sA uA vA aA.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cO sO /\ c977cc_normal cL sL /\ c977cc_normal cA sA /\
     aO = aA /\ aL = aA /\ &1 < aA /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\ ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cL sL uL vL aL (&1) (&1) /\ linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     uA + aA <= &2 * (cA + sA) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ldisj cO sO uO vO aO cA sA uA vA aA /\
     ldisj cO sO uO vO aO cL sL uL vL aL /\
     ldisj cL sL uL vL aL cA sA uA vA aA
     ==> linside cA sA uA vA aA (&1) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN PCPLW_NORMAL_TAC THEN
  let qO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`]
  and qL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
  and qA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] in
  PCPLW_USE PCPB_ONLY_BOTTOM_AXIS (qO @ qA) THEN
  PCPLW_USE PCLB_UPPER_FACE qA THEN
  PCPLW_USE PCPB_OWN_AXIS_ANGLE (qO @ qA) THEN
  PCPLW_USE PCLB_NORTHWEST_CAP qA THEN
  MP_TAC(SPECL qO C696PC_CORNER_FACES) THEN ANTS_TAC THENL [PCPLW_ANTS_TAC; STRIP_TAC] THEN
  (* B is weaker than the old boundary *)
  PCPLW_USE PCEO_P_B [`cO:real`; `sO:real`] THEN
  SUBGOAL_THEN `cO * c696cm_boundary cO sO = cO + sO - &2 * cO * sO - (&457 / &500) * sO pow 2`
    ASSUME_TAC THENL
  [REWRITE_TAC[c696cm_boundary] THEN
   SUBGOAL_THEN `~(cO = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `pceo_b cO sO < vO + aO` ASSUME_TAC THENL
  [SUBGOAL_THEN `pceo_b cO sO <= c696cm_boundary cO sO` (fun th -> MP_TAC th THEN RASM_ARITH_TAC)
   THEN MATCH_MP_TAC(REAL_ARITH `&0 <= y - x ==> x <= y`) THEN
   MATCH_MP_TAC PLOV_NONNEG_OF_MUL THEN EXISTS_TAC `cO:real` THEN
   CONJ_TAC THENL [RASM_ARITH_TAC; NLIN_TAC ~deg2:false [SQ_NONNEG `sO:real`]]; ALL_TAC] THEN
  (* the actual lower support of A on the bottom-square transverse axis *)
  PCPLW_PROD_TAC `cO:real` `sA - sO` THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cO:real`; `sO:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [PCPLW_ANTS_TAC; DISCH_TAC] THEN
  PCPLW_PROD_TAC `sO:real` `cO - cA` THEN
  SUBGOAL_THEN `&0 <= cO * sA - sO * cA` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLW_PROD_TAC `cO:real` `cA:real` THEN PCPLW_PROD_TAC `sO:real` `sA:real` THEN
  SUBGOAL_THEN `ABT_lower cA sA uA vA aA (--sO) cO =
                (cO * sA - sO * cA) * uA + (cO * cA + sO * sA) * vA` ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   SUBGOAL_THEN `--sO * cA + cO * sA = cO * sA - sO * cA /\
                 --(--sO) * sA + cO * cA = cO * cA + sO * sA` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `abs(cO * sA - sO * cA) = cO * sA - sO * cA /\
                 abs(cO * cA + sO * sA) = cO * cA + sO * sA` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  PCPLW_PROD_TAC `cO * sA - sO * cA` `&2 * (cA + sA) - &1 - uA` THEN
  PCPLW_PROD_TAC `cO * cA + sO * sA` `aA - &1` THEN
  SUBGOAL_THEN
   `pceo_b cO sO < (cO * sA - sO * cA) * (&2 * (cA + sA) - &1) +
                   (cO * cA + sO * sA) * ((vA + aA) - &1)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLW_USE PCEL_BOTTOM_COSINE [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `vA + aA:real`] THEN
  PCPLW_USE PCEO_STRONG_BASE_BOUND [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `vA + aA:real`] THEN
  PCPLW_USE PCEO_BASE_BOUND [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `vA + aA:real`] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `vA + aA:real`] PCEO_NORTHWEST_THRESHOLD) THEN
  ANTS_TAC THENL [PCPLW_ANTS_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `sA <= &3 / &5` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cA - &81 / &100`; `cA + &81 / &100`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(SPECL [`sA - &3 / &5`; `sA + &3 / &5`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLW_USE PCPL_LEFT_ALTERNATIVES (qL @ qA) THEN
  PCPLW_USE CSP_POSITIVE_ALTERNATIVES (qO @ qL) THEN
  let close th tms =
    MP_TAC(SPECL tms th) THEN ANTS_TAC THENL [PCPLW_ANTS_TAC; ASM_REWRITE_TAC[] THEN NO_TAC] in
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  FIRST
   [close PCPL_OWN_AXIS_IMPOSSIBLE (qO @ qL @ qA);
    close PCPL_CENTRAL_AXIS_IMPOSSIBLE (qO @ qL @ qA);
    close PLOV_OWN_AXIS_IMPOSSIBLE (qO @ qL @ qA);
    close PLOV_CENTRAL_AXIS_IMPOSSIBLE (qO @ qL @ qA)]);;
