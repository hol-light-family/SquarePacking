(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveBottomNegativeWallClosure.lean (Jatloe).  *)
(* The complete positive-singleton / negative-bottom-wall / negative central *)
(* neighbour cycle is impossible.  Normal: c977cc_normal; D.s = -r and       *)
(* B.s = -t are written sD = --r, sB = --t.                                  *)
(* C696PositiveCorner.corner_faces: C696PC_CORNER_FACES;                     *)
(* PositiveBottomNextAxes.negative_wall: PBNA_NEGATIVE_WALL;                 *)
(* CentralNegativeBottomAxes.alternatives: CNBA_ALTERNATIVES;                *)
(* PositiveBottomNegativeWallCycle.own_transverse: PBNWC_OWN_TRANSVERSE;     *)
(* PositiveBottomNegativeWallMixed.own_wall_transverse:                      *)
(*   PBNWM_OWN_WALL_TRANSVERSE;                                              *)
(* NegativeBottomTransverseChain.impossible: NBTC_IMPOSSIBLE;                *)
(* ShortMiddleSquare.impossible: SMS_IMPOSSIBLE; ownV: ABT_OWNV.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/PositiveBottomNegativeWallMixed.ml";;
needs "n12/geometry/PositiveBottomNegativeWallCycle.ml";;
needs "n12/geometry/NegativeBottomTransverseChain.ml";;
needs "n12/geometry/ShortMiddleSquare.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/PositiveBottomNextAxes.ml";;
needs "n12/geometry/CentralNegativeBottomAxes.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

(* Lean: impossible *)
let PBNWCL_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD cB sB uB vB aB r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     sD = --r /\ sB = --t /\
     c977cc_normal cO sO /\ c977cc_normal cD r /\ c977cc_normal cB t /\
     aO = aD /\ aD = aB /\ &1 < aO /\ t <= &3 / &10 /\
     lcont cO sO uO vO aO /\ lcont cD sD uD vD aD /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cO sO uO vO aO (&49 / &25) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&13 / &5) (&1) /\
     linside cD sD uD vD aD (&143 / &50) (&1) /\
     linside cD sD uD vD aD (&2) (&1) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     uB + aB <= &3 * cB - t /\ vB + aB <= &2 * cB + &3 * t /\
     ldisj cO sO uO vO aO cD sD uD vD aD /\
     ldisj cD sD uD vD aD cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  PCT_NORMAL_TAC THEN
  let conj_tac = REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
           CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC] in
  let use th tms = MP_TAC(SPECL tms th) THEN
    ANTS_TAC THENL [conj_tac; DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])] in
  let sqO = [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aB:real`]
  and sqD = [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`]
  and sqB = [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`] in
  MP_TAC(SPECL sqO C696PC_CORNER_FACES) THEN
  ANTS_TAC THENL [conj_tac; STRIP_TAC] THEN
  use PBNA_NEGATIVE_WALL (sqO @ sqD @ [`r:real`]) THEN
  use CNBA_ALTERNATIVES (sqD @ sqB @ [`t:real`]) THEN
  MP_TAC(SPECL sqD ABT_OWNV) THEN
  ANTS_TAC THENL [conj_tac; DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])] THEN
  let close th tms = MP_TAC(SPECL tms th) THEN
    MATCH_MP_TAC(TAUT `p ==> (p ==> false) ==> false`) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN conj_tac in
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  FIRST
   [close PBNWC_OWN_TRANSVERSE (sqO @ sqD @ sqB @ [`r:real`; `t:real`]);
    close PBNWM_OWN_WALL_TRANSVERSE (sqO @ sqD @ sqB @ [`r:real`; `t:real`]);
    close NBTC_IMPOSSIBLE (sqO @ sqD @ sqB @ [`r:real`; `t:real`]);
    close SMS_IMPOSSIBLE (sqO @ sqD @ sqB @
      [`&49 / &25`; `&19 / &25`; `&47 / &20`; `&33 / &20`; `r:real`; `cD:real`])]);;
