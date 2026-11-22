(* ========================================================================= *)
(* Port of Compact/Geometry/NegativeBottomNegativeWallClosure.lean (Jatloe,  *)
(* N12-jatloe; namespace N12Compact.NegativeBottomNegativeWallClosure).      *)
(* All four directed transverse selectors of the steep negative singleton /  *)
(* negative bottom wall / negative central neighbour are excluded.           *)
(* Normal: c977cc_normal; O.s = -s, D.s = -r, B.s = -t are written           *)
(* sO = --s, sD = --r, sB = --t.                                             *)
(* corner_face: C977NCO_CORNER_FACE;                                         *)
(* NegativeBottomNextAxes.negative_wall: NBNA_NEGATIVE_WALL;                 *)
(* CentralNegativeBottomAxes.alternatives: CNBA_ALTERNATIVES;                *)
(* NegativeBottomCentralAxis.impossible: NBCA_IMPOSSIBLE;                    *)
(* NegativeBottomOwnTransverse.impossible: NBOT_IMPOSSIBLE;                  *)
(* NegativeBottomTransverseChain.impossible: NBTC_IMPOSSIBLE;                *)
(* ShortMiddleSquare.impossible: SMS_IMPOSSIBLE; ownV: ABT_OWNV.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/NegativeBottomNextAxes.ml";;
needs "n12/geometry/CentralNegativeBottomAxes.ml";;
needs "n12/geometry/NegativeBottomCentralAxis.ml";;
needs "n12/geometry/NegativeBottomOwnTransverse.ml";;
needs "n12/geometry/NegativeBottomTransverseChain.ml";;
needs "n12/geometry/ShortMiddleSquare.ml";;

let NBNWCL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: impossible *)
let NBNWCL_IMPOSSIBLE = prove
 (`forall cO sO uO vO aO cD sD uD vD aD cB sB uB vB aB s r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     sO = --s /\ sD = --r /\ sB = --t /\
     c977cc_normal cO s /\ c977cc_normal cD r /\ c977cc_normal cB t /\
     aO = aD /\ aD = aB /\ &1 < aO /\ &47 / &100 < s /\ t <= &3 / &10 /\
     lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cO sO uO vO aO (&49 / &25) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
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
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sO = --s`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sD = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aD`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  NBNWCL_NORMAL_TAC THEN
  let conj_tac = REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
           CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC] in
  let use th tms = MP_TAC(SPECL tms th) THEN
    ANTS_TAC THENL [conj_tac; DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])] in
  let sqO = [`cO:real`; `--s`; `uO:real`; `vO:real`; `aB:real`]
  and sqD = [`cD:real`; `--r`; `uD:real`; `vD:real`; `aB:real`]
  and sqB = [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`] in
  MP_TAC(SPECL (sqO @ [`s:real`]) C977NCO_CORNER_FACE) THEN
  ANTS_TAC THENL [conj_tac; STRIP_TAC] THEN
  use NBNA_NEGATIVE_WALL (sqO @ sqD @ [`s:real`; `r:real`]) THEN
  use CNBA_ALTERNATIVES (sqD @ sqB @ [`t:real`]) THEN
  MP_TAC(SPECL sqD ABT_OWNV) THEN
  ANTS_TAC THENL [conj_tac; DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])] THEN
  let close th tms = MP_TAC(ISPECL tms th) THEN
    MATCH_MP_TAC(TAUT `p ==> (p ==> false) ==> false`) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN conj_tac in
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  FIRST
   [close NBCA_IMPOSSIBLE (sqO @ sqD @ sqB @ [`s:real`; `r:real`; `t:real`]);
    close NBOT_IMPOSSIBLE (sqD @ sqB @ [`r:real`; `t:real`; `cO:real`; `s:real`]);
    close NBTC_IMPOSSIBLE (sqO @ sqD @ sqB @ [`r:real`; `t:real`]);
    close SMS_IMPOSSIBLE (sqO @ sqD @ sqB @
      [`&49 / &25`; `&19 / &25`; `&47 / &20`; `&33 / &20`; `r:real`; `cD:real`])]);;
