(* ========================================================================= *)
(* Port of Compact/Geometry/SouthwestNegativeCorner.lean (Jatloe, N12-jatloe)*)
(* (namespace N12Compact.SouthwestNegativeCorner).                           *)
(* The full negative-central sector for an arbitrary bottom singleton O:     *)
(* O is canonicalized (CLF_CANONICAL_FRAME) and the two signed sectors are   *)
(* C696PC_POINT and C977NCO_POINT.                                           *)
(* Note: Lean variable T is renamed TT (T is truth in HOL).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;

(* Lean: point *)
let SNC_POINT = prove
 (`forall cO sO uO vO aO cA sA uA vA aA cL sL uL vL aL TT.
     cO * cO + sO * sO = &1 /\
     sA = --TT /\ c977cc_normal cA TT /\ aO = aA /\ &1 < aA /\
     lcont cO sO uO vO aO /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\
     ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&1) (&87 / &50) /\
     ldisj cO sO uO vO aO cA sA uA vA aA /\
     ldisj cA sA uA vA aA cL sL uL vL aL
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sA = --TT`)) THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aA:real`]
    CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj; c977cc_normal]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aA`)) THEN
  SUBGOAL_THEN `c1 pow 2 + s1 pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c1 * c1 + s1 * s1 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s1` THENL
  [MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aA:real`;
                 `cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`;
                 `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `TT:real`]
     C696PC_POINT);
   MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aA:real`;
                 `cA:real`; `--TT`; `uA:real`; `vA:real`; `aA:real`;
                 `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `--s1`; `TT:real`]
     C977NCO_POINT)] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[c977cc_normal; lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC ORELSE
   (UNDISCH_TAC `c1 pow 2 + s1 pow 2 = &1` THEN CONV_TAC REAL_RING)));;
