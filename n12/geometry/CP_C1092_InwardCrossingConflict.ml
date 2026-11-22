(* ========================================================================= *)
(* Port of Compact/Completion/C1092/InwardCrossingConflict.lean               *)
(* (namespace N12Compact.C1092InwardCrossingConflict).                       *)
(* positive_frame: CLF_POSITIVE_FRAME; CentralWallEscape: CWE_*;             *)
(* CentralWallPairAxes: CWPA_*; CentralWallPairSupport: CWPS_*.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/CentralWallPairAxes.ml";;
needs "n12/geometry/CentralWallPairSupport.ml";;

let C1092ICC_ANTS_TAC =
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: impossible *)
let C1092ICC_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR z.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ &0 < cA /\ &0 <= sA /\
     &2 * cA + &2 * sA <= uA /\
     --(&47 / &20) * sA + (&33 / &20) * cA <= vA /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&53 / &20) /\
     &0 <= z /\ z < &2 / &5 /\ (&1 + cA) * z = sA /\ sA * z = &1 - cA /\
     linside cA sA uA vA aA (&3) (&2 + z) /\
     lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aR`)) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = aR`)) THEN
  SUBGOAL_THEN `lcont c' s' u' v' aR /\ ldisj cA sA uA vA aR c' s' u' v' aR /\
                ~linside cR sR uR vR aR (&3) (&2 + z)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lcont cR sR uR vR aR` THEN
    UNDISCH_TAC `ldisj cA sA uA vA aR cR sR uR vR aR` THEN
    ASM_REWRITE_TAC[lcont; ldisj] THEN REPEAT DISCH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `aR:real`; `z:real`]
    CWE_LOWER_FACE) THEN C1092ICC_ANTS_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `aR:real`; `z:real`]
    CWE_WALL_INEQUALITIES) THEN C1092ICC_ANTS_TAC THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `z:real`] CWE_HALF_ANGLE_LT) THEN
  C1092ICC_ANTS_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `z:real`] CWE_SLOPE_OF_HALF_ANGLE) THEN
  C1092ICC_ANTS_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] CWPA_COSINE_BOUND) THEN
  C1092ICC_ANTS_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `c':real`; `s':real`; `z:real`]
    CWPA_WALL_ANGLE_ORDER) THEN C1092ICC_ANTS_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aR:real`;
                `c':real`; `s':real`; `u':real`; `v':real`; `aR:real`; `z:real`]
    CWPA_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aR:real`;
                  `c':real`; `s':real`; `u':real`; `v':real`; `aR:real`]
      CWPS_CENTRAL_AXIS_IMPOSSIBLE);
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aR:real`;
                  `c':real`; `s':real`; `u':real`; `v':real`; `aR:real`]
      CWPS_WALL_AXIS_IMPOSSIBLE)] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
