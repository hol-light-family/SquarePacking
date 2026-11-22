(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1091/ResidualEnding.lean          *)
(* (namespace N12Compact.Completion.OtherCases.C1091.Residual).  The raw     *)
(* residual ending: split on actual top ownership of G4.  q : Fin 12 ->      *)
(* OpenSquare is qc qs qu qv qa (unit normals explicit), Input is            *)
(* c1091ri_input; top_g4_impossible / no_top_g4_impossible are               *)
(* C1091RT_TOP_G4_IMPOSSIBLE / C1091RN_NO_TOP_G4_IMPOSSIBLE.  Tag C1091RE_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_ResidualNoTopG4.ml";;
needs "n12/geometry/CP_OtherCases_C1091_ResidualTopG4.ml";;

(* Lean: impossible *)
let C1091RE_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1091ri_input qc qs qu qv qa
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)` THENL
   [MATCH_MP_TAC(SPEC_ALL C1091RT_TOP_G4_IMPOSSIBLE);
    MATCH_MP_TAC(SPEC_ALL C1091RN_NO_TOP_G4_IMPOSSIBLE)] THEN
  ASM_REWRITE_TAC[]);;
