(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/OriginalEnding.lean          *)
(* (namespace N12Compact.Completion.OtherCases.C1090.OriginalData; Lean      *)
(* header: "Source only, uncompiled").  The C1090 continuous proof applied   *)
(* to the original marker family: AuxiliaryEntrance (owners p) =             *)
(* c1090od_auxent applied to the owner coordinate functions c1090od_owners.  *)
(* The unit normals of the owners (implicit in Lean's OpenSquare) come from  *)
(* OO_UNIT.  Tag C1090OE_.                                                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1090_OriginalData.ml";;
needs "n12/geometry/CP_OtherCases_C1090_StructuralReduction.ml";;

(* Lean: impossible_of_auxiliary_entrance *)
let C1090OE_IMPOSSIBLE_OF_AUXILIARY_ENTRANCE =
  let ent = list_mk_comb(`c1090od_auxent`, c1090od_owners) in
  let th = BETA_RULE (SPECL c1090od_owners C1090SR_IMPOSSIBLE_OF_EARLY_INPUT) in
  prove
   (list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
      mk_imp(mk_conj(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1090od_family`, ent), `false`)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN
    ASM_SIMP_TAC[OO_UNIT] THEN MATCH_MP_TAC C1090OD_EARLY_INPUT THEN ASM_REWRITE_TAC[]);;
