(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/RowIdentity.lean             *)
(* (namespace N12Compact.Completion.OtherCases.C1090.OriginalData; Lean      *)
(* header: "Uncompiled").  Original row 574 is bound to the literal C1090    *)
(* family (c1090od_family); the final contract stays conditional on the      *)
(* finite producer of AuxiliaryEntrance (owners p) = c1090od_auxent of the   *)
(* owner coordinate functions c1090od_owners.  Tag C1090RID_.                *)
(* ========================================================================= *)

needs "n12/geometry/RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_C1090_OriginalEnding.ml";;

(* Lean: lookup (private) *)
let C1090RID_LOOKUP = ri_lookup 574 `c1090od_family`;;

(* Lean: row_family *)
let C1090RID_ROW_FAMILY = ri_family_at 574 `c1090od_family`;;

(* Lean: excludes_case *)
let C1090RID_EXCLUDES_CASE = ri_excludes_case 574 `c1090od_family`;;

let C1090RID_PRODUCE =
  list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1090od_family`,
           list_mk_comb(`c1090od_auxent`, c1090od_owners)));;

(* Lean: family_excluded_of_auxiliary_entrance *)
let C1090RID_FAMILY_EXCLUDED_OF_AUXILIARY_ENTRANCE = prove
 (mk_imp(C1090RID_PRODUCE, `excl_fam c1090od_family`),
  DISCH_TAC THEN REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPEC_ALL C1090OE_IMPOSSIBLE_OF_AUXILIARY_ENTRANCE) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: case_excluded_of_auxiliary_entrance *)
let C1090RID_CASE_EXCLUDED_OF_AUXILIARY_ENTRANCE = prove
 (mk_imp(C1090RID_PRODUCE, `excl_case 1090`),
  DISCH_TAC THEN MATCH_MP_TAC C1090RID_EXCLUDES_CASE THEN
  MATCH_MP_TAC C1090RID_FAMILY_EXCLUDED_OF_AUXILIARY_ENTRANCE THEN ASM_REWRITE_TAC[]);;
