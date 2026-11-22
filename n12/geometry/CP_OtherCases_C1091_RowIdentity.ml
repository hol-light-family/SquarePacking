(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1091/RowIdentity.lean             *)
(* (namespace N12Compact.Completion.OtherCases.C1091.OriginalData).          *)
(* Original row 575 is bound to the literal C1091 family (c1091od_family);   *)
(* the final contract stays conditional on the six raw entrance points       *)
(* (ResidualEntrance (owners p) = c1091rp_entrance of c1091rp_owners).       *)
(* (Lean header: "Source only, uncompiled".)  Tag C1091RID_.                  *)
(* ========================================================================= *)

needs "n12/geometry/RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_C1091_ResidualProduction.ml";;

(* Lean: lookup (private) *)
let C1091RID_LOOKUP = ri_lookup 575 `c1091od_family`;;

(* Lean: row_family *)
let C1091RID_ROW_FAMILY = ri_family_at 575 `c1091od_family`;;

(* Lean: excludes_case *)
let C1091RID_EXCLUDES_CASE = ri_excludes_case 575 `c1091od_family`;;

let C1091RID_PRODUCE =
  list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family`,
           list_mk_comb(`c1091rp_entrance`, c1091rp_owners)));;

(* Lean: family_excluded_of_residual_entrance *)
let C1091RID_FAMILY_EXCLUDED_OF_RESIDUAL_ENTRANCE = prove
 (mk_imp(C1091RID_PRODUCE, `excl_fam c1091od_family`),
  DISCH_TAC THEN REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPEC_ALL C1091RP_IMPOSSIBLE_OF_RESIDUAL_ENTRANCE) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: case_excluded_of_residual_entrance *)
let C1091RID_CASE_EXCLUDED_OF_RESIDUAL_ENTRANCE = prove
 (mk_imp(C1091RID_PRODUCE, `excl_case 1091`),
  DISCH_TAC THEN MATCH_MP_TAC C1091RID_EXCLUDES_CASE THEN
  MATCH_MP_TAC C1091RID_FAMILY_EXCLUDED_OF_RESIDUAL_ENTRANCE THEN ASM_REWRITE_TAC[]);;
