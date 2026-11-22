(* ========================================================================= *)
(* Case 868 (Jatloe Compact/Cases/C868/Complete.lean): finite ownership over *)
(* nine original domains (Cases_C868_Ownership.ml, ForcedAuxiliary.ml) and   *)
(* hand geometry of the sectors of owners 256 / 3072 (PositiveSector,        *)
(* NegativeCornerSector, UpperCenter, NonnegativeSector) and the negative    *)
(* upper cap (UpperNegative*.ml).  Row 455 of the retained table.            *)
(* Load after n12/cases/cs_load.ml.  Result: C868_CASE_THMS.                 *)
(* ========================================================================= *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/Cases_C868_Complete.ml";;

let C868_CASE_THMS = [check_case_thm (455, C868C_EXCLUDED_ROW)];;
Printf.printf "C868: %d case theorem(s)\n%!" (length C868_CASE_THMS);;
