(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Data/Prefix09.lean                   *)
(* (S12Completion.C981.Coverage.prefix09): the concatenation of its 9 chunks. *)
(* Lean ++ is APPEND (associative, so the bracketing is immaterial).      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk000.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk001.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk002.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk003.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk004.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk005.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk006.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk007.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix09Chunks_Chunk008.ml";;

(* Lean: prefix09 *)
let c981cov_prefix09 = new_definition
 `c981cov_prefix09 : ((num->bool)list)list =
    APPEND c981cov_prefix09chunk000
    (APPEND c981cov_prefix09chunk001
    (APPEND c981cov_prefix09chunk002
    (APPEND c981cov_prefix09chunk003
    (APPEND c981cov_prefix09chunk004
    (APPEND c981cov_prefix09chunk005
    (APPEND c981cov_prefix09chunk006
    (APPEND c981cov_prefix09chunk007 c981cov_prefix09chunk008)))))))`;;
