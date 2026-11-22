(* ========================================================================= *)
(* Port of Completion/Cases/C981/Coverage/Data/Prefix10.lean                   *)
(* (S12Completion.C981.Coverage.prefix10): the concatenation of its 13 chunks. *)
(* Lean ++ is APPEND (associative, so the bracketing is immaterial).      *)
(* Chunks 009-012 live in geometry/Chunk009.ml .. Chunk012.ml (names as in n12/scripts/ready.py).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk000.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk001.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk002.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk003.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk004.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk005.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk006.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk007.ml";;
needs "n12/geometry/CC_C981_Coverage_Data_Prefix10Chunks_Chunk008.ml";;
needs "n12/geometry/Chunk009.ml";;
needs "n12/geometry/Chunk010.ml";;
needs "n12/geometry/Chunk011.ml";;
needs "n12/geometry/Chunk012.ml";;

(* Lean: prefix10 *)
let c981cov_prefix10 = new_definition
 `c981cov_prefix10 : ((num->bool)list)list =
    APPEND c981cov_prefix10chunk000
    (APPEND c981cov_prefix10chunk001
    (APPEND c981cov_prefix10chunk002
    (APPEND c981cov_prefix10chunk003
    (APPEND c981cov_prefix10chunk004
    (APPEND c981cov_prefix10chunk005
    (APPEND c981cov_prefix10chunk006
    (APPEND c981cov_prefix10chunk007
    (APPEND c981cov_prefix10chunk008
    (APPEND c981cov_prefix10chunk009
    (APPEND c981cov_prefix10chunk010
    (APPEND c981cov_prefix10chunk011 c981cov_prefix10chunk012)))))))))))`;;
