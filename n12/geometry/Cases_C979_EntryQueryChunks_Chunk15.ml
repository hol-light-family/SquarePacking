(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk15.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC15_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Chunk49.ml";;
needs "n12/geometry/Queries027.ml";;
needs "n12/geometry/Queries028.ml";;

(* Lean: single979_7_1 *)
let c979eqc15_single979_7_1 = { dmask = 3072; dlower = 0; dupper = 2;
  dallowed = [[]; [1]; [3]; [1; 3]; [4]; [1; 4]; [3; 4]; [6]; [1; 6]; [3; 6]; [4; 6]; [7]; [1; 7]; [3; 7]; [4; 7]; [6; 7]; [9]; [1; 9]; [3; 9]; [4; 9]; [6; 9]; [7; 9]];
  dqueries = [slq_hist_idx 866; slq_hist_idx 867; slq_hist_idx 868; slq_hist_idx 869; slq_hist_idx 870; slq_hist_idx 871; slq_hist_idx 872; slq_hist_idx 873; slq_hist_idx 874; slq_hist_idx 875; slq_hist_idx 876; slq_hist_idx 877; slq_hist_idx 878; slq_hist_idx 879; slq_hist_idx 880; slq_hist_idx 881; slq_hist_idx 882; slq_hist_idx 883; slq_hist_idx 884; slq_hist_idx 885; slq_hist_idx 886; slq_hist_idx 887; slq_hist_idx 888; slq_hist_idx 889; slq_hist_idx 890; slq_hist_idx 891; slq_hist_idx 892; slq_hist_idx 893; slq_hist_idx 894; slq_hist_idx 895; slq_hist_idx 896; slq_hist_idx 897; slq_hist_idx 898; slq_hist_idx 899] };;
(* Lean: single979_7_1_checked *)
let C979EQC15_SINGLE979_7_1_CHECKED = dsd_actual `c979eqb_family` 1 c979eqc15_single979_7_1;;
