(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk16.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC16_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Chunk49.ml";;

(* Lean: single979_8_0 *)
let c979eqc16_single979_8_0 = { dmask = 4096; dlower = 1; dupper = 2;
  dallowed = [[0]; [1]; [0; 1]; [0; 2]; [1; 3]];
  dqueries = [989; 990; 991; 992; 993; 994; 995; 996; 997; 998; 999; 1000; 1001; 1002; 1003; 1004; 1005; 1006; 1007; 1008; 1009; 1010; 1011; 1012; 1013; 1014; 1015; 1016; 1017; 1018; 1019; 1020; 1021; 1022; 1023; 1024; 1025; 1026; 1027; 1028; 1029; 1030; 1031; 1032; 1033; 1034; 1035; 1036; 1037; 1038] };;
(* Lean: single979_8_0_checked *)
let C979EQC16_SINGLE979_8_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc16_single979_8_0;;
