(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk06.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC06_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries043.ml";;

(* Lean: single979_3_0 *)
let c979eqc06_single979_3_0 = { dmask = 48; dlower = 0; dupper = 1;
  dallowed = [[]; [7]; [9]];
  dqueries = [slq_hist_idx 1387; slq_hist_idx 1388; slq_hist_idx 1389; slq_hist_idx 1390; slq_hist_idx 1391; slq_hist_idx 1392; slq_hist_idx 1393; slq_hist_idx 1394] };;
(* Lean: single979_3_0_checked *)
let C979EQC06_SINGLE979_3_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc06_single979_3_0;;
