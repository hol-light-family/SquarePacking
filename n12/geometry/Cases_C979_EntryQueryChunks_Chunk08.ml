(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk08.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC08_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries001.ml";;

(* Lean: single979_4_0 *)
let c979eqc08_single979_4_0 = { dmask = 192; dlower = 0; dupper = 1;
  dallowed = [[]; [1]; [3]];
  dqueries = [slq_hist_idx 53; slq_hist_idx 54; slq_hist_idx 55; slq_hist_idx 56; slq_hist_idx 57; slq_hist_idx 58; slq_hist_idx 59; slq_hist_idx 60] };;
(* Lean: single979_4_0_checked *)
let C979EQC08_SINGLE979_4_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc08_single979_4_0;;
