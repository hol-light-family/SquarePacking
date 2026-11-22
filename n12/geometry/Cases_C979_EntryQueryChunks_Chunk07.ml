(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk07.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC07_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries043.ml";;
needs "n12/geometry/Queries052.ml";;
needs "n12/geometry/Queries053.ml";;

(* Lean: single979_3_1 *)
let c979eqc07_single979_3_1 = { dmask = 48; dlower = 0; dupper = 2;
  dallowed = [[]; [7]; [9]; [7; 9]];
  dqueries = [slq_hist_idx 1395; slq_hist_idx 1396; slq_hist_idx 1683; slq_hist_idx 1397; slq_hist_idx 1684; slq_hist_idx 1685; slq_hist_idx 1398; slq_hist_idx 1686; slq_hist_idx 1687; slq_hist_idx 1688; slq_hist_idx 1399; slq_hist_idx 1689; slq_hist_idx 1690; slq_hist_idx 1691; slq_hist_idx 1692; slq_hist_idx 1400; slq_hist_idx 1693; slq_hist_idx 1694; slq_hist_idx 1695; slq_hist_idx 1696; slq_hist_idx 1697; slq_hist_idx 1401; slq_hist_idx 1698; slq_hist_idx 1699; slq_hist_idx 1700; slq_hist_idx 1701; slq_hist_idx 1702; slq_hist_idx 1703; slq_hist_idx 1704; slq_hist_idx 1705; slq_hist_idx 1706; slq_hist_idx 1707; slq_hist_idx 1708; slq_hist_idx 1709; slq_hist_idx 1710; slq_hist_idx 1402; slq_hist_idx 1711; slq_hist_idx 1712; slq_hist_idx 1713; slq_hist_idx 1714; slq_hist_idx 1715; slq_hist_idx 1716; slq_hist_idx 1717; slq_hist_idx 1718; slq_hist_idx 1719; slq_hist_idx 1720; slq_hist_idx 1721; slq_hist_idx 1722; slq_hist_idx 1723; slq_hist_idx 1724; slq_hist_idx 1725; slq_hist_idx 1726] };;
(* Lean: single979_3_1_checked *)
let C979EQC07_SINGLE979_3_1_CHECKED = dsd_actual `c979eqb_family` 1 c979eqc07_single979_3_1;;
