(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk22.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC22_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;


(* Lean: single979_11_0 *)
let c979eqc22_single979_11_0 = { dmask = 32768; dlower = 1; dupper = 2;
  dallowed = [[3]; [5]; [3; 5]; [7]; [3; 7]; [5; 7]];
  dqueries = [1536; 1537; 1538; 1539; 1540; 1541; 1542; 1543; 1544; 1545; 1546; 1547; 1548; 1549; 1550; 1551; 1552; 1553; 1554; 1555; 1556; 1557; 1558; 1559; 1560; 1561; 1562; 1563; 1564; 1565; 1566; 1567; 1568; 1569; 1570; 1571; 1572; 1573; 1574; 1575; 1576; 1577; 1578; 1579; 1580; 1581; 1582; 1583; 1584] };;
(* Lean: single979_11_0_checked *)
let C979EQC22_SINGLE979_11_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc22_single979_11_0;;
