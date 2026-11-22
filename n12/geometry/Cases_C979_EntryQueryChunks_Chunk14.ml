(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk14.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC14_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Chunk49.ml";;
needs "n12/geometry/Queries026.ml";;
needs "n12/geometry/Queries027.ml";;
needs "n12/geometry/Queries065.ml";;
needs "n12/geometry/Queries066.ml";;

(* Lean: single979_7_0 *)
let c979eqc14_single979_7_0 = { dmask = 3072; dlower = 1; dupper = 2;
  dallowed = [[5]; [0; 5]; [1; 5]; [3; 5]; [4; 5]; [5; 7]; [5; 8]; [5; 9]];
  dqueries = [slq_hist_idx 857; slq_hist_idx 858; slq_hist_idx 2090; slq_hist_idx 859; slq_hist_idx 2091; slq_hist_idx 2092; slq_hist_idx 860; slq_hist_idx 2093; slq_hist_idx 2094; slq_hist_idx 2095; slq_hist_idx 861; slq_hist_idx 2096; slq_hist_idx 2097; slq_hist_idx 2098; slq_hist_idx 2099; slq_hist_idx 2100; slq_hist_idx 862; slq_hist_idx 2101; slq_hist_idx 2102; slq_hist_idx 2103; slq_hist_idx 2104; slq_hist_idx 2105; slq_hist_idx 2106; slq_hist_idx 863; slq_hist_idx 2107; slq_hist_idx 2108; slq_hist_idx 2109; slq_hist_idx 2110; slq_hist_idx 2111; slq_hist_idx 2112; slq_hist_idx 864; slq_hist_idx 2113; slq_hist_idx 2114; slq_hist_idx 2115; slq_hist_idx 2116; slq_hist_idx 2117; slq_hist_idx 2118; slq_hist_idx 2119; slq_hist_idx 865; slq_hist_idx 2120; slq_hist_idx 2121; slq_hist_idx 2122; slq_hist_idx 2123; slq_hist_idx 2124; slq_hist_idx 2125; slq_hist_idx 2126; slq_hist_idx 2127] };;
(* Lean: single979_7_0_checked *)
let C979EQC14_SINGLE979_7_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc14_single979_7_0;;
