(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk09.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC09_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries024.ml";;
needs "n12/geometry/Queries025.ml";;

(* Lean: single979_4_1 *)
let c979eqc09_single979_4_1 = { dmask = 192; dlower = 0; dupper = 2;
  dallowed = [[]; [1]; [4]; [1; 4]];
  dqueries = [slq_hist_idx 769; slq_hist_idx 770; slq_hist_idx 771; slq_hist_idx 772; slq_hist_idx 773; slq_hist_idx 774; slq_hist_idx 775; slq_hist_idx 776; slq_hist_idx 777; slq_hist_idx 778; slq_hist_idx 779; slq_hist_idx 780; slq_hist_idx 781; slq_hist_idx 782; slq_hist_idx 783; slq_hist_idx 784; slq_hist_idx 785; slq_hist_idx 786; slq_hist_idx 787; slq_hist_idx 788; slq_hist_idx 789; slq_hist_idx 790; slq_hist_idx 791; slq_hist_idx 792; slq_hist_idx 793; slq_hist_idx 794; slq_hist_idx 795; slq_hist_idx 796; slq_hist_idx 797; slq_hist_idx 798; slq_hist_idx 799; slq_hist_idx 800; slq_hist_idx 801; slq_hist_idx 802; slq_hist_idx 803; slq_hist_idx 804; slq_hist_idx 805; slq_hist_idx 806; slq_hist_idx 807; slq_hist_idx 808; slq_hist_idx 809; slq_hist_idx 810; slq_hist_idx 811; slq_hist_idx 812; slq_hist_idx 813; slq_hist_idx 814; slq_hist_idx 815; slq_hist_idx 816; slq_hist_idx 817; slq_hist_idx 818; slq_hist_idx 819; slq_hist_idx 820] };;
(* Lean: single979_4_1_checked *)
let C979EQC09_SINGLE979_4_1_CHECKED = dsd_actual `c979eqb_family` 1 c979eqc09_single979_4_1;;
