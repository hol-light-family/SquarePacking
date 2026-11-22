(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk12.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC12_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Chunk49.ml";;

(* Lean: single979_6_0 *)
let c979eqc12_single979_6_0 = { dmask = 512; dlower = 1; dupper = 2;
  dallowed = [[4]; [2; 4]; [4; 5]; [6]; [4; 6]; [8]; [4; 8]; [5; 8]; [6; 8]; [4; 9]; [8; 9]];
  dqueries = [582; 583; 584; 585; 586; 587; 588; 589; 590; 591; 592; 593; 594; 595; 596; 597; 598; 599; 600; 601; 602; 603; 604; 605; 606; 607; 608; 609; 610; 611; 612; 613; 614; 615; 616; 617; 618; 619; 620; 621; 622; 623; 624; 625] };;
(* Lean: single979_6_0_checked *)
let C979EQC12_SINGLE979_6_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc12_single979_6_0;;
