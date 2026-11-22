(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk10.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC10_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;


(* Lean: single979_5_0 *)
let c979eqc10_single979_5_0 = { dmask = 256; dlower = 1; dupper = 2;
  dallowed = [[0]; [0; 1]; [2]; [0; 2]; [4]; [0; 4]; [1; 4]; [2; 4]; [0; 5]; [4; 5]; [4; 6]];
  dqueries = [429; 430; 431; 432; 433; 434; 435; 436; 437; 438; 439; 440; 441; 442; 443; 444; 445; 446; 447; 448; 449; 450; 451; 452; 453; 454; 455; 456; 457; 458; 459; 460; 461; 462; 463; 464; 465; 466; 467; 468; 469; 470; 471; 472] };;
(* Lean: single979_5_0_checked *)
let C979EQC10_SINGLE979_5_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc10_single979_5_0;;
