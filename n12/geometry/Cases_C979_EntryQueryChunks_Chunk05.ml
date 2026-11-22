(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk05.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC05_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries012.ml";;
needs "n12/geometry/Queries013.ml";;

(* Lean: single979_2_1 *)
let c979eqc05_single979_2_1 = { dmask = 12; dlower = 0; dupper = 2;
  dallowed = [[]; [5]; [8]; [5; 8]];
  dqueries = [slq_hist_idx 386; slq_hist_idx 387; slq_hist_idx 388; slq_hist_idx 389; slq_hist_idx 390; slq_hist_idx 391; slq_hist_idx 392; slq_hist_idx 393; slq_hist_idx 394; slq_hist_idx 395; slq_hist_idx 396; slq_hist_idx 397; slq_hist_idx 398; slq_hist_idx 399; slq_hist_idx 400; slq_hist_idx 401; slq_hist_idx 402; slq_hist_idx 403; slq_hist_idx 404; slq_hist_idx 405; slq_hist_idx 406; slq_hist_idx 407; slq_hist_idx 408; slq_hist_idx 409; slq_hist_idx 410; slq_hist_idx 411; slq_hist_idx 412; slq_hist_idx 413; slq_hist_idx 414; slq_hist_idx 415; slq_hist_idx 416; slq_hist_idx 417; slq_hist_idx 418; slq_hist_idx 419; slq_hist_idx 420; slq_hist_idx 421; slq_hist_idx 422; slq_hist_idx 423; slq_hist_idx 424; slq_hist_idx 425; slq_hist_idx 426; slq_hist_idx 427; slq_hist_idx 428; slq_hist_idx 429; slq_hist_idx 430; slq_hist_idx 431; slq_hist_idx 432; slq_hist_idx 433; slq_hist_idx 434; slq_hist_idx 435; slq_hist_idx 436; slq_hist_idx 437] };;
(* Lean: single979_2_1_checked *)
let C979EQC05_SINGLE979_2_1_CHECKED = dsd_actual `c979eqb_family` 1 c979eqc05_single979_2_1;;
