(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components06/GQueries.lean
   (namespace N12Compact.Completion.OtherCases.C983.Component06Data).
   Lean certified_query% n = local query n (slq_data / mq_signature);
   N12Compact.HistoricalOwnership.Queries.queryN_certified = historical query N
   (HOQ_QUERYN of QueriesNNN.ml), referred to by index slq_hist_idx N;
   signature = mq_signature (the Exact decides are the OCaml check c983c06gq_exact);
   SingleDomain = dsd record, Check = mq_single, product = pk_product of the two
   half domains, trim = mr_trim, diameterFilter = mr_diameter_filter,
   DomainTransport.cache = dc_cache, NamedDomain = dt_named.
   family = c983ri_family (C983/RowIdentity).  Tag c983c06gq_ / C983C06GQ_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;
needs "n12/geometry/Queries044.ml";;
needs "n12/geometry/Queries045.ml";;
needs "n12/geometry/Queries046.ml";;
needs "n12/geometry/Queries047.ml";;
needs "n12/geometry/Queries048.ml";;

(* Lean signatures = queries.map signature (the Exact decides) *)
let c983c06gq_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c06gq_exact";;

(* Lean: gQueries6 *)
let c983c06gq_gQueries6 : int list = [760; 761; 762; 763; 764; 765; 766; slq_hist_idx 1462];;
(* Lean: gSignatures6 *)
let c983c06gq_gSignatures6 : (int * int * int list * int list) list =
  [(1024, 1, [0], [1]);
   (1024, 1, [1], []);
   (1024, 1, [2], [3]);
   (1024, 1, [3], [6; 7]);
   (1024, 1, [4], [6; 7]);
   (1024, 1, [5], [6; 8]);
   (1024, 1, [8], [6]);
   (1024, 1, [5; 6], [3])];;
(* Lean: gExact6 *)
let () = c983c06gq_exact c983c06gq_gSignatures6 c983c06gq_gQueries6;;
