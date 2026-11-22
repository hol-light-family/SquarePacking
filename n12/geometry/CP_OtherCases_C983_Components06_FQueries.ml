(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components06/FQueries.lean
   (namespace N12Compact.Completion.OtherCases.C983.Component06Data).
   Lean certified_query% n = local query n (slq_data / mq_signature);
   N12Compact.HistoricalOwnership.Queries.queryN_certified = historical query N
   (HOQ_QUERYN of QueriesNNN.ml), referred to by index slq_hist_idx N;
   signature = mq_signature (the Exact decides are the OCaml check c983c06fq_exact);
   SingleDomain = dsd record, Check = mq_single, product = pk_product of the two
   half domains, trim = mr_trim, diameterFilter = mr_diameter_filter,
   DomainTransport.cache = dc_cache, NamedDomain = dt_named.
   family = c983ri_family (C983/RowIdentity).  Tag c983c06fq_ / C983C06FQ_.  *)
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
let c983c06fq_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c06fq_exact";;

(* Lean: fQueries6 *)
let c983c06fq_fQueries6 : int list = [753; 754; 755; 756; 757; 758; 759; slq_hist_idx 1418; slq_hist_idx 1411];;
(* Lean: fSignatures6 *)
let c983c06fq_fSignatures6 : (int * int * int list * int list) list =
  [(1024, 0, [0], [4]);
   (1024, 0, [1], [3; 5]);
   (1024, 0, [2], [6]);
   (1024, 0, [3], [5]);
   (1024, 0, [4], [5; 9]);
   (1024, 0, [6], []);
   (1024, 0, [8], [5; 9]);
   (1024, 0, [1; 5], [4]);
   (1024, 0, [1; 3], [])];;
(* Lean: fExact6 *)
let () = c983c06fq_exact c983c06fq_fSignatures6 c983c06fq_fQueries6;;
