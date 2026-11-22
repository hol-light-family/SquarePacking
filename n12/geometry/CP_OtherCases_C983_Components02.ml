(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components02.lean
   (namespace N12Compact.Completion.OtherCases.C983).
   Lean certified_query% n = local query n (slq_data / mq_signature);
   N12Compact.HistoricalOwnership.Queries.queryN_certified = historical query N
   (HOQ_QUERYN of QueriesNNN.ml), referred to by index slq_hist_idx N;
   signature = mq_signature (the Exact decides are the OCaml check c983c02_exact);
   SingleDomain = dsd record, Check = mq_single, product = pk_product of the two
   half domains, trim = mr_trim, diameterFilter = mr_diameter_filter,
   DomainTransport.cache = dc_cache, NamedDomain = dt_named.
   family = c983ri_family (C983/RowIdentity).  Tag c983c02_ / C983C02_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;
needs "n12/geometry/Queries000.ml";;
needs "n12/geometry/Queries012.ml";;
needs "n12/geometry/Queries013.ml";;

(* Lean signatures = queries.map signature (the Exact decides) *)
let c983c02_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c02_exact";;

(* Lean: fQueries2 (private) *)
let c983c02_f_queries : int list = [slq_hist_idx 0; slq_hist_idx 1; slq_hist_idx 2; slq_hist_idx 3; slq_hist_idx 4; slq_hist_idx 5; slq_hist_idx 6; slq_hist_idx 7];;
(* Lean: fSignatures2 (private) *)
let c983c02_f_signatures : (int * int * int list * int list) list =
  [(12, 0, [0], []);
   (12, 0, [1], []);
   (12, 0, [2], [6]);
   (12, 0, [3], []);
   (12, 0, [4], []);
   (12, 0, [5], []);
   (12, 0, [7], []);
   (12, 0, [9], [8])];;
(* Lean: fExact2 (private) *)
let () = c983c02_exact c983c02_f_signatures c983c02_f_queries;;
(* Lean: fSingle2 (private) *)
let c983c02_f_single =
  {dmask = 12; dlower = 0; dupper = 2; dallowed = [[]; [6]; [8]; [2; 6]; [6; 8]; [8; 9]]; dqueries = c983c02_f_queries};;
(* Lean: fChecked2 (private) *)
let C983C02_F_CHECKED = mq_single `c983ri_family` 0 c983c02_f_single;;
(* Lean: gQueries2 (private) *)
let c983c02_g_queries : int list = [slq_hist_idx 386; slq_hist_idx 387; slq_hist_idx 389; slq_hist_idx 392; slq_hist_idx 396; slq_hist_idx 406; slq_hist_idx 413; slq_hist_idx 428];;
(* Lean: gSignatures2 (private) *)
let c983c02_g_signatures : (int * int * int list * int list) list =
  [(12, 1, [0], []);
   (12, 1, [1], []);
   (12, 1, [2], [5]);
   (12, 1, [3], []);
   (12, 1, [4], []);
   (12, 1, [6], []);
   (12, 1, [7], []);
   (12, 1, [9], [8])];;
(* Lean: gExact2 (private) *)
let () = c983c02_exact c983c02_g_signatures c983c02_g_queries;;
(* Lean: gSingle2 (private) *)
let c983c02_g_single =
  {dmask = 12; dlower = 0; dupper = 1; dallowed = [[]; [5]; [8]]; dqueries = c983c02_g_queries};;
(* Lean: gChecked2 (private) *)
let C983C02_G_CHECKED = mq_single `c983ri_family` 1 c983c02_g_single;;
(* Lean: rawDomain2 (private) *)
let C983C02_RAW_DOMAIN =
  if c983c02_f_single.dmask <> c983c02_g_single.dmask then failwith "c983c02: masks" else
  pk_product C983C02_F_CHECKED C983C02_G_CHECKED;;
(* Lean: cachedProduct2 (private) *)
let C983C02_CACHED_PRODUCT = dc_cache C983C02_RAW_DOMAIN 12
  `[({}:num->bool); {15}; {18}; {6}; {6,15}; {6,18}; {8}; {8,15}; {8,18}; {2,6}; {2,6,15}; {2,6,18}; {6,8}; {6,8,15}; {6,8,18}; {8,9}; {8,9,15}; {8,9,18}]`;;
(* Lean: combinedQueries2 (private) *)
let c983c02_combined_queries : int list = [slq_hist_idx 438; slq_hist_idx 8];;
(* Lean: combinedSignatures2 (private) *)
let c983c02_combined_signatures : (int * int * int list * int list) list =
  [(12, 2, [15], [6]);
   (12, 2, [8], [18])];;
(* Lean: combinedExact2 (private) *)
let () = c983c02_exact c983c02_combined_signatures c983c02_combined_queries;;
(* Lean: filtered2 (private) *)
let C983C02_FILTERED = mr_diameter_filter (mr_trim C983C02_CACHED_PRODUCT c983c02_combined_queries);;
(* Lean: initial2 *)
let C983C02_INITIAL = dt_named (dc_cache C983C02_FILTERED 12
  `[({}:num->bool); {18}; {6}; {6,15}; {6,18}; {8,18}; {6,8,18}; {8,9,18}]`);;
