(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components03.lean
   (namespace N12Compact.Completion.OtherCases.C983).
   Lean certified_query% n = local query n (slq_data / mq_signature);
   N12Compact.HistoricalOwnership.Queries.queryN_certified = historical query N
   (HOQ_QUERYN of QueriesNNN.ml), referred to by index slq_hist_idx N;
   signature = mq_signature (the Exact decides are the OCaml check c983c03_exact);
   SingleDomain = dsd record, Check = mq_single, product = pk_product of the two
   half domains, trim = mr_trim, diameterFilter = mr_diameter_filter,
   DomainTransport.cache = dc_cache, NamedDomain = dt_named.
   family = c983ri_family (C983/RowIdentity).  Tag c983c03_ / C983C03_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;
needs "n12/geometry/Queries043.ml";;

(* Lean signatures = queries.map signature (the Exact decides) *)
let c983c03_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c03_exact";;

(* Lean: fQueries3 (private) *)
let c983c03_f_queries : int list = [slq_hist_idx 1387; slq_hist_idx 1388; slq_hist_idx 1389; slq_hist_idx 1390; slq_hist_idx 1391; slq_hist_idx 1392; slq_hist_idx 1393; slq_hist_idx 1394];;
(* Lean: fSignatures3 (private) *)
let c983c03_f_signatures : (int * int * int list * int list) list =
  [(48, 0, [0], []);
   (48, 0, [1], []);
   (48, 0, [2], []);
   (48, 0, [3], [7]);
   (48, 0, [4], []);
   (48, 0, [5], []);
   (48, 0, [6], []);
   (48, 0, [8], [9])];;
(* Lean: fExact3 (private) *)
let () = c983c03_exact c983c03_f_signatures c983c03_f_queries;;
(* Lean: fSingle3 (private) *)
let c983c03_f_single =
  {dmask = 48; dlower = 0; dupper = 2; dallowed = [[]; [7]; [9]; [3; 7]; [7; 9]; [8; 9]]; dqueries = c983c03_f_queries};;
(* Lean: fChecked3 (private) *)
let C983C03_F_CHECKED = mq_single `c983ri_family` 0 c983c03_f_single;;
(* Lean: gQueries3 (private) *)
let c983c03_g_queries : int list = [slq_hist_idx 1395; slq_hist_idx 1396; slq_hist_idx 1397; slq_hist_idx 1398; slq_hist_idx 1399; slq_hist_idx 1400; slq_hist_idx 1401; slq_hist_idx 1402];;
(* Lean: gSignatures3 (private) *)
let c983c03_g_signatures : (int * int * int list * int list) list =
  [(48, 1, [0], []);
   (48, 1, [1], []);
   (48, 1, [2], []);
   (48, 1, [3], []);
   (48, 1, [4], [7]);
   (48, 1, [5], []);
   (48, 1, [6], []);
   (48, 1, [8], [9])];;
(* Lean: gExact3 (private) *)
let () = c983c03_exact c983c03_g_signatures c983c03_g_queries;;
(* Lean: gSingle3 (private) *)
let c983c03_g_single =
  {dmask = 48; dlower = 0; dupper = 1; dallowed = [[]; [7]; [9]]; dqueries = c983c03_g_queries};;
(* Lean: gChecked3 (private) *)
let C983C03_G_CHECKED = mq_single `c983ri_family` 1 c983c03_g_single;;
(* Lean: rawDomain3 (private) *)
let C983C03_RAW_DOMAIN =
  if c983c03_f_single.dmask <> c983c03_g_single.dmask then failwith "c983c03: masks" else
  pk_product C983C03_F_CHECKED C983C03_G_CHECKED;;
(* Lean: cachedProduct3 (private) *)
let C983C03_CACHED_PRODUCT = dc_cache C983C03_RAW_DOMAIN 48
  `[({}:num->bool); {17}; {19}; {7}; {7,17}; {7,19}; {9}; {9,17}; {9,19}; {3,7}; {3,7,17}; {3,7,19}; {7,9}; {7,9,17}; {7,9,19}; {8,9}; {8,9,17}; {8,9,19}]`;;
(* Lean: combinedQueries3 (private) *)
let c983c03_combined_queries : int list = [slq_hist_idx 1403; slq_hist_idx 1404];;
(* Lean: combinedSignatures3 (private) *)
let c983c03_combined_signatures : (int * int * int list * int list) list =
  [(48, 2, [17], [7]);
   (48, 2, [9], [19])];;
(* Lean: combinedExact3 (private) *)
let () = c983c03_exact c983c03_combined_signatures c983c03_combined_queries;;
(* Lean: filtered3 (private) *)
let C983C03_FILTERED = mr_diameter_filter (mr_trim C983C03_CACHED_PRODUCT c983c03_combined_queries);;
(* Lean: initial3 *)
let C983C03_INITIAL = dt_named (dc_cache C983C03_FILTERED 48
  `[({}:num->bool); {19}; {7}; {7,17}; {7,19}; {9,19}; {7,9,19}; {8,9,19}]`);;
