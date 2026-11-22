(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components11.lean.           *)
(* Genuine full C983 auxiliary budget for original owner 11, mask 32768.     *)
(* Query certificates are reused symbolically under the exact owned/foreign  *)
(* signature conditions. All finite cuts are ordinary kernel decisions.      *)
(* Lean certified_query% n = local query n (slq_data / mq_signature);      *)
(* SingleDomain = dsd record, Check = mq_single, product = mq_product,      *)
(* trim = mr_trim, diameterFilter = mr_diameter_filter, cache = dc_cache,   *)
(* NamedDomain = (|- cdom fam m al, |- m IN fam) via dt_named.              *)
(* family = c983ri_family (C983/RowIdentity).                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean signatures = queries.map signature (the fExact / gExact decides) *)
let c983c11_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c11_exact";;

(* Lean: fQueries11 (private) *)
let c983c11_fqueries = [1536; 1537; 1539; 1545; 1554; 1566; 1575; 1544; 1552; 1553; 1560; 1565; 1558];;
(* Lean: fSignatures11 (private) *)
let c983c11_fsignatures =
  [(32768, 0, [0], []);
   (32768, 0, [1], []);
   (32768, 0, [2], [3; 5]);
   (32768, 0, [4], [5]);
   (32768, 0, [6], [5; 7]);
   (32768, 0, [8], []);
   (32768, 0, [9], []);
   (32768, 0, [2; 3], []);
   (32768, 0, [2; 5], []);
   (32768, 0, [4; 5], []);
   (32768, 0, [5; 6], []);
   (32768, 0, [6; 7], []);
   (32768, 0, [3; 6], [5])];;
(* Lean: fExact11 (private) *)
let () = c983c11_exact c983c11_fsignatures c983c11_fqueries;;
(* Lean: fSingle11 (private) *)
let c983c11_fsingle =
  {dmask = 32768; dlower = 1; dupper = 3; dallowed = [[3]; [5]; [7]; [3; 5]; [3; 7]; [5; 7]; [3; 5; 7]]; dqueries = c983c11_fqueries};;

(* Lean: gQueries11 (private) *)
let c983c11_gqueries = [1585; 1586; 1588; 1591; 1598; 1604; 1617; 1626];;
(* Lean: gSignatures11 (private) *)
let c983c11_gsignatures =
  [(32768, 1, [0], []);
   (32768, 1, [1], [4]);
   (32768, 1, [2], []);
   (32768, 1, [3], []);
   (32768, 1, [5], []);
   (32768, 1, [6], []);
   (32768, 1, [8], []);
   (32768, 1, [9], [7])];;
(* Lean: gExact11 (private) *)
let () = c983c11_exact c983c11_gsignatures c983c11_gqueries;;
(* Lean: gSingle11 (private) *)
let c983c11_gsingle =
  {dmask = 32768; dlower = 1; dupper = 2; dallowed = [[4]; [7]; [1; 4]; [4; 7]; [7; 9]]; dqueries = c983c11_gqueries};;

(* Lean: fChecked11, gChecked11, rawDomain11 (private): the two half domains *)
(* (kinds 0 and 1) and their product  |- cdom c983ri_family 32768 [..] *)
let C983C11_FCHECKED = mq_single `c983ri_family` 0 c983c11_fsingle;;
let C983C11_GCHECKED = mq_single `c983ri_family` 1 c983c11_gsingle;;
let C983C11_RAW_DOMAIN =
  if c983c11_fsingle.dmask <> c983c11_gsingle.dmask then failwith "c983c11: masks" else
  pk_product C983C11_FCHECKED C983C11_GCHECKED;;

(* Lean: cachedProduct11 (private) *)
let C983C11_CACHED_PRODUCT = dc_cache C983C11_RAW_DOMAIN 32768
  `[{3,14}; {3,17}; {3,11,14}; {3,14,17}; {3,17,19}; {5,14}; {5,17}; {5,11,14}; {5,14,17}; {5,17,19}; {7,14}; {7,17}; {7,11,14}; {7,14,17}; {7,17,19}; {3,5,14}; {3,5,17}; {3,5,11,14}; {3,5,14,17}; {3,5,17,19}; {3,7,14}; {3,7,17}; {3,7,11,14}; {3,7,14,17}; {3,7,17,19}; {5,7,14}; {5,7,17}; {5,7,11,14}; {5,7,14,17}; {5,7,17,19}; {3,5,7,14}; {3,5,7,17}; {3,5,7,11,14}; {3,5,7,14,17}; {3,5,7,17,19}]`;;

(* Lean: combinedQueries11, combinedSignatures11, combinedExact11 (private) *)
let c983c11_combinedqueries : int list = [1644; 1635; 1645; 1636; 1639; 1650];;
let c983c11_combinedsignatures : (int * int * int list * int list) list =
  [(32768, 2, [3; 17], [14]);
   (32768, 2, [5; 14], [3; 7]);
   (32768, 2, [5; 17], [3; 7]);
   (32768, 2, [7; 14], [17]);
   (32768, 2, [5; 11; 14], []);
   (32768, 2, [5; 17; 19], [])];;
let () = c983c11_exact c983c11_combinedsignatures c983c11_combinedqueries;;

(* Lean: filtered11 (private) *)
let C983C11_FILTERED = mr_diameter_filter (mr_trim C983C11_CACHED_PRODUCT c983c11_combinedqueries);;

(* Lean: initial11 *)
let C983C11_INITIAL = dt_named (dc_cache C983C11_FILTERED 32768
  `[{3,14}; {3,11,14}; {3,14,17}; {7,17}; {7,14,17}; {7,17,19}; {3,5,14}; {3,5,14,17}; {3,7,14,17}; {5,7,17}; {5,7,14,17}; {3,5,7,14,17}]`);;
