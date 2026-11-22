(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components08.lean.           *)
(* Genuine full C983 auxiliary budget for original owner 8, mask 4096.       *)
(* Query certificates are reused symbolically under the exact owned/foreign  *)
(* signature conditions. All finite cuts are ordinary kernel decisions.      *)
(* Same structure and toolkit as Components01 (see there):                   *)
(* certified_query%% n = local query n, SingleDomain = dsd record, Check =     *)
(* mq_single, product = mq_product / pk_product, trim = mr_trim,             *)
(* diameterFilter = mr_diameter_filter, cache = dc_cache, NamedDomain =      *)
(* dt_named.  family = c983ri_family.  Tag c983c08_ / C983C08_.              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean signatures = queries.map signature (the Exact decides) *)
let c983c08_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c08_exact";;

(* Lean: fQueries8 (private) *)
let c983c08_fqueries = [989; 991; 994; 999; 1005; 1012; 1020; 1029];;
(* Lean: fSignatures8 (private) *)
let c983c08_fsignatures =
  [(4096, 0, [2], [0]);
   (4096, 0, [3], [1]);
   (4096, 0, [4], []);
   (4096, 0, [5], []);
   (4096, 0, [6], []);
   (4096, 0, [7], []);
   (4096, 0, [8], []);
   (4096, 0, [9], [])];;
(* Lean: fExact8 (private) *)
let () = c983c08_exact c983c08_fsignatures c983c08_fqueries;;
(* Lean: fSingle8 (private) *)
let c983c08_fsingle =
  {dmask = 4096; dlower = 1; dupper = 3; dallowed = [[0]; [1]; [0; 1]; [0; 2]; [1; 3]; [0; 1; 2]; [0; 1; 3]]; dqueries = c983c08_fqueries};;

(* Lean: gQueries8 (private) *)
let c983c08_gqueries = [1039; 1043; 1048; 1054; 1061; 1069; 1078; 1070; 1080; 1058; 1073; 1082];;
(* Lean: gSignatures8 (private) *)
let c983c08_gsignatures =
  [(4096, 1, [2], []);
   (4096, 1, [4], []);
   (4096, 1, [5], []);
   (4096, 1, [6], [3]);
   (4096, 1, [7], []);
   (4096, 1, [8], [0; 3]);
   (4096, 1, [9], [1; 3]);
   (4096, 1, [0; 8], []);
   (4096, 1, [1; 9], []);
   (4096, 1, [3; 6], []);
   (4096, 1, [3; 8], []);
   (4096, 1, [3; 9], [])];;
(* Lean: gExact8 (private) *)
let () = c983c08_exact c983c08_gsignatures c983c08_gqueries;;
(* Lean: gSingle8 (private) *)
let c983c08_gsingle =
  {dmask = 4096; dlower = 1; dupper = 2; dallowed = [[0]; [1]; [3]; [0; 1]; [0; 3]; [1; 3]]; dqueries = c983c08_gqueries};;

(* Lean: fChecked8, gChecked8, rawDomain8 (private): the two half domains      *)
(* (kinds 0 and 1) and their product  |- cdom c983ri_family 4096 [..]          *)
let C983C08_FCHECKED = mq_single `c983ri_family` 0 c983c08_fsingle;;
let C983C08_GCHECKED = mq_single `c983ri_family` 1 c983c08_gsingle;;
let C983C08_RAW_DOMAIN =
  if c983c08_fsingle.dmask <> c983c08_gsingle.dmask then failwith "c983c08: masks" else
  pk_product C983C08_FCHECKED C983C08_GCHECKED;;

(* Lean: cachedProduct8 (private) *)
let C983C08_CACHED_PRODUCT = dc_cache C983C08_RAW_DOMAIN 4096
  `[{0,10}; {0,11}; {0,13}; {0,10,11}; {0,10,13}; {0,11,13}; {1,10}; {1,11}; {1,13}; {1,10,11}; {1,10,13}; {1,11,13}; {0,1,10}; {0,1,11}; {0,1,13}; {0,1,10,11}; {0,1,10,13}; {0,1,11,13}; {0,2,10}; {0,2,11}; {0,2,13}; {0,2,10,11}; {0,2,10,13}; {0,2,11,13}; {1,3,10}; {1,3,11}; {1,3,13}; {1,3,10,11}; {1,3,10,13}; {1,3,11,13}; {0,1,2,10}; {0,1,2,11}; {0,1,2,13}; {0,1,2,10,11}; {0,1,2,10,13}; {0,1,2,11,13}; {0,1,3,10}; {0,1,3,11}; {0,1,3,13}; {0,1,3,10,11}; {0,1,3,10,13}; {0,1,3,11,13}]`;;

(* Lean: combinedQueries8, combinedSignatures8, combinedExact8 (private) *)
let c983c08_combinedqueries = [1090; 1096; 1088; 1097; 1099; 1100];;
let c983c08_combinedsignatures =
  [(4096, 2, [0; 11], [1]);
   (4096, 2, [0; 13], [10; 11]);
   (4096, 2, [1; 10], [0]);
   (4096, 2, [1; 13], [10; 11]);
   (4096, 2, [0; 2; 13], []);
   (4096, 2, [1; 3; 13], [])];;
let () = c983c08_exact c983c08_combinedsignatures c983c08_combinedqueries;;

(* Lean: filtered8 (private) *)
let C983C08_FILTERED = mr_diameter_filter (mr_trim C983C08_CACHED_PRODUCT c983c08_combinedqueries);;

(* Lean: initial8 *)
let C983C08_INITIAL = dt_named (dc_cache C983C08_FILTERED 4096
  `[{0,10}; {0,10,13}; {1,11}; {1,11,13}; {0,1,10}; {0,1,11}; {0,1,10,11}; {0,1,10,13}; {0,1,11,13}; {0,2,10}; {1,3,11}; {0,1,2,10}; {0,1,3,11}]`);;
