(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components10.lean.           *)
(* Genuine full C983 auxiliary budget for original owner 10, mask 16384.     *)
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
let c983c10_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c10_exact";;

(* Lean: fQueries10 (private) *)
let c983c10_fqueries = [1294; 1295; 1297; 1300; 1304; 1309; 1315; 1322];;
(* Lean: fSignatures10 (private) *)
let c983c10_fsignatures =
  [(16384, 0, [0], []);
   (16384, 0, [1], []);
   (16384, 0, [2], []);
   (16384, 0, [3], []);
   (16384, 0, [4], []);
   (16384, 0, [5], []);
   (16384, 0, [6], [8]);
   (16384, 0, [7], [9])];;
(* Lean: fExact10 (private) *)
let () = c983c10_exact c983c10_fsignatures c983c10_fqueries;;
(* Lean: fSingle10 (private) *)
let c983c10_fsingle =
  {dmask = 16384; dlower = 1; dupper = 3; dallowed = [[8]; [9]; [6; 8]; [7; 9]; [8; 9]; [6; 8; 9]; [7; 8; 9]]; dqueries = c983c10_fqueries};;

(* Lean: gQueries10 (private) *)
let c983c10_gqueries = [1344; 1345; 1347; 1350; 1354; 1359; 1371; 1365; 1379; 1366; 1387; 1368];;
(* Lean: gSignatures10 (private) *)
let c983c10_gsignatures =
  [(16384, 1, [0], [6; 8]);
   (16384, 1, [1], [6; 9]);
   (16384, 1, [2], []);
   (16384, 1, [3], [6]);
   (16384, 1, [4], []);
   (16384, 1, [5], []);
   (16384, 1, [7], []);
   (16384, 1, [0; 6], []);
   (16384, 1, [0; 8], []);
   (16384, 1, [1; 6], []);
   (16384, 1, [1; 9], []);
   (16384, 1, [3; 6], [])];;
(* Lean: gExact10 (private) *)
let () = c983c10_exact c983c10_gsignatures c983c10_gqueries;;
(* Lean: gSingle10 (private) *)
let c983c10_gsingle =
  {dmask = 16384; dlower = 1; dupper = 2; dallowed = [[6]; [8]; [9]; [6; 8]; [6; 9]; [8; 9]]; dqueries = c983c10_gqueries};;

(* Lean: fChecked10, gChecked10, rawDomain10 (private): the two half domains *)
(* (kinds 0 and 1) and their product  |- cdom c983ri_family 16384 [..] *)
let C983C10_FCHECKED = mq_single `c983ri_family` 0 c983c10_fsingle;;
let C983C10_GCHECKED = mq_single `c983ri_family` 1 c983c10_gsingle;;
let C983C10_RAW_DOMAIN =
  if c983c10_fsingle.dmask <> c983c10_gsingle.dmask then failwith "c983c10: masks" else
  pk_product C983C10_FCHECKED C983C10_GCHECKED;;

(* Lean: cachedProduct10 (private) *)
let C983C10_CACHED_PRODUCT = dc_cache C983C10_RAW_DOMAIN 16384
  `[{8,16}; {8,18}; {8,19}; {8,16,18}; {8,16,19}; {8,18,19}; {9,16}; {9,18}; {9,19}; {9,16,18}; {9,16,19}; {9,18,19}; {6,8,16}; {6,8,18}; {6,8,19}; {6,8,16,18}; {6,8,16,19}; {6,8,18,19}; {7,9,16}; {7,9,18}; {7,9,19}; {7,9,16,18}; {7,9,16,19}; {7,9,18,19}; {8,9,16}; {8,9,18}; {8,9,19}; {8,9,16,18}; {8,9,16,19}; {8,9,18,19}; {6,8,9,16}; {6,8,9,18}; {6,8,9,19}; {6,8,9,16,18}; {6,8,9,16,19}; {6,8,9,18,19}; {7,8,9,16}; {7,8,9,18}; {7,8,9,19}; {7,8,9,16,18}; {7,8,9,16,19}; {7,8,9,18,19}]`;;

(* Lean: combinedQueries10, combinedSignatures10, combinedExact10 (private) *)
let c983c10_combinedqueries : int list = [1393; 1403; 1395; 1398; 1394; 1396];;
let c983c10_combinedsignatures : (int * int * int list * int list) list =
  [(16384, 2, [8; 16], [18; 19]);
   (16384, 2, [8; 19], [9]);
   (16384, 2, [9; 16], [18; 19]);
   (16384, 2, [9; 18], [8]);
   (16384, 2, [6; 8; 16], []);
   (16384, 2, [7; 9; 16], [])];;
let () = c983c10_exact c983c10_combinedsignatures c983c10_combinedqueries;;

(* Lean: filtered10 (private) *)
let C983C10_FILTERED = mr_diameter_filter (mr_trim C983C10_CACHED_PRODUCT c983c10_combinedqueries);;

(* Lean: initial10 *)
let C983C10_INITIAL = dt_named (dc_cache C983C10_FILTERED 16384
  `[{8,18}; {8,16,18}; {9,19}; {9,16,19}; {6,8,18}; {7,9,19}; {8,9,18}; {8,9,19}; {8,9,16,18}; {8,9,16,19}; {8,9,18,19}; {6,8,9,18}; {7,8,9,19}]`);;
