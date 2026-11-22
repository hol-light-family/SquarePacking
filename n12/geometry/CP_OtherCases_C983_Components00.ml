(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components00.lean.           *)
(* Genuine full C983 auxiliary budget for original owner 0, mask 1.          *)
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
let c983c00_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c00_exact";;

(* Lean: fQueries0 (private) *)
let c983c00_fqueries = [0; 1; 5; 9; 14; 20; 27; 35; 44; 3; 8; 12; 17; 23; 30; 38; 47];;
(* Lean: fSignatures0 (private) *)
let c983c00_fsignatures =
  [(1, 0, [0], [2]);
   (1, 0, [1], [0]);
   (1, 0, [3], [2]);
   (1, 0, [4], [2]);
   (1, 0, [5], [2]);
   (1, 0, [6], [2]);
   (1, 0, [7], [2]);
   (1, 0, [8], [2]);
   (1, 0, [9], [2]);
   (1, 0, [0; 2], []);
   (1, 0, [2; 3], []);
   (1, 0, [2; 4], []);
   (1, 0, [2; 5], []);
   (1, 0, [2; 6], []);
   (1, 0, [2; 7], []);
   (1, 0, [2; 8], []);
   (1, 0, [2; 9], [])];;
(* Lean: fExact0 (private) *)
let () = c983c00_exact c983c00_fsignatures c983c00_fqueries;;
(* Lean: fSingle0 (private) *)
let c983c00_fsingle =
  {dmask = 1; dlower = 1; dupper = 3; dallowed = [[2]]; dqueries = c983c00_fqueries};;

(* Lean: gQueries0 (private) *)
let c983c00_gqueries = [54; 55; 58; 62; 67; 73; 80; 88; 97; 70; 76; 91; 100];;
(* Lean: gSignatures0 (private) *)
let c983c00_gsignatures =
  [(1, 1, [0], [2]);
   (1, 1, [1], [0]);
   (1, 1, [3], []);
   (1, 1, [4], []);
   (1, 1, [5], [2]);
   (1, 1, [6], [2]);
   (1, 1, [7], []);
   (1, 1, [8], [2]);
   (1, 1, [9], [2]);
   (1, 1, [2; 5], []);
   (1, 1, [2; 6], []);
   (1, 1, [2; 8], []);
   (1, 1, [2; 9], [])];;
(* Lean: gExact0 (private) *)
let () = c983c00_exact c983c00_gsignatures c983c00_gqueries;;
(* Lean: gSingle0 (private) *)
let c983c00_gsingle =
  {dmask = 1; dlower = 1; dupper = 2; dallowed = [[2]; [0; 2]]; dqueries = c983c00_gqueries};;

(* Lean: fChecked0, gChecked0, rawDomain0 (private): the two half domains      *)
(* (kinds 0 and 1) and their product  |- cdom c983ri_family 1 [..]          *)
let C983C00_FCHECKED = mq_single `c983ri_family` 0 c983c00_fsingle;;
let C983C00_GCHECKED = mq_single `c983ri_family` 1 c983c00_gsingle;;
let C983C00_RAW_DOMAIN =
  if c983c00_fsingle.dmask <> c983c00_gsingle.dmask then failwith "c983c00: masks" else
  pk_product C983C00_FCHECKED C983C00_GCHECKED;;

(* Lean: cachedProduct0 (private) *)
let C983C00_CACHED_PRODUCT = dc_cache C983C00_RAW_DOMAIN 1
  `[{2,12}; {2,10,12}]`;;

(* Lean: combinedQueries0, combinedSignatures0, combinedExact0 (private) *)
let c983c00_combinedqueries : int list = [];;
let c983c00_combinedsignatures : (int * int * int list * int list) list =
  [];;
let () = c983c00_exact c983c00_combinedsignatures c983c00_combinedqueries;;

(* Lean: filtered0 (private) *)
let C983C00_FILTERED = mr_diameter_filter (mr_trim C983C00_CACHED_PRODUCT c983c00_combinedqueries);;

(* Lean: initial0 *)
let C983C00_INITIAL = dt_named (dc_cache C983C00_FILTERED 1
  `[{2,12}; {2,10,12}]`);;
