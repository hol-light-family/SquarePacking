(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components01.lean.           *)
(* Genuine full C983 auxiliary budget for original owner 1, mask 2.          *)
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
let c983c01_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c01_exact";;

(* Lean: fQueries1 (private) *)
let c983c01_fqueries = [107; 109; 111; 115; 120; 126; 133; 141; 150; 116; 121; 127; 134; 142; 151];;
(* Lean: fSignatures1 (private) *)
let c983c01_fsignatures =
  [(2, 0, [1], []);
   (2, 0, [2], [0]);
   (2, 0, [3], []);
   (2, 0, [4], [0]);
   (2, 0, [5], [0]);
   (2, 0, [6], [0]);
   (2, 0, [7], [0]);
   (2, 0, [8], [0]);
   (2, 0, [9], [0]);
   (2, 0, [0; 4], []);
   (2, 0, [0; 5], []);
   (2, 0, [0; 6], [2]);
   (2, 0, [0; 7], []);
   (2, 0, [0; 8], []);
   (2, 0, [0; 9], [])];;
(* Lean: fExact1 (private) *)
let () = c983c01_exact c983c01_fsignatures c983c01_fqueries;;
(* Lean: fSingle1 (private) *)
let c983c01_fsingle =
  {dmask = 2; dlower = 1; dupper = 3; dallowed = [[0]; [0; 2]; [0; 2; 6]]; dqueries = c983c01_fqueries};;

(* Lean: gQueries1 (private) *)
let c983c01_gqueries = [160; 162; 165; 169; 174; 180; 187; 195; 204; 163; 166; 175; 181; 188; 196; 205];;
(* Lean: gSignatures1 (private) *)
let c983c01_gsignatures =
  [(2, 1, [1], []);
   (2, 1, [2], [0]);
   (2, 1, [3], [0]);
   (2, 1, [4], []);
   (2, 1, [5], [0]);
   (2, 1, [6], [0]);
   (2, 1, [7], [0]);
   (2, 1, [8], [0]);
   (2, 1, [9], [0]);
   (2, 1, [0; 2], []);
   (2, 1, [0; 3], []);
   (2, 1, [0; 5], [2]);
   (2, 1, [0; 6], []);
   (2, 1, [0; 7], []);
   (2, 1, [0; 8], []);
   (2, 1, [0; 9], [])];;
(* Lean: gExact1 (private) *)
let () = c983c01_exact c983c01_gsignatures c983c01_gqueries;;
(* Lean: gSingle1 (private) *)
let c983c01_gsingle =
  {dmask = 2; dlower = 1; dupper = 2; dallowed = [[0]]; dqueries = c983c01_gqueries};;

(* Lean: fChecked1, gChecked1, rawDomain1 (private): the two half domains      *)
(* (kinds 0 and 1) and their product  |- cdom c983ri_family 2 [..]          *)
let C983C01_FCHECKED = mq_single `c983ri_family` 0 c983c01_fsingle;;
let C983C01_GCHECKED = mq_single `c983ri_family` 1 c983c01_gsingle;;
let C983C01_RAW_DOMAIN =
  if c983c01_fsingle.dmask <> c983c01_gsingle.dmask then failwith "c983c01: masks" else
  pk_product C983C01_FCHECKED C983C01_GCHECKED;;

(* Lean: cachedProduct1 (private) *)
let C983C01_CACHED_PRODUCT = dc_cache C983C01_RAW_DOMAIN 2
  `[{0,10}; {0,2,10}; {0,2,6,10}]`;;

(* Lean: combinedQueries1, combinedSignatures1, combinedExact1 (private) *)
let c983c01_combinedqueries : int list = [];;
let c983c01_combinedsignatures : (int * int * int list * int list) list = [];;
let () = c983c01_exact c983c01_combinedsignatures c983c01_combinedqueries;;

(* Lean: filtered1 (private) *)
let C983C01_FILTERED = mr_diameter_filter (mr_trim C983C01_CACHED_PRODUCT c983c01_combinedqueries);;

(* Lean: initial1 *)
let C983C01_INITIAL = dt_named (dc_cache C983C01_FILTERED 2
  `[{0,10}; {0,2,10}]`);;
