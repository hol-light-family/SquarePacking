(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components09.lean.           *)
(* Genuine full C983 auxiliary budget for original owner 9, mask 8192.       *)
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
let c983c09_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c09_exact";;

(* Lean: fQueries9 (private) *)
let c983c09_fqueries = [1145; 1146; 1150; 1157; 1167; 1175; 1184; 1153; 1156; 1162; 1172; 1174; 1170];;
(* Lean: fSignatures9 (private) *)
let c983c09_fsignatures =
  [(8192, 0, [0], []);
   (8192, 0, [1], []);
   (8192, 0, [3], [2; 4]);
   (8192, 0, [5], [4]);
   (8192, 0, [7], [4; 6]);
   (8192, 0, [8], []);
   (8192, 0, [9], []);
   (8192, 0, [2; 3], []);
   (8192, 0, [3; 4], []);
   (8192, 0, [4; 5], []);
   (8192, 0, [4; 7], []);
   (8192, 0, [6; 7], []);
   (8192, 0, [2; 7], [4])];;
(* Lean: fExact9 (private) *)
let () = c983c09_exact c983c09_fsignatures c983c09_fqueries;;
(* Lean: fSingle9 (private) *)
let c983c09_fsingle =
  {dmask = 8192; dlower = 1; dupper = 3; dallowed = [[2]; [4]; [6]; [2; 4]; [2; 6]; [4; 6]; [2; 4; 6]]; dqueries = c983c09_fqueries};;

(* Lean: gQueries9 (private) *)
let c983c09_gqueries = [1194; 1195; 1198; 1202; 1211; 1218; 1226; 1234];;
(* Lean: gSignatures9 (private) *)
let c983c09_gsignatures =
  [(8192, 1, [0], [2]);
   (8192, 1, [1], []);
   (8192, 1, [3], []);
   (8192, 1, [4], []);
   (8192, 1, [6], []);
   (8192, 1, [7], []);
   (8192, 1, [8], [5]);
   (8192, 1, [9], [])];;
(* Lean: gExact9 (private) *)
let () = c983c09_exact c983c09_gsignatures c983c09_gqueries;;
(* Lean: gSingle9 (private) *)
let c983c09_gsingle =
  {dmask = 8192; dlower = 1; dupper = 2; dallowed = [[2]; [5]; [0; 2]; [2; 5]; [5; 8]]; dqueries = c983c09_gqueries};;

(* Lean: fChecked9, gChecked9, rawDomain9 (private): the two half domains *)
(* (kinds 0 and 1) and their product  |- cdom c983ri_family 8192 [..] *)
let C983C09_FCHECKED = mq_single `c983ri_family` 0 c983c09_fsingle;;
let C983C09_GCHECKED = mq_single `c983ri_family` 1 c983c09_gsingle;;
let C983C09_RAW_DOMAIN =
  if c983c09_fsingle.dmask <> c983c09_gsingle.dmask then failwith "c983c09: masks" else
  pk_product C983C09_FCHECKED C983C09_GCHECKED;;

(* Lean: cachedProduct9 (private) *)
let C983C09_CACHED_PRODUCT = dc_cache C983C09_RAW_DOMAIN 8192
  `[{2,12}; {2,15}; {2,10,12}; {2,12,15}; {2,15,18}; {4,12}; {4,15}; {4,10,12}; {4,12,15}; {4,15,18}; {6,12}; {6,15}; {6,10,12}; {6,12,15}; {6,15,18}; {2,4,12}; {2,4,15}; {2,4,10,12}; {2,4,12,15}; {2,4,15,18}; {2,6,12}; {2,6,15}; {2,6,10,12}; {2,6,12,15}; {2,6,15,18}; {4,6,12}; {4,6,15}; {4,6,10,12}; {4,6,12,15}; {4,6,15,18}; {2,4,6,12}; {2,4,6,15}; {2,4,6,10,12}; {2,4,6,12,15}; {2,4,6,15,18}]`;;

(* Lean: combinedQueries9, combinedSignatures9, combinedExact9 (private) *)
let c983c09_combinedqueries : int list = [1253; 1244; 1254; 1245; 1248; 1259];;
let c983c09_combinedsignatures : (int * int * int list * int list) list =
  [(8192, 2, [2; 15], [12]);
   (8192, 2, [4; 12], [2; 6]);
   (8192, 2, [4; 15], [2; 6]);
   (8192, 2, [6; 12], [15]);
   (8192, 2, [4; 10; 12], []);
   (8192, 2, [4; 15; 18], [])];;
let () = c983c09_exact c983c09_combinedsignatures c983c09_combinedqueries;;

(* Lean: filtered9 (private) *)
let C983C09_FILTERED = mr_diameter_filter (mr_trim C983C09_CACHED_PRODUCT c983c09_combinedqueries);;

(* Lean: initial9 *)
let C983C09_INITIAL = dt_named (dc_cache C983C09_FILTERED 8192
  `[{2,12}; {2,10,12}; {2,12,15}; {6,15}; {6,12,15}; {6,15,18}; {2,4,12}; {2,4,12,15}; {2,6,12,15}; {4,6,15}; {4,6,12,15}; {2,4,6,12,15}]`);;
