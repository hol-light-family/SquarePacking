(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975Domains.lean.                 *)
(* Authentic C975 owner domains with the true F3/G3 census, as theorems      *)
(*   |- cdom c975d_family mask [allowed]   (Lean CertifiedDomain family)     *)
(*   |- hdom c975d_family 34816 1 c975d_topGAllowed   (Lean topG)            *)
(* The private bounds lemma (budget 1..2 of every combined half) is checked  *)
(* inside ro_combined / ro_transformed; Lean cached_domain = cdom_cache /    *)
(* cdom_named.  The C997Domains allowed lists are taken from the C997D_*     *)
(* theorems.  rawTopG reuses the C715 typed domain mergedF (its 45 queries   *)
(* re-proved by the kernel for mask 34816, kind 1, under quarterFG) through  *)
(* dht_transported (DirectHalfTransport).                                    *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C997Domains.ml";;
needs "n12/geometry/CP_FiniteCases_DirectHalfTransport.ml";;
needs "n12/geometry/CP_OtherCases_C715_MergedQueries.ml";;

(* Lean: family *)
let c975d_family = new_definition
 `c975d_family = {1,2,12,48,192,256,512,1024,4096,8192,16384,34816}`;;
let C975D_F = `c975d_family`;;

(* Lean: count (private) *)
let C975D_COUNT = prove
 (`forall k. k < 2 ==> CARD (c975d_family INTER auxex k) = 3`,
  REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN GEN_TAC THEN
  DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[card_exempt C975D_F 0; card_exempt C975D_F 1]);;

let c975d_al th = rand (concl th);;

(* Lean: southwest *)
let C975D_SOUTHWEST = cdom_cache (ro_combined C975D_F 1) (c975d_al C997D_SOUTHWEST);;

(* Lean: leftSingletonAllowed *)
let c975d_leftSingletonAllowed = new_definition
 `c975d_leftSingletonAllowed = [{0,10}; {0,2,10}]`;;

(* Lean: leftSingleton *)
let C975D_LEFT_SINGLETON = cdom_named (ro_combined C975D_F 3) c975d_leftSingletonAllowed;;

(* Lean: bottom *)
let C975D_BOTTOM = cdom_cache (ro_combined C975D_F 19) (c975d_al C997D_BOTTOM);;

(* Lean: southwestCentral *)
let C975D_SOUTHWEST_CENTRAL = cdom_cache (ro_combined C975D_F 6) (c975d_al C997D_SOUTHWEST_CENTRAL);;

(* Lean: leftAllowed *)
let c975d_leftAllowed = new_definition
 `c975d_leftAllowed = [{0,10}; {0,10,13}; {1,11}; {1,11,13}; {0,1,10}; {0,1,11};
    {0,1,10,11}; {0,1,10,13}; {0,1,11,13}; {0,2,10}; {1,3,11}]`;;

(* Lean: left *)
let C975D_LEFT = cdom_named (ro_combined C975D_F 17) c975d_leftAllowed;;

(* Lean: southeast *)
let C975D_SOUTHEAST = cdom_cache (ro_combined C975D_F 8) (c975d_al C997D_SOUTHEAST);;

(* Lean: right *)
let C975D_RIGHT = cdom_cache (ro_combined C975D_F 21) (c975d_al C997D_RIGHT);;

(* Lean: northeast (reflectedCombined / reflected_combined / reflected_checked / first_range /
   reflected_included are the list computation inside ro_transformed) *)
let C975D_NORTHEAST =
  ro_transformed C975D_F 1024 (false, true, false) 13 RO_REFLECTXF RO_REFLECTXG
    (c975d_al C997D_NORTHEAST);;

(* Lean: C715.mergedF as a DirectSingleDomain with its query certificates *)
let c975d_mergedF = { dht_mask = c715mq_mergedF.dmask; dht_lower = c715mq_mergedF.dlower;
  dht_upper = c715mq_mergedF.dupper; dht_allowed = c715mq_mergedF.dallowed;
  dht_queries = c715mq_mergedF_hints };;

(* Lean: rawTopG (private) *)
let C975D_RAW_TOPG =
  dht_transported C975D_F 34816 c975d_mergedF `c715ri_family` 0 1 (true, true, false) DHT_QUARTERFG;;

(* Lean: topGAllowed *)
let c975d_topGAllowed = new_definition
 `c975d_topGAllowed = [{3}; {1}; {4}; {3,6}; {4,6}; {1,3}; {3,7}; {3,4}; {1,4}; {4,7}]`;;

(* Lean: topG_checked (private): rawTopG.allowed = topGAllowed (as lists of sets) *)
let () =
  let raw = map numset_of (dest_list (c975d_al C975D_RAW_TOPG))
  and tg = map numset_of (dest_list (rhs (concl c975d_topGAllowed))) in
  if raw <> tg then failwith "C975D: topG_checked fails";;

(* Lean: topG *)
let C975D_TOPG = hdom_named C975D_RAW_TOPG c975d_topGAllowed;;
