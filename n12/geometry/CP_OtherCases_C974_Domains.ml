(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C974/Domains.lean.                 *)
(* Authentic C974 domains with the actual F3/G3 census, as theorems    *)
(*   |- cdom c974d_family mask [allowed]   (Lean CertifiedDomain family).    *)
(* The private bounds lemma (budget 1..2 of every combined half) is checked  *)
(* inside ro_combined / ro_transformed; Lean cached_domain = cdom_cache /    *)
(* cdom_named.  reflectedCombined / reflected_* are the list computation     *)
(* inside ro_transformed.  The cut theorems quantify over the literal        *)
(* allowed lists (decide +kernel = OO_LIST_CUT_TAC).  Tag C974D_.            *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975FiniteCuts.ml";;

(* Lean: family *)
let c974d_family = new_definition
 `c974d_family = {1,2,12,48,192,256,512,1024,4096,8192,16384,32768}`;;
let C974D_F = `c974d_family`;;

(* Lean: count (private) *)
let C974D_COUNT = prove
 (`forall k. k < 2 ==> CARD (c974d_family INTER auxex k) = 3`,
  REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN GEN_TAC THEN
  DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[card_exempt C974D_F 0; card_exempt C974D_F 1]);;

let c974d_al th = rand (concl th);;

(* Lean: southwest *)
let C974D_SOUTHWEST = cdom_cache (ro_combined C974D_F 1) (c974d_al C997D_SOUTHWEST);;

(* Lean: leftSingleton *)
let C974D_LEFT_SINGLETON = cdom_named (ro_combined C974D_F 3) c975d_leftSingletonAllowed;;

(* Lean: bottom *)
let C974D_BOTTOM = cdom_cache (ro_combined C974D_F 19) (c974d_al C997D_BOTTOM);;

(* Lean: southwestCentral *)
let C974D_SOUTHWEST_CENTRAL = cdom_cache (ro_combined C974D_F 6) (c974d_al C997D_SOUTHWEST_CENTRAL);;

(* Lean: left *)
let C974D_LEFT = cdom_named (ro_combined C974D_F 17) c975d_leftAllowed;;

(* Lean: southeast *)
let C974D_SOUTHEAST = cdom_cache (ro_combined C974D_F 8) (c974d_al C997D_SOUTHEAST);;

(* Lean: right *)
let C974D_RIGHT = cdom_cache (ro_combined C974D_F 21) (c974d_al C997D_RIGHT);;

(* Lean: top *)
let C974D_TOP = cdom_cache (ro_combined C974D_F 24) (c974d_al C997D_TOP);;

(* Lean: northeast *)
let C974D_NORTHEAST =
  ro_transformed C974D_F 1024 (false, true, false) 13 RO_REFLECTXF RO_REFLECTXG
    (c974d_al C997D_NORTHEAST);;

let c974d_cut al body =
  let s = `s:num->bool` in
  prove (mk_forall(s, mk_imp(mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, s), al), body)),
         OO_LIST_CUT_TAC []);;

(* Lean: northeast_cut *)
let C974D_NORTHEAST_CUT = c974d_cut (c974d_al C997D_NORTHEAST)
  `~(9 IN s) ==> ~(19 IN s) ==> (5 IN s \/ 7 IN s) /\ (16 IN s \/ 17 IN s)`;;

(* Lean: top_cut *)
let C974D_TOP_CUT = c974d_cut (c974d_al C997D_TOP) `17 IN s \/ (3 IN s /\ 14 IN s)`;;
