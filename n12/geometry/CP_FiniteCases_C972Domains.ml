(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C972Domains.lean.                 *)
(* Authentic C972 owner domains with the actual F3/G3 census, as theorems    *)
(*   |- cdom c972d_family mask [allowed]   (Lean CertifiedDomain family).    *)
(* The private bounds lemma (budget 1..2 of every combined half) is checked  *)
(* inside ro_combined / ro_transformed; Lean cached_domain = cdom_cache /    *)
(* cdom_named.  reflectedCombined / reflected_* are the list computation     *)
(* inside ro_transformed.  The cut theorems quantify over the literal        *)
(* allowed lists (decide +kernel = OO_LIST_CUT_TAC).  Tag C972D_.            *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975FiniteCuts.ml";;

(* Lean: family *)
let c972d_family = new_definition
 `c972d_family = {1,2,12,48,192,256,512,1024,2048,4096,8192,16384}`;;
let C972D_F = `c972d_family`;;

(* Lean: count (private) *)
let C972D_COUNT = prove
 (`forall k. k < 2 ==> CARD (c972d_family INTER auxex k) = 3`,
  REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN GEN_TAC THEN
  DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[card_exempt C972D_F 0; card_exempt C972D_F 1]);;

let c972d_al th = rand (concl th);;

(* Lean: southwest *)
let C972D_SOUTHWEST = cdom_cache (ro_combined C972D_F 1) (c972d_al C997D_SOUTHWEST);;

(* Lean: leftSingleton *)
let C972D_LEFT_SINGLETON = cdom_named (ro_combined C972D_F 3) c975d_leftSingletonAllowed;;

(* Lean: bottom *)
let C972D_BOTTOM = cdom_cache (ro_combined C972D_F 19) (c972d_al C997D_BOTTOM);;

(* Lean: southwestCentral *)
let C972D_SOUTHWEST_CENTRAL = cdom_cache (ro_combined C972D_F 6) (c972d_al C997D_SOUTHWEST_CENTRAL);;

(* Lean: left *)
let C972D_LEFT = cdom_named (ro_combined C972D_F 17) c975d_leftAllowed;;

(* Lean: southeast *)
let C972D_SOUTHEAST = cdom_cache (ro_combined C972D_F 8) (c972d_al C997D_SOUTHEAST);;

(* Lean: right *)
let C972D_RIGHT = cdom_cache (ro_combined C972D_F 21) (c972d_al C997D_RIGHT);;

(* Lean: northwest *)
let C972D_NORTHWEST = ro_combined C972D_F 13;;

(* Lean: northeast *)
let C972D_NORTHEAST =
  ro_transformed C972D_F 1024 (false, true, false) 13 RO_REFLECTXF RO_REFLECTXG
    (c972d_al C997D_NORTHEAST);;

let c972d_cut al body =
  let s = `s:num->bool` in
  prove (mk_forall(s, mk_imp(mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, s), al), body)),
         OO_LIST_CUT_TAC []);;

(* Lean: northeast_cut *)
let C972D_NORTHEAST_CUT = c972d_cut (c972d_al C997D_NORTHEAST)
  `~(9 IN s) ==> ~(19 IN s) ==> (5 IN s \/ 7 IN s) /\ (16 IN s \/ 17 IN s)`;;

(* Lean: northwest_cut (over combinedSpec13.allowed = the allowed list of northwest) *)
let C972D_NORTHWEST_CUT = c972d_cut (c972d_al C972D_NORTHWEST)
  `~(0 IN s) ==> ~(1 IN s) ==> ~(4 IN s) ==> ~(7 IN s) ==> ~(10 IN s) ==> ~(11 IN s) ==>
   ~(13 IN s) ==> ~(17 IN s) ==> (3 IN s \/ 5 IN s) /\ 14 IN s`;;
