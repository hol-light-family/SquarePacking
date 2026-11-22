(* ========================================================================= *)
(* Phase 2: Compact/Completion/CommonCases/C888C889Domains.lean.             *)
(* Authentic C888/C889 domains (b = false: C888 with right mask 16384,       *)
(* b = true: C889 with 16416), cached after the real F3/G2 budget.           *)
(* Domains are theorems  |- cdom (c888d_family_b) mask [list]; the private  *)
(* direct / halfturned* helpers are the producers oo_restrict23,             *)
(* ro_combined and ro_transformed (half turn, RO_HALFTURN).                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: rightMask, family *)
let c888d_family_f = new_definition
 `c888d_family_f = {1,2,12,16,192,512,1024,2304,4096,8192,16384,32768}`;;
let c888d_family_t = new_definition
 `c888d_family_t = {1,2,12,16,192,512,1024,2304,4096,8192,16416,32768}`;;
let C888D_FAMS = [(false, `c888d_family_f`); (true, `c888d_family_t`)];;

(* Lean: budget_counts (private) *)
let C888D_BUDGET_COUNTS = map (fun (_, f) -> CONJ (card_exempt f 0) (card_exempt f 1)) C888D_FAMS;;

let c888d_direct fam n = oo_restrict23 (ro_combined fam n);;

(* Lean: southwestAllowed, singletonAllowed, bottomAllowed, southAllowed, rightAllowed,
   northFullAllowed, northAllowed *)
let c888d_southwest_allowed = new_definition `c888d_southwest_allowed = [{2,12}]`;;
let c888d_singleton_allowed = new_definition `c888d_singleton_allowed = [{7,17}]`;;
let c888d_bottom_allowed = new_definition `c888d_bottom_allowed = [{2,12}; {6,15}; {2,4,12}; {4,6,15}]`;;
let c888d_south_allowed = new_definition `c888d_south_allowed = [{4,15}; {4,16}; {4,18}; {6,15}; {6,16}; {6,18}; {8,15}; {8,16}; {8,18}; {4,5,16}; {4,6,15}; {4,6,16}; {4,6,18}; {4,8,15}; {4,8,16}; {4,8,18}; {4,9,16}; {5,8,16}; {6,8,15}; {6,8,16}; {6,8,18}; {8,9,16}]`;;
let c888d_right_allowed = new_definition `c888d_right_allowed = [{8,18}; {9,19}; {6,8,18}; {7,9,19}; {8,9,18}; {8,9,19}]`;;
let c888d_north_full_allowed = new_definition `c888d_north_full_allowed = [{9,19}; {9,17}; {9,16}; {9,19,17}; {9,19,16}; {9,17,16}; {7,19}; {7,17}; {7,16}; {7,19,17}; {7,19,16}; {7,17,16}; {5,19}; {5,17}; {5,16}; {5,19,17}; {5,19,16}; {5,17,16}; {5,17,14}; {5,17,13}; {5,16,14}; {5,16,13}; {9,8,16}; {9,8,19,16}; {9,8,18,16}; {9,8,17,16}; {9,7,19}; {9,7,17}; {9,7,16}; {9,7,19,17}; {9,7,19,16}; {9,7,17,16}; {9,5,19}; {9,5,17}; {9,5,16}; {9,5,19,17}; {9,5,19,16}; {9,5,17,16}; {9,5,17,14}; {9,5,17,13}; {9,5,16,14}; {9,5,16,13}; {9,4,16}; {9,4,19,16}; {9,4,17,16}; {8,5,16}; {8,5,17,16}; {8,5,16,14}; {8,5,16,13}; {7,5,19}; {7,5,17}; {7,5,16}; {7,5,19,17}; {7,5,19,16}; {7,5,17,16}; {7,5,17,14}; {7,5,17,13}; {7,5,16,13}; {5,4,16}; {5,4,19,16}; {5,4,17,16}; {5,4,16,14}; {5,4,16,13}; {5,3,17,14}]`;;
let c888d_north_allowed = new_definition `c888d_north_allowed = [{9,19}; {9,17}; {9,16}; {7,19}; {7,17}; {7,16}; {5,19}; {5,17}; {5,16}; {9,8,16}; {9,7,19}; {9,7,17}; {9,7,16}; {9,5,19}; {9,5,17}; {9,5,16}; {9,4,16}; {8,5,16}; {7,5,19}; {7,5,17}; {7,5,16}; {5,4,16}]`;;

(* Lean: southwestDomain b, singletonDomain b, bottomDomain b, southDomain b *)
let C888D_SOUTHWEST_DOMAIN = map (fun (b, f) -> (b, cdom_named (c888d_direct f 1) c888d_southwest_allowed)) C888D_FAMS;;
let C888D_SINGLETON_DOMAIN = map (fun (b, f) -> (b, cdom_named (c888d_direct f 4) c888d_singleton_allowed)) C888D_FAMS;;
let C888D_BOTTOM_DOMAIN = map (fun (b, f) -> (b, cdom_named (c888d_direct f 19) c888d_bottom_allowed)) C888D_FAMS;;
let C888D_SOUTH_DOMAIN = map (fun (b, f) -> (b, cdom_named (c888d_direct f 8) c888d_south_allowed)) C888D_FAMS;;

(* Lean: rightDomain (family false only) *)
let C888D_RIGHT_DOMAIN = cdom_named (c888d_direct `c888d_family_f` 21) c888d_right_allowed;;

(* Lean: northDomain b (halfturned_checked / halfturned_included are the list
   computation inside ro_transformed) *)
let C888D_NORTH_DOMAIN = map (fun (b, f) ->
    (b, cdom_named (oo_restrict23 (ro_transformed f 1024 (false, true, true) 6 RO_HALFTURN RO_HALFTURN
                                     (rhs (concl c888d_north_full_allowed)))) c888d_north_allowed)) C888D_FAMS;;
