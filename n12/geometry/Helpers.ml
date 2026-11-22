(* ========================================================================= *)
(* Phase 2: Compact/Cases/MergedLower/Helpers.lean (merged-lower domain     *)
(* helpers).  Lean defs producing CertifiedDomain are OCaml producers:      *)
(*   mlh_direct fam n          restrictFCardOne (ofCombined combinedSpec n)  *)
(*   mlh_reflected fam mask n  restrictFCardOne (ofTransformedCombined       *)
(*                             reflectX ... (reflectedAllowed w))            *)
(*   mlh_halfturned fam mask n the same under the half turn                  *)
(*   mlh_reflected_allowed n / mlh_halfturned_allowed n : the Lean lists     *)
(*   reflectedAllowed w / halfturnedAllowed w (as HOL list terms).           *)
(* reflectedAllowed_mem / halfturnedAllowed_mem are the membership checks   *)
(* done inside the producers (cdom_cache).                                   *)
(* ========================================================================= *)

needs "n12/geometry/RelaxedOwnerDomain.ml";;

(* Lean: direct *)
let mlh_direct fam n = ro_restrict_f1 (ro_combined fam n);;

let mlh_moved_allowed permF permG n =
  let (_, _, f, g, allowed) = pk_comb_row n in
  let (_,_,_,_,_,af) = pk_single_row f and (_,_,_,_,_,ag) = pk_single_row g in
  let comb x y = List.sort compare (x @ map (fun j -> j + 10) y) in
  let pairs = List.concat (map (fun x -> map (fun y -> (x, y)) ag) af) in
  let kept = filter (fun (x, y) -> mem (comb x y) (map (List.sort compare) allowed)) pairs in
  mk_list (map (fun (x, y) -> mk_numset (comb (map (fun j -> el j permF) x) (map (fun j -> el j permG) y))) kept,
           `:num->bool`);;

(* Lean: reflectedAllowed, halfturnedAllowed *)
let mlh_reflected_allowed n = mlh_moved_allowed RO_REFLECTXF RO_REFLECTXG n;;
let mlh_halfturned_allowed n = mlh_moved_allowed RO_HALFTURN RO_HALFTURN n;;

(* Lean: reflected *)
let mlh_reflected fam mask n =
  ro_restrict_f1 (ro_transformed fam mask (false, true, false) n RO_REFLECTXF RO_REFLECTXG
                    (mlh_reflected_allowed n));;

(* Lean: halfturned *)
let mlh_halfturned fam mask n =
  ro_restrict_f1 (ro_transformed fam mask (false, true, true) n RO_HALFTURN RO_HALFTURN
                    (mlh_halfturned_allowed n));;
