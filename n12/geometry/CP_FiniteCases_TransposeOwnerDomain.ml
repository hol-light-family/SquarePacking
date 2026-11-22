(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/TransposeOwnerDomain.lean.        *)
(* A checked single spec under a symmetry, possibly between the F and G     *)
(* grids, as a half domain of the actual family.                            *)
(*                                                                           *)
(*   tod_transported fam mask n (sw, rx, ry) k l perm                        *)
(*     = Lean  transported family mask singleSpec_n _ t _ _ _ k l _ perm     *)
(*            perm_points budget                                             *)
(*     |- hdom fam mask l [pushOwners perm s | s in singleSpec_n.allowed]    *)
(* The Lean side conditions are checked: the spec kind is k, t maps the mask *)
(* to mask (targetMask), perm matches the points (perm_points, e.g.          *)
(* swapFG_points), and Bounds family mask w l (budget).                     *)
(* Lean cross_kind_exact (AuxExact of the pulled square) is not needed as a *)
(* HOL theorem: every local query of the source spec is re-proved by the    *)
(* kernel for the image square (mapped points and owner indices), as in     *)
(* cornerpair.ml.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/RelaxedOwnerDomain.ml";;

(* Lean: swapFG *)
let TOD_SWAPFG = [2;5;0;8;3;6;1;9;4;7];;

(* Lean: swapFG_points / any points premise: t maps AUXPTS k j to AUXPTS l (perm j) *)
let tod_check_points trf k l perm =
  List.iter (fun j -> if not (qeq (tr_q trf (aux_q k j)) (aux_q l (el j perm))) then
     failwith (Printf.sprintf "tod: permutation does not match point %d" j)) (0--9);;

(* Lean: transported *)
let tod_transported fam mask n trf k l perm =
  let (_, sm, ks, _, _, _) = pk_single_row n in
  if ks <> k then failwith "tod_transported: spec kind" else
  if mask_action trf sm <> mask then failwith "tod_transported: target mask" else
  tod_check_points trf k l perm;
  let id = ro_fresh_id () in
  transformed_spec id n mask l trf perm;
  pk_single fam id;;
