(* ========================================================================= *)
(* Port of Compact/Bridge/MidpointCase.lean (N12Compact.MidpointCase):       *)
(* original-packing entry for the unit-span midpoint contradiction           *)
(* (MidpointRowTemplate.impossible = MPRT_IMPOSSIBLE, MidpointRowTemplate.ml). *)
(*                                                                           *)
(* Lean  d : Data = <transform, masks, owned, topX>  is the OCaml tuple      *)
(* (trf, [m0; m1; m2; m3], [S0; S1; S2; S3], topX), trf = (swap, reflectX,   *)
(* reflectY), owned sets as int lists, topX a rational string.              *)
(* impossible_actual quantifies over all d with d.Check family; in HOL it is *)
(* the producer                                                              *)
(*   mpc_impossible_actual fam d                                             *)
(*     |- !c1 c2 a b l. NPACK c1 c2 a b l /\                                *)
(*          IMAGE binarysum (FFP c1 c2 a b l) = fam /\                      *)
(*          ooaux c1 c2 a b l m0 = S0 /\ .. /\ ooaux c1 c2 a b l m3 = S3     *)
(*          ==> F                                                            *)
(* which re-checks every condition of d.Check (owner_bridge.ml; a failure =  *)
(* the Lean decide would fail).  Tag MPC_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/owner_bridge.ml";;
needs "n12/geometry/MidpointRowTemplate.ml";;

(* Lean: insidePoints *)
let mpc_inside_points topx =
  [|[("2","113/50"); ("113/50","2"); ("47/20","47/20")];
    [("33/20","47/20"); ("87/50","2"); (topx,"3")];
    [("457/500","2"); ("1","12/5")];
    [("1543/500","2"); ("3","12/5")]|];;

(* Lean: outsidePoints *)
let MPC_OUTSIDE = [|[("33/20","33/20"); ("47/20","33/20")];
                    [];
                    [("1","87/50")];
                    [("3","87/50")]|];;

(* Lean: Data.Check (checked while the proof is built: masks in family by
   in_fam, distinct pairs 01, 03, 12, 13 by oo_apart, point memberships by
   ob_inside / ob_outside) *)

(* Lean: impossible_actual *)
let mpc_impossible_actual fam (trf, masks, owned, topx) =
  if List.length masks <> 4 || List.length owned <> 4 then failwith "mpc: data" else
  let ctx = ob_ctx fam trf (zip masks (map mk_numset owned)) in
  List.iter (fun m -> ignore (ob_inf ctx m)) masks;
  let fs = ref [] in
  let ins = mpc_inside_points topx in
  List.iteri (fun i m -> List.iter (ob_inside ctx fs m) ins.(i)) masks;
  List.iteri (fun i m -> List.iter (ob_outside ctx fs m) MPC_OUTSIDE.(i)) masks;
  ob_close ctx (ob_apply ctx fs MPRT_IMPOSSIBLE masks [ob_rat topx]);;

(* a check of the producer: the span recipe spanNE {5,14,16} {3,13} {1,11} {9,19}
   (topX = 8/5) of Bridge/FourSquareVectorCover in the family of MergedLower case 71 *)
let MPC_CHECK_71 = mpc_impossible_actual
  (mk_numset [1; 2; 4; 8; 48; 192; 768; 1024; 2048; 4096; 16384; 32768])
  ((false, false, false), [1024; 2048; 4096; 16384], [[5; 14; 16]; [3; 13]; [1; 11]; [9; 19]], "8/5");;
