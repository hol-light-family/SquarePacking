(* ========================================================================= *)
(* Port of Compact/Bridge/EndpointHighRightCase.lean                         *)
(* (N12Compact.EndpointHighRightCase): original-packing entry for the       *)
(* EndpointHighRight template (EHR_IMPOSSIBLE, EndpointHighRight.ml).        *)
(*                                                                           *)
(* Lean  d : Data = <transform, masks, owned>  is the OCaml tuple            *)
(* (trf, [m0; m1; m2; m3], [S0; S1; S2; S3]), trf = (swap, reflectX,         *)
(* reflectY), owned sets as int lists.  impossible_actual quantifies over    *)
(* all d with d.Check family; in HOL it is the producer                      *)
(*   ehrc_impossible_actual fam d                                            *)
(*     |- !c1 c2 a b l. NPACK c1 c2 a b l /\                                *)
(*          IMAGE binarysum (FFP c1 c2 a b l) = fam /\                      *)
(*          ooaux c1 c2 a b l m0 = S0 /\ .. /\ ooaux c1 c2 a b l m3 = S3     *)
(*          ==> F                                                            *)
(* which re-checks every condition of d.Check (owner_bridge.ml; a failure =  *)
(* the Lean decide would fail).  Tag EHRC_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/owner_bridge.ml";;
needs "n12/geometry/EndpointHighRight.ml";;

(* Lean: insidePoints *)
let EHRC_INSIDE = [|[("2","113/50"); ("113/50","2"); ("47/20","47/20")];
                    [("33/20","47/20"); ("87/50","2"); ("8/5","3")];
                    [("1","12/5")];
                    [("3","113/50"); ("3","72/25")]|];;

(* Lean: outsidePoints (of owner 0) *)
let EHRC_OUTSIDE = [("33/20","33/20"); ("47/20","33/20")];;

(* Lean: Data.Check (checked while the proof is built: masks in family by
   in_fam, distinct pairs 01, 03, 12 by oo_apart, point memberships by
   ob_inside / ob_outside) *)

(* Lean: impossible_actual *)
let ehrc_impossible_actual fam (trf, masks, owned) =
  if List.length masks <> 4 || List.length owned <> 4 then failwith "ehrc: data" else
  let ctx = ob_ctx fam trf (zip masks (map mk_numset owned)) in
  List.iter (fun m -> ignore (ob_inf ctx m)) masks;
  let fs = ref [] in
  List.iteri (fun i m -> List.iter (ob_inside ctx fs m) EHRC_INSIDE.(i)) masks;
  List.iter (ob_outside ctx fs (el 0 masks)) EHRC_OUTSIDE;
  (* rTop, rHigh by S12.inside_segment *)
  ob_segment ctx fs (el 3 masks) ("3", "113/50") ("3", "72/25") "7/31";
  ob_segment ctx fs (el 3 masks) ("3", "113/50") ("3", "72/25") "12/31";
  ob_close ctx (ob_apply ctx fs EHR_IMPOSSIBLE masks []);;

(* a check of the producer: the endpoint patterns of Cases/Endpoint684.lean
   (roles 256, 512, 16384, 2 under the half-turn); the first pattern accepted *)
let EHRC_CHECK_684 = tryfind (fun ow -> ehrc_impossible_actual
    (mk_numset [1; 2; 12; 16; 32; 192; 256; 512; 3072; 4096; 16384; 32768])
    ((false, true, true), [256; 512; 16384; 2], ow))
  [[[4;13];[6;15];[8;18];[0;10]];
   [[4;13];[6;16];[8;18];[0;10]];
   [[4;13];[6;15;16];[8;18];[0;10]];
   [[4;13;15];[6;16];[8;18];[0;10]];
   [[4;13;16];[6;15];[8;18];[0;10]];
   [[4;13];[6;15];[8;16;18];[0;10]]];;
