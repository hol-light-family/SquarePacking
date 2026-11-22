(* ========================================================================= *)
(* Port of Compact/Bridge/FourSquareCaseHighRight.lean                       *)
(* (N12Compact.FourSquareCaseHighRight): original-packing bridge for the    *)
(* FourSquareHighRight template (FSHR_IMPOSSIBLE, FourSquareHighRight.ml).   *)
(*                                                                           *)
(* Lean  d : Data = <transform, masks, owned, leftBarrier>  is the OCaml     *)
(* tuple (trf, [m0; m1; m2; m3], [S0; S1; S2; S3], leftBarrier), trf =       *)
(* (swap, reflectX, reflectY), owned sets as int lists.  Lean statements     *)
(* quantify over all d with d.Check family; in HOL they are producers that   *)
(* re-check every condition of d.Check (owner_bridge.ml; a failure = the     *)
(* Lean decide would fail):                                                  *)
(*   fschr_impossible_of_owned fam d                                         *)
(*     |- !c1 c2 a b l. NPACK c1 c2 a b l /\                                *)
(*          IMAGE binarysum (FFP c1 c2 a b l) = fam /\                      *)
(*          ooaux c1 c2 a b l m0 = S0 /\ .. /\ ooaux c1 c2 a b l m3 = S3     *)
(*          ==> F                                                            *)
(*   fschr_impossible fam d                                                  *)
(*     |- (!c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> ooaux .. m0 = S0 /\ ..) *)
(*        ==> !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> F                 *)
(* (ooaux c1 c2 a b l m = natCombinedOwners p (ownerIndex p m)).  Tag FSCHR_. *)
(* ========================================================================= *)

needs "n12/geometry/owner_bridge.ml";;
needs "n12/geometry/FourSquareHighRight.ml";;

(* Lean: insidePoints *)
let FSCHR_INSIDE = [|[("2","113/50"); ("113/50","2"); ("47/20","47/20")];
                     [("33/20","47/20"); ("8/5","3"); ("87/50","3")];
                     [("457/500","2"); ("1","12/5")];
                     [("3","113/50"); ("3","72/25")]|];;

(* Lean: outsidePoints *)
let FSCHR_OUTSIDE = [|[("33/20","33/20"); ("47/20","33/20")];
                      [("1","1543/500"); ("2","1543/500")];
                      [("33/20","33/20")];
                      []|];;

(* Lean: Data.Check (each condition is checked while the proof is built:
   masks in family by in_fam, the distinct pairs by oo_apart, the point
   memberships by ob_inside / ob_outside / ob_barrier) *)

(* Lean: impossible_of_owned *)
let fschr_impossible_of_owned fam (trf, masks, owned, lb) =
  if List.length masks <> 4 || List.length owned <> 4 then failwith "fschr: data" else
  let ctx = ob_ctx fam trf (zip masks (map mk_numset owned)) in
  List.iter (fun m -> ignore (ob_inf ctx m)) (masks @ [lb]);
  let fs = ref [] in
  List.iteri (fun i m -> List.iter (ob_inside ctx fs m) FSCHR_INSIDE.(i)) masks;
  List.iteri (fun i m -> List.iter (ob_outside ctx fs m) FSCHR_OUTSIDE.(i)) masks;
  ob_barrier ctx fs (el 2 masks) lb ("19/25", "187/100");
  (* rTop, rHigh by S12.inside_segment *)
  ob_segment ctx fs (el 3 masks) ("3", "113/50") ("3", "72/25") "7/31";
  ob_segment ctx fs (el 3 masks) ("3", "113/50") ("3", "72/25") "12/31";
  ob_close ctx (ob_apply ctx fs FSHR_IMPOSSIBLE masks []);;

(* Lean: impossible *)
let fschr_impossible fam d = ob_forced (fschr_impossible_of_owned fam d);;

(* a check of the producers: case 1073 (Cases/FourSquareHighRight/Case1073.lean) *)
let FSCHR_CHECK_1073 = fschr_impossible
  (mk_numset [1; 12; 16; 192; 256; 512; 1024; 2048; 4096; 8192; 16416; 32768])
  ((true, false, false), [1024; 512; 8192; 16], [[5; 16]; [8; 18]; [6; 15]; [7; 17]], 1);;
