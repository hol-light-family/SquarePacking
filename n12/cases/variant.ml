(* ========================================================================= *)
(* The 11 FourSquareVariant cases (Jatloe: Compact/Cases/FourSquareVariant,  *)
(* Bridge/FourSquareCaseVariant): the template FourSquareLowerBarrier with   *)
(* extra forced owners, discharged by the generic bridge.                    *)
(* Result: VARIANT_CASE_THMS : (int * thm) list  (row index, |- EXCLUDED_ROW) *)
(* ========================================================================= *)
needs "n12/geometry/gen_bridge.ml";;
needs "n12/geometry/cornerpair.ml";;
needs "n12/geometry/var_data.ml";;
needs "n12/geometry/FourSquareLowerBarrier.ml";;

let case_timer f c cid =
  let t1 = Sys.time() in
  let r = try Some (f c) with Failure m -> (Printf.printf "case %d FAIL: %s\n%!" cid m; None)
                            | e -> (Printf.printf "case %d EXN: %s\n%!" cid (Printexc.to_string e); None) in
  Printf.printf "case %d %s %.0fs\n%!" cid (if r = None then "failed" else "done") (Sys.time() -. t1);
  r;;

let var_case_thm (cid, fam, doms, trf, masks, owned, lb, rb) =
  let (mk, me) = chop_list 4 masks and (ok, oe) = chop_list 4 owned in
  gen_case_thm_x (zip me oe) FSLB_IMPOSSIBLE (cid, fam, doms, trf, mk, ok);;

let VARIANT_CASE_THMS =
  mapfilter (fun c -> let (cid,_,_,_,_,_,_,_) = c in
                      match case_timer var_case_thm c cid with Some x -> x | None -> failwith "")
    VAR_FourSquareVariant;;
Printf.printf "VARIANT: %d of %d cases proved\n%!" (length VARIANT_CASE_THMS) (length VAR_FourSquareVariant);;
