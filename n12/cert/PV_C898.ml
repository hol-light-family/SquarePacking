(* ========================================================================= *)
(* W-F6 for C898: CK_INITIAL for the 11 C898 owners (704 roots, Lean         *)
(* Cases/C898/RecipeInitial, C898Entry.ownerK_cover's geometric part):       *)
(*   |- !c s u v a. ... ==> oriented_pose_covered (MAP cr_leaf c898_dK_0) .. *)
(* Data: n12/data/cert/pv898_{owners,roots}.txt (n12/scripts/pv_extract.py --c898,   *)
(* n12/scripts/pv_oracle.py --c898), C898 dictionary terms of C8_Data.ml (W-C898). *)
(*   pv898_initial_thm k ; CK898_INITIAL : (int * thm) list                  *)
(* ========================================================================= *)

needs "n12/cert/C8_Data.ml";;
needs "n12/cert/PV_Eval.ml";;

let pv898_owner_list = pv_load_owners "n12/data/cert/pv898_owners.txt";;
let () = pv_load_roots "n12/data/cert/pv898_roots.txt" c8p_tm;;
let () = Hashtbl.replace pv_dom_defs "898" (fun k -> c8dom_def (string_of_int k ^ "_0"));;

let pv898_t0 = Unix.gettimeofday ();;
let CK898_INITIAL =
  let todo = List.filter (fun key -> not (Hashtbl.mem pv_initial_tbl key)) pv898_owner_list in
  ignore (pv_all_owners !pv_hist_domains todo);
  List.map (fun (c, k) -> (k, Hashtbl.find pv_initial_tbl (c, k))) pv898_owner_list;;
let pv898_initial_thm k = Hashtbl.find pv_initial_tbl ("898", k);;
let () =
  List.iter (fun (k, th) ->
      if hyp th <> [] then failwith (Printf.sprintf "CK898_INITIAL %d has hypotheses" k)) CK898_INITIAL;
  Printf.printf "C898 INITIAL COVERS: %d theorems, %.1fs\n%!" (List.length CK898_INITIAL)
    (Unix.gettimeofday () -. pv898_t0);;
