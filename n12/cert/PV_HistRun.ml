(* ========================================================================= *)
(* W-F6: proves CK_INITIAL for all 64 (case, owner) entries of the six       *)
(* historical cases (6,144 roots), design §4.3:                              *)
(*   pv_initial_thm (case, owner), e.g. pv_initial_thm ("713", 7)           *)
(*   CK_INITIAL : ((string * int) * thm) list                                *)
(* pv_hist_domains (default 8) OCaml domains evaluate the roots (one pool    *)
(* over all roots, longest first), then each owner is assembled.             *)
(* ========================================================================= *)

needs "n12/cert/PV_Eval.ml";;


let pv_t0 = Unix.gettimeofday ();;
let CK_INITIAL =
  let todo = List.filter (fun key -> not (Hashtbl.mem pv_initial_tbl key)) !pv_owner_list in
  ignore (pv_all_owners !pv_hist_domains todo);
  List.map (fun key -> (key, Hashtbl.find pv_initial_tbl key)) !pv_owner_list;;
let pv_initial_thm key = Hashtbl.find pv_initial_tbl key;;
let () =
  List.iter (fun ((c, k), th) ->
      if hyp th <> [] then failwith (Printf.sprintf "CK_INITIAL %s %d has hypotheses" c k)) CK_INITIAL;
  Printf.printf "ALL INITIAL COVERS: %d theorems (%d roots), %.1fs\n%!" (List.length CK_INITIAL)
    (Hashtbl.fold (fun _ l n -> n + List.length l) pv_roots 0) (Unix.gettimeofday () -. pv_t0);;
