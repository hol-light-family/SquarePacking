(* ========================================================================= *)
(* Case 84 (Jatloe Bridge/C84Complete, C84Ownership, C84MergedBottomDomain): *)
(* forced auxiliary points (ForcedAuxiliary) over ten relaxed domains, then  *)
(* C84MergedPair.impossible for the merged bottom (8704) and left (2304)     *)
(* owners; the corner owner 4 holds (113/50,1) and (12/5,1).                 *)
(* Result: C84_CASE_THMS.                                                    *)
(* ========================================================================= *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/c84_bridge.ml";;
needs "n12/geometry/C84MergedPair.ml";;

type c84d = C84x of xdom | C84bottom | C84pair;;
let c84_dfun sq_of hnp hrow r sq d =
  match d with
    C84x xd -> xdfun None sq_of hnp hrow r sq xd
  | C84bottom -> product_domain sq None (small_budget_domain hnp hrow sq 0) (c84_bottom_domain hnp hrow r sq)
  | C84pair -> product_domain sq None (small_budget_domain hnp hrow sq 0) (half_domain hnp hrow r sq (Hsing 1));;

let C84_RX = (false, true, false);;
let C84_CASE = (84, [1; 2; 4; 8; 48; 192; 1024; 2304; 4096; 8704; 16384; 32768],
  [(1, C84x(Xrcomb 1)); (4, C84x(Xrtr(1, C84_RX))); (2, C84x(Xrcomb 3)); (8, C84x(Xrtr(3, C84_RX)));
   (32768, C84x(Xrcomb 24)); (4096, C84x(Xrcomb 17)); (16384, C84x(Xrcomb 21));
   (1024, C84x(Xrtr(13, C84_RX))); (8704, C84bottom); (2304, C84pair)]);;

let c84_case_thm c =
  let ctx = case_ctx c84_dfun [] c in
  let pts = [(8704, 16); (2304, 13); (4, 15); (4, 6)] in
  let facts = map (fun (m, j) -> (m, point_of_member (forced_point ctx m j))) pts in
  let grouped = map (fun m -> (m, map snd (filter (fun (m', _) -> m' = m) facts))) [8704; 2304; 4] in
  APPLY_EXTRA_FACTS := grouped;
  let f = try apply_tmpl ctx [] C84MP_IMPOSSIBLE (false, false, false) [8704; 2304]
          with e -> (APPLY_EXTRA_FACTS := []; raise e) in
  APPLY_EXTRA_FACTS := [];
  close_case ctx f;;

let C84_CASE_THMS = map check_case_thm
  (run_cases "C84" c84_case_thm (fun (cid,_,_) -> cid) [C84_CASE]);;
