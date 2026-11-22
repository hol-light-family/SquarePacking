(* ========================================================================= *)
(* Phase 2: transformed single specs (Jatloe: TransformedOwnerBudget) and   *)
(* the corner-pair domains for masks 520 and 2112 (CornerPairDomain).        *)
(*                                                                           *)
(* A spec proved for marker set m under symmetry t yields a spec for the    *)
(* image marker set: every local query of the source is re-proved directly  *)
(* for the image (points mapped by t, auxiliary indices by the induced      *)
(* permutation), so nothing is transported but the query data.             *)
(* ========================================================================= *)

needs "n12/geometry/gen_bridge.ml";;

(* register (m, k, owned) |-> query with the given points *)
let add_query (m, k, owned, uin, uout) =
  if not (Hashtbl.mem LQ_TABLE (m, k, owned)) then
    Hashtbl.add LQ_TABLE (m, k, owned) (query_theorem (-1, m, k, owned, uin, uout));;

let perm_of l j = el j l;;

let transformed_spec newid srcid tmask kt trf perm =
  let (_, sm, ks, lo, hi, allowed) = find (fun (i,_,_,_,_,_) -> i = srcid) SINGLE_SPECS in
  let pa = map (fun s -> List.sort compare (map (perm_of perm) s)) allowed in
  let qs = filter (fun (_, m, k, _, _, _) -> m = sm && k = ks) LOCAL_QUERIES in
  let tq = map (fun (_, _, _, ow, uin, uout) ->
      let tp (x, y) = let (x1, y1) = tr_point trf (term_of_rat x, term_of_rat y) in
                      (rat_of_term x1, rat_of_term y1) in
      (tmask, kt, List.sort compare (map (perm_of perm) ow), map tp uin, map tp uout)) qs in
  List.iter add_query tq;
  EXTRA_SINGLE := (newid, tmask, kt, lo, hi, pa) :: !EXTRA_SINGLE;;

let broad_spec newid m k =
  EXTRA_SINGLE := (newid, m, k, 1, 1, map (fun j -> [j]) (0--9)) :: !EXTRA_SINGLE;;

let REFLECTXF = [8;9;6;7;4;5;2;3;0;1] and TURNFG = [4;7;1;9;3;6;0;8;2;5];;

let q2 (a, b) = (nlin_rat a, nlin_rat b);;

let () =
  (* mask 520: kind 0 from spec 24 under reflectX, kind 1 broad *)
  transformed_spec 1000 24 520 0 (false, true, false) REFLECTXF;
  broad_spec 1001 520 1;
  let hull = map q2 [("1543/500","1"); ("47/20","33/20"); ("3","87/50")] and tgt = [q2 ("3","8/5")] in
  List.iter (fun j -> add_query (520, 2, List.sort compare [8; j + 10], hull, tgt))
    (filter (fun j -> j <> 8) (0--9));
  EXTRA_COMBINED := (2000, 520, 1000, 1001,
      [8; 18] :: map (fun j -> [6; j + 10]) (0--9)) :: !EXTRA_COMBINED;
  (* mask 2112: kind 1 from spec 24 under swap+reflectY, kind 0 broad *)
  transformed_spec 1002 24 2112 1 (true, false, true) TURNFG;
  broad_spec 1003 2112 0;
  let hull = map q2 [("1","1543/500"); ("33/20","47/20"); ("87/50","3")] and tgt = [q2 ("8/5","3")] in
  List.iter (fun j -> add_query (2112, 2, List.sort compare [j; 14], hull, tgt))
    (filter (fun j -> j <> 3) (0--9));
  EXTRA_COMBINED := (2001, 2112, 1003, 1002,
      [3; 14] :: map (fun j -> [j; 11]) (0--9)) :: !EXTRA_COMBINED;;

(* the specs themselves *)
let () = List.iter (fun (i, m, k, lo, hi, al) ->
    if not (Hashtbl.mem SPEC_TBL i) then Hashtbl.replace SPEC_TBL i (spec_theorem m k lo hi al))
  !EXTRA_SINGLE;;
