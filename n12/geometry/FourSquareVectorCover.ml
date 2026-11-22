(* ========================================================================= *)
(* Port of Compact/Bridge/FourSquareVectorCover.lean                         *)
(* (N12Compact.FourSquareVectorCover): whole ownership domains closed by a   *)
(* choice of two symbolic arguments (FourSquareCase / MidpointCase).         *)
(*                                                                           *)
(* Lean  Recipe := Sum FourSquareCase.Data MidpointCase.Data  is the OCaml   *)
(* type fsvc_recipe (Vcfour = .inl, Vcmid = .inr); FourSquareCase.Data =     *)
(* (trf, masks, owned, leftBarrier, rightBarrier), MidpointCase.Data as in   *)
(* MidpointCase.ml.  Lean  ds : List (CertifiedDomain family)  is a list of  *)
(* theorems |- cdom fam m al (members / distinct are checked by in_fam and   *)
(* on the masks).  The Lean statements quantify over decidable checks; in    *)
(* HOL they are producers that re-check them (a failure = the Lean decide    *)
(* would fail):                                                              *)
(*   fsvc_geometry fam r       Recipe.GeometryCheck, as the theorem          *)
(*     |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam /\                        *)
(*          ooaux .. (masks 0) = owned 0 /\ .. /\ ooaux .. (masks 3) = owned 3 *)
(*          ==> F                                                            *)
(*   fsvc_impossible fam ds recipes                                          *)
(*     |- !c1 c2 a b l. NPACK c1 c2 a b l /\                                *)
(*          IMAGE binarysum (FFP c1 c2 a b l) = fam ==> F                   *)
(* (Check ds recipes, check_of_parts and impossible: every assignment of the *)
(* domains, pairwise disjoint, binds the four owners of some recipe).        *)
(* Lean FourSquareCase (imported; HOL alias fs_bridge.ml works in the row    *)
(* context) is re-ported here in the owner vocabulary as                     *)
(* fsvc_four_square_impossible_actual.  Tag FSVC_.                           *)
(* ========================================================================= *)

needs "n12/geometry/owner_bridge.ml";;
needs "n12/geometry/FourSquareTemplate.ml";;
needs "n12/geometry/MidpointCase.ml";;

(* ------------------------------------------------------------------------- *)
(* FourSquareCase (Compact/Bridge/FourSquareCase.lean), owner vocabulary.    *)
(* ------------------------------------------------------------------------- *)

(* Lean: FourSquareCase.insidePoints *)
let FSVC_FS_INSIDE = [|[("2","113/50"); ("113/50","2"); ("47/20","47/20")];
                       [("33/20","47/20"); ("8/5","3"); ("87/50","3")];
                       [("457/500","2"); ("1","12/5")];
                       [("3","12/5"); ("1543/500","2")]|];;

(* Lean: FourSquareCase.outsidePoints *)
let FSVC_FS_OUTSIDE = [|[("33/20","33/20"); ("47/20","33/20")];
                        [("1","1543/500"); ("2","1543/500")];
                        [("33/20","33/20")];
                        []|];;

(* Lean: FourSquareCase.impossible_actual (Data.Check re-checked: masks and
   barriers in family, distinct pairs 01 03 12 13, masks 2 <> leftBarrier,
   masks 3 <> rightBarrier, query / seed memberships) *)
let fsvc_four_square_impossible_actual fam (trf, masks, owned, lb, rb) =
  if List.length masks <> 4 || List.length owned <> 4 then failwith "fsvc_four_square: data" else
  let ctx = ob_ctx fam trf (zip masks (map mk_numset owned)) in
  List.iter (fun m -> ignore (ob_inf ctx m)) (masks @ [lb; rb]);
  let fs = ref [] in
  List.iteri (fun i m -> List.iter (ob_inside ctx fs m) FSVC_FS_INSIDE.(i)) masks;
  List.iteri (fun i m -> List.iter (ob_outside ctx fs m) FSVC_FS_OUTSIDE.(i)) masks;
  ob_barrier ctx fs (el 2 masks) lb ("19/25", "187/100");
  ob_barrier ctx fs (el 3 masks) rb ("81/25", "187/100");
  ob_close ctx (ob_apply ctx fs FST_IMPOSSIBLE masks []);;

(* ------------------------------------------------------------------------- *)
(* Recipes.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Lean: Recipe *)
type fsvc_recipe =
    Vcfour of ((bool * bool * bool) * int list * int list list * int * int)
  | Vcmid of ((bool * bool * bool) * int list * int list list * string);;

(* Lean: Recipe.masks, Recipe.owned *)
let fsvc_masks r = match r with Vcfour (_, ms, _, _, _) -> ms | Vcmid (_, ms, _, _) -> ms;;
let fsvc_owned r = match r with Vcfour (_, _, ow, _, _) -> ow | Vcmid (_, _, ow, _) -> ow;;

(* Lean: Recipe.GeometryCheck (with FourSquareCase / MidpointCase impossible_actual) *)
let fsvc_geometry fam r = match r with
    Vcfour d -> fsvc_four_square_impossible_actual fam d
  | Vcmid d -> mpc_impossible_actual fam d;;

(* Lean: Recipe.Check (binding part): the four owners of r are bound in the
   assignment (mask, set) list *)
let fsvc_binds r assignment =
  forall2 (fun m ow -> exists (fun (m', s) -> m' = m && setify s = setify ow) assignment)
    (fsvc_masks r) (fsvc_owned r);;

(* ------------------------------------------------------------------------- *)
(* Lean: check_of_parts + impossible.  The geometry of each recipe is        *)
(* checked once; the enumeration of the domain assignments (S12              *)
(* certified_domain_assignments_mem: an assignment of pairwise disjoint      *)
(* allowed sets) checks only the bindings.                                   *)
(* ------------------------------------------------------------------------- *)

let fsvc_impossible fam ds recipes =
  let vars = OB_VARS in
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let masks = map cdom_mask ds in
  (* Lean: members, distinct *)
  if length (setify masks) <> length masks then failwith "fsvc_impossible: repeated masks" else
  List.iter (fun d -> if cdom_fam d <> fam then failwith "fsvc_impossible: domain family") ds;
  (* Lean: geometry (check_of_parts) *)
  let geo = map (fun r -> (r, fsvc_geometry fam r)) recipes in
  let mems = map (fun d -> CONV_RULE (REWRITE_CONV (fam_defs (rand (concl d)) @ [MEM]))
      (MATCH_MP CDOM_OWNER (CONJ d (CONJ hnp (CONJ hrow (in_fam (cdom_mask d) fam)))))) ds in
  let da = Array.of_list (List.combine masks mems) in
  let n = Array.length da in
  let disj mi mj =
    let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral mi, mk_small_numeral mj))) in
    MATCH_MP OO_AUX_DISJOINT (end_itlist CONJ [hnp; hrow; in_fam mi fam; in_fam mj fam; ne]) in
  (* Lean: coverage; a leaf closes by the first recipe bound in the assignment *)
  let leaf chosen =
    let assignment = map (fun (m, _, ls) -> (m, ls)) chosen in
    let (r, gth) = try find (fun (r, _) -> fsvc_binds r assignment) geo
      with Failure _ -> failwith ("fsvc_impossible: no recipe for " ^
        String.concat " " (map (fun (m, ls) -> Printf.sprintf "%d:{%s}" m
          (String.concat "," (map string_of_int ls))) (rev assignment))) in
    let eqs = map2 (fun m ow ->
        let (_, e, _) = find (fun (m', _, ls) -> m' = m && setify ls = setify ow) chosen in
        TRANS e (setlit_eq (rhs (concl e)) (mk_numset ow))) (fsvc_masks r) (fsvc_owned r) in
    MP (SPECL vars gth) (end_itlist CONJ ([hnp; hrow] @ eqs)) in
  let rec dfs j chosen =
    if j = n then leaf chosen else
    let (mj, dj) = da.(j) in
    let rec cases_of th =
      if is_disj (concl th) then
        let p, q = dest_disj (concl th) in DISJ_CASES th (pick (ASSUME p)) (cases_of (ASSUME q))
      else if concl th = `false` then th else pick th
    and pick eqj =
      let ls = numset_of (rhs (concl eqj)) in
      let rec conflict ch = match ch with
          [] -> None
        | (mt, eqt, lt) :: rest ->
            if exists (fun x -> mem x ls) lt then
              let d1 = SUBS [eqt; eqj] (disj mt mj) in
              Some (CONV_RULE (LAND_CONV setlit_conv THENC RAND_CONV setlit_conv THENC disjoint_conv) d1)
            else conflict rest in
      match conflict chosen with
        Some f -> f
      | None -> dfs (j + 1) ((mj, eqj, ls) :: chosen) in
    cases_of dj in
  GENL vars (DISCH hyp (dfs 0 []));;

(* a check of the geometry producers: the recipes upperNE {5,16} {3,14} {1,11} {9,19}
   and spanNE {5,16} {3,13} {1,11} {9,19} of Cases/MergedLower/Recipes.lean in the
   family of case 71 *)
let FSVC_CHECK_GEOMETRY = map (fsvc_geometry
    (mk_numset [1; 2; 4; 8; 48; 192; 768; 1024; 2048; 4096; 16384; 32768]))
  [Vcfour ((false, false, false), [1024; 2048; 4096; 16384], [[5; 16]; [3; 14]; [1; 11]; [9; 19]], 2, 8);
   Vcmid ((false, false, false), [1024; 2048; 4096; 16384], [[5; 16]; [3; 13]; [1; 11]; [9; 19]], "8/5")];;
