(* ========================================================================= *)
(* Port of Compact/Bridge/ForcedAuxiliary.lean (N12Compact.ForcedAuxiliary). *)
(* A finite ownership cover forces an auxiliary point of one owner without   *)
(* fixing its other points.                                                  *)
(* Lean  withoutPoint ds mask index  + feasible .. = false  + contains  are  *)
(* one OCaml producer: the depth-first search over the allowed sets of the   *)
(* certified domains ds (pairwise disjoint owner sets, OO_AUX_DISJOINT) is   *)
(* replayed in the kernel; every surviving assignment must give the owner m  *)
(* the index (otherwise withoutPoint would be feasible and the producer      *)
(* fails, exactly when the Lean decide check fails).                         *)
(*   fa_contains fam ds m idx :                                              *)
(*     |- !c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP ..) = fam  *)
(*                      ==> idx IN ooaux c1 c2 a b l m                       *)
(*   fa_cover fam ds m [i1; ..; ik] : the same with the disjunction          *)
(*     i1 IN ooaux .. m \/ .. \/ ik IN ooaux .. m   (filter "none of them").  *)
(* ds : list of |- cdom fam mask al  with distinct masks in fam.             *)
(* Tag FA_.                                                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

let FA_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* generic DFS over the allowed sets of the domains ds; leaf receives the list
   (mask, |- ooaux .. mask = S) of the chosen (pairwise disjoint) owner sets and
   returns a theorem of goal (under the hypothesis hyp) *)
let fa_search fam ds goal leaf =
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let masks = map cdom_mask ds in
  if length (setify masks) <> length masks then failwith "fa_search: repeated masks" else
  let mems = map (fun d -> CONV_RULE (REWRITE_CONV (fam_defs (rand (concl d)) @ [MEM]))
      (MATCH_MP CDOM_OWNER (CONJ d (CONJ hnp (CONJ hrow (in_fam (cdom_mask d) fam)))))) ds in
  let da = Array.of_list (List.combine masks mems) in
  let n = Array.length da in
  let disj mi mj =
    let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral mi, mk_small_numeral mj))) in
    MATCH_MP OO_AUX_DISJOINT (end_itlist CONJ [hnp; hrow; in_fam mi fam; in_fam mj fam; ne]) in
  let rec dfs j chosen =
    if j = n then leaf (rev (map (fun (m, e, _) -> (m, e)) chosen)) else
    let (mj, dj) = da.(j) in
    let rec cases_of th =
      if is_disj (concl th) then
        let p, q = dest_disj (concl th) in DISJ_CASES th (pick (ASSUME p)) (cases_of (ASSUME q))
      else if concl th = `false` then CONTR goal th else pick th
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
        Some f -> CONTR goal f
      | None -> dfs (j + 1) ((mj, eqj, ls) :: chosen) in
    cases_of dj in
  GENL FA_VARS (DISCH hyp (dfs 0 []));;

(* |- d1 \/ .. \/ dk  from  |- di *)
let fa_inject goal th =
  let rec build ds = match ds with
      [d] -> if aconv d (concl th) then th else failwith "fa_inject"
    | d :: rest -> if aconv d (concl th) then DISJ1 th (list_mk_disj rest) else DISJ2 d (build rest)
    | [] -> failwith "fa_inject" in
  build (disjuncts goal);;

let fa_mem_tm j m = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j), ooaux_tm m);;

(* |- j IN ooaux .. m  from  |- ooaux .. m = S  with j in the literal S *)
let fa_mem_of_eq j e =
  let th = AP_TERM (mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j)) e in
  EQ_MP (SYM th) (EQT_ELIM ((REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM] THENC
                            NUM_REDUCE_CONV THENC REWRITE_CONV[]) (rhs (concl th))));;

(* Lean: withoutPoint (filter by several indices) + contains *)
let fa_cover fam ds m idxs =
  if not (mem m (map cdom_mask ds)) then failwith "fa_cover: no domain for the mask" else
  let goal = list_mk_disj (map (fun j -> fa_mem_tm j m) idxs) in
  fa_search fam ds goal (fun chosen ->
    let e = assoc m chosen in
    let s = numset_of (rhs (concl e)) in
    match filter (fun j -> mem j s) idxs with
      j :: _ -> fa_inject goal (fa_mem_of_eq j e)
    | [] -> failwith (Printf.sprintf "fa_cover: feasible assignment without the points (mask %d)" m));;

(* Lean: contains *)
let fa_contains fam ds m idx = fa_cover fam ds m [idx];;
