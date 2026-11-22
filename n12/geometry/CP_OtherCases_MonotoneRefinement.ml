(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MonotoneRefinement.lean.           *)
(*   mr_trim th [query indices]   Lean trim (combined owners refuted by a    *)
(*                                compatible extended kind-2 query)          *)
(*   mr_diameter_filter th        Lean diameterFilter (owners whose inside   *)
(*                                points have squared distance >=           *)
(*                                2 (1001/1000)^2 are refuted by PK_DIAM)   *)
(* Both return |- cdom fam m [filtered literal list].                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MonotoneQueries.ml";;

(* Lean: trim *)
let mr_trim th qidxs =
  let m = cdom_mask th in
  let sigs = map (fun n -> (n, mq_signature n)) qidxs in
  List.iter (fun (_, (m', k', _, _)) -> if m' <> m || k' <> 2 then failwith "mr_trim: query mask / kind") sigs;
  List.fold_left (fun th s ->
      let ls = numset_of s in
      match (try Some (find (fun (_, sg) -> mq_compatible sg m 2 ls) sigs) with Failure _ -> None) with
        Some (n, _) -> ignore (mq_extended n ls); pk_remove th s
      | None -> th) th (dest_list (rand (concl th)));;

(* Lean: actual_diameter (inside_distance_bound): two inside points are closer than
   sqrt 2 * side *)
let PK_DIAM = prove
 (`forall c1 c2 a b l z w:real^2.
        a * a + b * b = &1 /\ l <= &1001 / &1000 /\ &0 < l /\
        &2 * (&1001 / &1000) * (&1001 / &1000) <=
        (z$1 - w$1) * (z$1 - w$1) + (z$2 - w$2) * (z$2 - w$2)
        ==> ~(z IN osq c1 c2 a b l /\ w IN osq c1 c2 a b l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`; `z:real^2`; `w:real^2`] OSQ_DIAMETER) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`l:real`; `&1001 / &1000`; `l:real`; `&1001 / &1000`] REAL_LE_MUL2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let qdist2 (x, y) (x', y') = let dx = x -/ x' and dy = y -/ y' in dx */ dx +/ dy */ dy;;
let DIAM_LIMIT = num 2 */ nlin_rat "1001/1000" */ nlin_rat "1001/1000";;

(* inside points of a square owning m with combined owners s:  hyps |- [vector IN osq ..] *)
let mr_inside_thms m s =
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let auxp = mk_eq(auxown_tm 2, set_tm s) in
  let seeds = pk_seeds SPEC5 (map ASSUME LQ_HYPS) (marker_facts (ASSUME ownp)) (bits m) in
  let afacts = filter (fun f -> not (is_neg (concl f))) (aux_facts 2 (ASSUME auxp)) in
  (ownp, auxp, seeds @ afacts);;

let mr_far_pair m s =
  let pts = seed_points m @ map (aux_q 2) s in
  let rec go l = match l with
      [] -> None
    | p :: rest -> (match (try Some (find (fun q -> qdist2 p q >=/ DIAM_LIMIT) rest) with Failure _ -> None) with
                      Some q -> Some (p, q) | None -> go rest) in
  go pts;;

(* Lean: diameterFilter *)
let mr_diameter_filter th =
  let m = cdom_mask th in
  List.fold_left (fun th s ->
      let ls = numset_of s in
      match mr_far_pair m ls with
        None -> th
      | Some (p, q) ->
          let (ownp, auxp, ins) = mr_inside_thms m ls in
          let find_pt pt = find (fun t -> qeq (pt_of_mem t) pt) ins in
          let tp = find_pt p and tq = find_pt q in
          let zt = lhand (concl tp) and wt = lhand (concl tq) in
          let dth = SPECL ([`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] @ [zt; wt]) PK_DIAM in
          let num_ok = EQT_ELIM ((REWRITE_CONV[VECTOR_2] THENC REAL_RAT_REDUCE_CONV)
                         (rand (rand (rand (lhand (concl dth)))))) in
          let lt0 = REAL_ARITH `&1 < l ==> &0 < l` in
          let hs = map ASSUME LQ_HYPS in
          let f = MP (NOT_ELIM (MP dth (end_itlist CONJ [el 2 hs; el 1 hs; MP lt0 (el 0 hs); num_ok])))
                     (CONJ tp tq) in
          let ownb = mk_eq(`owned c1 c2 a b l`, bitset_tm m) in
          let auxl = mk_eq(auxown_tm 2, s) in
          let f = PROVE_HYP (TRANS (ASSUME ownb) (bitset_bits m)) f in
          let f = PROVE_HYP (TRANS (ASSUME auxl) (setlit_conv s)) f in
          let loc = GENL SPEC5 (disch_conj (LQ_HYPS @ [ownb; auxl]) f) in
          let r = MATCH_MP CDOM_REMOVE (CONJ th loc) in
          CONV_RULE (RAND_CONV (filter_eval_conv setlit_eq_dconv)) r) th (dest_list (rand (concl th)));;
