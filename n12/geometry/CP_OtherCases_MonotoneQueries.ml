(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MonotoneQueries.lean.              *)
(* A local query stays valid when more auxiliaries are owned, provided the   *)
(* certificate's needed outside auxiliaries stay absent.  In HOL a query is *)
(* its point data (LOCAL_QUERIES: inside points uin, outside points uout);   *)
(* the extended query is re-proved by query_theorem with the same points:    *)
(*   mq_extended n owned  (Lean extended_checked / extended_sound)           *)
(*   |- !c1 c2 a b l. LQ hyps ==> owned c1 c2 a b l = set_of_list (bits m)   *)
(*        ==> auxown k c1 c2 a b l = set_of_list owned ==> F                 *)
(* Lean neededOutside / blocked / signature: mq_blocked n, mq_signature n.   *)
(* Lean SingleDomain w (mask, lower, upper, allowed, queries) is a dsd record *)
(* (SmallOwnerDomainThree.ml); SingleDomain.actual = mq_single fam k w       *)
(* (|- hdom fam mask k allowed); product = mq_product fam f g.               *)
(* ========================================================================= *)

needs "n12/geometry/SmallOwnerDomainThree.ml";;

(* Lean: blocked (indices of the needed outside auxiliary points) *)
let mq_blocked n =
  let (_, _, k, _, _, uout) = slq_data n in
  filter (fun j -> exists (qeq (aux_q k j)) uout) (0 -- (AUX_LEN.(k) - 1));;

(* Lean: signature *)
let mq_signature n = let (_, m, k, ow, _, _) = slq_data n in (m, k, ow, mq_blocked n);;

(* Lean: compatible *)
let mq_compatible (m', k', ow, bl) m k owned =
  m' = m && k' = k && forall (fun j -> mem j owned) ow && not (exists (fun j -> mem j owned) bl);;

(* Lean: extended_checked / extended_sound *)
let mq_extended n owned =
  let owned = List.sort compare owned in
  let (_, m, k, ow, uin, uout) = slq_data n in
  if not (mq_compatible (mq_signature n) m k owned) then failwith "mq_extended: not compatible" else
  try Hashtbl.find LQ_TABLE (m, k, owned) with Not_found ->
  let th = query_theorem (-1, m, k, owned, uin, uout) in
  Hashtbl.add LQ_TABLE (m, k, owned) th; th;;

(* Lean: SingleDomain.actual (Check: budget equalities, upper <= 3, every subset of the
   interval allowed or refuted by a compatible extended query) *)
let mq_single fam k w =
  let lo = pk_num (pklow_thm w.dmask k) and hi = pk_num (pkup_thm fam w.dmask k) in
  if w.dlower <> lo || w.dupper <> hi || hi > 3 then failwith "mq_single: bounds" else
  let al = map (List.sort compare) w.dallowed in
  let sigs = map (fun n -> (n, mq_signature n)) w.dqueries in
  List.iter (fun s ->
      if lo <= length s && length s <= hi && not (mem s al) then
        let (n, _) = try find (fun (_, sg) -> mq_compatible sg w.dmask k s) sigs
                     with Failure _ -> failwith "mq_single: an owner set is not refuted" in
        ignore (mq_extended n s)) SODT_SMALL3;
  let sth = spec_theorem w.dmask k lo hi al in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits w.dmask)) in
  let (hl, hh) = bound_tms k lo hi in
  let hyps = LQ_HYPS @ [ownp; hl; hh] in
  let th = List.fold_left MP (SPECL SPEC5 sth) (map ASSUME hyps) in
  pk_hdom_local fam w.dmask k lo hi hyps th (mk_list(map mk_numset w.dallowed, `:num->bool`));;

(* Lean: product *)
let mq_product fam f g =
  if f.dmask <> g.dmask then failwith "mq_product: masks" else
  pk_product (mq_single fam 0 f) (mq_single fam 1 g);;
