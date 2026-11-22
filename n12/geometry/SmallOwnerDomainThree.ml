(* ========================================================================= *)
(* Phase 2: Compact/Bridge/SmallOwnerDomainThree.lean, with S12              *)
(* DirectSingleDomain.  A Lean DirectSingleDomain w is the OCaml record     *)
(* dsd = { dmask; dlower; dupper; dallowed : int list list; dqueries : int list } *)
(* (queries by S12.localQueries index).  Lean  w.actual  for a checked w is  *)
(*   dsd_actual fam k w :  |- hdom fam w.mask k [w.allowed]                  *)
(* which checks w.Check (lower / upper equal the budget; every subset in    *)
(* the interval is allowed or refuted by an exact query of the list).       *)
(* Lean smallSubsetsThree is SODT_SMALL3; its completeness is part of the    *)
(* DFS over all subsets inside spec_theorem.  Lean checked = dsd_actual      *)
(* (with upper <= 3).                                                        *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;
needs "n12/geometry/RelaxedOwnerDomain.ml";;

type dsd = { dmask : int; dlower : int; dupper : int; dallowed : int list list; dqueries : int list };;

(* Lean: triples, smallSubsetsThree *)
let SODT_SMALL3 = RO_SMALL @
  List.concat (map (fun i -> List.concat (map (fun j -> map (fun l -> [i; j; l])
      (filter (fun l -> j < l) (0--9))) (filter (fun j -> i < j) (0--9)))) (0--9));;

(* Lean: S12.DirectSingleDomain.actual (Check including the budget equalities) *)
let dsd_actual fam k w =
  let lo = pk_num (pklow_thm w.dmask k) and hi = pk_num (pkup_thm fam w.dmask k) in
  if w.dlower <> lo || w.dupper <> hi then failwith "dsd_actual: bounds differ from the budget" else
  let qs = map slq_select w.dqueries in
  List.iter (fun (m, kq, _, _) -> if m <> w.dmask || kq <> k then failwith "dsd_actual: query mask / kind") qs;
  let al = map (List.sort compare) w.dallowed in
  let sth = spec_theorem w.dmask k lo hi al in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits w.dmask)) in
  let (hl, hh) = bound_tms k lo hi in
  let hyps = LQ_HYPS @ [ownp; hl; hh] in
  let th = List.fold_left MP (SPECL SPEC5 sth) (map ASSUME hyps) in
  pk_hdom_local fam w.dmask k lo hi hyps th (mk_list(map mk_numset w.dallowed, `:num->bool`));;

(* Lean: SmallOwnerDomainThree.checked *)
let sodt_checked fam k w =
  if w.dupper > 3 then failwith "sodt_checked: upper > 3" else dsd_actual fam k w;;

(* Lean: S12.CertifiedDomain.ofDirectProduct *)
let dsd_product fam a b =
  if a.dmask <> b.dmask then failwith "dsd_product: masks" else
  pk_product (dsd_actual fam 0 a) (dsd_actual fam 1 b);;
