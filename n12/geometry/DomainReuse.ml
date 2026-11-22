(* ========================================================================= *)
(* Port of Completion/Cases/C981/DomainReuse.lean (S12Completion.DomainReuse)*)
(*                                                                           *)
(* direct_check_transport: a Lean DirectSingleDomain.Check depends on the   *)
(* family only through its budget upper bound pkup fam mask k, i.e. through *)
(* CARD (fam INTER auxex k).  HOL theorem C981DR_PKUP_TRANSPORT states this; *)
(* the OCaml c981dr_direct_check_transport w a b k checks the card equality  *)
(* (as theorems) and returns the domain of the checked w for family b,       *)
(*   |- hdom b w.dmask k [w.allowed]   (via dsd_actual, SmallOwnerDomainThree)*)
(* failing when Lean's hypothesis h or hw would fail.                        *)
(*                                                                           *)
(* refineQueries d qs: c981dr_refine_queries (|- cdom f m al) qs, qs a list  *)
(* of checked local queries (m, k, owned) registered in LQ_TABLE (by        *)
(* slq_select / slq_new); the metadata check hq (mask = m, kind = 2) is      *)
(* enforced; each owned set is removed by CertifiedDomain.remove (pk_remove, *)
(* which filters every allowed set equal to it, as Lean's filter does).      *)
(* ========================================================================= *)

needs "n12/geometry/SmallOwnerDomainThree.ml";;

(* Lean: direct_check_transport (the family-dependent part of Check) *)
let C981DR_PKUP_TRANSPORT = prove
 (`forall fa fb m k. CARD (fa INTER auxex k) = CARD (fb INTER auxex k)
     ==> pkup fa m k = pkup fb m k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[pkup]);;

let c981dr_direct_check_transport w fa fb k =
  let ca = pk_num (pkup_thm fa w.dmask k) and cb = pk_num (pkup_thm fb w.dmask k) in
  if ca <> cb then failwith "c981dr_direct_check_transport: budgets differ" else
  ignore (dsd_actual fa k w);
  dsd_actual fb k w;;

(* Lean: refineQueries *)
let c981dr_refine_queries th qs =
  let m = cdom_mask th in
  List.fold_left (fun th (qm, qk, ow) ->
      if qm <> m || qk <> 2 then failwith "c981dr_refine_queries: query mask / kind" else
      if not (Hashtbl.mem LQ_TABLE (qm, qk, List.sort compare ow))
      then failwith "c981dr_refine_queries: unchecked query" else
      pk_remove th (mk_numset (List.sort compare ow))) th qs;;
