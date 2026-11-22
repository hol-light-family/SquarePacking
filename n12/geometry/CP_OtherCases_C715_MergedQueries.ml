(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C715/MergedQueries.lean.           *)
(* Exact local refutations for the genuine merged owner of markers 10 and 14 *)
(* (mask 17408).  Each Lean checked_local_query is registered with slq_new   *)
(* (SharedLocalQueries.ml): the kernel re-proves it from its inside /        *)
(* outside points (.hull: three hull points inside, target outside; .four:  *)
(* the transformed FourPointDatum A, B inside, P, E outside; .short: the    *)
(* window points inside, the transformed short-side targets outside).        *)
(*   C715MQ_MERGEDF_QUERYn : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000  *)
(*     ==> a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m) *)
(*     ==> auxown k c1 c2 a b l = set_of_list owned ==> F  (LocalQuery.sound) *)
(* Lean DirectSingleDomain mergedF / mergedG are the dsd records             *)
(* c715mq_mergedF / c715mq_mergedG (dqueries = [] since their queries are    *)
(* new, not entries of S12.localQueries; the query signatures are kept in    *)
(* c715mq_mergedF_signatures / ..G..).  Lean mergedF_checked (via            *)
(* SmallOwnerDomain.checked) is                                              *)
(*   C715MQ_MERGEDF_CHECKED : |- hdom c715ri_family 17408 0 [{5}; {7}; ..]    *)
(*   C715MQ_MERGEDG_CHECKED : |- hdom c715ri_family 17408 1 [{6}; {8}; {9}]   *)
(* c715mq_small_checked performs Lean's SmallOwnerDomain.Check (budget       *)
(* equalities, upper <= 2, every small subset in the budget interval allowed *)
(* or refuted by a query of the signature list) before the kernel proof.     *)
(* The certificate hints of the queries are kept as c715mq_mergedF_hints /  *)
(* c715mq_mergedG_hints (DirectHalfTransport's dht_queries format), for     *)
(* transported reuse (FiniteCases/C975Domains.rawTopG).                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C715_RowIdentity.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

(* Lean: SmallOwnerDomain.checked (+ Check); sigs = the query signatures   *)
let c715mq_small_checked fam k w sigs =
  let lo = pk_num (pklow_thm w.dmask k) and hi = pk_num (pkup_thm fam w.dmask k) in
  if w.dlower <> lo || w.dupper <> hi then failwith "c715mq_small_checked: budget" else
  if hi > 2 then failwith "c715mq_small_checked: upper > 2" else
  let sigs = map (fun (m, kq, ow) -> (m, kq, List.sort compare ow)) sigs in
  List.iter (fun (m, kq, ow) ->
      if not (Hashtbl.mem LQ_TABLE (m, kq, ow)) then failwith "c715mq_small_checked: unchecked query")
    sigs;
  let al = map (List.sort compare) w.dallowed in
  List.iter (fun s ->
      let c = List.length s in
      if lo <= c && c <= hi && not (mem s al) && not (mem (w.dmask, k, s) sigs)
      then failwith "c715mq_small_checked: subset neither allowed nor refuted") RO_SMALL;
  dsd_actual fam k { w with dqueries = [] };;

(* query hints (mask, kind, owned, inside points, outside points) of the
   Lean mergedFQuery* certificates, in Lean order *)
let c715mq_mergedF_hints = [
  (* mergedFQuery1 *) (17408, 0, [0],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "87/50")],
      [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery2 *) (17408, 0, [1],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "113/50")],
      [(nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery4 *) (17408, 0, [2],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery8 *) (17408, 0, [3],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "3")],
      [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery16 *) (17408, 0, [4],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
      [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery64 *) (17408, 0, [6],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "1")],
      [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery256 *) (17408, 0, [8],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
      [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery3 *) (17408, 0, [0; 1],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "113/50")],
      [(nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery5 *) (17408, 0, [0; 2],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "33/20", nlin_rat "33/20")]);
  (* mergedFQuery9 *) (17408, 0, [0; 3],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "3")],
      [(nlin_rat "33/20", nlin_rat "47/20")]);
  (* mergedFQuery17 *) (17408, 0, [0; 4],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "87/50")],
      [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery33 *) (17408, 0, [0; 5],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "87/50")],
      [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);
  (* mergedFQuery65 *) (17408, 0, [0; 6],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1")],
      [(nlin_rat "33/20", nlin_rat "33/20")]);
  (* mergedFQuery129 *) (17408, 0, [0; 7],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "3")],
      [(nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery257 *) (17408, 0, [0; 8],
      [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50")],
      [(nlin_rat "2", nlin_rat "87/50")]);
  (* mergedFQuery513 *) (17408, 0, [0; 9],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "87/50")],
      [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery6 *) (17408, 0, [1; 2],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "33/20", nlin_rat "33/20")]);
  (* mergedFQuery10 *) (17408, 0, [1; 3],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "3")],
      [(nlin_rat "33/20", nlin_rat "47/20")]);
  (* mergedFQuery18 *) (17408, 0, [1; 4],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "113/50")],
      [(nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery34 *) (17408, 0, [1; 5],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "113/50")],
      [(nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "33/20", nlin_rat "47/20")]);
  (* mergedFQuery66 *) (17408, 0, [1; 6],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery130 *) (17408, 0, [1; 7],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "3")],
      [(nlin_rat "33/20", nlin_rat "47/20")]);
  (* mergedFQuery258 *) (17408, 0, [1; 8],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "113/50")],
      [(nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery514 *) (17408, 0, [1; 9],
      [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "113/50")],
      [(nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery12 *) (17408, 0, [2; 3],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "8/5", nlin_rat "3")],
      [(nlin_rat "33/20", nlin_rat "33/20")]);
  (* mergedFQuery20 *) (17408, 0, [2; 4],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery36 *) (17408, 0, [2; 5],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery68 *) (17408, 0, [2; 6],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery132 *) (17408, 0, [2; 7],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery260 *) (17408, 0, [2; 8],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery516 *) (17408, 0, [2; 9],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery24 *) (17408, 0, [3; 4],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
      [(nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery40 *) (17408, 0, [3; 5],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "3")],
      [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);
  (* mergedFQuery72 *) (17408, 0, [3; 6],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery136 *) (17408, 0, [3; 7],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "3")],
      [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery264 *) (17408, 0, [3; 8],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "3")],
      [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery520 *) (17408, 0, [3; 9],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "8/5", nlin_rat "3")],
      [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery80 *) (17408, 0, [4; 6],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery144 *) (17408, 0, [4; 7],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "87/50")],
      [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery272 *) (17408, 0, [4; 8],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
      [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery96 *) (17408, 0, [5; 6],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery192 *) (17408, 0, [6; 7],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "1")],
      [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery320 *) (17408, 0, [6; 8],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
      [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")]);
  (* mergedFQuery576 *) (17408, 0, [6; 9],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "12/5", nlin_rat "1")],
      [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedFQuery384 *) (17408, 0, [7; 8],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "3", nlin_rat "87/50")],
      [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "47/20", nlin_rat "33/20"); (nlin_rat "2", nlin_rat "113/50")])];;

(* Lean: mergedFQuery1 *)
let C715MQ_MERGEDF_QUERY1 = slq_new (el 0 c715mq_mergedF_hints);;
(* Lean: mergedFQuery2 *)
let C715MQ_MERGEDF_QUERY2 = slq_new (el 1 c715mq_mergedF_hints);;
(* Lean: mergedFQuery4 *)
let C715MQ_MERGEDF_QUERY4 = slq_new (el 2 c715mq_mergedF_hints);;
(* Lean: mergedFQuery8 *)
let C715MQ_MERGEDF_QUERY8 = slq_new (el 3 c715mq_mergedF_hints);;
(* Lean: mergedFQuery16 *)
let C715MQ_MERGEDF_QUERY16 = slq_new (el 4 c715mq_mergedF_hints);;
(* Lean: mergedFQuery64 *)
let C715MQ_MERGEDF_QUERY64 = slq_new (el 5 c715mq_mergedF_hints);;
(* Lean: mergedFQuery256 *)
let C715MQ_MERGEDF_QUERY256 = slq_new (el 6 c715mq_mergedF_hints);;
(* Lean: mergedFQuery3 *)
let C715MQ_MERGEDF_QUERY3 = slq_new (el 7 c715mq_mergedF_hints);;
(* Lean: mergedFQuery5 *)
let C715MQ_MERGEDF_QUERY5 = slq_new (el 8 c715mq_mergedF_hints);;
(* Lean: mergedFQuery9 *)
let C715MQ_MERGEDF_QUERY9 = slq_new (el 9 c715mq_mergedF_hints);;
(* Lean: mergedFQuery17 *)
let C715MQ_MERGEDF_QUERY17 = slq_new (el 10 c715mq_mergedF_hints);;
(* Lean: mergedFQuery33 *)
let C715MQ_MERGEDF_QUERY33 = slq_new (el 11 c715mq_mergedF_hints);;
(* Lean: mergedFQuery65 *)
let C715MQ_MERGEDF_QUERY65 = slq_new (el 12 c715mq_mergedF_hints);;
(* Lean: mergedFQuery129 *)
let C715MQ_MERGEDF_QUERY129 = slq_new (el 13 c715mq_mergedF_hints);;
(* Lean: mergedFQuery257 *)
let C715MQ_MERGEDF_QUERY257 = slq_new (el 14 c715mq_mergedF_hints);;
(* Lean: mergedFQuery513 *)
let C715MQ_MERGEDF_QUERY513 = slq_new (el 15 c715mq_mergedF_hints);;
(* Lean: mergedFQuery6 *)
let C715MQ_MERGEDF_QUERY6 = slq_new (el 16 c715mq_mergedF_hints);;
(* Lean: mergedFQuery10 *)
let C715MQ_MERGEDF_QUERY10 = slq_new (el 17 c715mq_mergedF_hints);;
(* Lean: mergedFQuery18 *)
let C715MQ_MERGEDF_QUERY18 = slq_new (el 18 c715mq_mergedF_hints);;
(* Lean: mergedFQuery34 *)
let C715MQ_MERGEDF_QUERY34 = slq_new (el 19 c715mq_mergedF_hints);;
(* Lean: mergedFQuery66 *)
let C715MQ_MERGEDF_QUERY66 = slq_new (el 20 c715mq_mergedF_hints);;
(* Lean: mergedFQuery130 *)
let C715MQ_MERGEDF_QUERY130 = slq_new (el 21 c715mq_mergedF_hints);;
(* Lean: mergedFQuery258 *)
let C715MQ_MERGEDF_QUERY258 = slq_new (el 22 c715mq_mergedF_hints);;
(* Lean: mergedFQuery514 *)
let C715MQ_MERGEDF_QUERY514 = slq_new (el 23 c715mq_mergedF_hints);;
(* Lean: mergedFQuery12 *)
let C715MQ_MERGEDF_QUERY12 = slq_new (el 24 c715mq_mergedF_hints);;
(* Lean: mergedFQuery20 *)
let C715MQ_MERGEDF_QUERY20 = slq_new (el 25 c715mq_mergedF_hints);;
(* Lean: mergedFQuery36 *)
let C715MQ_MERGEDF_QUERY36 = slq_new (el 26 c715mq_mergedF_hints);;
(* Lean: mergedFQuery68 *)
let C715MQ_MERGEDF_QUERY68 = slq_new (el 27 c715mq_mergedF_hints);;
(* Lean: mergedFQuery132 *)
let C715MQ_MERGEDF_QUERY132 = slq_new (el 28 c715mq_mergedF_hints);;
(* Lean: mergedFQuery260 *)
let C715MQ_MERGEDF_QUERY260 = slq_new (el 29 c715mq_mergedF_hints);;
(* Lean: mergedFQuery516 *)
let C715MQ_MERGEDF_QUERY516 = slq_new (el 30 c715mq_mergedF_hints);;
(* Lean: mergedFQuery24 *)
let C715MQ_MERGEDF_QUERY24 = slq_new (el 31 c715mq_mergedF_hints);;
(* Lean: mergedFQuery40 *)
let C715MQ_MERGEDF_QUERY40 = slq_new (el 32 c715mq_mergedF_hints);;
(* Lean: mergedFQuery72 *)
let C715MQ_MERGEDF_QUERY72 = slq_new (el 33 c715mq_mergedF_hints);;
(* Lean: mergedFQuery136 *)
let C715MQ_MERGEDF_QUERY136 = slq_new (el 34 c715mq_mergedF_hints);;
(* Lean: mergedFQuery264 *)
let C715MQ_MERGEDF_QUERY264 = slq_new (el 35 c715mq_mergedF_hints);;
(* Lean: mergedFQuery520 *)
let C715MQ_MERGEDF_QUERY520 = slq_new (el 36 c715mq_mergedF_hints);;
(* Lean: mergedFQuery80 *)
let C715MQ_MERGEDF_QUERY80 = slq_new (el 37 c715mq_mergedF_hints);;
(* Lean: mergedFQuery144 *)
let C715MQ_MERGEDF_QUERY144 = slq_new (el 38 c715mq_mergedF_hints);;
(* Lean: mergedFQuery272 *)
let C715MQ_MERGEDF_QUERY272 = slq_new (el 39 c715mq_mergedF_hints);;
(* Lean: mergedFQuery96 *)
let C715MQ_MERGEDF_QUERY96 = slq_new (el 40 c715mq_mergedF_hints);;
(* Lean: mergedFQuery192 *)
let C715MQ_MERGEDF_QUERY192 = slq_new (el 41 c715mq_mergedF_hints);;
(* Lean: mergedFQuery320 *)
let C715MQ_MERGEDF_QUERY320 = slq_new (el 42 c715mq_mergedF_hints);;
(* Lean: mergedFQuery576 *)
let C715MQ_MERGEDF_QUERY576 = slq_new (el 43 c715mq_mergedF_hints);;
(* Lean: mergedFQuery384 *)
let C715MQ_MERGEDF_QUERY384 = slq_new (el 44 c715mq_mergedF_hints);;

(* Lean: mergedF *)
let c715mq_mergedF = { dmask = 17408; dlower = 1; dupper = 2;
  dallowed = [[5]; [7]; [9]; [4; 5]; [4; 9]; [5; 7]; [5; 8]; [5; 9]; [7; 9]; [8; 9]]; dqueries = [] };;

(* Lean: mergedFSignatures (private) *)
let c715mq_mergedF_signatures = [(17408, 0, [0]); (17408, 0, [1]); (17408, 0, [2]); (17408, 0, [3]); (17408, 0, [4]); (17408, 0, [6]); (17408, 0, [8]); (17408, 0, [0; 1]); (17408, 0, [0; 2]); (17408, 0, [0; 3]); (17408, 0, [0; 4]); (17408, 0, [0; 5]); (17408, 0, [0; 6]); (17408, 0, [0; 7]); (17408, 0, [0; 8]); (17408, 0, [0; 9]); (17408, 0, [1; 2]); (17408, 0, [1; 3]); (17408, 0, [1; 4]); (17408, 0, [1; 5]); (17408, 0, [1; 6]); (17408, 0, [1; 7]); (17408, 0, [1; 8]); (17408, 0, [1; 9]); (17408, 0, [2; 3]); (17408, 0, [2; 4]); (17408, 0, [2; 5]); (17408, 0, [2; 6]); (17408, 0, [2; 7]); (17408, 0, [2; 8]); (17408, 0, [2; 9]); (17408, 0, [3; 4]); (17408, 0, [3; 5]); (17408, 0, [3; 6]); (17408, 0, [3; 7]); (17408, 0, [3; 8]); (17408, 0, [3; 9]); (17408, 0, [4; 6]); (17408, 0, [4; 7]); (17408, 0, [4; 8]); (17408, 0, [5; 6]); (17408, 0, [6; 7]); (17408, 0, [6; 8]); (17408, 0, [6; 9]); (17408, 0, [7; 8])];;

(* Lean: mergedF_checked *)
let C715MQ_MERGEDF_CHECKED =
  c715mq_small_checked `c715ri_family` 0 c715mq_mergedF c715mq_mergedF_signatures;;

(* query hints (mask, kind, owned, inside points, outside points) of the
   Lean mergedGQuery* certificates, in Lean order *)
let c715mq_mergedG_hints = [
  (* mergedGQuery1 *) (17408, 1, [0],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "8/5")],
      [(nlin_rat "87/50", nlin_rat "2")]);
  (* mergedGQuery2 *) (17408, 1, [1],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "1", nlin_rat "12/5")],
      [(nlin_rat "33/20", nlin_rat "47/20")]);
  (* mergedGQuery4 *) (17408, 1, [2],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedGQuery8 *) (17408, 1, [3],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "87/50", nlin_rat "2")],
      [(nlin_rat "113/50", nlin_rat "2")]);
  (* mergedGQuery16 *) (17408, 1, [4],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "87/50", nlin_rat "3")],
      [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "113/50", nlin_rat "2")]);
  (* mergedGQuery32 *) (17408, 1, [5],
      [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1")],
      [(nlin_rat "47/20", nlin_rat "33/20")]);
  (* mergedGQuery128 *) (17408, 1, [7],
      [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
      [(nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2")])];;

(* Lean: mergedGQuery1 *)
let C715MQ_MERGEDG_QUERY1 = slq_new (el 0 c715mq_mergedG_hints);;
(* Lean: mergedGQuery2 *)
let C715MQ_MERGEDG_QUERY2 = slq_new (el 1 c715mq_mergedG_hints);;
(* Lean: mergedGQuery4 *)
let C715MQ_MERGEDG_QUERY4 = slq_new (el 2 c715mq_mergedG_hints);;
(* Lean: mergedGQuery8 *)
let C715MQ_MERGEDG_QUERY8 = slq_new (el 3 c715mq_mergedG_hints);;
(* Lean: mergedGQuery16 *)
let C715MQ_MERGEDG_QUERY16 = slq_new (el 4 c715mq_mergedG_hints);;
(* Lean: mergedGQuery32 *)
let C715MQ_MERGEDG_QUERY32 = slq_new (el 5 c715mq_mergedG_hints);;
(* Lean: mergedGQuery128 *)
let C715MQ_MERGEDG_QUERY128 = slq_new (el 6 c715mq_mergedG_hints);;

(* Lean: mergedG *)
let c715mq_mergedG = { dmask = 17408; dlower = 1; dupper = 1;
  dallowed = [[6]; [8]; [9]]; dqueries = [] };;

(* Lean: mergedGSignatures (private) *)
let c715mq_mergedG_signatures = [(17408, 1, [0]); (17408, 1, [1]); (17408, 1, [2]); (17408, 1, [3]); (17408, 1, [4]); (17408, 1, [5]); (17408, 1, [7])];;

(* Lean: mergedG_checked *)
let C715MQ_MERGEDG_CHECKED =
  c715mq_small_checked `c715ri_family` 1 c715mq_mergedG c715mq_mergedG_signatures;;
