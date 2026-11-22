(* ========================================================================= *)
(* Phase 2: Compact/Bridge/SharedLocalQueries.lean.                          *)
(* Lean  certified_query% n  (query n of S12.localQueries, with its check)  *)
(* is  slq_select n : the Phase-1 local query n re-proved by the kernel:     *)
(*   |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==> a * a + b * b = &1    *)
(*        ==> owalls c1 c2 a b l ==> owned c1 c2 a b l = set_of_list (bits m) *)
(*        ==> auxown k c1 c2 a b l = set_of_list owned ==> F                 *)
(* (Lean LocalQuery.sound for this query; index n is the first field of     *)
(* LOCAL_QUERIES).  Lean remove = slq_remove.  A genuinely new query        *)
(* (checked_local_query) is registered with slq_new (m, k, owned, uin, uout) *)
(* (its inside / outside points, as in localq_data.ml).                      *)
(* ========================================================================= *)

needs "n12/geometry/PackingContext.ml";;

(* Historical queries (Compact/HistoricalOwnership/QueriesNNN.lean, Lean queryN /
   queryN_certified) are registered by slq_hist n data (in QueriesNNN.ml) under the index
   slq_hist_idx n = 1000000 + n, so index-based tools (slq_data, slq_select, mq_signature,
   mq_extended, dqueries of domain records) can refer to them like S12.localQueries entries. *)
let SLQ_HIST = Hashtbl.create 3000;;
let slq_hist_idx n = 1000000 + n;;

let slq_data n =
  try Hashtbl.find SLQ_HIST n with Not_found ->
  try find (fun (i,_,_,_,_,_) -> i = n) LOCAL_QUERIES
  with Failure _ -> failwith (Printf.sprintf "slq: no local query %d" n);;

let SLQ_TBL = Hashtbl.create 200;;
(* Lean: select / certified_query% *)
let slq_select n =
  try Hashtbl.find SLQ_TBL n with Not_found ->
  let (_, m, k, ow, _, _) as q = slq_data n in
  let th = query_theorem q in
  if not (Hashtbl.mem LQ_TABLE (m, k, ow)) then Hashtbl.add LQ_TABLE (m, k, ow) th;
  let r = (m, k, ow, th) in Hashtbl.add SLQ_TBL n r; r;;

(* Lean: checked_local_query (a new query given by its points) *)
let slq_new (m, k, ow, uin, uout) =
  let ow = List.sort compare ow in
  let th = query_theorem (-1, m, k, ow, uin, uout) in
  Hashtbl.replace LQ_TABLE (m, k, ow) th; th;;

(* a historical checked_local_query queryN (registered at index slq_hist_idx n) *)
let slq_hist n (m, k, ow, uin, uout) =
  let th = slq_new (m, k, ow, uin, uout) in
  let i = slq_hist_idx n in
  Hashtbl.replace SLQ_HIST i (i, m, k, List.sort compare ow, uin, uout);
  Hashtbl.replace SLQ_TBL i (m, k, List.sort compare ow, th); th;;

(* Lean: remove *)
let slq_remove th n =
  let (m, k, ow, _) = slq_select n in
  if k <> 2 || m <> cdom_mask th then failwith "slq_remove: mask / kind" else
  pk_remove th (mk_numset ow);;
