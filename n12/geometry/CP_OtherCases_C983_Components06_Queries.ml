(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/Components06/Queries.lean
   (namespace N12Compact.Completion.OtherCases.C983.Component06Data).
   Literal query data.  Lean certified_query% n = local query n of S12.localQueries;
   Lean N12Compact.HistoricalOwnership.Queries.queryN_certified = the historical query N
   (HOQ_QUERYN of QueriesNNN.ml), referred to by index slq_hist_idx N; mq_signature gives
   Lean's signature; the Exact decide is the OCaml check c983c06q_exact (fails on mismatch).
   Tag c983c06q_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;
needs "n12/geometry/CP_OtherCases_DomainCache.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;
needs "n12/geometry/Queries044.ml";;
needs "n12/geometry/Queries045.ml";;
needs "n12/geometry/Queries046.ml";;
needs "n12/geometry/Queries047.ml";;
needs "n12/geometry/Queries048.ml";;

(* Lean signatures = queries.map signature (the Exact decides) *)
let c983c06q_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "c983c06q_exact";;

(* Lean: combinedQueries6 *)
let c983c06q_combinedQueries6 = [slq_hist_idx 1481; slq_hist_idx 1498; slq_hist_idx 1500; slq_hist_idx 1499; slq_hist_idx 1501; slq_hist_idx 1502; slq_hist_idx 1512; slq_hist_idx 1514; slq_hist_idx 1513; slq_hist_idx 1515; slq_hist_idx 1516; slq_hist_idx 1482; slq_hist_idx 1485; slq_hist_idx 1489; slq_hist_idx 1492; slq_hist_idx 1496; slq_hist_idx 1519; slq_hist_idx 1523; slq_hist_idx 1505; slq_hist_idx 1509; slq_hist_idx 1533; slq_hist_idx 1536];;
(* Lean: combinedSignatures6 *)
let c983c06q_combinedSignatures6 =
  [(1024, 2, [5; 16; 18], [9]);
   (1024, 2, [7; 13; 16], [5]);
   (1024, 2, [7; 13; 17], [5]);
   (1024, 2, [7; 14; 16], [17]);
   (1024, 2, [7; 14; 17], [5]);
   (1024, 2, [7; 16; 18], [19]);
   (1024, 2, [9; 13; 16], [5]);
   (1024, 2, [9; 13; 17], [5]);
   (1024, 2, [9; 14; 16], [5; 7]);
   (1024, 2, [9; 14; 17], [5]);
   (1024, 2, [9; 16; 18], [8]);
   (1024, 2, [3; 5; 16], [17]);
   (1024, 2, [3; 5; 17], [14]);
   (1024, 2, [3; 5; 19], [7]);
   (1024, 2, [4; 5; 17], [16]);
   (1024, 2, [4; 5; 19], [16]);
   (1024, 2, [4; 9; 17], [16]);
   (1024, 2, [4; 9; 19], [16]);
   (1024, 2, [5; 8; 17], [16; 19]);
   (1024, 2, [5; 8; 19], [9]);
   (1024, 2, [8; 9; 17], [16]);
   (1024, 2, [8; 9; 19], [16])];;
(* Lean: combinedExact6 *)
let () = c983c06q_exact c983c06q_combinedSignatures6 c983c06q_combinedQueries6;;
