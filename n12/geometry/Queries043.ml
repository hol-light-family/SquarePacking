(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries043.lean *)
(* (N12Compact.HistoricalOwnership.Queries): exact inherited local queries.  Each Lean *)
(* checked_local_query is registered with slq_hist n (SharedLocalQueries.ml):*)
(* the HOL kernel re-proves the query from its inside / outside points     *)
(* (a .hull query: its three hull points inside, its fourth point outside; *)
(* a .four query: the transformed FourPointDatum A, B inside, P, E outside; *)
(* a .short query: its cluster points inside, the pattern points outside).  *)
(* HOQ_QUERYn : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>  *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query1376 *)
let HOQ_QUERY1376 = slq_hist 1376 (32768, 1, [2; 8; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1377 *)
let HOQ_QUERY1377 = slq_hist 1377 (32768, 1, [3; 8; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1378 *)
let HOQ_QUERY1378 = slq_hist 1378 (32768, 1, [4; 8; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1379 *)
let HOQ_QUERY1379 = slq_hist 1379 (32768, 1, [5; 8; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1380 *)
let HOQ_QUERY1380 = slq_hist 1380 (32768, 1, [6; 8; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1381 *)
let HOQ_QUERY1381 = slq_hist 1381 (32768, 1, [7; 8; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1382 *)
let HOQ_QUERY1382 = slq_hist 1382 (32768, 2, [3; 14; 17; 19],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1383 *)
let HOQ_QUERY1383 = slq_hist 1383 (32768, 2, [5; 11; 14; 17],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1384 *)
let HOQ_QUERY1384 = slq_hist 1384 (32768, 2, [5; 14; 17; 19],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1385 *)
let HOQ_QUERY1385 = slq_hist 1385 (32768, 2, [7; 11; 14; 17],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1386 *)
let HOQ_QUERY1386 = slq_hist 1386 (12, 2, [8; 15],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
(* Lean: query1387 *)
let HOQ_QUERY1387 = slq_hist 1387 (48, 0, [0],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1388 *)
let HOQ_QUERY1388 = slq_hist 1388 (48, 0, [1],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1389 *)
let HOQ_QUERY1389 = slq_hist 1389 (48, 0, [2],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1390 *)
let HOQ_QUERY1390 = slq_hist 1390 (48, 0, [3],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query1391 *)
let HOQ_QUERY1391 = slq_hist 1391 (48, 0, [4],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1392 *)
let HOQ_QUERY1392 = slq_hist 1392 (48, 0, [5],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1393 *)
let HOQ_QUERY1393 = slq_hist 1393 (48, 0, [6],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1394 *)
let HOQ_QUERY1394 = slq_hist 1394 (48, 0, [8],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query1395 *)
let HOQ_QUERY1395 = slq_hist 1395 (48, 1, [0],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1396 *)
let HOQ_QUERY1396 = slq_hist 1396 (48, 1, [1],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1397 *)
let HOQ_QUERY1397 = slq_hist 1397 (48, 1, [2],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1398 *)
let HOQ_QUERY1398 = slq_hist 1398 (48, 1, [3],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1399 *)
let HOQ_QUERY1399 = slq_hist 1399 (48, 1, [4],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "3")]);;
(* Lean: query1400 *)
let HOQ_QUERY1400 = slq_hist 1400 (48, 1, [5],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1401 *)
let HOQ_QUERY1401 = slq_hist 1401 (48, 1, [6],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1402 *)
let HOQ_QUERY1402 = slq_hist 1402 (48, 1, [8],
  [(nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query1403 *)
let HOQ_QUERY1403 = slq_hist 1403 (48, 2, [17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query1404 *)
let HOQ_QUERY1404 = slq_hist 1404 (48, 2, [9],
  [(nlin_rat "3", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "1543/500")],
  [(nlin_rat "3", nlin_rat "12/5")]);;
(* Lean: query1405 *)
let HOQ_QUERY1405 = slq_hist 1405 (48, 2, [9; 17],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query1406 *)
let HOQ_QUERY1406 = slq_hist 1406 (192, 2, [1; 14],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "1", nlin_rat "1543/500")],
  [(nlin_rat "1", nlin_rat "12/5")]);;
(* Lean: query1407 *)
let HOQ_QUERY1407 = slq_hist 1407 (1024, 0, [0; 1],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
