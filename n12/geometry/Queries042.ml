(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries042.lean *)
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

(* Lean: query1344 *)
let HOQ_QUERY1344 = slq_hist 1344 (32768, 1, [4; 7; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1345 *)
let HOQ_QUERY1345 = slq_hist 1345 (32768, 1, [5; 7; 8],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1346 *)
let HOQ_QUERY1346 = slq_hist 1346 (32768, 1, [6; 7; 8],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1347 *)
let HOQ_QUERY1347 = slq_hist 1347 (32768, 1, [0; 1; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1348 *)
let HOQ_QUERY1348 = slq_hist 1348 (32768, 1, [0; 2; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1349 *)
let HOQ_QUERY1349 = slq_hist 1349 (32768, 1, [1; 2; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1350 *)
let HOQ_QUERY1350 = slq_hist 1350 (32768, 1, [0; 3; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1351 *)
let HOQ_QUERY1351 = slq_hist 1351 (32768, 1, [1; 3; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1352 *)
let HOQ_QUERY1352 = slq_hist 1352 (32768, 1, [2; 3; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1353 *)
let HOQ_QUERY1353 = slq_hist 1353 (32768, 1, [0; 4; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1354 *)
let HOQ_QUERY1354 = slq_hist 1354 (32768, 1, [1; 4; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "3"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1355 *)
let HOQ_QUERY1355 = slq_hist 1355 (32768, 1, [2; 4; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1356 *)
let HOQ_QUERY1356 = slq_hist 1356 (32768, 1, [3; 4; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1357 *)
let HOQ_QUERY1357 = slq_hist 1357 (32768, 1, [0; 5; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1358 *)
let HOQ_QUERY1358 = slq_hist 1358 (32768, 1, [1; 5; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1359 *)
let HOQ_QUERY1359 = slq_hist 1359 (32768, 1, [2; 5; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1360 *)
let HOQ_QUERY1360 = slq_hist 1360 (32768, 1, [3; 5; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1361 *)
let HOQ_QUERY1361 = slq_hist 1361 (32768, 1, [4; 5; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1362 *)
let HOQ_QUERY1362 = slq_hist 1362 (32768, 1, [0; 6; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1363 *)
let HOQ_QUERY1363 = slq_hist 1363 (32768, 1, [1; 6; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1364 *)
let HOQ_QUERY1364 = slq_hist 1364 (32768, 1, [2; 6; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1365 *)
let HOQ_QUERY1365 = slq_hist 1365 (32768, 1, [3; 6; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1366 *)
let HOQ_QUERY1366 = slq_hist 1366 (32768, 1, [4; 6; 9],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1367 *)
let HOQ_QUERY1367 = slq_hist 1367 (32768, 1, [5; 6; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1368 *)
let HOQ_QUERY1368 = slq_hist 1368 (32768, 1, [0; 7; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1369 *)
let HOQ_QUERY1369 = slq_hist 1369 (32768, 1, [1; 7; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1370 *)
let HOQ_QUERY1370 = slq_hist 1370 (32768, 1, [2; 7; 9],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1371 *)
let HOQ_QUERY1371 = slq_hist 1371 (32768, 1, [3; 7; 9],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1372 *)
let HOQ_QUERY1372 = slq_hist 1372 (32768, 1, [5; 7; 9],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1373 *)
let HOQ_QUERY1373 = slq_hist 1373 (32768, 1, [6; 7; 9],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1374 *)
let HOQ_QUERY1374 = slq_hist 1374 (32768, 1, [0; 8; 9],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1375 *)
let HOQ_QUERY1375 = slq_hist 1375 (32768, 1, [1; 8; 9],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
