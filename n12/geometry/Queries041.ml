(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries041.lean *)
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

(* Lean: query1312 *)
let HOQ_QUERY1312 = slq_hist 1312 (32768, 1, [4; 5; 7],
  [(nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1313 *)
let HOQ_QUERY1313 = slq_hist 1313 (32768, 1, [0; 6; 7],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1314 *)
let HOQ_QUERY1314 = slq_hist 1314 (32768, 1, [1; 6; 7],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "2"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1315 *)
let HOQ_QUERY1315 = slq_hist 1315 (32768, 1, [2; 6; 7],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1316 *)
let HOQ_QUERY1316 = slq_hist 1316 (32768, 1, [3; 6; 7],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "47/20"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1317 *)
let HOQ_QUERY1317 = slq_hist 1317 (32768, 1, [4; 6; 7],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1318 *)
let HOQ_QUERY1318 = slq_hist 1318 (32768, 1, [5; 6; 7],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "47/20", nlin_rat "47/20"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1319 *)
let HOQ_QUERY1319 = slq_hist 1319 (32768, 1, [0; 1; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1320 *)
let HOQ_QUERY1320 = slq_hist 1320 (32768, 1, [0; 2; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1321 *)
let HOQ_QUERY1321 = slq_hist 1321 (32768, 1, [1; 2; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1322 *)
let HOQ_QUERY1322 = slq_hist 1322 (32768, 1, [0; 3; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1323 *)
let HOQ_QUERY1323 = slq_hist 1323 (32768, 1, [1; 3; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "87/50", nlin_rat "2"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1324 *)
let HOQ_QUERY1324 = slq_hist 1324 (32768, 1, [2; 3; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1325 *)
let HOQ_QUERY1325 = slq_hist 1325 (32768, 1, [0; 4; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1326 *)
let HOQ_QUERY1326 = slq_hist 1326 (32768, 1, [1; 4; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1327 *)
let HOQ_QUERY1327 = slq_hist 1327 (32768, 1, [2; 4; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "87/50", nlin_rat "2")]);;
(* Lean: query1328 *)
let HOQ_QUERY1328 = slq_hist 1328 (32768, 1, [3; 4; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1329 *)
let HOQ_QUERY1329 = slq_hist 1329 (32768, 1, [0; 5; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1330 *)
let HOQ_QUERY1330 = slq_hist 1330 (32768, 1, [1; 5; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1331 *)
let HOQ_QUERY1331 = slq_hist 1331 (32768, 1, [2; 5; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1332 *)
let HOQ_QUERY1332 = slq_hist 1332 (32768, 1, [3; 5; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1333 *)
let HOQ_QUERY1333 = slq_hist 1333 (32768, 1, [4; 5; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1334 *)
let HOQ_QUERY1334 = slq_hist 1334 (32768, 1, [0; 6; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1335 *)
let HOQ_QUERY1335 = slq_hist 1335 (32768, 1, [1; 6; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1336 *)
let HOQ_QUERY1336 = slq_hist 1336 (32768, 1, [2; 6; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1337 *)
let HOQ_QUERY1337 = slq_hist 1337 (32768, 1, [3; 6; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1338 *)
let HOQ_QUERY1338 = slq_hist 1338 (32768, 1, [4; 6; 8],
  [(nlin_rat "87/50", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "2", nlin_rat "1543/500")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query1339 *)
let HOQ_QUERY1339 = slq_hist 1339 (32768, 1, [5; 6; 8],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query1340 *)
let HOQ_QUERY1340 = slq_hist 1340 (32768, 1, [0; 7; 8],
  [(nlin_rat "1", nlin_rat "8/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query1341 *)
let HOQ_QUERY1341 = slq_hist 1341 (32768, 1, [1; 7; 8],
  [(nlin_rat "1", nlin_rat "12/5"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query1342 *)
let HOQ_QUERY1342 = slq_hist 1342 (32768, 1, [2; 7; 8],
  [(nlin_rat "87/50", nlin_rat "1"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
(* Lean: query1343 *)
let HOQ_QUERY1343 = slq_hist 1343 (32768, 1, [3; 7; 8],
  [(nlin_rat "87/50", nlin_rat "2"); (nlin_rat "3", nlin_rat "8/5"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "113/50", nlin_rat "2")]);;
