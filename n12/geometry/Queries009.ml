(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries009.lean                          *)
(* (N12Compact.HistoricalOwnership.Queries): exact historical local queries.*)
(* Each Lean checked_local_query is registered with slq_hist n               *)
(* (SharedLocalQueries.ml): the HOL kernel re-proves the query from its     *)
(* inside / outside points (a .hull query: its three hull points inside,    *)
(* its fourth point outside; a .four query: the transformed FourPointDatum *)
(* A, B inside, P, E outside; a .short query: its cluster points inside,   *)
(* the transformed pattern points outside).                                 *)
(* HOQ_QUERYN : |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==>          *)
(*   a * a + b * b = &1 ==> owalls .. ==> owned .. = set_of_list (bits m)   *)
(*   ==> auxown k c1 c2 a b l = set_of_list owned ==> F   (LocalQuery.sound) *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: query288 *)
let HOQ_QUERY288 = slq_hist 288 (2, 1, [1; 2; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query289 *)
let HOQ_QUERY289 = slq_hist 289 (2, 1, [0; 3; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query290 *)
let HOQ_QUERY290 = slq_hist 290 (2, 1, [1; 3; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query291 *)
let HOQ_QUERY291 = slq_hist 291 (2, 1, [2; 3; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query292 *)
let HOQ_QUERY292 = slq_hist 292 (2, 1, [0; 4; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query293 *)
let HOQ_QUERY293 = slq_hist 293 (2, 1, [1; 4; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query294 *)
let HOQ_QUERY294 = slq_hist 294 (2, 1, [2; 4; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query295 *)
let HOQ_QUERY295 = slq_hist 295 (2, 1, [3; 4; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query296 *)
let HOQ_QUERY296 = slq_hist 296 (2, 1, [0; 5; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query297 *)
let HOQ_QUERY297 = slq_hist 297 (2, 1, [1; 5; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query298 *)
let HOQ_QUERY298 = slq_hist 298 (2, 1, [2; 5; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query299 *)
let HOQ_QUERY299 = slq_hist 299 (2, 1, [3; 5; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query300 *)
let HOQ_QUERY300 = slq_hist 300 (2, 1, [4; 5; 6],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query301 *)
let HOQ_QUERY301 = slq_hist 301 (2, 1, [0; 1; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query302 *)
let HOQ_QUERY302 = slq_hist 302 (2, 1, [0; 2; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "87/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query303 *)
let HOQ_QUERY303 = slq_hist 303 (2, 1, [1; 2; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query304 *)
let HOQ_QUERY304 = slq_hist 304 (2, 1, [0; 3; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query305 *)
let HOQ_QUERY305 = slq_hist 305 (2, 1, [1; 3; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query306 *)
let HOQ_QUERY306 = slq_hist 306 (2, 1, [2; 3; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query307 *)
let HOQ_QUERY307 = slq_hist 307 (2, 1, [0; 4; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query308 *)
let HOQ_QUERY308 = slq_hist 308 (2, 1, [1; 4; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query309 *)
let HOQ_QUERY309 = slq_hist 309 (2, 1, [2; 4; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query310 *)
let HOQ_QUERY310 = slq_hist 310 (2, 1, [3; 4; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query311 *)
let HOQ_QUERY311 = slq_hist 311 (2, 1, [0; 5; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "113/50", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query312 *)
let HOQ_QUERY312 = slq_hist 312 (2, 1, [1; 5; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query313 *)
let HOQ_QUERY313 = slq_hist 313 (2, 1, [2; 5; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query314 *)
let HOQ_QUERY314 = slq_hist 314 (2, 1, [3; 5; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query315 *)
let HOQ_QUERY315 = slq_hist 315 (2, 1, [4; 5; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query316 *)
let HOQ_QUERY316 = slq_hist 316 (2, 1, [0; 6; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query317 *)
let HOQ_QUERY317 = slq_hist 317 (2, 1, [1; 6; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "457/500", nlin_rat "2")]);;
(* Lean: query318 *)
let HOQ_QUERY318 = slq_hist 318 (2, 1, [2; 6; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query319 *)
let HOQ_QUERY319 = slq_hist 319 (2, 1, [3; 6; 7],
  [(nlin_rat "19/25", nlin_rat "187/100"); (nlin_rat "457/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
