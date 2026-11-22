(* ========================================================================= *)
(* Port of Compact/HistoricalOwnership/Queries007.lean                          *)
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

(* Lean: query224 *)
let HOQ_QUERY224 = slq_hist 224 (1, 1, [1; 7; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query225 *)
let HOQ_QUERY225 = slq_hist 225 (1, 1, [2; 7; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query226 *)
let HOQ_QUERY226 = slq_hist 226 (1, 1, [3; 7; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query227 *)
let HOQ_QUERY227 = slq_hist 227 (1, 1, [4; 7; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query228 *)
let HOQ_QUERY228 = slq_hist 228 (1, 1, [5; 7; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query229 *)
let HOQ_QUERY229 = slq_hist 229 (1, 1, [6; 7; 8],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query230 *)
let HOQ_QUERY230 = slq_hist 230 (1, 1, [0; 1; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query231 *)
let HOQ_QUERY231 = slq_hist 231 (1, 1, [0; 2; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query232 *)
let HOQ_QUERY232 = slq_hist 232 (1, 1, [1; 2; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query233 *)
let HOQ_QUERY233 = slq_hist 233 (1, 1, [0; 3; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query234 *)
let HOQ_QUERY234 = slq_hist 234 (1, 1, [1; 3; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query235 *)
let HOQ_QUERY235 = slq_hist 235 (1, 1, [2; 3; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query236 *)
let HOQ_QUERY236 = slq_hist 236 (1, 1, [0; 4; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query237 *)
let HOQ_QUERY237 = slq_hist 237 (1, 1, [1; 4; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query238 *)
let HOQ_QUERY238 = slq_hist 238 (1, 1, [2; 4; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query239 *)
let HOQ_QUERY239 = slq_hist 239 (1, 1, [3; 4; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query240 *)
let HOQ_QUERY240 = slq_hist 240 (1, 1, [0; 5; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query241 *)
let HOQ_QUERY241 = slq_hist 241 (1, 1, [1; 5; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query242 *)
let HOQ_QUERY242 = slq_hist 242 (1, 1, [2; 5; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500")]);;
(* Lean: query243 *)
let HOQ_QUERY243 = slq_hist 243 (1, 1, [3; 5; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query244 *)
let HOQ_QUERY244 = slq_hist 244 (1, 1, [4; 5; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query245 *)
let HOQ_QUERY245 = slq_hist 245 (1, 1, [0; 6; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "12/5"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query246 *)
let HOQ_QUERY246 = slq_hist 246 (1, 1, [1; 6; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query247 *)
let HOQ_QUERY247 = slq_hist 247 (1, 1, [2; 6; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query248 *)
let HOQ_QUERY248 = slq_hist 248 (1, 1, [3; 6; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query249 *)
let HOQ_QUERY249 = slq_hist 249 (1, 1, [4; 6; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query250 *)
let HOQ_QUERY250 = slq_hist 250 (1, 1, [5; 6; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "87/50", nlin_rat "1")]);;
(* Lean: query251 *)
let HOQ_QUERY251 = slq_hist 251 (1, 1, [0; 7; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query252 *)
let HOQ_QUERY252 = slq_hist 252 (1, 1, [1; 7; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "1", nlin_rat "8/5")]);;
(* Lean: query253 *)
let HOQ_QUERY253 = slq_hist 253 (1, 1, [2; 7; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query254 *)
let HOQ_QUERY254 = slq_hist 254 (1, 1, [3; 7; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query255 *)
let HOQ_QUERY255 = slq_hist 255 (1, 1, [4; 7; 9],
  [(nlin_rat "1", nlin_rat "457/500"); (nlin_rat "187/100", nlin_rat "19/25"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
