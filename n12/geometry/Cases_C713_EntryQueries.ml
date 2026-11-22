(* ========================================================================= *)
(* Port of Compact/Cases/C713/EntryQueries.lean (namespace S12): direct       *)
(* single-owner domains of the C713 entry.  A Lean DirectSingleDomain         *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case713Family k  (SmallOwnerDomain.checked, whose private signature lists  *)
(* are just the query signatures) is                                        *)
(*   dsd_actual `c713eqb_family` k w : |- hdom fam mask k allowed               *)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C713EQS_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C713_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/EntryQuery00.ml";;
needs "n12/geometry/EntryQuery01.ml";;
needs "n12/geometry/EntryQuery02.ml";;
needs "n12/geometry/EntryQuery03.ml";;
needs "n12/geometry/EntryQuery04.ml";;
needs "n12/geometry/EntryQuery05.ml";;
needs "n12/geometry/EntryQuery06.ml";;
needs "n12/geometry/EntryQuery07.ml";;
needs "n12/geometry/EntryQuery08.ml";;
needs "n12/geometry/EntryQuery09.ml";;

(* the literal queries of EntryQuery00-03 used here are registered under c713eq_idx k *)
(* (EntryQuery04.ml) like those of EntryQuery04-09, so that dqueries can name them  *)
let _ = let (m, k, ow, uin, uout) = (12, 0, [0],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 125 (0, m, k, ow, uin, uout) C713EQ01_QUERY713_125;;
let _ = let (m, k, ow, uin, uout) = (12, 0, [1],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 126 (0, m, k, ow, uin, uout) C713EQ01_QUERY713_126;;
let _ = let (m, k, ow, uin, uout) = (12, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]) in c713eq_register 127 (0, m, k, ow, uin, uout) C713EQ01_QUERY713_127;;
let _ = let (m, k, ow, uin, uout) = (12, 0, [3],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 128 (0, m, k, ow, uin, uout) C713EQ02_QUERY713_128;;
let _ = let (m, k, ow, uin, uout) = (12, 0, [4],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 129 (0, m, k, ow, uin, uout) C713EQ02_QUERY713_129;;
let _ = let (m, k, ow, uin, uout) = (12, 0, [5],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 130 (0, m, k, ow, uin, uout) C713EQ02_QUERY713_130;;
let _ = let (m, k, ow, uin, uout) = (12, 0, [7],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 131 (0, m, k, ow, uin, uout) C713EQ02_QUERY713_131;;
let _ = let (m, k, ow, uin, uout) = (12, 0, [9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]) in c713eq_register 132 (0, m, k, ow, uin, uout) C713EQ02_QUERY713_132;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 1],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 199 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_199;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 2],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]) in c713eq_register 201 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_201;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [1; 2],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]) in c713eq_register 202 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_202;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 3],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 204 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_204;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [1; 3],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 205 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_205;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [2; 3],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]) in c713eq_register 206 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_206;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 4],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]) in c713eq_register 208 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_208;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [1; 4],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 209 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_209;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [2; 4],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 210 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_210;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [3; 4],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "2", nlin_rat "113/50")]) in c713eq_register 211 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_211;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 5],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 213 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_213;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [1; 5],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 214 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_214;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [2; 5],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]) in c713eq_register 215 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_215;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [3; 5],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 216 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_216;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [4; 5],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 217 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_217;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 6],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]) in c713eq_register 219 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_219;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [1; 6],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 220 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_220;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [2; 6],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 221 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_221;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [3; 6],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "2", nlin_rat "113/50")]) in c713eq_register 222 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_222;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [4; 6],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 223 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_223;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [5; 6],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 224 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_224;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 7],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]) in c713eq_register 226 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_226;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [1; 7],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 227 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_227;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [2; 7],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "87/50")]) in c713eq_register 228 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_228;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [3; 7],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]) in c713eq_register 229 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_229;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [4; 7],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 230 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_230;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [5; 7],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 231 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_231;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [6; 7],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]) in c713eq_register 232 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_232;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 8],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]) in c713eq_register 234 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_234;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [1; 8],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 235 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_235;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [2; 8],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 236 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_236;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [3; 8],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 237 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_237;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [4; 8],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]) in c713eq_register 238 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_238;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [5; 8],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 239 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_239;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [6; 8],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "72/25")],
  [(nlin_rat "3", nlin_rat "113/50")]) in c713eq_register 240 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_240;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [7; 8],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "3", nlin_rat "113/50")]) in c713eq_register 241 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_241;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [0; 9],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]) in c713eq_register 242 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_242;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [1; 9],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]) in c713eq_register 243 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_243;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [2; 9],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]) in c713eq_register 244 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_244;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [3; 9],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]) in c713eq_register 245 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_245;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [4; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 246 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_246;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [5; 9],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]) in c713eq_register 247 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_247;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [6; 9],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]) in c713eq_register 248 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_248;;
let _ = let (m, k, ow, uin, uout) = (32, 0, [8; 9],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]) in c713eq_register 249 (0, m, k, ow, uin, uout) C713EQ03_QUERY713_249;;

(* Lean: single713_0_0 *)
let c713eqs_single713_0_0 = { dmask = 1; dlower = 1; dupper = 2;
  dallowed = [[2]];
  dqueries = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53] };;
(* Lean: single713_0_0_checked *)
let C713EQS_SINGLE713_0_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_0_0;;
(* Lean: single713_0_1 *)
let c713eqs_single713_0_1 = { dmask = 1; dlower = 1; dupper = 1;
  dallowed = [[2]];
  dqueries = [54; 55; 58; 62; 67; 73; 80; 88; 97] };;
(* Lean: single713_0_1_checked *)
let C713EQS_SINGLE713_0_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_0_1;;
(* Lean: single713_1_0 *)
let c713eqs_single713_1_0 = { dmask = 2; dlower = 1; dupper = 2;
  dallowed = [[0]; [0; 2]];
  dqueries = [107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124; 125; 126; 127; 128; 129; 130; 131; 132; 133; 134; 135; 136; 137; 138; 139; 140; 141; 142; 143; 144; 145; 146; 147; 148; 149; 150; 151; 152; 153; 154; 155; 156; 157; 158; 159] };;
(* Lean: single713_1_0_checked *)
let C713EQS_SINGLE713_1_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_1_0;;
(* Lean: single713_1_1 *)
let c713eqs_single713_1_1 = { dmask = 2; dlower = 1; dupper = 1;
  dallowed = [[0]];
  dqueries = [160; 162; 165; 169; 174; 180; 187; 195; 204] };;
(* Lean: single713_1_1_checked *)
let C713EQS_SINGLE713_1_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_1_1;;
(* Lean: single713_2_0 *)
let c713eqs_single713_2_0 = { dmask = 12; dlower = 0; dupper = 1;
  dallowed = [[]; [6]; [8]];
  dqueries = [c713eq_idx 125; c713eq_idx 126; c713eq_idx 127; c713eq_idx 128; c713eq_idx 129; c713eq_idx 130; c713eq_idx 131; c713eq_idx 132] };;
(* Lean: single713_2_0_checked *)
let C713EQS_SINGLE713_2_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_2_0;;
(* Lean: single713_2_1 *)
let c713eqs_single713_2_1 = { dmask = 12; dlower = 0; dupper = 0;
  dallowed = [[]];
  dqueries = [] };;
(* Lean: single713_2_1_checked *)
let C713EQS_SINGLE713_2_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_2_1;;
(* Lean: single713_3_0 *)
let c713eqs_single713_3_0 = { dmask = 16; dlower = 1; dupper = 2;
  dallowed = [[7]];
  dqueries = [339; 340; 341; 342; 343; 344; 345; 346; 347; 348; 349; 350; 351; 352; 353; 354; 355; 356; 357; 358; 359; 360; 361; 362; 363; 364; 365; 366; 367; 368; 369; 370; 371; 372; 373; 374; 375; 376; 377; 378; 379; 380; 381; 382; 383; 384; 385; 386; 387; 388; 389; 390; 391; 392] };;
(* Lean: single713_3_0_checked *)
let C713EQS_SINGLE713_3_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_3_0;;
(* Lean: single713_3_1 *)
let c713eqs_single713_3_1 = { dmask = 16; dlower = 1; dupper = 1;
  dallowed = [[7]];
  dqueries = [393; 394; 395; 396; 397; 398; 399; 400; 401] };;
(* Lean: single713_3_1_checked *)
let C713EQS_SINGLE713_3_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_3_1;;
(* Lean: single713_4_0 *)
let c713eqs_single713_4_0 = { dmask = 32; dlower = 1; dupper = 2;
  dallowed = [[9]; [7; 9]];
  dqueries = [402; 403; c713eq_idx 199; 404; c713eq_idx 201; c713eq_idx 202; 405; c713eq_idx 204; c713eq_idx 205; c713eq_idx 206; 406; c713eq_idx 208; c713eq_idx 209; c713eq_idx 210; c713eq_idx 211; 407; c713eq_idx 213; c713eq_idx 214; c713eq_idx 215; c713eq_idx 216; c713eq_idx 217; 408; c713eq_idx 219; c713eq_idx 220; c713eq_idx 221; c713eq_idx 222; c713eq_idx 223; c713eq_idx 224; 409; c713eq_idx 226; c713eq_idx 227; c713eq_idx 228; c713eq_idx 229; c713eq_idx 230; c713eq_idx 231; c713eq_idx 232; 410; c713eq_idx 234; c713eq_idx 235; c713eq_idx 236; c713eq_idx 237; c713eq_idx 238; c713eq_idx 239; c713eq_idx 240; c713eq_idx 241; c713eq_idx 242; c713eq_idx 243; c713eq_idx 244; c713eq_idx 245; c713eq_idx 246; c713eq_idx 247; c713eq_idx 248; c713eq_idx 249] };;
(* Lean: single713_4_0_checked *)
let C713EQS_SINGLE713_4_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_4_0;;
(* Lean: single713_4_1 *)
let c713eqs_single713_4_1 = { dmask = 32; dlower = 1; dupper = 1;
  dallowed = [[9]];
  dqueries = [411; 412; 413; 414; 415; 416; c713eq_idx 256; c713eq_idx 257; c713eq_idx 258] };;
(* Lean: single713_4_1_checked *)
let C713EQS_SINGLE713_4_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_4_1;;
(* Lean: single713_5_0 *)
let c713eqs_single713_5_0 = { dmask = 192; dlower = 0; dupper = 1;
  dallowed = [[]; [1]; [3]];
  dqueries = [c713eq_idx 259; c713eq_idx 260; c713eq_idx 261; c713eq_idx 262; c713eq_idx 263; c713eq_idx 264; c713eq_idx 265; c713eq_idx 266] };;
(* Lean: single713_5_0_checked *)
let C713EQS_SINGLE713_5_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_5_0;;
(* Lean: single713_5_1 *)
let c713eqs_single713_5_1 = { dmask = 192; dlower = 0; dupper = 0;
  dallowed = [[]];
  dqueries = [] };;
(* Lean: single713_5_1_checked *)
let C713EQS_SINGLE713_5_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_5_1;;
(* Lean: single713_6_0 *)
let c713eqs_single713_6_0 = { dmask = 512; dlower = 1; dupper = 2;
  dallowed = [[4]; [2; 4]; [4; 5]; [6]; [4; 6]; [8]; [4; 8]; [5; 8]; [6; 8]; [4; 9]; [8; 9]];
  dqueries = [c713eq_idx 268; c713eq_idx 269; c713eq_idx 270; c713eq_idx 271; c713eq_idx 272; c713eq_idx 273; c713eq_idx 274; c713eq_idx 275; c713eq_idx 276; c713eq_idx 277; c713eq_idx 278; c713eq_idx 279; c713eq_idx 280; c713eq_idx 281; c713eq_idx 282; c713eq_idx 283; c713eq_idx 284; c713eq_idx 285; c713eq_idx 286; c713eq_idx 287; c713eq_idx 288; c713eq_idx 289; c713eq_idx 290; c713eq_idx 291; c713eq_idx 292; c713eq_idx 293; c713eq_idx 294; c713eq_idx 295; c713eq_idx 296; c713eq_idx 297; c713eq_idx 298; c713eq_idx 299; c713eq_idx 300; c713eq_idx 301; c713eq_idx 302; c713eq_idx 303; c713eq_idx 304; c713eq_idx 305; c713eq_idx 306; c713eq_idx 307; c713eq_idx 308; c713eq_idx 309; c713eq_idx 310; c713eq_idx 311] };;
(* Lean: single713_6_0_checked *)
let C713EQS_SINGLE713_6_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_6_0;;
(* Lean: single713_6_1 *)
let c713eqs_single713_6_1 = { dmask = 512; dlower = 1; dupper = 1;
  dallowed = [[5]; [6]; [8]];
  dqueries = [c713eq_idx 312; c713eq_idx 313; c713eq_idx 314; c713eq_idx 315; c713eq_idx 316; c713eq_idx 317; c713eq_idx 318] };;
(* Lean: single713_6_1_checked *)
let C713EQS_SINGLE713_6_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_6_1;;
(* Lean: single713_7_0 *)
let c713eqs_single713_7_0 = { dmask = 2304; dlower = 0; dupper = 1;
  dallowed = [[]; [0]; [1]; [2]; [3]; [4]; [5]];
  dqueries = [c713eq_idx 330; c713eq_idx 331; c713eq_idx 332; c713eq_idx 333] };;
(* Lean: single713_7_0_checked *)
let C713EQS_SINGLE713_7_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_7_0;;
(* Lean: single713_7_1 *)
let c713eqs_single713_7_1 = { dmask = 2304; dlower = 1; dupper = 1;
  dallowed = [[3]];
  dqueries = [c713eq_idx 334; c713eq_idx 335; c713eq_idx 336; c713eq_idx 337; c713eq_idx 338; c713eq_idx 339; c713eq_idx 340; c713eq_idx 341; c713eq_idx 342] };;
(* Lean: single713_7_1_checked *)
let C713EQS_SINGLE713_7_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_7_1;;
(* Lean: single713_8_0 *)
let c713eqs_single713_8_0 = { dmask = 4096; dlower = 1; dupper = 2;
  dallowed = [[0]; [1]; [0; 1]; [0; 2]; [1; 3]];
  dqueries = [c713eq_idx 343; c713eq_idx 344; c713eq_idx 345; c713eq_idx 346; c713eq_idx 347; c713eq_idx 348; c713eq_idx 349; c713eq_idx 350; c713eq_idx 351; c713eq_idx 352; c713eq_idx 353; c713eq_idx 354; c713eq_idx 355; c713eq_idx 356; c713eq_idx 357; c713eq_idx 358; c713eq_idx 359; c713eq_idx 360; c713eq_idx 361; c713eq_idx 362; c713eq_idx 363; c713eq_idx 364; c713eq_idx 365; c713eq_idx 366; c713eq_idx 367; c713eq_idx 368; c713eq_idx 369; c713eq_idx 370; c713eq_idx 371; c713eq_idx 372; c713eq_idx 373; c713eq_idx 374; c713eq_idx 375; c713eq_idx 376; c713eq_idx 377; c713eq_idx 378; c713eq_idx 379; c713eq_idx 380; c713eq_idx 381; c713eq_idx 382; c713eq_idx 383; c713eq_idx 384; c713eq_idx 385; c713eq_idx 386; c713eq_idx 387; c713eq_idx 388; c713eq_idx 389; c713eq_idx 390; c713eq_idx 391; c713eq_idx 392] };;
(* Lean: single713_8_0_checked *)
let C713EQS_SINGLE713_8_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_8_0;;
(* Lean: single713_8_1 *)
let c713eqs_single713_8_1 = { dmask = 4096; dlower = 1; dupper = 1;
  dallowed = [[0]; [1]; [3]];
  dqueries = [c713eq_idx 393; c713eq_idx 394; c713eq_idx 395; c713eq_idx 396; c713eq_idx 397; c713eq_idx 398; c713eq_idx 399] };;
(* Lean: single713_8_1_checked *)
let C713EQS_SINGLE713_8_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_8_1;;
(* Lean: single713_9_0 *)
let c713eqs_single713_9_0 = { dmask = 8192; dlower = 1; dupper = 2;
  dallowed = [[2]; [4]; [2; 4]; [6]; [2; 6]; [4; 6]];
  dqueries = [c713eq_idx 409; c713eq_idx 410; c713eq_idx 411; c713eq_idx 412; c713eq_idx 413; c713eq_idx 414; c713eq_idx 415; c713eq_idx 416; c713eq_idx 417; c713eq_idx 418; c713eq_idx 419; c713eq_idx 420; c713eq_idx 421; c713eq_idx 422; c713eq_idx 423; c713eq_idx 424; c713eq_idx 425; c713eq_idx 426; c713eq_idx 427; c713eq_idx 428; c713eq_idx 429; c713eq_idx 430; c713eq_idx 431; c713eq_idx 432; c713eq_idx 433; c713eq_idx 434; c713eq_idx 435; c713eq_idx 436; c713eq_idx 437; c713eq_idx 438; c713eq_idx 439; c713eq_idx 440; c713eq_idx 441; c713eq_idx 442; c713eq_idx 443; c713eq_idx 444; c713eq_idx 445; c713eq_idx 446; c713eq_idx 447; c713eq_idx 448; c713eq_idx 449; c713eq_idx 450; c713eq_idx 451; c713eq_idx 452; c713eq_idx 453; c713eq_idx 454; c713eq_idx 455; c713eq_idx 456; c713eq_idx 457] };;
(* Lean: single713_9_0_checked *)
let C713EQS_SINGLE713_9_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_9_0;;
(* Lean: single713_9_1 *)
let c713eqs_single713_9_1 = { dmask = 8192; dlower = 1; dupper = 1;
  dallowed = [[2]; [5]];
  dqueries = [c713eq_idx 458; c713eq_idx 459; c713eq_idx 460; c713eq_idx 461; c713eq_idx 462; c713eq_idx 463; c713eq_idx 464; c713eq_idx 465] };;
(* Lean: single713_9_1_checked *)
let C713EQS_SINGLE713_9_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_9_1;;
(* Lean: single713_10_0 *)
let c713eqs_single713_10_0 = { dmask = 16384; dlower = 1; dupper = 2;
  dallowed = [[8]; [6; 8]; [9]; [7; 9]; [8; 9]];
  dqueries = [c713eq_idx 474; c713eq_idx 475; c713eq_idx 476; c713eq_idx 477; c713eq_idx 478; c713eq_idx 479; c713eq_idx 480; c713eq_idx 481; c713eq_idx 482; c713eq_idx 483; c713eq_idx 484; c713eq_idx 485; c713eq_idx 486; c713eq_idx 487; c713eq_idx 488; c713eq_idx 489; c713eq_idx 490; c713eq_idx 491; c713eq_idx 492; c713eq_idx 493; c713eq_idx 494; c713eq_idx 495; c713eq_idx 496; c713eq_idx 497; c713eq_idx 498; c713eq_idx 499; c713eq_idx 500; c713eq_idx 501; c713eq_idx 502; c713eq_idx 503; c713eq_idx 504; c713eq_idx 505; c713eq_idx 506; c713eq_idx 507; c713eq_idx 508; c713eq_idx 509; c713eq_idx 510; c713eq_idx 511; c713eq_idx 512; c713eq_idx 513; c713eq_idx 514; c713eq_idx 515; c713eq_idx 516; c713eq_idx 517; c713eq_idx 518; c713eq_idx 519; c713eq_idx 520; c713eq_idx 521; c713eq_idx 522; c713eq_idx 523] };;
(* Lean: single713_10_0_checked *)
let C713EQS_SINGLE713_10_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_10_0;;
(* Lean: single713_10_1 *)
let c713eqs_single713_10_1 = { dmask = 16384; dlower = 1; dupper = 1;
  dallowed = [[6]; [8]; [9]];
  dqueries = [c713eq_idx 524; c713eq_idx 525; c713eq_idx 526; c713eq_idx 527; c713eq_idx 528; c713eq_idx 529; c713eq_idx 530] };;
(* Lean: single713_10_1_checked *)
let C713EQS_SINGLE713_10_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_10_1;;
(* Lean: single713_11_0 *)
let c713eqs_single713_11_0 = { dmask = 32768; dlower = 1; dupper = 2;
  dallowed = [[3]; [5]; [3; 5]; [7]; [3; 7]; [5; 7]];
  dqueries = [c713eq_idx 540; c713eq_idx 541; c713eq_idx 542; c713eq_idx 543; c713eq_idx 544; c713eq_idx 545; c713eq_idx 546; c713eq_idx 547; c713eq_idx 548; c713eq_idx 549; c713eq_idx 550; c713eq_idx 551; c713eq_idx 552; c713eq_idx 553; c713eq_idx 554; c713eq_idx 555; c713eq_idx 556; c713eq_idx 557; c713eq_idx 558; c713eq_idx 559; c713eq_idx 560; c713eq_idx 561; c713eq_idx 562; c713eq_idx 563; c713eq_idx 564; c713eq_idx 565; c713eq_idx 566; c713eq_idx 567; c713eq_idx 568; c713eq_idx 569; c713eq_idx 570; c713eq_idx 571; c713eq_idx 572; c713eq_idx 573; c713eq_idx 574; c713eq_idx 575; c713eq_idx 576; c713eq_idx 577; c713eq_idx 578; c713eq_idx 579; c713eq_idx 580; c713eq_idx 581; c713eq_idx 582; c713eq_idx 583; c713eq_idx 584; c713eq_idx 585; c713eq_idx 586; c713eq_idx 587; c713eq_idx 588] };;
(* Lean: single713_11_0_checked *)
let C713EQS_SINGLE713_11_0_CHECKED = dsd_actual `c713eqb_family` 0 c713eqs_single713_11_0;;
(* Lean: single713_11_1 *)
let c713eqs_single713_11_1 = { dmask = 32768; dlower = 1; dupper = 1;
  dallowed = [[4]; [7]];
  dqueries = [c713eq_idx 589; c713eq_idx 590; c713eq_idx 591; c713eq_idx 592; c713eq_idx 593; c713eq_idx 594; c713eq_idx 595; c713eq_idx 596] };;
(* Lean: single713_11_1_checked *)
let C713EQS_SINGLE713_11_1_CHECKED = dsd_actual `c713eqb_family` 1 c713eqs_single713_11_1;;
