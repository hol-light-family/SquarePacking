(* ========================================================================= *)
(* Port of Compact/Cases/C713/EntryQuery03.lean (namespace S12): the exact   *)
(* local queries of the C713 entry.  A Lean alias                             *)
(*   def queryC_j : LocalQuery := localQueryN  with  c713_query_at ..._checked  *)
(* is slq_select N (the Phase-1 local query N of S12.localQueries re-proved  *)
(* by the kernel; the Lean chunk index is only the decide mechanism), giving  *)
(* (mask, kind, owned, |- LocalQuery.sound); a literal query proved by        *)
(* decide is registered with slq_new from its inside / outside points (.hull:*)
(* three hull points inside, target outside; .four: the transformed          *)
(* FourPointDatum A, B inside, P, E outside), giving |- LocalQuery.sound:      *)
(*   |- !c1 c2 a b l. &1 < l ==> l <= &1001 / &1000 ==> a * a + b * b = &1    *)
(*        ==> owalls .. ==> owned .. = set_of_list (bits m)                   *)
(*        ==> auxown k c1 c2 a b l = set_of_list owned ==> F                  *)
(* Both register the query in LQ_TABLE for the domain checkers.               *)
(* Tag C713EQ03_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C713_EntryQueryBase.ml";;

(* Lean: query713_192, query713_192_checked *)
let C713EQ03_QUERY713_192 = slq_select 397;;
(* Lean: query713_193, query713_193_checked *)
let C713EQ03_QUERY713_193 = slq_select 398;;
(* Lean: query713_194, query713_194_checked *)
let C713EQ03_QUERY713_194 = slq_select 399;;
(* Lean: query713_195, query713_195_checked *)
let C713EQ03_QUERY713_195 = slq_select 400;;
(* Lean: query713_196, query713_196_checked *)
let C713EQ03_QUERY713_196 = slq_select 401;;
(* Lean: query713_197, query713_197_checked *)
let C713EQ03_QUERY713_197 = slq_select 402;;
(* Lean: query713_198, query713_198_checked *)
let C713EQ03_QUERY713_198 = slq_select 403;;
(* Lean: query713_199, query713_199_checked *)
let C713EQ03_QUERY713_199 = slq_new (32, 0, [0; 1],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_200, query713_200_checked *)
let C713EQ03_QUERY713_200 = slq_select 404;;
(* Lean: query713_201, query713_201_checked *)
let C713EQ03_QUERY713_201 = slq_new (32, 0, [0; 2],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query713_202, query713_202_checked *)
let C713EQ03_QUERY713_202 = slq_new (32, 0, [1; 2],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query713_203, query713_203_checked *)
let C713EQ03_QUERY713_203 = slq_select 405;;
(* Lean: query713_204, query713_204_checked *)
let C713EQ03_QUERY713_204 = slq_new (32, 0, [0; 3],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_205, query713_205_checked *)
let C713EQ03_QUERY713_205 = slq_new (32, 0, [1; 3],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_206, query713_206_checked *)
let C713EQ03_QUERY713_206 = slq_new (32, 0, [2; 3],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query713_207, query713_207_checked *)
let C713EQ03_QUERY713_207 = slq_select 406;;
(* Lean: query713_208, query713_208_checked *)
let C713EQ03_QUERY713_208 = slq_new (32, 0, [0; 4],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query713_209, query713_209_checked *)
let C713EQ03_QUERY713_209 = slq_new (32, 0, [1; 4],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_210, query713_210_checked *)
let C713EQ03_QUERY713_210 = slq_new (32, 0, [2; 4],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_211, query713_211_checked *)
let C713EQ03_QUERY713_211 = slq_new (32, 0, [3; 4],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query713_212, query713_212_checked *)
let C713EQ03_QUERY713_212 = slq_select 407;;
(* Lean: query713_213, query713_213_checked *)
let C713EQ03_QUERY713_213 = slq_new (32, 0, [0; 5],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_214, query713_214_checked *)
let C713EQ03_QUERY713_214 = slq_new (32, 0, [1; 5],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_215, query713_215_checked *)
let C713EQ03_QUERY713_215 = slq_new (32, 0, [2; 5],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query713_216, query713_216_checked *)
let C713EQ03_QUERY713_216 = slq_new (32, 0, [3; 5],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_217, query713_217_checked *)
let C713EQ03_QUERY713_217 = slq_new (32, 0, [4; 5],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_218, query713_218_checked *)
let C713EQ03_QUERY713_218 = slq_select 408;;
(* Lean: query713_219, query713_219_checked *)
let C713EQ03_QUERY713_219 = slq_new (32, 0, [0; 6],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "33/20", nlin_rat "33/20")]);;
(* Lean: query713_220, query713_220_checked *)
let C713EQ03_QUERY713_220 = slq_new (32, 0, [1; 6],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_221, query713_221_checked *)
let C713EQ03_QUERY713_221 = slq_new (32, 0, [2; 6],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_222, query713_222_checked *)
let C713EQ03_QUERY713_222 = slq_new (32, 0, [3; 6],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query713_223, query713_223_checked *)
let C713EQ03_QUERY713_223 = slq_new (32, 0, [4; 6],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_224, query713_224_checked *)
let C713EQ03_QUERY713_224 = slq_new (32, 0, [5; 6],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_225, query713_225_checked *)
let C713EQ03_QUERY713_225 = slq_select 409;;
(* Lean: query713_226, query713_226_checked *)
let C713EQ03_QUERY713_226 = slq_new (32, 0, [0; 7],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query713_227, query713_227_checked *)
let C713EQ03_QUERY713_227 = slq_new (32, 0, [1; 7],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_228, query713_228_checked *)
let C713EQ03_QUERY713_228 = slq_new (32, 0, [2; 7],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query713_229, query713_229_checked *)
let C713EQ03_QUERY713_229 = slq_new (32, 0, [3; 7],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query713_230, query713_230_checked *)
let C713EQ03_QUERY713_230 = slq_new (32, 0, [4; 7],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_231, query713_231_checked *)
let C713EQ03_QUERY713_231 = slq_new (32, 0, [5; 7],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_232, query713_232_checked *)
let C713EQ03_QUERY713_232 = slq_new (32, 0, [6; 7],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query713_233, query713_233_checked *)
let C713EQ03_QUERY713_233 = slq_select 410;;
(* Lean: query713_234, query713_234_checked *)
let C713EQ03_QUERY713_234 = slq_new (32, 0, [0; 8],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "87/50")]);;
(* Lean: query713_235, query713_235_checked *)
let C713EQ03_QUERY713_235 = slq_new (32, 0, [1; 8],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_236, query713_236_checked *)
let C713EQ03_QUERY713_236 = slq_new (32, 0, [2; 8],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_237, query713_237_checked *)
let C713EQ03_QUERY713_237 = slq_new (32, 0, [3; 8],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_238, query713_238_checked *)
let C713EQ03_QUERY713_238 = slq_new (32, 0, [4; 8],
  [(nlin_rat "2", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query713_239, query713_239_checked *)
let C713EQ03_QUERY713_239 = slq_new (32, 0, [5; 8],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_240, query713_240_checked *)
let C713EQ03_QUERY713_240 = slq_new (32, 0, [6; 8],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "3", nlin_rat "72/25")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query713_241, query713_241_checked *)
let C713EQ03_QUERY713_241 = slq_new (32, 0, [7; 8],
  [(nlin_rat "12/5", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100")],
  [(nlin_rat "3", nlin_rat "113/50")]);;
(* Lean: query713_242, query713_242_checked *)
let C713EQ03_QUERY713_242 = slq_new (32, 0, [0; 9],
  [(nlin_rat "1", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "113/50")]);;
(* Lean: query713_243, query713_243_checked *)
let C713EQ03_QUERY713_243 = slq_new (32, 0, [1; 9],
  [(nlin_rat "1", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: query713_244, query713_244_checked *)
let C713EQ03_QUERY713_244 = slq_new (32, 0, [2; 9],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_245, query713_245_checked *)
let C713EQ03_QUERY713_245 = slq_new (32, 0, [3; 9],
  [(nlin_rat "8/5", nlin_rat "3"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "12/5", nlin_rat "3")]);;
(* Lean: query713_246, query713_246_checked *)
let C713EQ03_QUERY713_246 = slq_new (32, 0, [4; 9],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_247, query713_247_checked *)
let C713EQ03_QUERY713_247 = slq_new (32, 0, [5; 9],
  [(nlin_rat "2", nlin_rat "113/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: query713_248, query713_248_checked *)
let C713EQ03_QUERY713_248 = slq_new (32, 0, [6; 9],
  [(nlin_rat "12/5", nlin_rat "1"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
(* Lean: query713_249, query713_249_checked *)
let C713EQ03_QUERY713_249 = slq_new (32, 0, [8; 9],
  [(nlin_rat "3", nlin_rat "87/50"); (nlin_rat "81/25", nlin_rat "213/100"); (nlin_rat "1543/500", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2")]);;
(* Lean: query713_250, query713_250_checked *)
let C713EQ03_QUERY713_250 = slq_select 411;;
(* Lean: query713_251, query713_251_checked *)
let C713EQ03_QUERY713_251 = slq_select 412;;
(* Lean: query713_252, query713_252_checked *)
let C713EQ03_QUERY713_252 = slq_select 413;;
(* Lean: query713_253, query713_253_checked *)
let C713EQ03_QUERY713_253 = slq_select 414;;
(* Lean: query713_254, query713_254_checked *)
let C713EQ03_QUERY713_254 = slq_select 415;;
(* Lean: query713_255, query713_255_checked *)
let C713EQ03_QUERY713_255 = slq_select 416;;
