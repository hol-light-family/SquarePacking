(* ========================================================================= *)
(* Port of Compact/Cases/C713/EntryQuery02.lean (namespace S12): the exact   *)
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
(* Tag C713EQ02_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C713_EntryQueryBase.ml";;

(* Lean: query713_128, query713_128_checked *)
let C713EQ02_QUERY713_128 = slq_new (12, 0, [3],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_129, query713_129_checked *)
let C713EQ02_QUERY713_129 = slq_new (12, 0, [4],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_130, query713_130_checked *)
let C713EQ02_QUERY713_130 = slq_new (12, 0, [5],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_131, query713_131_checked *)
let C713EQ02_QUERY713_131 = slq_new (12, 0, [7],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_132, query713_132_checked *)
let C713EQ02_QUERY713_132 = slq_new (12, 0, [9],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "3", nlin_rat "87/50")]);;
(* Lean: query713_133, query713_133_checked *)
let C713EQ02_QUERY713_133 = slq_new (12, 2, [8],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "3", nlin_rat "8/5")]);;
(* Lean: query713_134, query713_134_checked *)
let C713EQ02_QUERY713_134 = slq_select 339;;
(* Lean: query713_135, query713_135_checked *)
let C713EQ02_QUERY713_135 = slq_select 340;;
(* Lean: query713_136, query713_136_checked *)
let C713EQ02_QUERY713_136 = slq_select 341;;
(* Lean: query713_137, query713_137_checked *)
let C713EQ02_QUERY713_137 = slq_select 342;;
(* Lean: query713_138, query713_138_checked *)
let C713EQ02_QUERY713_138 = slq_select 343;;
(* Lean: query713_139, query713_139_checked *)
let C713EQ02_QUERY713_139 = slq_select 344;;
(* Lean: query713_140, query713_140_checked *)
let C713EQ02_QUERY713_140 = slq_select 345;;
(* Lean: query713_141, query713_141_checked *)
let C713EQ02_QUERY713_141 = slq_select 346;;
(* Lean: query713_142, query713_142_checked *)
let C713EQ02_QUERY713_142 = slq_select 347;;
(* Lean: query713_143, query713_143_checked *)
let C713EQ02_QUERY713_143 = slq_select 348;;
(* Lean: query713_144, query713_144_checked *)
let C713EQ02_QUERY713_144 = slq_select 349;;
(* Lean: query713_145, query713_145_checked *)
let C713EQ02_QUERY713_145 = slq_select 350;;
(* Lean: query713_146, query713_146_checked *)
let C713EQ02_QUERY713_146 = slq_select 351;;
(* Lean: query713_147, query713_147_checked *)
let C713EQ02_QUERY713_147 = slq_select 352;;
(* Lean: query713_148, query713_148_checked *)
let C713EQ02_QUERY713_148 = slq_select 353;;
(* Lean: query713_149, query713_149_checked *)
let C713EQ02_QUERY713_149 = slq_select 354;;
(* Lean: query713_150, query713_150_checked *)
let C713EQ02_QUERY713_150 = slq_select 355;;
(* Lean: query713_151, query713_151_checked *)
let C713EQ02_QUERY713_151 = slq_select 356;;
(* Lean: query713_152, query713_152_checked *)
let C713EQ02_QUERY713_152 = slq_select 357;;
(* Lean: query713_153, query713_153_checked *)
let C713EQ02_QUERY713_153 = slq_select 358;;
(* Lean: query713_154, query713_154_checked *)
let C713EQ02_QUERY713_154 = slq_select 359;;
(* Lean: query713_155, query713_155_checked *)
let C713EQ02_QUERY713_155 = slq_select 360;;
(* Lean: query713_156, query713_156_checked *)
let C713EQ02_QUERY713_156 = slq_select 361;;
(* Lean: query713_157, query713_157_checked *)
let C713EQ02_QUERY713_157 = slq_select 362;;
(* Lean: query713_158, query713_158_checked *)
let C713EQ02_QUERY713_158 = slq_select 363;;
(* Lean: query713_159, query713_159_checked *)
let C713EQ02_QUERY713_159 = slq_select 364;;
(* Lean: query713_160, query713_160_checked *)
let C713EQ02_QUERY713_160 = slq_select 365;;
(* Lean: query713_161, query713_161_checked *)
let C713EQ02_QUERY713_161 = slq_select 366;;
(* Lean: query713_162, query713_162_checked *)
let C713EQ02_QUERY713_162 = slq_select 367;;
(* Lean: query713_163, query713_163_checked *)
let C713EQ02_QUERY713_163 = slq_select 368;;
(* Lean: query713_164, query713_164_checked *)
let C713EQ02_QUERY713_164 = slq_select 369;;
(* Lean: query713_165, query713_165_checked *)
let C713EQ02_QUERY713_165 = slq_select 370;;
(* Lean: query713_166, query713_166_checked *)
let C713EQ02_QUERY713_166 = slq_select 371;;
(* Lean: query713_167, query713_167_checked *)
let C713EQ02_QUERY713_167 = slq_select 372;;
(* Lean: query713_168, query713_168_checked *)
let C713EQ02_QUERY713_168 = slq_select 373;;
(* Lean: query713_169, query713_169_checked *)
let C713EQ02_QUERY713_169 = slq_select 374;;
(* Lean: query713_170, query713_170_checked *)
let C713EQ02_QUERY713_170 = slq_select 375;;
(* Lean: query713_171, query713_171_checked *)
let C713EQ02_QUERY713_171 = slq_select 376;;
(* Lean: query713_172, query713_172_checked *)
let C713EQ02_QUERY713_172 = slq_select 377;;
(* Lean: query713_173, query713_173_checked *)
let C713EQ02_QUERY713_173 = slq_select 378;;
(* Lean: query713_174, query713_174_checked *)
let C713EQ02_QUERY713_174 = slq_select 379;;
(* Lean: query713_175, query713_175_checked *)
let C713EQ02_QUERY713_175 = slq_select 380;;
(* Lean: query713_176, query713_176_checked *)
let C713EQ02_QUERY713_176 = slq_select 381;;
(* Lean: query713_177, query713_177_checked *)
let C713EQ02_QUERY713_177 = slq_select 382;;
(* Lean: query713_178, query713_178_checked *)
let C713EQ02_QUERY713_178 = slq_select 383;;
(* Lean: query713_179, query713_179_checked *)
let C713EQ02_QUERY713_179 = slq_select 384;;
(* Lean: query713_180, query713_180_checked *)
let C713EQ02_QUERY713_180 = slq_select 385;;
(* Lean: query713_181, query713_181_checked *)
let C713EQ02_QUERY713_181 = slq_select 386;;
(* Lean: query713_182, query713_182_checked *)
let C713EQ02_QUERY713_182 = slq_select 387;;
(* Lean: query713_183, query713_183_checked *)
let C713EQ02_QUERY713_183 = slq_select 388;;
(* Lean: query713_184, query713_184_checked *)
let C713EQ02_QUERY713_184 = slq_select 389;;
(* Lean: query713_185, query713_185_checked *)
let C713EQ02_QUERY713_185 = slq_select 390;;
(* Lean: query713_186, query713_186_checked *)
let C713EQ02_QUERY713_186 = slq_select 391;;
(* Lean: query713_187, query713_187_checked *)
let C713EQ02_QUERY713_187 = slq_select 392;;
(* Lean: query713_188, query713_188_checked *)
let C713EQ02_QUERY713_188 = slq_select 393;;
(* Lean: query713_189, query713_189_checked *)
let C713EQ02_QUERY713_189 = slq_select 394;;
(* Lean: query713_190, query713_190_checked *)
let C713EQ02_QUERY713_190 = slq_select 395;;
(* Lean: query713_191, query713_191_checked *)
let C713EQ02_QUERY713_191 = slq_select 396;;
