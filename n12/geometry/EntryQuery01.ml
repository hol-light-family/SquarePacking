(* ========================================================================= *)
(* Port of Compact/Cases/C713/EntryQuery01.lean (namespace S12): the exact   *)
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
(* Tag C713EQ01_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C713_EntryQueryBase.ml";;

(* Lean: query713_64, query713_64_checked *)
let C713EQ01_QUERY713_64 = slq_select 108;;
(* Lean: query713_65, query713_65_checked *)
let C713EQ01_QUERY713_65 = slq_select 109;;
(* Lean: query713_66, query713_66_checked *)
let C713EQ01_QUERY713_66 = slq_select 110;;
(* Lean: query713_67, query713_67_checked *)
let C713EQ01_QUERY713_67 = slq_select 111;;
(* Lean: query713_68, query713_68_checked *)
let C713EQ01_QUERY713_68 = slq_select 112;;
(* Lean: query713_69, query713_69_checked *)
let C713EQ01_QUERY713_69 = slq_select 113;;
(* Lean: query713_70, query713_70_checked *)
let C713EQ01_QUERY713_70 = slq_select 114;;
(* Lean: query713_71, query713_71_checked *)
let C713EQ01_QUERY713_71 = slq_select 115;;
(* Lean: query713_72, query713_72_checked *)
let C713EQ01_QUERY713_72 = slq_select 116;;
(* Lean: query713_73, query713_73_checked *)
let C713EQ01_QUERY713_73 = slq_select 117;;
(* Lean: query713_74, query713_74_checked *)
let C713EQ01_QUERY713_74 = slq_select 118;;
(* Lean: query713_75, query713_75_checked *)
let C713EQ01_QUERY713_75 = slq_select 119;;
(* Lean: query713_76, query713_76_checked *)
let C713EQ01_QUERY713_76 = slq_select 120;;
(* Lean: query713_77, query713_77_checked *)
let C713EQ01_QUERY713_77 = slq_select 121;;
(* Lean: query713_78, query713_78_checked *)
let C713EQ01_QUERY713_78 = slq_select 122;;
(* Lean: query713_79, query713_79_checked *)
let C713EQ01_QUERY713_79 = slq_select 123;;
(* Lean: query713_80, query713_80_checked *)
let C713EQ01_QUERY713_80 = slq_select 124;;
(* Lean: query713_81, query713_81_checked *)
let C713EQ01_QUERY713_81 = slq_select 125;;
(* Lean: query713_82, query713_82_checked *)
let C713EQ01_QUERY713_82 = slq_select 126;;
(* Lean: query713_83, query713_83_checked *)
let C713EQ01_QUERY713_83 = slq_select 127;;
(* Lean: query713_84, query713_84_checked *)
let C713EQ01_QUERY713_84 = slq_select 128;;
(* Lean: query713_85, query713_85_checked *)
let C713EQ01_QUERY713_85 = slq_select 129;;
(* Lean: query713_86, query713_86_checked *)
let C713EQ01_QUERY713_86 = slq_select 130;;
(* Lean: query713_87, query713_87_checked *)
let C713EQ01_QUERY713_87 = slq_select 131;;
(* Lean: query713_88, query713_88_checked *)
let C713EQ01_QUERY713_88 = slq_select 132;;
(* Lean: query713_89, query713_89_checked *)
let C713EQ01_QUERY713_89 = slq_select 133;;
(* Lean: query713_90, query713_90_checked *)
let C713EQ01_QUERY713_90 = slq_select 134;;
(* Lean: query713_91, query713_91_checked *)
let C713EQ01_QUERY713_91 = slq_select 135;;
(* Lean: query713_92, query713_92_checked *)
let C713EQ01_QUERY713_92 = slq_select 136;;
(* Lean: query713_93, query713_93_checked *)
let C713EQ01_QUERY713_93 = slq_select 137;;
(* Lean: query713_94, query713_94_checked *)
let C713EQ01_QUERY713_94 = slq_select 138;;
(* Lean: query713_95, query713_95_checked *)
let C713EQ01_QUERY713_95 = slq_select 139;;
(* Lean: query713_96, query713_96_checked *)
let C713EQ01_QUERY713_96 = slq_select 140;;
(* Lean: query713_97, query713_97_checked *)
let C713EQ01_QUERY713_97 = slq_select 141;;
(* Lean: query713_98, query713_98_checked *)
let C713EQ01_QUERY713_98 = slq_select 142;;
(* Lean: query713_99, query713_99_checked *)
let C713EQ01_QUERY713_99 = slq_select 143;;
(* Lean: query713_100, query713_100_checked *)
let C713EQ01_QUERY713_100 = slq_select 144;;
(* Lean: query713_101, query713_101_checked *)
let C713EQ01_QUERY713_101 = slq_select 145;;
(* Lean: query713_102, query713_102_checked *)
let C713EQ01_QUERY713_102 = slq_select 146;;
(* Lean: query713_103, query713_103_checked *)
let C713EQ01_QUERY713_103 = slq_select 147;;
(* Lean: query713_104, query713_104_checked *)
let C713EQ01_QUERY713_104 = slq_select 148;;
(* Lean: query713_105, query713_105_checked *)
let C713EQ01_QUERY713_105 = slq_select 149;;
(* Lean: query713_106, query713_106_checked *)
let C713EQ01_QUERY713_106 = slq_select 150;;
(* Lean: query713_107, query713_107_checked *)
let C713EQ01_QUERY713_107 = slq_select 151;;
(* Lean: query713_108, query713_108_checked *)
let C713EQ01_QUERY713_108 = slq_select 152;;
(* Lean: query713_109, query713_109_checked *)
let C713EQ01_QUERY713_109 = slq_select 153;;
(* Lean: query713_110, query713_110_checked *)
let C713EQ01_QUERY713_110 = slq_select 154;;
(* Lean: query713_111, query713_111_checked *)
let C713EQ01_QUERY713_111 = slq_select 155;;
(* Lean: query713_112, query713_112_checked *)
let C713EQ01_QUERY713_112 = slq_select 156;;
(* Lean: query713_113, query713_113_checked *)
let C713EQ01_QUERY713_113 = slq_select 157;;
(* Lean: query713_114, query713_114_checked *)
let C713EQ01_QUERY713_114 = slq_select 158;;
(* Lean: query713_115, query713_115_checked *)
let C713EQ01_QUERY713_115 = slq_select 159;;
(* Lean: query713_116, query713_116_checked *)
let C713EQ01_QUERY713_116 = slq_select 160;;
(* Lean: query713_117, query713_117_checked *)
let C713EQ01_QUERY713_117 = slq_select 162;;
(* Lean: query713_118, query713_118_checked *)
let C713EQ01_QUERY713_118 = slq_select 165;;
(* Lean: query713_119, query713_119_checked *)
let C713EQ01_QUERY713_119 = slq_select 169;;
(* Lean: query713_120, query713_120_checked *)
let C713EQ01_QUERY713_120 = slq_select 174;;
(* Lean: query713_121, query713_121_checked *)
let C713EQ01_QUERY713_121 = slq_select 180;;
(* Lean: query713_122, query713_122_checked *)
let C713EQ01_QUERY713_122 = slq_select 187;;
(* Lean: query713_123, query713_123_checked *)
let C713EQ01_QUERY713_123 = slq_select 195;;
(* Lean: query713_124, query713_124_checked *)
let C713EQ01_QUERY713_124 = slq_select 204;;
(* Lean: query713_125, query713_125_checked *)
let C713EQ01_QUERY713_125 = slq_new (12, 0, [0],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_126, query713_126_checked *)
let C713EQ01_QUERY713_126 = slq_new (12, 0, [1],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: query713_127, query713_127_checked *)
let C713EQ01_QUERY713_127 = slq_new (12, 0, [2],
  [(nlin_rat "8/5", nlin_rat "1"); (nlin_rat "1543/500", nlin_rat "1")],
  [(nlin_rat "12/5", nlin_rat "1")]);;
