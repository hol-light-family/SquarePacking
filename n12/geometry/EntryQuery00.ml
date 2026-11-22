(* ========================================================================= *)
(* Port of Compact/Cases/C713/EntryQuery00.lean (namespace S12): the exact   *)
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
(* Tag C713EQ00_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C713_EntryQueryBase.ml";;

(* Lean: query713_0, query713_0_checked *)
let C713EQ00_QUERY713_0 = slq_select 0;;
(* Lean: query713_1, query713_1_checked *)
let C713EQ00_QUERY713_1 = slq_select 1;;
(* Lean: query713_2, query713_2_checked *)
let C713EQ00_QUERY713_2 = slq_select 2;;
(* Lean: query713_3, query713_3_checked *)
let C713EQ00_QUERY713_3 = slq_select 3;;
(* Lean: query713_4, query713_4_checked *)
let C713EQ00_QUERY713_4 = slq_select 4;;
(* Lean: query713_5, query713_5_checked *)
let C713EQ00_QUERY713_5 = slq_select 5;;
(* Lean: query713_6, query713_6_checked *)
let C713EQ00_QUERY713_6 = slq_select 6;;
(* Lean: query713_7, query713_7_checked *)
let C713EQ00_QUERY713_7 = slq_select 7;;
(* Lean: query713_8, query713_8_checked *)
let C713EQ00_QUERY713_8 = slq_select 8;;
(* Lean: query713_9, query713_9_checked *)
let C713EQ00_QUERY713_9 = slq_select 9;;
(* Lean: query713_10, query713_10_checked *)
let C713EQ00_QUERY713_10 = slq_select 10;;
(* Lean: query713_11, query713_11_checked *)
let C713EQ00_QUERY713_11 = slq_select 11;;
(* Lean: query713_12, query713_12_checked *)
let C713EQ00_QUERY713_12 = slq_select 12;;
(* Lean: query713_13, query713_13_checked *)
let C713EQ00_QUERY713_13 = slq_select 13;;
(* Lean: query713_14, query713_14_checked *)
let C713EQ00_QUERY713_14 = slq_select 14;;
(* Lean: query713_15, query713_15_checked *)
let C713EQ00_QUERY713_15 = slq_select 15;;
(* Lean: query713_16, query713_16_checked *)
let C713EQ00_QUERY713_16 = slq_select 16;;
(* Lean: query713_17, query713_17_checked *)
let C713EQ00_QUERY713_17 = slq_select 17;;
(* Lean: query713_18, query713_18_checked *)
let C713EQ00_QUERY713_18 = slq_select 18;;
(* Lean: query713_19, query713_19_checked *)
let C713EQ00_QUERY713_19 = slq_select 19;;
(* Lean: query713_20, query713_20_checked *)
let C713EQ00_QUERY713_20 = slq_select 20;;
(* Lean: query713_21, query713_21_checked *)
let C713EQ00_QUERY713_21 = slq_select 21;;
(* Lean: query713_22, query713_22_checked *)
let C713EQ00_QUERY713_22 = slq_select 22;;
(* Lean: query713_23, query713_23_checked *)
let C713EQ00_QUERY713_23 = slq_select 23;;
(* Lean: query713_24, query713_24_checked *)
let C713EQ00_QUERY713_24 = slq_select 24;;
(* Lean: query713_25, query713_25_checked *)
let C713EQ00_QUERY713_25 = slq_select 25;;
(* Lean: query713_26, query713_26_checked *)
let C713EQ00_QUERY713_26 = slq_select 26;;
(* Lean: query713_27, query713_27_checked *)
let C713EQ00_QUERY713_27 = slq_select 27;;
(* Lean: query713_28, query713_28_checked *)
let C713EQ00_QUERY713_28 = slq_select 28;;
(* Lean: query713_29, query713_29_checked *)
let C713EQ00_QUERY713_29 = slq_select 29;;
(* Lean: query713_30, query713_30_checked *)
let C713EQ00_QUERY713_30 = slq_select 30;;
(* Lean: query713_31, query713_31_checked *)
let C713EQ00_QUERY713_31 = slq_select 31;;
(* Lean: query713_32, query713_32_checked *)
let C713EQ00_QUERY713_32 = slq_select 32;;
(* Lean: query713_33, query713_33_checked *)
let C713EQ00_QUERY713_33 = slq_select 33;;
(* Lean: query713_34, query713_34_checked *)
let C713EQ00_QUERY713_34 = slq_select 34;;
(* Lean: query713_35, query713_35_checked *)
let C713EQ00_QUERY713_35 = slq_select 35;;
(* Lean: query713_36, query713_36_checked *)
let C713EQ00_QUERY713_36 = slq_select 36;;
(* Lean: query713_37, query713_37_checked *)
let C713EQ00_QUERY713_37 = slq_select 37;;
(* Lean: query713_38, query713_38_checked *)
let C713EQ00_QUERY713_38 = slq_select 38;;
(* Lean: query713_39, query713_39_checked *)
let C713EQ00_QUERY713_39 = slq_select 39;;
(* Lean: query713_40, query713_40_checked *)
let C713EQ00_QUERY713_40 = slq_select 40;;
(* Lean: query713_41, query713_41_checked *)
let C713EQ00_QUERY713_41 = slq_select 41;;
(* Lean: query713_42, query713_42_checked *)
let C713EQ00_QUERY713_42 = slq_select 42;;
(* Lean: query713_43, query713_43_checked *)
let C713EQ00_QUERY713_43 = slq_select 43;;
(* Lean: query713_44, query713_44_checked *)
let C713EQ00_QUERY713_44 = slq_select 44;;
(* Lean: query713_45, query713_45_checked *)
let C713EQ00_QUERY713_45 = slq_select 45;;
(* Lean: query713_46, query713_46_checked *)
let C713EQ00_QUERY713_46 = slq_select 46;;
(* Lean: query713_47, query713_47_checked *)
let C713EQ00_QUERY713_47 = slq_select 47;;
(* Lean: query713_48, query713_48_checked *)
let C713EQ00_QUERY713_48 = slq_select 48;;
(* Lean: query713_49, query713_49_checked *)
let C713EQ00_QUERY713_49 = slq_select 49;;
(* Lean: query713_50, query713_50_checked *)
let C713EQ00_QUERY713_50 = slq_select 50;;
(* Lean: query713_51, query713_51_checked *)
let C713EQ00_QUERY713_51 = slq_select 51;;
(* Lean: query713_52, query713_52_checked *)
let C713EQ00_QUERY713_52 = slq_select 52;;
(* Lean: query713_53, query713_53_checked *)
let C713EQ00_QUERY713_53 = slq_select 53;;
(* Lean: query713_54, query713_54_checked *)
let C713EQ00_QUERY713_54 = slq_select 54;;
(* Lean: query713_55, query713_55_checked *)
let C713EQ00_QUERY713_55 = slq_select 55;;
(* Lean: query713_56, query713_56_checked *)
let C713EQ00_QUERY713_56 = slq_select 58;;
(* Lean: query713_57, query713_57_checked *)
let C713EQ00_QUERY713_57 = slq_select 62;;
(* Lean: query713_58, query713_58_checked *)
let C713EQ00_QUERY713_58 = slq_select 67;;
(* Lean: query713_59, query713_59_checked *)
let C713EQ00_QUERY713_59 = slq_select 73;;
(* Lean: query713_60, query713_60_checked *)
let C713EQ00_QUERY713_60 = slq_select 80;;
(* Lean: query713_61, query713_61_checked *)
let C713EQ00_QUERY713_61 = slq_select 88;;
(* Lean: query713_62, query713_62_checked *)
let C713EQ00_QUERY713_62 = slq_select 97;;
(* Lean: query713_63, query713_63_checked *)
let C713EQ00_QUERY713_63 = slq_select 107;;
