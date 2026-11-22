(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk19.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC19_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries031.ml";;
needs "n12/geometry/Queries032.ml";;
needs "n12/geometry/Queries033.ml";;
needs "n12/geometry/Queries034.ml";;
needs "n12/geometry/Queries035.ml";;

(* Lean: single979_9_1 *)
let c979eqc19_single979_9_1 = { dmask = 8192; dlower = 1; dupper = 3;
  dallowed = [[2]; [0; 2]; [5]; [2; 5]; [0; 2; 5]; [5; 8]; [2; 5; 8]];
  dqueries = [1194; 1195; 1196; 1197; slq_hist_idx 1021; 1198; 1199; 1200; slq_hist_idx 1022; 1201; slq_hist_idx 1023; slq_hist_idx 1024; 1202; 1203; 1204; slq_hist_idx 1025; 1205; slq_hist_idx 1026; slq_hist_idx 1027; 1206; slq_hist_idx 1028; slq_hist_idx 1029; slq_hist_idx 1030; 1207; 1208; slq_hist_idx 1031; slq_hist_idx 1032; 1209; slq_hist_idx 1033; slq_hist_idx 1034; slq_hist_idx 1035; 1210; slq_hist_idx 1036; slq_hist_idx 1037; slq_hist_idx 1038; slq_hist_idx 1039; 1211; 1212; 1213; slq_hist_idx 1040; 1214; slq_hist_idx 1041; slq_hist_idx 1042; 1215; slq_hist_idx 1043; slq_hist_idx 1044; slq_hist_idx 1045; 1216; slq_hist_idx 1046; slq_hist_idx 1047; slq_hist_idx 1048; slq_hist_idx 1049; 1217; slq_hist_idx 1050; slq_hist_idx 1051; slq_hist_idx 1052; slq_hist_idx 1053; slq_hist_idx 1054; 1218; 1219; 1220; slq_hist_idx 1055; 1221; slq_hist_idx 1056; slq_hist_idx 1057; 1222; slq_hist_idx 1058; slq_hist_idx 1059; slq_hist_idx 1060; 1223; slq_hist_idx 1061; slq_hist_idx 1062; slq_hist_idx 1063; slq_hist_idx 1064; 1224; slq_hist_idx 1065; slq_hist_idx 1066; slq_hist_idx 1067; slq_hist_idx 1068; slq_hist_idx 1069; 1225; slq_hist_idx 1070; slq_hist_idx 1071; slq_hist_idx 1072; slq_hist_idx 1073; slq_hist_idx 1074; slq_hist_idx 1075; 1226; 1227; 1228; slq_hist_idx 1076; 1229; slq_hist_idx 1077; slq_hist_idx 1078; 1230; slq_hist_idx 1079; slq_hist_idx 1080; slq_hist_idx 1081; 1231; slq_hist_idx 1082; slq_hist_idx 1083; slq_hist_idx 1084; slq_hist_idx 1085; slq_hist_idx 1086; slq_hist_idx 1087; slq_hist_idx 1088; slq_hist_idx 1089; 1232; slq_hist_idx 1090; slq_hist_idx 1091; slq_hist_idx 1092; slq_hist_idx 1093; slq_hist_idx 1094; slq_hist_idx 1095; 1233; slq_hist_idx 1096; slq_hist_idx 1097; slq_hist_idx 1098; slq_hist_idx 1099; slq_hist_idx 1100; slq_hist_idx 1101; slq_hist_idx 1102; 1234; 1235; 1236; slq_hist_idx 1103; 1237; slq_hist_idx 1104; slq_hist_idx 1105; 1238; slq_hist_idx 1106; slq_hist_idx 1107; slq_hist_idx 1108; 1239; slq_hist_idx 1109; slq_hist_idx 1110; slq_hist_idx 1111; slq_hist_idx 1112; 1240; slq_hist_idx 1113; slq_hist_idx 1114; slq_hist_idx 1115; slq_hist_idx 1116; slq_hist_idx 1117; 1241; slq_hist_idx 1118; slq_hist_idx 1119; slq_hist_idx 1120; slq_hist_idx 1121; slq_hist_idx 1122; slq_hist_idx 1123; 1242; slq_hist_idx 1124; slq_hist_idx 1125; slq_hist_idx 1126; slq_hist_idx 1127; slq_hist_idx 1128; slq_hist_idx 1129; slq_hist_idx 1130; 1243; slq_hist_idx 1131; slq_hist_idx 1132; slq_hist_idx 1133; slq_hist_idx 1134; slq_hist_idx 1135; slq_hist_idx 1136; slq_hist_idx 1137; slq_hist_idx 1138] };;
(* Lean: single979_9_1_checked *)
let C979EQC19_SINGLE979_9_1_CHECKED = sodt_checked `c979eqb_family` 1 c979eqc19_single979_9_1;;
