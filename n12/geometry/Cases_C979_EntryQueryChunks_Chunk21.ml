(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk21.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC21_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries035.ml";;
needs "n12/geometry/Queries036.ml";;
needs "n12/geometry/Queries037.ml";;
needs "n12/geometry/Queries038.ml";;
needs "n12/geometry/Queries039.ml";;

(* Lean: single979_10_1 *)
let c979eqc21_single979_10_1 = { dmask = 16384; dlower = 1; dupper = 3;
  dallowed = [[6]; [8]; [6; 8]; [9]; [6; 9]; [8; 9]; [6; 8; 9]];
  dqueries = [1344; 1345; 1346; 1347; 1348; 1349; slq_hist_idx 1143; 1350; 1351; 1352; slq_hist_idx 1144; 1353; slq_hist_idx 1145; slq_hist_idx 1146; 1354; 1355; 1356; slq_hist_idx 1147; 1357; slq_hist_idx 1148; slq_hist_idx 1149; 1358; slq_hist_idx 1150; slq_hist_idx 1151; slq_hist_idx 1152; 1359; 1360; 1361; slq_hist_idx 1153; 1362; slq_hist_idx 1154; slq_hist_idx 1155; 1363; slq_hist_idx 1156; slq_hist_idx 1157; slq_hist_idx 1158; 1364; slq_hist_idx 1159; slq_hist_idx 1160; slq_hist_idx 1161; slq_hist_idx 1162; 1365; 1366; slq_hist_idx 1163; 1367; slq_hist_idx 1164; slq_hist_idx 1165; 1368; slq_hist_idx 1166; slq_hist_idx 1167; slq_hist_idx 1168; 1369; slq_hist_idx 1169; slq_hist_idx 1170; slq_hist_idx 1171; slq_hist_idx 1172; 1370; slq_hist_idx 1173; slq_hist_idx 1174; slq_hist_idx 1175; slq_hist_idx 1176; slq_hist_idx 1177; 1371; 1372; 1373; slq_hist_idx 1178; 1374; slq_hist_idx 1179; slq_hist_idx 1180; 1375; slq_hist_idx 1181; slq_hist_idx 1182; slq_hist_idx 1183; 1376; slq_hist_idx 1184; slq_hist_idx 1185; slq_hist_idx 1186; slq_hist_idx 1187; 1377; slq_hist_idx 1188; slq_hist_idx 1189; slq_hist_idx 1190; slq_hist_idx 1191; slq_hist_idx 1192; 1378; slq_hist_idx 1193; slq_hist_idx 1194; slq_hist_idx 1195; slq_hist_idx 1196; slq_hist_idx 1197; slq_hist_idx 1198; 1379; 1380; slq_hist_idx 1199; 1381; slq_hist_idx 1200; slq_hist_idx 1201; 1382; slq_hist_idx 1202; slq_hist_idx 1203; slq_hist_idx 1204; 1383; slq_hist_idx 1205; slq_hist_idx 1206; slq_hist_idx 1207; slq_hist_idx 1208; 1384; slq_hist_idx 1209; slq_hist_idx 1210; slq_hist_idx 1211; slq_hist_idx 1212; slq_hist_idx 1213; slq_hist_idx 1214; slq_hist_idx 1215; slq_hist_idx 1216; slq_hist_idx 1217; slq_hist_idx 1218; slq_hist_idx 1219; 1385; slq_hist_idx 1220; slq_hist_idx 1221; slq_hist_idx 1222; slq_hist_idx 1223; slq_hist_idx 1224; slq_hist_idx 1225; slq_hist_idx 1226; 1386; 1387; slq_hist_idx 1227; 1388; slq_hist_idx 1228; slq_hist_idx 1229; 1389; slq_hist_idx 1230; slq_hist_idx 1231; slq_hist_idx 1232; 1390; slq_hist_idx 1233; slq_hist_idx 1234; slq_hist_idx 1235; slq_hist_idx 1236; 1391; slq_hist_idx 1237; slq_hist_idx 1238; slq_hist_idx 1239; slq_hist_idx 1240; slq_hist_idx 1241; slq_hist_idx 1242; slq_hist_idx 1243; slq_hist_idx 1244; slq_hist_idx 1245; slq_hist_idx 1246; slq_hist_idx 1247; 1392; slq_hist_idx 1248; slq_hist_idx 1249; slq_hist_idx 1250; slq_hist_idx 1251; slq_hist_idx 1252; slq_hist_idx 1253; slq_hist_idx 1254; slq_hist_idx 1255; slq_hist_idx 1256; slq_hist_idx 1257; slq_hist_idx 1258; slq_hist_idx 1259; slq_hist_idx 1260; slq_hist_idx 1261] };;
(* Lean: single979_10_1_checked *)
let C979EQC21_SINGLE979_10_1_CHECKED = sodt_checked `c979eqb_family` 1 c979eqc21_single979_10_1;;
