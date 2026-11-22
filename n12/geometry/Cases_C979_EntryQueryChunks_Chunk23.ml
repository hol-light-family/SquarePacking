(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk23.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC23_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries039.ml";;
needs "n12/geometry/Queries040.ml";;
needs "n12/geometry/Queries041.ml";;
needs "n12/geometry/Queries042.ml";;
needs "n12/geometry/Queries043.ml";;

(* Lean: single979_11_1 *)
let c979eqc23_single979_11_1 = { dmask = 32768; dlower = 1; dupper = 3;
  dallowed = [[4]; [1; 4]; [7]; [4; 7]; [1; 4; 7]; [7; 9]; [4; 7; 9]];
  dqueries = [1585; 1586; 1587; 1588; 1589; 1590; slq_hist_idx 1264; 1591; 1592; 1593; slq_hist_idx 1265; 1594; slq_hist_idx 1266; slq_hist_idx 1267; 1595; slq_hist_idx 1268; 1596; slq_hist_idx 1269; slq_hist_idx 1270; 1597; slq_hist_idx 1271; slq_hist_idx 1272; slq_hist_idx 1273; 1598; 1599; 1600; slq_hist_idx 1274; 1601; slq_hist_idx 1275; slq_hist_idx 1276; 1602; slq_hist_idx 1277; slq_hist_idx 1278; slq_hist_idx 1279; 1603; slq_hist_idx 1280; slq_hist_idx 1281; slq_hist_idx 1282; slq_hist_idx 1283; 1604; 1605; 1606; slq_hist_idx 1284; 1607; slq_hist_idx 1285; slq_hist_idx 1286; 1608; slq_hist_idx 1287; slq_hist_idx 1288; slq_hist_idx 1289; 1609; slq_hist_idx 1290; slq_hist_idx 1291; slq_hist_idx 1292; slq_hist_idx 1293; 1610; slq_hist_idx 1294; slq_hist_idx 1295; slq_hist_idx 1296; slq_hist_idx 1297; slq_hist_idx 1298; 1611; 1612; slq_hist_idx 1299; 1613; slq_hist_idx 1300; slq_hist_idx 1301; 1614; slq_hist_idx 1302; slq_hist_idx 1303; slq_hist_idx 1304; slq_hist_idx 1305; slq_hist_idx 1306; slq_hist_idx 1307; 1615; slq_hist_idx 1308; slq_hist_idx 1309; slq_hist_idx 1310; slq_hist_idx 1311; slq_hist_idx 1312; 1616; slq_hist_idx 1313; slq_hist_idx 1314; slq_hist_idx 1315; slq_hist_idx 1316; slq_hist_idx 1317; slq_hist_idx 1318; 1617; 1618; 1619; slq_hist_idx 1319; 1620; slq_hist_idx 1320; slq_hist_idx 1321; 1621; slq_hist_idx 1322; slq_hist_idx 1323; slq_hist_idx 1324; 1622; slq_hist_idx 1325; slq_hist_idx 1326; slq_hist_idx 1327; slq_hist_idx 1328; 1623; slq_hist_idx 1329; slq_hist_idx 1330; slq_hist_idx 1331; slq_hist_idx 1332; slq_hist_idx 1333; 1624; slq_hist_idx 1334; slq_hist_idx 1335; slq_hist_idx 1336; slq_hist_idx 1337; slq_hist_idx 1338; slq_hist_idx 1339; 1625; slq_hist_idx 1340; slq_hist_idx 1341; slq_hist_idx 1342; slq_hist_idx 1343; slq_hist_idx 1344; slq_hist_idx 1345; slq_hist_idx 1346; 1626; 1627; 1628; slq_hist_idx 1347; 1629; slq_hist_idx 1348; slq_hist_idx 1349; 1630; slq_hist_idx 1350; slq_hist_idx 1351; slq_hist_idx 1352; 1631; slq_hist_idx 1353; slq_hist_idx 1354; slq_hist_idx 1355; slq_hist_idx 1356; 1632; slq_hist_idx 1357; slq_hist_idx 1358; slq_hist_idx 1359; slq_hist_idx 1360; slq_hist_idx 1361; 1633; slq_hist_idx 1362; slq_hist_idx 1363; slq_hist_idx 1364; slq_hist_idx 1365; slq_hist_idx 1366; slq_hist_idx 1367; slq_hist_idx 1368; slq_hist_idx 1369; slq_hist_idx 1370; slq_hist_idx 1371; slq_hist_idx 1372; slq_hist_idx 1373; 1634; slq_hist_idx 1374; slq_hist_idx 1375; slq_hist_idx 1376; slq_hist_idx 1377; slq_hist_idx 1378; slq_hist_idx 1379; slq_hist_idx 1380; slq_hist_idx 1381] };;
(* Lean: single979_11_1_checked *)
let C979EQC23_SINGLE979_11_1_CHECKED = sodt_checked `c979eqb_family` 1 c979eqc23_single979_11_1;;
