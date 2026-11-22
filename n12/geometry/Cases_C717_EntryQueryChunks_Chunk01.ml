(* ========================================================================= *)
(* Port of Compact/Cases/C717/EntryQueryChunks/Chunk01.lean (namespace S12):*)
(* direct single-owner domains of the C717 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case717Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c717eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C717EQC01_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C717_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Queries004.ml";;
needs "n12/geometry/Queries005.ml";;
needs "n12/geometry/Queries006.ml";;
needs "n12/geometry/Queries007.ml";;
needs "n12/geometry/Queries008.ml";;
needs "n12/geometry/Queries009.ml";;
needs "n12/geometry/Queries010.ml";;
needs "n12/geometry/Queries011.ml";;
needs "n12/geometry/Queries012.ml";;
needs "n12/geometry/Queries013.ml";;
needs "n12/geometry/Queries014.ml";;
needs "n12/geometry/Queries015.ml";;
needs "n12/geometry/Queries016.ml";;
needs "n12/geometry/Queries017.ml";;
needs "n12/geometry/Queries018.ml";;
needs "n12/geometry/Queries019.ml";;
needs "n12/geometry/Queries020.ml";;
needs "n12/geometry/Queries021.ml";;
needs "n12/geometry/Queries022.ml";;
needs "n12/geometry/Queries023.ml";;
needs "n12/geometry/Queries024.ml";;
needs "n12/geometry/Queries025.ml";;
needs "n12/geometry/Queries026.ml";;
needs "n12/geometry/Queries027.ml";;
needs "n12/geometry/Queries028.ml";;
needs "n12/geometry/Queries029.ml";;
needs "n12/geometry/Queries030.ml";;
needs "n12/geometry/Queries031.ml";;
needs "n12/geometry/Queries032.ml";;
needs "n12/geometry/Queries033.ml";;
needs "n12/geometry/Queries034.ml";;
needs "n12/geometry/Queries035.ml";;
needs "n12/geometry/Queries036.ml";;
needs "n12/geometry/Queries037.ml";;
needs "n12/geometry/Queries038.ml";;
needs "n12/geometry/Queries039.ml";;
needs "n12/geometry/Queries040.ml";;
needs "n12/geometry/Queries041.ml";;
needs "n12/geometry/Queries042.ml";;
needs "n12/geometry/Queries043.ml";;

(* Lean: single717_6_0 *)
let c717eqc01_single717_6_0 = { dmask = 768; dlower = 1; dupper = 1;
  dallowed = [[4]];
  dqueries = [744; 745; 746; 747; 748; 749; 750; 751; 752] };;
(* Lean: single717_6_0_checked *)
let C717EQC01_SINGLE717_6_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc01_single717_6_0;;
(* Lean: single717_6_1 *)
let c717eqc01_single717_6_1 = { dmask = 768; dlower = 0; dupper = 2;
  dallowed = [[]; [0]; [2]; [0; 2]; [3]; [0; 3]; [2; 3]; [5]; [0; 5]; [2; 5]; [3; 5]; [6]; [0; 6]; [2; 6]; [3; 6]; [5; 6]; [8]; [0; 8]; [2; 8]; [3; 8]; [5; 8]; [6; 8]];
  dqueries = [slq_hist_idx 823; slq_hist_idx 824; slq_hist_idx 825; slq_hist_idx 826; slq_hist_idx 827; slq_hist_idx 828; slq_hist_idx 829; slq_hist_idx 830; slq_hist_idx 831; slq_hist_idx 832; slq_hist_idx 833; slq_hist_idx 834; slq_hist_idx 835; slq_hist_idx 836; slq_hist_idx 837; slq_hist_idx 838; slq_hist_idx 839; slq_hist_idx 840; slq_hist_idx 841; slq_hist_idx 842; slq_hist_idx 843; slq_hist_idx 844; slq_hist_idx 845; slq_hist_idx 846; slq_hist_idx 847; slq_hist_idx 848; slq_hist_idx 849; slq_hist_idx 850; slq_hist_idx 851; slq_hist_idx 852; slq_hist_idx 853; slq_hist_idx 854; slq_hist_idx 855; slq_hist_idx 856] };;
(* Lean: single717_6_1_checked *)
let C717EQC01_SINGLE717_6_1_CHECKED = dsd_actual `c717eqb_family` 1 c717eqc01_single717_6_1;;
(* Lean: single717_7_0 *)
let c717eqc01_single717_7_0 = { dmask = 3072; dlower = 1; dupper = 1;
  dallowed = [[5]];
  dqueries = [slq_hist_idx 857; slq_hist_idx 858; slq_hist_idx 859; slq_hist_idx 860; slq_hist_idx 861; slq_hist_idx 862; slq_hist_idx 863; slq_hist_idx 864; slq_hist_idx 865] };;
(* Lean: single717_7_0_checked *)
let C717EQC01_SINGLE717_7_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc01_single717_7_0;;
(* Lean: single717_7_1 *)
let c717eqc01_single717_7_1 = { dmask = 3072; dlower = 0; dupper = 2;
  dallowed = [[]; [1]; [3]; [1; 3]; [4]; [1; 4]; [3; 4]; [6]; [1; 6]; [3; 6]; [4; 6]; [7]; [1; 7]; [3; 7]; [4; 7]; [6; 7]; [9]; [1; 9]; [3; 9]; [4; 9]; [6; 9]; [7; 9]];
  dqueries = [slq_hist_idx 866; slq_hist_idx 867; slq_hist_idx 868; slq_hist_idx 869; slq_hist_idx 870; slq_hist_idx 871; slq_hist_idx 872; slq_hist_idx 873; slq_hist_idx 874; slq_hist_idx 875; slq_hist_idx 876; slq_hist_idx 877; slq_hist_idx 878; slq_hist_idx 879; slq_hist_idx 880; slq_hist_idx 881; slq_hist_idx 882; slq_hist_idx 883; slq_hist_idx 884; slq_hist_idx 885; slq_hist_idx 886; slq_hist_idx 887; slq_hist_idx 888; slq_hist_idx 889; slq_hist_idx 890; slq_hist_idx 891; slq_hist_idx 892; slq_hist_idx 893; slq_hist_idx 894; slq_hist_idx 895; slq_hist_idx 896; slq_hist_idx 897; slq_hist_idx 898; slq_hist_idx 899] };;
(* Lean: single717_7_1_checked *)
let C717EQC01_SINGLE717_7_1_CHECKED = dsd_actual `c717eqb_family` 1 c717eqc01_single717_7_1;;
(* Lean: single717_8_0 *)
let c717eqc01_single717_8_0 = { dmask = 4096; dlower = 1; dupper = 1;
  dallowed = [[0]; [1]];
  dqueries = [989; 991; 994; 999; 1005; 1012; 1020; 1029] };;
(* Lean: single717_8_0_checked *)
let C717EQC01_SINGLE717_8_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc01_single717_8_0;;
(* Lean: single717_8_1 *)
let c717eqc01_single717_8_1 = { dmask = 4096; dlower = 1; dupper = 3;
  dallowed = [[0]; [1]; [0; 1]; [3]; [0; 3]; [1; 3]; [0; 1; 3]];
  dqueries = [1039; 1040; 1041; slq_hist_idx 900; 1042; slq_hist_idx 901; slq_hist_idx 902; 1043; 1044; 1045; slq_hist_idx 903; 1046; slq_hist_idx 904; slq_hist_idx 905; 1047; slq_hist_idx 906; slq_hist_idx 907; slq_hist_idx 908; 1048; 1049; 1050; slq_hist_idx 909; 1051; slq_hist_idx 910; slq_hist_idx 911; 1052; slq_hist_idx 912; slq_hist_idx 913; slq_hist_idx 914; 1053; slq_hist_idx 915; slq_hist_idx 916; slq_hist_idx 917; slq_hist_idx 918; 1054; 1055; 1056; slq_hist_idx 919; 1057; slq_hist_idx 920; slq_hist_idx 921; 1058; slq_hist_idx 922; slq_hist_idx 923; slq_hist_idx 924; 1059; slq_hist_idx 925; slq_hist_idx 926; slq_hist_idx 927; slq_hist_idx 928; 1060; slq_hist_idx 929; slq_hist_idx 930; slq_hist_idx 931; slq_hist_idx 932; slq_hist_idx 933; 1061; 1062; 1063; slq_hist_idx 934; 1064; slq_hist_idx 935; slq_hist_idx 936; 1065; slq_hist_idx 937; slq_hist_idx 938; slq_hist_idx 939; 1066; slq_hist_idx 940; slq_hist_idx 941; slq_hist_idx 942; slq_hist_idx 943; 1067; slq_hist_idx 944; slq_hist_idx 945; slq_hist_idx 946; slq_hist_idx 947; slq_hist_idx 948; 1068; slq_hist_idx 949; slq_hist_idx 950; slq_hist_idx 951; slq_hist_idx 952; slq_hist_idx 953; slq_hist_idx 954; 1069; 1070; 1071; slq_hist_idx 955; 1072; slq_hist_idx 956; slq_hist_idx 957; 1073; slq_hist_idx 958; slq_hist_idx 959; slq_hist_idx 960; 1074; slq_hist_idx 961; slq_hist_idx 962; slq_hist_idx 963; slq_hist_idx 964; 1075; slq_hist_idx 965; slq_hist_idx 966; slq_hist_idx 967; slq_hist_idx 968; slq_hist_idx 969; 1076; slq_hist_idx 970; slq_hist_idx 971; slq_hist_idx 972; slq_hist_idx 973; slq_hist_idx 974; slq_hist_idx 975; 1077; slq_hist_idx 976; slq_hist_idx 977; slq_hist_idx 978; slq_hist_idx 979; slq_hist_idx 980; slq_hist_idx 981; slq_hist_idx 982; 1078; 1079; 1080; slq_hist_idx 983; 1081; slq_hist_idx 984; slq_hist_idx 985; 1082; slq_hist_idx 986; slq_hist_idx 987; slq_hist_idx 988; 1083; slq_hist_idx 989; slq_hist_idx 990; slq_hist_idx 991; slq_hist_idx 992; 1084; slq_hist_idx 993; slq_hist_idx 994; slq_hist_idx 995; slq_hist_idx 996; slq_hist_idx 997; 1085; slq_hist_idx 998; slq_hist_idx 999; slq_hist_idx 1000; slq_hist_idx 1001; slq_hist_idx 1002; slq_hist_idx 1003; 1086; slq_hist_idx 1004; slq_hist_idx 1005; slq_hist_idx 1006; slq_hist_idx 1007; slq_hist_idx 1008; slq_hist_idx 1009; slq_hist_idx 1010; 1087; slq_hist_idx 1011; slq_hist_idx 1012; slq_hist_idx 1013; slq_hist_idx 1014; slq_hist_idx 1015; slq_hist_idx 1016; slq_hist_idx 1017; slq_hist_idx 1018] };;
(* Lean: single717_8_1_checked *)
let C717EQC01_SINGLE717_8_1_CHECKED = sodt_checked `c717eqb_family` 1 c717eqc01_single717_8_1;;
(* Lean: single717_9_0 *)
let c717eqc01_single717_9_0 = { dmask = 8192; dlower = 1; dupper = 1;
  dallowed = [[2]; [4]; [6]];
  dqueries = [1145; 1146; 1150; 1157; 1167; 1175; 1184] };;
(* Lean: single717_9_0_checked *)
let C717EQC01_SINGLE717_9_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc01_single717_9_0;;
(* Lean: single717_9_1 *)
let c717eqc01_single717_9_1 = { dmask = 8192; dlower = 1; dupper = 3;
  dallowed = [[2]; [0; 2]; [5]; [2; 5]; [0; 2; 5]; [5; 8]; [2; 5; 8]];
  dqueries = [1194; 1195; 1196; 1197; slq_hist_idx 1021; 1198; 1199; 1200; slq_hist_idx 1022; 1201; slq_hist_idx 1023; slq_hist_idx 1024; 1202; 1203; 1204; slq_hist_idx 1025; 1205; slq_hist_idx 1026; slq_hist_idx 1027; 1206; slq_hist_idx 1028; slq_hist_idx 1029; slq_hist_idx 1030; 1207; 1208; slq_hist_idx 1031; slq_hist_idx 1032; 1209; slq_hist_idx 1033; slq_hist_idx 1034; slq_hist_idx 1035; 1210; slq_hist_idx 1036; slq_hist_idx 1037; slq_hist_idx 1038; slq_hist_idx 1039; 1211; 1212; 1213; slq_hist_idx 1040; 1214; slq_hist_idx 1041; slq_hist_idx 1042; 1215; slq_hist_idx 1043; slq_hist_idx 1044; slq_hist_idx 1045; 1216; slq_hist_idx 1046; slq_hist_idx 1047; slq_hist_idx 1048; slq_hist_idx 1049; 1217; slq_hist_idx 1050; slq_hist_idx 1051; slq_hist_idx 1052; slq_hist_idx 1053; slq_hist_idx 1054; 1218; 1219; 1220; slq_hist_idx 1055; 1221; slq_hist_idx 1056; slq_hist_idx 1057; 1222; slq_hist_idx 1058; slq_hist_idx 1059; slq_hist_idx 1060; 1223; slq_hist_idx 1061; slq_hist_idx 1062; slq_hist_idx 1063; slq_hist_idx 1064; 1224; slq_hist_idx 1065; slq_hist_idx 1066; slq_hist_idx 1067; slq_hist_idx 1068; slq_hist_idx 1069; 1225; slq_hist_idx 1070; slq_hist_idx 1071; slq_hist_idx 1072; slq_hist_idx 1073; slq_hist_idx 1074; slq_hist_idx 1075; 1226; 1227; 1228; slq_hist_idx 1076; 1229; slq_hist_idx 1077; slq_hist_idx 1078; 1230; slq_hist_idx 1079; slq_hist_idx 1080; slq_hist_idx 1081; 1231; slq_hist_idx 1082; slq_hist_idx 1083; slq_hist_idx 1084; slq_hist_idx 1085; slq_hist_idx 1086; slq_hist_idx 1087; slq_hist_idx 1088; slq_hist_idx 1089; 1232; slq_hist_idx 1090; slq_hist_idx 1091; slq_hist_idx 1092; slq_hist_idx 1093; slq_hist_idx 1094; slq_hist_idx 1095; 1233; slq_hist_idx 1096; slq_hist_idx 1097; slq_hist_idx 1098; slq_hist_idx 1099; slq_hist_idx 1100; slq_hist_idx 1101; slq_hist_idx 1102; 1234; 1235; 1236; slq_hist_idx 1103; 1237; slq_hist_idx 1104; slq_hist_idx 1105; 1238; slq_hist_idx 1106; slq_hist_idx 1107; slq_hist_idx 1108; 1239; slq_hist_idx 1109; slq_hist_idx 1110; slq_hist_idx 1111; slq_hist_idx 1112; 1240; slq_hist_idx 1113; slq_hist_idx 1114; slq_hist_idx 1115; slq_hist_idx 1116; slq_hist_idx 1117; 1241; slq_hist_idx 1118; slq_hist_idx 1119; slq_hist_idx 1120; slq_hist_idx 1121; slq_hist_idx 1122; slq_hist_idx 1123; 1242; slq_hist_idx 1124; slq_hist_idx 1125; slq_hist_idx 1126; slq_hist_idx 1127; slq_hist_idx 1128; slq_hist_idx 1129; slq_hist_idx 1130; 1243; slq_hist_idx 1131; slq_hist_idx 1132; slq_hist_idx 1133; slq_hist_idx 1134; slq_hist_idx 1135; slq_hist_idx 1136; slq_hist_idx 1137; slq_hist_idx 1138] };;
(* Lean: single717_9_1_checked *)
let C717EQC01_SINGLE717_9_1_CHECKED = sodt_checked `c717eqb_family` 1 c717eqc01_single717_9_1;;
(* Lean: single717_10_0 *)
let c717eqc01_single717_10_0 = { dmask = 16384; dlower = 1; dupper = 1;
  dallowed = [[8]; [9]];
  dqueries = [1294; 1295; 1297; 1300; 1304; 1309; 1315; 1322] };;
(* Lean: single717_10_0_checked *)
let C717EQC01_SINGLE717_10_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc01_single717_10_0;;
(* Lean: single717_10_1 *)
let c717eqc01_single717_10_1 = { dmask = 16384; dlower = 1; dupper = 3;
  dallowed = [[6]; [8]; [6; 8]; [9]; [6; 9]; [8; 9]; [6; 8; 9]];
  dqueries = [1344; 1345; 1346; 1347; 1348; 1349; slq_hist_idx 1143; 1350; 1351; 1352; slq_hist_idx 1144; 1353; slq_hist_idx 1145; slq_hist_idx 1146; 1354; 1355; 1356; slq_hist_idx 1147; 1357; slq_hist_idx 1148; slq_hist_idx 1149; 1358; slq_hist_idx 1150; slq_hist_idx 1151; slq_hist_idx 1152; 1359; 1360; 1361; slq_hist_idx 1153; 1362; slq_hist_idx 1154; slq_hist_idx 1155; 1363; slq_hist_idx 1156; slq_hist_idx 1157; slq_hist_idx 1158; 1364; slq_hist_idx 1159; slq_hist_idx 1160; slq_hist_idx 1161; slq_hist_idx 1162; 1365; 1366; slq_hist_idx 1163; 1367; slq_hist_idx 1164; slq_hist_idx 1165; 1368; slq_hist_idx 1166; slq_hist_idx 1167; slq_hist_idx 1168; 1369; slq_hist_idx 1169; slq_hist_idx 1170; slq_hist_idx 1171; slq_hist_idx 1172; 1370; slq_hist_idx 1173; slq_hist_idx 1174; slq_hist_idx 1175; slq_hist_idx 1176; slq_hist_idx 1177; 1371; 1372; 1373; slq_hist_idx 1178; 1374; slq_hist_idx 1179; slq_hist_idx 1180; 1375; slq_hist_idx 1181; slq_hist_idx 1182; slq_hist_idx 1183; 1376; slq_hist_idx 1184; slq_hist_idx 1185; slq_hist_idx 1186; slq_hist_idx 1187; 1377; slq_hist_idx 1188; slq_hist_idx 1189; slq_hist_idx 1190; slq_hist_idx 1191; slq_hist_idx 1192; 1378; slq_hist_idx 1193; slq_hist_idx 1194; slq_hist_idx 1195; slq_hist_idx 1196; slq_hist_idx 1197; slq_hist_idx 1198; 1379; 1380; slq_hist_idx 1199; 1381; slq_hist_idx 1200; slq_hist_idx 1201; 1382; slq_hist_idx 1202; slq_hist_idx 1203; slq_hist_idx 1204; 1383; slq_hist_idx 1205; slq_hist_idx 1206; slq_hist_idx 1207; slq_hist_idx 1208; 1384; slq_hist_idx 1209; slq_hist_idx 1210; slq_hist_idx 1211; slq_hist_idx 1212; slq_hist_idx 1213; slq_hist_idx 1214; slq_hist_idx 1215; slq_hist_idx 1216; slq_hist_idx 1217; slq_hist_idx 1218; slq_hist_idx 1219; 1385; slq_hist_idx 1220; slq_hist_idx 1221; slq_hist_idx 1222; slq_hist_idx 1223; slq_hist_idx 1224; slq_hist_idx 1225; slq_hist_idx 1226; 1386; 1387; slq_hist_idx 1227; 1388; slq_hist_idx 1228; slq_hist_idx 1229; 1389; slq_hist_idx 1230; slq_hist_idx 1231; slq_hist_idx 1232; 1390; slq_hist_idx 1233; slq_hist_idx 1234; slq_hist_idx 1235; slq_hist_idx 1236; 1391; slq_hist_idx 1237; slq_hist_idx 1238; slq_hist_idx 1239; slq_hist_idx 1240; slq_hist_idx 1241; slq_hist_idx 1242; slq_hist_idx 1243; slq_hist_idx 1244; slq_hist_idx 1245; slq_hist_idx 1246; slq_hist_idx 1247; 1392; slq_hist_idx 1248; slq_hist_idx 1249; slq_hist_idx 1250; slq_hist_idx 1251; slq_hist_idx 1252; slq_hist_idx 1253; slq_hist_idx 1254; slq_hist_idx 1255; slq_hist_idx 1256; slq_hist_idx 1257; slq_hist_idx 1258; slq_hist_idx 1259; slq_hist_idx 1260; slq_hist_idx 1261] };;
(* Lean: single717_10_1_checked *)
let C717EQC01_SINGLE717_10_1_CHECKED = sodt_checked `c717eqb_family` 1 c717eqc01_single717_10_1;;
(* Lean: single717_11_0 *)
let c717eqc01_single717_11_0 = { dmask = 32768; dlower = 1; dupper = 1;
  dallowed = [[3]; [5]; [7]];
  dqueries = [1536; 1537; 1539; 1545; 1554; 1566; 1575] };;
(* Lean: single717_11_0_checked *)
let C717EQC01_SINGLE717_11_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc01_single717_11_0;;
(* Lean: single717_11_1 *)
let c717eqc01_single717_11_1 = { dmask = 32768; dlower = 1; dupper = 3;
  dallowed = [[4]; [1; 4]; [7]; [4; 7]; [1; 4; 7]; [7; 9]; [4; 7; 9]];
  dqueries = [1585; 1586; 1587; 1588; 1589; 1590; slq_hist_idx 1264; 1591; 1592; 1593; slq_hist_idx 1265; 1594; slq_hist_idx 1266; slq_hist_idx 1267; 1595; slq_hist_idx 1268; 1596; slq_hist_idx 1269; slq_hist_idx 1270; 1597; slq_hist_idx 1271; slq_hist_idx 1272; slq_hist_idx 1273; 1598; 1599; 1600; slq_hist_idx 1274; 1601; slq_hist_idx 1275; slq_hist_idx 1276; 1602; slq_hist_idx 1277; slq_hist_idx 1278; slq_hist_idx 1279; 1603; slq_hist_idx 1280; slq_hist_idx 1281; slq_hist_idx 1282; slq_hist_idx 1283; 1604; 1605; 1606; slq_hist_idx 1284; 1607; slq_hist_idx 1285; slq_hist_idx 1286; 1608; slq_hist_idx 1287; slq_hist_idx 1288; slq_hist_idx 1289; 1609; slq_hist_idx 1290; slq_hist_idx 1291; slq_hist_idx 1292; slq_hist_idx 1293; 1610; slq_hist_idx 1294; slq_hist_idx 1295; slq_hist_idx 1296; slq_hist_idx 1297; slq_hist_idx 1298; 1611; 1612; slq_hist_idx 1299; 1613; slq_hist_idx 1300; slq_hist_idx 1301; 1614; slq_hist_idx 1302; slq_hist_idx 1303; slq_hist_idx 1304; slq_hist_idx 1305; slq_hist_idx 1306; slq_hist_idx 1307; 1615; slq_hist_idx 1308; slq_hist_idx 1309; slq_hist_idx 1310; slq_hist_idx 1311; slq_hist_idx 1312; 1616; slq_hist_idx 1313; slq_hist_idx 1314; slq_hist_idx 1315; slq_hist_idx 1316; slq_hist_idx 1317; slq_hist_idx 1318; 1617; 1618; 1619; slq_hist_idx 1319; 1620; slq_hist_idx 1320; slq_hist_idx 1321; 1621; slq_hist_idx 1322; slq_hist_idx 1323; slq_hist_idx 1324; 1622; slq_hist_idx 1325; slq_hist_idx 1326; slq_hist_idx 1327; slq_hist_idx 1328; 1623; slq_hist_idx 1329; slq_hist_idx 1330; slq_hist_idx 1331; slq_hist_idx 1332; slq_hist_idx 1333; 1624; slq_hist_idx 1334; slq_hist_idx 1335; slq_hist_idx 1336; slq_hist_idx 1337; slq_hist_idx 1338; slq_hist_idx 1339; 1625; slq_hist_idx 1340; slq_hist_idx 1341; slq_hist_idx 1342; slq_hist_idx 1343; slq_hist_idx 1344; slq_hist_idx 1345; slq_hist_idx 1346; 1626; 1627; 1628; slq_hist_idx 1347; 1629; slq_hist_idx 1348; slq_hist_idx 1349; 1630; slq_hist_idx 1350; slq_hist_idx 1351; slq_hist_idx 1352; 1631; slq_hist_idx 1353; slq_hist_idx 1354; slq_hist_idx 1355; slq_hist_idx 1356; 1632; slq_hist_idx 1357; slq_hist_idx 1358; slq_hist_idx 1359; slq_hist_idx 1360; slq_hist_idx 1361; 1633; slq_hist_idx 1362; slq_hist_idx 1363; slq_hist_idx 1364; slq_hist_idx 1365; slq_hist_idx 1366; slq_hist_idx 1367; slq_hist_idx 1368; slq_hist_idx 1369; slq_hist_idx 1370; slq_hist_idx 1371; slq_hist_idx 1372; slq_hist_idx 1373; 1634; slq_hist_idx 1374; slq_hist_idx 1375; slq_hist_idx 1376; slq_hist_idx 1377; slq_hist_idx 1378; slq_hist_idx 1379; slq_hist_idx 1380; slq_hist_idx 1381] };;
(* Lean: single717_11_1_checked *)
let C717EQC01_SINGLE717_11_1_CHECKED = sodt_checked `c717eqb_family` 1 c717eqc01_single717_11_1;;
