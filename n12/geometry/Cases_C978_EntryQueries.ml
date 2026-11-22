(* ========================================================================= *)
(* Port of Compact/Cases/C978/EntryQueries.lean (namespace S12): direct       *)
(* single-owner domains of the C978 entry.  A Lean DirectSingleDomain         *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case978Family k  (SmallOwnerDomain.checked, whose private signature lists  *)
(* are just the query signatures) is                                        *)
(*   dsd_actual `c978eqb_family` k w : |- hdom fam mask k allowed               *)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C978EQS_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C978_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Queries000.ml";;
needs "n12/geometry/Queries001.ml";;
needs "n12/geometry/Queries012.ml";;
needs "n12/geometry/Queries013.ml";;
needs "n12/geometry/Queries024.ml";;
needs "n12/geometry/Queries025.ml";;
needs "n12/geometry/Queries043.ml";;
needs "n12/geometry/Queries048.ml";;
needs "n12/geometry/Queries049.ml";;
needs "n12/geometry/Queries050.ml";;
needs "n12/geometry/Queries051.ml";;
needs "n12/geometry/Queries052.ml";;

(* Lean: single978_0_0 *)
let c978eqs_single978_0_0 = { dmask = 1; dlower = 1; dupper = 2;
  dallowed = [[2]];
  dqueries = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53] };;
(* Lean: single978_0_0_checked *)
let C978EQS_SINGLE978_0_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_0_0;;
(* Lean: single978_0_1 *)
let c978eqs_single978_0_1 = { dmask = 1; dlower = 1; dupper = 2;
  dallowed = [[2]; [0; 2]];
  dqueries = [54; 55; 56; 57; 58; 59; 60; 61; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; 101; 102; 103; 104; 105; 106] };;
(* Lean: single978_0_1_checked *)
let C978EQS_SINGLE978_0_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_0_1;;
(* Lean: single978_1_0 *)
let c978eqs_single978_1_0 = { dmask = 2; dlower = 1; dupper = 2;
  dallowed = [[0]; [0; 2]];
  dqueries = [107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124; 125; 126; 127; 128; 129; 130; 131; 132; 133; 134; 135; 136; 137; 138; 139; 140; 141; 142; 143; 144; 145; 146; 147; 148; 149; 150; 151; 152; 153; 154; 155; 156; 157; 158; 159] };;
(* Lean: single978_1_0_checked *)
let C978EQS_SINGLE978_1_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_1_0;;
(* Lean: single978_1_1 *)
let c978eqs_single978_1_1 = { dmask = 2; dlower = 1; dupper = 2;
  dallowed = [[0]];
  dqueries = [160; 161; 162; 163; 164; 165; 166; 167; 168; 169; 170; 171; 172; 173; 174; 175; 176; 177; 178; 179; 180; 181; 182; 183; 184; 185; 186; 187; 188; 189; 190; 191; 192; 193; 194; 195; 196; 197; 198; 199; 200; 201; 202; 203; 204; 205; 206; 207; 208; 209; 210; 211; 212; 213] };;
(* Lean: single978_1_1_checked *)
let C978EQS_SINGLE978_1_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_1_1;;
(* Lean: single978_2_0 *)
let c978eqs_single978_2_0 = { dmask = 12; dlower = 0; dupper = 1;
  dallowed = [[]; [6]; [8]];
  dqueries = [slq_hist_idx 0; slq_hist_idx 1; slq_hist_idx 2; slq_hist_idx 3; slq_hist_idx 4; slq_hist_idx 5; slq_hist_idx 6; slq_hist_idx 7] };;
(* Lean: single978_2_0_checked *)
let C978EQS_SINGLE978_2_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_2_0;;
(* Lean: single978_2_1 *)
let c978eqs_single978_2_1 = { dmask = 12; dlower = 0; dupper = 1;
  dallowed = [[]; [5]; [8]];
  dqueries = [slq_hist_idx 386; slq_hist_idx 387; slq_hist_idx 389; slq_hist_idx 392; slq_hist_idx 396; slq_hist_idx 406; slq_hist_idx 413; slq_hist_idx 428] };;
(* Lean: single978_2_1_checked *)
let C978EQS_SINGLE978_2_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_2_1;;
(* Lean: single978_3_0 *)
let c978eqs_single978_3_0 = { dmask = 48; dlower = 0; dupper = 1;
  dallowed = [[]; [7]; [9]];
  dqueries = [slq_hist_idx 1387; slq_hist_idx 1388; slq_hist_idx 1389; slq_hist_idx 1390; slq_hist_idx 1391; slq_hist_idx 1392; slq_hist_idx 1393; slq_hist_idx 1394] };;
(* Lean: single978_3_0_checked *)
let C978EQS_SINGLE978_3_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_3_0;;
(* Lean: single978_3_1 *)
let c978eqs_single978_3_1 = { dmask = 48; dlower = 0; dupper = 1;
  dallowed = [[]; [7]; [9]];
  dqueries = [slq_hist_idx 1395; slq_hist_idx 1396; slq_hist_idx 1397; slq_hist_idx 1398; slq_hist_idx 1399; slq_hist_idx 1400; slq_hist_idx 1401; slq_hist_idx 1402] };;
(* Lean: single978_3_1_checked *)
let C978EQS_SINGLE978_3_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_3_1;;
(* Lean: single978_4_0 *)
let c978eqs_single978_4_0 = { dmask = 192; dlower = 0; dupper = 1;
  dallowed = [[]; [1]; [3]];
  dqueries = [slq_hist_idx 53; slq_hist_idx 54; slq_hist_idx 55; slq_hist_idx 56; slq_hist_idx 57; slq_hist_idx 58; slq_hist_idx 59; slq_hist_idx 60] };;
(* Lean: single978_4_0_checked *)
let C978EQS_SINGLE978_4_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_4_0;;
(* Lean: single978_4_1 *)
let c978eqs_single978_4_1 = { dmask = 192; dlower = 0; dupper = 1;
  dallowed = [[]; [1]; [4]];
  dqueries = [slq_hist_idx 769; slq_hist_idx 771; slq_hist_idx 774; slq_hist_idx 781; slq_hist_idx 787; slq_hist_idx 794; slq_hist_idx 802; slq_hist_idx 811] };;
(* Lean: single978_4_1_checked *)
let C978EQS_SINGLE978_4_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_4_1;;
(* Lean: single978_5_0 *)
let c978eqs_single978_5_0 = { dmask = 256; dlower = 1; dupper = 2;
  dallowed = [[0]; [0; 1]; [2]; [0; 2]; [4]; [0; 4]; [1; 4]; [2; 4]; [0; 5]; [4; 5]; [4; 6]];
  dqueries = [429; 430; 431; 432; 433; 434; 435; 436; 437; 438; 439; 440; 441; 442; 443; 444; 445; 446; 447; 448; 449; 450; 451; 452; 453; 454; 455; 456; 457; 458; 459; 460; 461; 462; 463; 464; 465; 466; 467; 468; 469; 470; 471; 472] };;
(* Lean: single978_5_0_checked *)
let C978EQS_SINGLE978_5_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_5_0;;
(* Lean: single978_5_1 *)
let c978eqs_single978_5_1 = { dmask = 256; dlower = 1; dupper = 2;
  dallowed = [[0]; [2]; [0; 2]; [3]; [0; 3]; [1; 3]; [2; 3]; [2; 5]; [3; 5]; [2; 6]; [3; 6]];
  dqueries = [473; 474; 475; 476; 477; 478; 479; 480; 481; 482; 483; 484; 485; 486; 487; 488; 489; 490; 491; 492; 493; 494; 495; 496; 497; 498; 499; 500; 501; 502; 503; 504; 505; 506; 507; 508; 509; 510; 511; 512; 513; 514; 515; 516] };;
(* Lean: single978_5_1_checked *)
let C978EQS_SINGLE978_5_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_5_1;;
(* Lean: single978_6_0 *)
let c978eqs_single978_6_0 = { dmask = 512; dlower = 1; dupper = 2;
  dallowed = [[4]; [2; 4]; [4; 5]; [6]; [4; 6]; [8]; [4; 8]; [5; 8]; [6; 8]; [4; 9]; [8; 9]];
  dqueries = [582; 583; 584; 585; 586; 587; 588; 589; 590; 591; 592; 593; 594; 595; 596; 597; 598; 599; 600; 601; 602; 603; 604; 605; 606; 607; 608; 609; 610; 611; 612; 613; 614; 615; 616; 617; 618; 619; 620; 621; 622; 623; 624; 625] };;
(* Lean: single978_6_0_checked *)
let C978EQS_SINGLE978_6_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_6_0;;
(* Lean: single978_6_1 *)
let c978eqs_single978_6_1 = { dmask = 512; dlower = 1; dupper = 2;
  dallowed = [[5]; [2; 5]; [3; 5]; [6]; [2; 6]; [3; 6]; [5; 6]; [8]; [5; 8]; [6; 8]; [6; 9]];
  dqueries = [626; 627; 628; 629; 630; 631; 632; 633; 634; 635; 636; 637; 638; 639; 640; 641; 642; 643; 644; 645; 646; 647; 648; 649; 650; 651; 652; 653; 654; 655; 656; 657; 658; 659; 660; 661; 662; 663; 664; 665; 666; 667; 668; 669] };;
(* Lean: single978_6_1_checked *)
let C978EQS_SINGLE978_6_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_6_1;;
(* Lean: single978_7_0 *)
let c978eqs_single978_7_0 = { dmask = 2048; dlower = 1; dupper = 2;
  dallowed = [[1]; [0; 1]; [3]; [1; 3]; [1; 4]; [5]; [0; 5]; [1; 5]; [3; 5]; [4; 5]; [5; 7]];
  dqueries = [813; 814; 815; 816; 817; 818; 819; 820; 821; 822; 823; 824; 825; 826; 827; 828; 829; 830; 831; 832; 833; 834; 835; 836; 837; 838; 839; 840; 841; 842; 843; 844; 845; 846; 847; 848; 849; 850; 851; 852; 853; 854; 855; 856] };;
(* Lean: single978_7_0_checked *)
let C978EQS_SINGLE978_7_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_7_0;;
(* Lean: single978_7_1 *)
let c978eqs_single978_7_1 = { dmask = 2048; dlower = 1; dupper = 2;
  dallowed = [[1]; [3]; [0; 3]; [1; 3]; [4]; [1; 4]; [3; 4]; [3; 6]; [4; 6]; [3; 7]; [4; 7]];
  dqueries = [857; 858; 859; 860; 861; 862; 863; 864; 865; 866; 867; 868; 869; 870; 871; 872; 873; 874; 875; 876; 877; 878; 879; 880; 881; 882; 883; 884; 885; 886; 887; 888; 889; 890; 891; 892; 893; 894; 895; 896; 897; 898; 899; 900] };;
(* Lean: single978_7_1_checked *)
let C978EQS_SINGLE978_7_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_7_1;;
(* Lean: single978_8_0 *)
let c978eqs_single978_8_0 = { dmask = 4096; dlower = 1; dupper = 2;
  dallowed = [[0]; [1]; [0; 1]; [0; 2]; [1; 3]];
  dqueries = [989; 990; 991; 992; 993; 994; 995; 996; 997; 998; 999; 1000; 1001; 1002; 1003; 1004; 1005; 1006; 1007; 1008; 1009; 1010; 1011; 1012; 1013; 1014; 1015; 1016; 1017; 1018; 1019; 1020; 1021; 1022; 1023; 1024; 1025; 1026; 1027; 1028; 1029; 1030; 1031; 1032; 1033; 1034; 1035; 1036; 1037; 1038] };;
(* Lean: single978_8_0_checked *)
let C978EQS_SINGLE978_8_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_8_0;;
(* Lean: single978_8_1 *)
let c978eqs_single978_8_1 = { dmask = 4096; dlower = 1; dupper = 2;
  dallowed = [[0]; [1]; [0; 1]; [3]; [0; 3]; [1; 3]];
  dqueries = [1039; 1040; 1041; 1042; 1043; 1044; 1045; 1046; 1047; 1048; 1049; 1050; 1051; 1052; 1053; 1054; 1055; 1056; 1057; 1058; 1059; 1060; 1061; 1062; 1063; 1064; 1065; 1066; 1067; 1068; 1069; 1070; 1071; 1072; 1073; 1074; 1075; 1076; 1077; 1078; 1079; 1080; 1081; 1082; 1083; 1084; 1085; 1086; 1087] };;
(* Lean: single978_8_1_checked *)
let C978EQS_SINGLE978_8_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_8_1;;
(* Lean: single978_9_0 *)
let c978eqs_single978_9_0 = { dmask = 8192; dlower = 1; dupper = 2;
  dallowed = [[2]; [4]; [2; 4]; [6]; [2; 6]; [4; 6]];
  dqueries = [1145; 1146; 1147; 1148; 1149; 1150; 1151; 1152; 1153; 1154; 1155; 1156; 1157; 1158; 1159; 1160; 1161; 1162; 1163; 1164; 1165; 1166; 1167; 1168; 1169; 1170; 1171; 1172; 1173; 1174; 1175; 1176; 1177; 1178; 1179; 1180; 1181; 1182; 1183; 1184; 1185; 1186; 1187; 1188; 1189; 1190; 1191; 1192; 1193] };;
(* Lean: single978_9_0_checked *)
let C978EQS_SINGLE978_9_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_9_0;;
(* Lean: single978_9_1 *)
let c978eqs_single978_9_1 = { dmask = 8192; dlower = 1; dupper = 2;
  dallowed = [[2]; [0; 2]; [5]; [2; 5]; [5; 8]];
  dqueries = [1194; 1195; 1196; 1197; 1198; 1199; 1200; 1201; 1202; 1203; 1204; 1205; 1206; 1207; 1208; 1209; 1210; 1211; 1212; 1213; 1214; 1215; 1216; 1217; 1218; 1219; 1220; 1221; 1222; 1223; 1224; 1225; 1226; 1227; 1228; 1229; 1230; 1231; 1232; 1233; 1234; 1235; 1236; 1237; 1238; 1239; 1240; 1241; 1242; 1243] };;
(* Lean: single978_9_1_checked *)
let C978EQS_SINGLE978_9_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_9_1;;
(* Lean: single978_10_0 *)
let c978eqs_single978_10_0 = { dmask = 16384; dlower = 1; dupper = 2;
  dallowed = [[8]; [6; 8]; [9]; [7; 9]; [8; 9]];
  dqueries = [1294; 1295; 1296; 1297; 1298; 1299; 1300; 1301; 1302; 1303; 1304; 1305; 1306; 1307; 1308; 1309; 1310; 1311; 1312; 1313; 1314; 1315; 1316; 1317; 1318; 1319; 1320; 1321; 1322; 1323; 1324; 1325; 1326; 1327; 1328; 1329; 1330; 1331; 1332; 1333; 1334; 1335; 1336; 1337; 1338; 1339; 1340; 1341; 1342; 1343] };;
(* Lean: single978_10_0_checked *)
let C978EQS_SINGLE978_10_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_10_0;;
(* Lean: single978_10_1 *)
let c978eqs_single978_10_1 = { dmask = 16384; dlower = 1; dupper = 2;
  dallowed = [[6]; [8]; [6; 8]; [9]; [6; 9]; [8; 9]];
  dqueries = [1344; 1345; 1346; 1347; 1348; 1349; 1350; 1351; 1352; 1353; 1354; 1355; 1356; 1357; 1358; 1359; 1360; 1361; 1362; 1363; 1364; 1365; 1366; 1367; 1368; 1369; 1370; 1371; 1372; 1373; 1374; 1375; 1376; 1377; 1378; 1379; 1380; 1381; 1382; 1383; 1384; 1385; 1386; 1387; 1388; 1389; 1390; 1391; 1392] };;
(* Lean: single978_10_1_checked *)
let C978EQS_SINGLE978_10_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_10_1;;
(* Lean: single978_11_0 *)
let c978eqs_single978_11_0 = { dmask = 33792; dlower = 1; dupper = 2;
  dallowed = [[3]; [5]; [3; 5]; [4; 5]; [7]; [3; 7]; [5; 7]; [5; 8]; [5; 9]; [7; 9]];
  dqueries = [slq_hist_idx 1538; slq_hist_idx 1539; slq_hist_idx 1540; slq_hist_idx 1541; slq_hist_idx 1542; slq_hist_idx 1543; slq_hist_idx 1544; slq_hist_idx 1545; slq_hist_idx 1546; slq_hist_idx 1547; slq_hist_idx 1548; slq_hist_idx 1549; slq_hist_idx 1550; slq_hist_idx 1551; slq_hist_idx 1552; slq_hist_idx 1553; slq_hist_idx 1554; slq_hist_idx 1555; slq_hist_idx 1556; slq_hist_idx 1557; slq_hist_idx 1558; slq_hist_idx 1559; slq_hist_idx 1560; slq_hist_idx 1561; slq_hist_idx 1562; slq_hist_idx 1563; slq_hist_idx 1564; slq_hist_idx 1565; slq_hist_idx 1566; slq_hist_idx 1567; slq_hist_idx 1568; slq_hist_idx 1569; slq_hist_idx 1570; slq_hist_idx 1571; slq_hist_idx 1572; slq_hist_idx 1573; slq_hist_idx 1574; slq_hist_idx 1575; slq_hist_idx 1576; slq_hist_idx 1577; slq_hist_idx 1578; slq_hist_idx 1579; slq_hist_idx 1580; slq_hist_idx 1581; slq_hist_idx 1582] };;
(* Lean: single978_11_0_checked *)
let C978EQS_SINGLE978_11_0_CHECKED = dsd_actual `c978eqb_family` 0 c978eqs_single978_11_0;;
(* Lean: single978_11_1 *)
let c978eqs_single978_11_1 = { dmask = 33792; dlower = 1; dupper = 2;
  dallowed = [[6]; [3; 6]; [4; 6]; [7]; [3; 7]; [4; 7]; [6; 7]; [9]; [6; 9]; [7; 9]];
  dqueries = [1713; 1714; slq_hist_idx 1583; 1715; slq_hist_idx 1584; slq_hist_idx 1585; 1716; slq_hist_idx 1586; slq_hist_idx 1587; slq_hist_idx 1588; 1717; slq_hist_idx 1589; slq_hist_idx 1590; slq_hist_idx 1591; slq_hist_idx 1592; 1718; slq_hist_idx 1593; slq_hist_idx 1594; slq_hist_idx 1595; slq_hist_idx 1596; slq_hist_idx 1597; slq_hist_idx 1598; slq_hist_idx 1599; slq_hist_idx 1600; slq_hist_idx 1601; slq_hist_idx 1602; slq_hist_idx 1603; slq_hist_idx 1604; slq_hist_idx 1605; 1719; slq_hist_idx 1606; slq_hist_idx 1607; slq_hist_idx 1608; slq_hist_idx 1609; slq_hist_idx 1610; slq_hist_idx 1611; slq_hist_idx 1612; slq_hist_idx 1613; slq_hist_idx 1614; slq_hist_idx 1615; slq_hist_idx 1616; slq_hist_idx 1617; slq_hist_idx 1618; slq_hist_idx 1619; slq_hist_idx 1620] };;
(* Lean: single978_11_1_checked *)
let C978EQS_SINGLE978_11_1_CHECKED = dsd_actual `c978eqb_family` 1 c978eqs_single978_11_1;;
