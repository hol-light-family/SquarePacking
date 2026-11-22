(* ========================================================================= *)
(* Port of Compact/Cases/C701/EntryQueries.lean (namespace S12): direct       *)
(* single-owner domains of the C701 entry.  A Lean DirectSingleDomain         *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case701Family k  (SmallOwnerDomain.checked, whose private signature lists  *)
(* are just the query signatures) is                                        *)
(*   dsd_actual `c701eqb_family` k w : |- hdom fam mask k allowed               *)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C701EQS_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C701_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Queries000.ml";;
needs "n12/geometry/Queries001.ml";;
needs "n12/geometry/Queries002.ml";;
needs "n12/geometry/Queries003.ml";;
needs "n12/geometry/Queries004.ml";;

(* Lean: single701_0_0 *)
let c701eqs_single701_0_0 = { dmask = 1; dlower = 1; dupper = 2;
  dallowed = [[2]];
  dqueries = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53] };;
(* Lean: single701_0_0_checked *)
let C701EQS_SINGLE701_0_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_0_0;;
(* Lean: single701_0_1 *)
let c701eqs_single701_0_1 = { dmask = 1; dlower = 1; dupper = 1;
  dallowed = [[2]];
  dqueries = [54; 55; 58; 62; 67; 73; 80; 88; 97] };;
(* Lean: single701_0_1_checked *)
let C701EQS_SINGLE701_0_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_0_1;;
(* Lean: single701_1_0 *)
let c701eqs_single701_1_0 = { dmask = 2; dlower = 1; dupper = 2;
  dallowed = [[0]; [0; 2]];
  dqueries = [107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122; 123; 124; 125; 126; 127; 128; 129; 130; 131; 132; 133; 134; 135; 136; 137; 138; 139; 140; 141; 142; 143; 144; 145; 146; 147; 148; 149; 150; 151; 152; 153; 154; 155; 156; 157; 158; 159] };;
(* Lean: single701_1_0_checked *)
let C701EQS_SINGLE701_1_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_1_0;;
(* Lean: single701_1_1 *)
let c701eqs_single701_1_1 = { dmask = 2; dlower = 1; dupper = 1;
  dallowed = [[0]];
  dqueries = [160; 162; 165; 169; 174; 180; 187; 195; 204] };;
(* Lean: single701_1_1_checked *)
let C701EQS_SINGLE701_1_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_1_1;;
(* Lean: single701_2_0 *)
let c701eqs_single701_2_0 = { dmask = 12; dlower = 0; dupper = 1;
  dallowed = [[]; [6]; [8]];
  dqueries = [slq_hist_idx 0; slq_hist_idx 1; slq_hist_idx 2; slq_hist_idx 3; slq_hist_idx 4; slq_hist_idx 5; slq_hist_idx 6; slq_hist_idx 7] };;
(* Lean: single701_2_0_checked *)
let C701EQS_SINGLE701_2_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_2_0;;
(* Lean: single701_2_1 *)
let c701eqs_single701_2_1 = { dmask = 12; dlower = 0; dupper = 0;
  dallowed = [[]];
  dqueries = [] };;
(* Lean: single701_2_1_checked *)
let C701EQS_SINGLE701_2_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_2_1;;
(* Lean: single701_3_0 *)
let c701eqs_single701_3_0 = { dmask = 16; dlower = 1; dupper = 2;
  dallowed = [[7]];
  dqueries = [339; 340; 341; 342; 343; 344; 345; 346; 347; 348; 349; 350; 351; 352; 353; 354; 355; 356; 357; 358; 359; 360; 361; 362; 363; 364; 365; 366; 367; 368; 369; 370; 371; 372; 373; 374; 375; 376; 377; 378; 379; 380; 381; 382; 383; 384; 385; 386; 387; 388; 389; 390; 391; 392] };;
(* Lean: single701_3_0_checked *)
let C701EQS_SINGLE701_3_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_3_0;;
(* Lean: single701_3_1 *)
let c701eqs_single701_3_1 = { dmask = 16; dlower = 1; dupper = 1;
  dallowed = [[7]];
  dqueries = [393; 394; 395; 396; 397; 398; 399; 400; 401] };;
(* Lean: single701_3_1_checked *)
let C701EQS_SINGLE701_3_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_3_1;;
(* Lean: single701_4_0 *)
let c701eqs_single701_4_0 = { dmask = 32; dlower = 1; dupper = 2;
  dallowed = [[9]; [7; 9]];
  dqueries = [402; 403; slq_hist_idx 9; 404; slq_hist_idx 10; slq_hist_idx 11; 405; slq_hist_idx 12; slq_hist_idx 13; slq_hist_idx 14; 406; slq_hist_idx 15; slq_hist_idx 16; slq_hist_idx 17; slq_hist_idx 18; 407; slq_hist_idx 19; slq_hist_idx 20; slq_hist_idx 21; slq_hist_idx 22; slq_hist_idx 23; 408; slq_hist_idx 24; slq_hist_idx 25; slq_hist_idx 26; slq_hist_idx 27; slq_hist_idx 28; slq_hist_idx 29; 409; slq_hist_idx 30; slq_hist_idx 31; slq_hist_idx 32; slq_hist_idx 33; slq_hist_idx 34; slq_hist_idx 35; slq_hist_idx 36; 410; slq_hist_idx 37; slq_hist_idx 38; slq_hist_idx 39; slq_hist_idx 40; slq_hist_idx 41; slq_hist_idx 42; slq_hist_idx 43; slq_hist_idx 44; slq_hist_idx 45; slq_hist_idx 46; slq_hist_idx 47; slq_hist_idx 48; slq_hist_idx 49; slq_hist_idx 50; slq_hist_idx 51; slq_hist_idx 52] };;
(* Lean: single701_4_0_checked *)
let C701EQS_SINGLE701_4_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_4_0;;
(* Lean: single701_4_1 *)
let c701eqs_single701_4_1 = { dmask = 32; dlower = 1; dupper = 1;
  dallowed = [[9]];
  dqueries = [411; 412; 413; 414; 415; 416; 417; 418; 419] };;
(* Lean: single701_4_1_checked *)
let C701EQS_SINGLE701_4_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_4_1;;
(* Lean: single701_5_0 *)
let c701eqs_single701_5_0 = { dmask = 192; dlower = 0; dupper = 1;
  dallowed = [[]; [1]; [3]];
  dqueries = [slq_hist_idx 53; slq_hist_idx 54; slq_hist_idx 55; slq_hist_idx 56; slq_hist_idx 57; slq_hist_idx 58; slq_hist_idx 59; slq_hist_idx 60] };;
(* Lean: single701_5_0_checked *)
let C701EQS_SINGLE701_5_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_5_0;;
(* Lean: single701_5_1 *)
let c701eqs_single701_5_1 = { dmask = 192; dlower = 0; dupper = 0;
  dallowed = [[]];
  dqueries = [] };;
(* Lean: single701_5_1_checked *)
let C701EQS_SINGLE701_5_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_5_1;;
(* Lean: single701_6_0 *)
let c701eqs_single701_6_0 = { dmask = 256; dlower = 1; dupper = 2;
  dallowed = [[0]; [0; 1]; [2]; [0; 2]; [4]; [0; 4]; [1; 4]; [2; 4]; [0; 5]; [4; 5]; [4; 6]];
  dqueries = [429; 430; 431; 432; 433; 434; 435; 436; 437; 438; 439; 440; 441; 442; 443; 444; 445; 446; 447; 448; 449; 450; 451; 452; 453; 454; 455; 456; 457; 458; 459; 460; 461; 462; 463; 464; 465; 466; 467; 468; 469; 470; 471; 472] };;
(* Lean: single701_6_0_checked *)
let C701EQS_SINGLE701_6_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_6_0;;
(* Lean: single701_6_1 *)
let c701eqs_single701_6_1 = { dmask = 256; dlower = 1; dupper = 1;
  dallowed = [[0]; [2]; [3]];
  dqueries = [473; 476; 481; 485; 490; 498; 507] };;
(* Lean: single701_6_1_checked *)
let C701EQS_SINGLE701_6_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_6_1;;
(* Lean: single701_7_0 *)
let c701eqs_single701_7_0 = { dmask = 1536; dlower = 0; dupper = 1;
  dallowed = [[]; [4]; [5]; [6]; [7]; [8]; [9]];
  dqueries = [slq_hist_idx 62; slq_hist_idx 63; slq_hist_idx 64; slq_hist_idx 65] };;
(* Lean: single701_7_0_checked *)
let C701EQS_SINGLE701_7_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_7_0;;
(* Lean: single701_7_1 *)
let c701eqs_single701_7_1 = { dmask = 1536; dlower = 1; dupper = 1;
  dallowed = [[6]];
  dqueries = [slq_hist_idx 66; slq_hist_idx 67; slq_hist_idx 68; slq_hist_idx 69; slq_hist_idx 70; slq_hist_idx 71; slq_hist_idx 72; slq_hist_idx 73; slq_hist_idx 74] };;
(* Lean: single701_7_1_checked *)
let C701EQS_SINGLE701_7_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_7_1;;
(* Lean: single701_8_0 *)
let c701eqs_single701_8_0 = { dmask = 4096; dlower = 1; dupper = 2;
  dallowed = [[0]; [1]; [0; 1]; [0; 2]; [1; 3]];
  dqueries = [989; 990; 991; 992; 993; 994; 995; 996; 997; 998; 999; 1000; 1001; 1002; 1003; 1004; 1005; 1006; 1007; 1008; 1009; 1010; 1011; 1012; 1013; 1014; 1015; 1016; 1017; 1018; 1019; 1020; 1021; 1022; 1023; 1024; 1025; 1026; 1027; 1028; 1029; 1030; 1031; 1032; 1033; 1034; 1035; 1036; 1037; 1038] };;
(* Lean: single701_8_0_checked *)
let C701EQS_SINGLE701_8_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_8_0;;
(* Lean: single701_8_1 *)
let c701eqs_single701_8_1 = { dmask = 4096; dlower = 1; dupper = 1;
  dallowed = [[0]; [1]; [3]];
  dqueries = [1039; 1043; 1048; 1054; 1061; 1069; 1078] };;
(* Lean: single701_8_1_checked *)
let C701EQS_SINGLE701_8_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_8_1;;
(* Lean: single701_9_0 *)
let c701eqs_single701_9_0 = { dmask = 8192; dlower = 1; dupper = 2;
  dallowed = [[2]; [4]; [2; 4]; [6]; [2; 6]; [4; 6]];
  dqueries = [1145; 1146; 1147; 1148; 1149; 1150; 1151; 1152; 1153; 1154; 1155; 1156; 1157; 1158; 1159; 1160; 1161; 1162; 1163; 1164; 1165; 1166; 1167; 1168; 1169; 1170; 1171; 1172; 1173; 1174; 1175; 1176; 1177; 1178; 1179; 1180; 1181; 1182; 1183; 1184; 1185; 1186; 1187; 1188; 1189; 1190; 1191; 1192; 1193] };;
(* Lean: single701_9_0_checked *)
let C701EQS_SINGLE701_9_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_9_0;;
(* Lean: single701_9_1 *)
let c701eqs_single701_9_1 = { dmask = 8192; dlower = 1; dupper = 1;
  dallowed = [[2]; [5]];
  dqueries = [1194; 1195; 1198; 1202; 1211; 1218; 1226; 1234] };;
(* Lean: single701_9_1_checked *)
let C701EQS_SINGLE701_9_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_9_1;;
(* Lean: single701_10_0 *)
let c701eqs_single701_10_0 = { dmask = 16384; dlower = 1; dupper = 2;
  dallowed = [[8]; [6; 8]; [9]; [7; 9]; [8; 9]];
  dqueries = [1294; 1295; 1296; 1297; 1298; 1299; 1300; 1301; 1302; 1303; 1304; 1305; 1306; 1307; 1308; 1309; 1310; 1311; 1312; 1313; 1314; 1315; 1316; 1317; 1318; 1319; 1320; 1321; 1322; 1323; 1324; 1325; 1326; 1327; 1328; 1329; 1330; 1331; 1332; 1333; 1334; 1335; 1336; 1337; 1338; 1339; 1340; 1341; 1342; 1343] };;
(* Lean: single701_10_0_checked *)
let C701EQS_SINGLE701_10_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_10_0;;
(* Lean: single701_10_1 *)
let c701eqs_single701_10_1 = { dmask = 16384; dlower = 1; dupper = 1;
  dallowed = [[6]; [8]; [9]];
  dqueries = [1344; 1345; 1347; 1350; 1354; 1359; 1371] };;
(* Lean: single701_10_1_checked *)
let C701EQS_SINGLE701_10_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_10_1;;
(* Lean: single701_11_0 *)
let c701eqs_single701_11_0 = { dmask = 34816; dlower = 1; dupper = 2;
  dallowed = [[3]; [1; 3]; [5]; [0; 5]; [1; 5]; [3; 5]; [4; 5]; [7]; [3; 7]; [5; 7]];
  dqueries = [slq_hist_idx 75; slq_hist_idx 76; slq_hist_idx 77; slq_hist_idx 78; slq_hist_idx 79; slq_hist_idx 80; slq_hist_idx 81; slq_hist_idx 82; slq_hist_idx 83; slq_hist_idx 84; slq_hist_idx 85; slq_hist_idx 86; slq_hist_idx 87; slq_hist_idx 88; slq_hist_idx 89; slq_hist_idx 90; slq_hist_idx 91; slq_hist_idx 92; slq_hist_idx 93; slq_hist_idx 94; slq_hist_idx 95; slq_hist_idx 96; slq_hist_idx 97; slq_hist_idx 98; slq_hist_idx 99; slq_hist_idx 100; slq_hist_idx 101; slq_hist_idx 102; slq_hist_idx 103; slq_hist_idx 104; slq_hist_idx 105; slq_hist_idx 106; slq_hist_idx 107; slq_hist_idx 108; slq_hist_idx 109; slq_hist_idx 110; slq_hist_idx 111; slq_hist_idx 112; slq_hist_idx 113; slq_hist_idx 114; slq_hist_idx 115; slq_hist_idx 116; slq_hist_idx 117; slq_hist_idx 118; slq_hist_idx 119] };;
(* Lean: single701_11_0_checked *)
let C701EQS_SINGLE701_11_0_CHECKED = dsd_actual `c701eqb_family` 0 c701eqs_single701_11_0;;
(* Lean: single701_11_1 *)
let c701eqs_single701_11_1 = { dmask = 34816; dlower = 1; dupper = 1;
  dallowed = [[1]; [3]; [4]];
  dqueries = [slq_hist_idx 120; slq_hist_idx 121; slq_hist_idx 122; slq_hist_idx 123; slq_hist_idx 124; slq_hist_idx 125; slq_hist_idx 126] };;
(* Lean: single701_11_1_checked *)
let C701EQS_SINGLE701_11_1_CHECKED = dsd_actual `c701eqb_family` 1 c701eqs_single701_11_1;;
