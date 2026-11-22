(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk20.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC20_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;


(* Lean: single979_10_0 *)
let c979eqc20_single979_10_0 = { dmask = 16384; dlower = 1; dupper = 2;
  dallowed = [[8]; [6; 8]; [9]; [7; 9]; [8; 9]];
  dqueries = [1294; 1295; 1296; 1297; 1298; 1299; 1300; 1301; 1302; 1303; 1304; 1305; 1306; 1307; 1308; 1309; 1310; 1311; 1312; 1313; 1314; 1315; 1316; 1317; 1318; 1319; 1320; 1321; 1322; 1323; 1324; 1325; 1326; 1327; 1328; 1329; 1330; 1331; 1332; 1333; 1334; 1335; 1336; 1337; 1338; 1339; 1340; 1341; 1342; 1343] };;
(* Lean: single979_10_0_checked *)
let C979EQC20_SINGLE979_10_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc20_single979_10_0;;
