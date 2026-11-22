(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk18.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC18_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;


(* Lean: single979_9_0 *)
let c979eqc18_single979_9_0 = { dmask = 8192; dlower = 1; dupper = 2;
  dallowed = [[2]; [4]; [2; 4]; [6]; [2; 6]; [4; 6]];
  dqueries = [1145; 1146; 1147; 1148; 1149; 1150; 1151; 1152; 1153; 1154; 1155; 1156; 1157; 1158; 1159; 1160; 1161; 1162; 1163; 1164; 1165; 1166; 1167; 1168; 1169; 1170; 1171; 1172; 1173; 1174; 1175; 1176; 1177; 1178; 1179; 1180; 1181; 1182; 1183; 1184; 1185; 1186; 1187; 1188; 1189; 1190; 1191; 1192; 1193] };;
(* Lean: single979_9_0_checked *)
let C979EQC18_SINGLE979_9_0_CHECKED = dsd_actual `c979eqb_family` 0 c979eqc18_single979_9_0;;
