(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk01.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC01_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries004.ml";;
needs "n12/geometry/Queries005.ml";;
needs "n12/geometry/Queries006.ml";;
needs "n12/geometry/Queries007.ml";;
needs "n12/geometry/Queries008.ml";;

(* Lean: single979_0_1 *)
let c979eqc01_single979_0_1 = { dmask = 1; dlower = 1; dupper = 3;
  dallowed = [[2]; [0; 2]];
  dqueries = [54; 55; 56; 57; slq_hist_idx 146; 58; 59; 60; slq_hist_idx 147; 61; slq_hist_idx 148; slq_hist_idx 149; 62; 63; 64; slq_hist_idx 150; 65; slq_hist_idx 151; slq_hist_idx 152; 66; slq_hist_idx 153; slq_hist_idx 154; slq_hist_idx 155; 67; 68; 69; slq_hist_idx 156; 70; slq_hist_idx 157; slq_hist_idx 158; 71; slq_hist_idx 159; slq_hist_idx 160; slq_hist_idx 161; 72; slq_hist_idx 162; slq_hist_idx 163; slq_hist_idx 164; slq_hist_idx 165; 73; 74; 75; slq_hist_idx 166; 76; slq_hist_idx 167; slq_hist_idx 168; 77; slq_hist_idx 169; slq_hist_idx 170; slq_hist_idx 171; 78; slq_hist_idx 172; slq_hist_idx 173; slq_hist_idx 174; slq_hist_idx 175; 79; slq_hist_idx 176; slq_hist_idx 177; slq_hist_idx 178; slq_hist_idx 179; slq_hist_idx 180; 80; 81; 82; slq_hist_idx 181; 83; slq_hist_idx 182; slq_hist_idx 183; 84; slq_hist_idx 184; slq_hist_idx 185; slq_hist_idx 186; 85; slq_hist_idx 187; slq_hist_idx 188; slq_hist_idx 189; slq_hist_idx 190; 86; slq_hist_idx 191; slq_hist_idx 192; slq_hist_idx 193; slq_hist_idx 194; slq_hist_idx 195; 87; slq_hist_idx 196; slq_hist_idx 197; slq_hist_idx 198; slq_hist_idx 199; slq_hist_idx 200; slq_hist_idx 201; 88; 89; 90; slq_hist_idx 202; 91; slq_hist_idx 203; slq_hist_idx 204; 92; slq_hist_idx 205; slq_hist_idx 206; slq_hist_idx 207; 93; slq_hist_idx 208; slq_hist_idx 209; slq_hist_idx 210; slq_hist_idx 211; 94; slq_hist_idx 212; slq_hist_idx 213; slq_hist_idx 214; slq_hist_idx 215; slq_hist_idx 216; 95; slq_hist_idx 217; slq_hist_idx 218; slq_hist_idx 219; slq_hist_idx 220; slq_hist_idx 221; slq_hist_idx 222; 96; slq_hist_idx 223; slq_hist_idx 224; slq_hist_idx 225; slq_hist_idx 226; slq_hist_idx 227; slq_hist_idx 228; slq_hist_idx 229; 97; 98; 99; slq_hist_idx 230; 100; slq_hist_idx 231; slq_hist_idx 232; 101; slq_hist_idx 233; slq_hist_idx 234; slq_hist_idx 235; 102; slq_hist_idx 236; slq_hist_idx 237; slq_hist_idx 238; slq_hist_idx 239; 103; slq_hist_idx 240; slq_hist_idx 241; slq_hist_idx 242; slq_hist_idx 243; slq_hist_idx 244; 104; slq_hist_idx 245; slq_hist_idx 246; slq_hist_idx 247; slq_hist_idx 248; slq_hist_idx 249; slq_hist_idx 250; 105; slq_hist_idx 251; slq_hist_idx 252; slq_hist_idx 253; slq_hist_idx 254; slq_hist_idx 255; slq_hist_idx 256; slq_hist_idx 257; 106; slq_hist_idx 258; slq_hist_idx 259; slq_hist_idx 260; slq_hist_idx 261; slq_hist_idx 262; slq_hist_idx 263; slq_hist_idx 264; slq_hist_idx 265] };;
(* Lean: single979_0_1_checked *)
let C979EQC01_SINGLE979_0_1_CHECKED = sodt_checked `c979eqb_family` 1 c979eqc01_single979_0_1;;
