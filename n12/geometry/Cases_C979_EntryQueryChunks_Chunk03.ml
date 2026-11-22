(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk03.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC03_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries008.ml";;
needs "n12/geometry/Queries009.ml";;
needs "n12/geometry/Queries010.ml";;
needs "n12/geometry/Queries011.ml";;
needs "n12/geometry/Queries012.ml";;

(* Lean: single979_1_1 *)
let c979eqc03_single979_1_1 = { dmask = 2; dlower = 1; dupper = 3;
  dallowed = [[0]];
  dqueries = [160; 161; 162; 163; 164; slq_hist_idx 266; 165; 166; 167; slq_hist_idx 267; 168; slq_hist_idx 268; slq_hist_idx 269; 169; 170; 171; slq_hist_idx 270; 172; slq_hist_idx 271; slq_hist_idx 272; 173; slq_hist_idx 273; slq_hist_idx 274; slq_hist_idx 275; 174; 175; 176; slq_hist_idx 276; 177; slq_hist_idx 277; slq_hist_idx 278; 178; slq_hist_idx 279; slq_hist_idx 280; slq_hist_idx 281; 179; slq_hist_idx 282; slq_hist_idx 283; slq_hist_idx 284; slq_hist_idx 285; 180; 181; 182; slq_hist_idx 286; 183; slq_hist_idx 287; slq_hist_idx 288; 184; slq_hist_idx 289; slq_hist_idx 290; slq_hist_idx 291; 185; slq_hist_idx 292; slq_hist_idx 293; slq_hist_idx 294; slq_hist_idx 295; 186; slq_hist_idx 296; slq_hist_idx 297; slq_hist_idx 298; slq_hist_idx 299; slq_hist_idx 300; 187; 188; 189; slq_hist_idx 301; 190; slq_hist_idx 302; slq_hist_idx 303; 191; slq_hist_idx 304; slq_hist_idx 305; slq_hist_idx 306; 192; slq_hist_idx 307; slq_hist_idx 308; slq_hist_idx 309; slq_hist_idx 310; 193; slq_hist_idx 311; slq_hist_idx 312; slq_hist_idx 313; slq_hist_idx 314; slq_hist_idx 315; 194; slq_hist_idx 316; slq_hist_idx 317; slq_hist_idx 318; slq_hist_idx 319; slq_hist_idx 320; slq_hist_idx 321; 195; 196; 197; slq_hist_idx 322; 198; slq_hist_idx 323; slq_hist_idx 324; 199; slq_hist_idx 325; slq_hist_idx 326; slq_hist_idx 327; 200; slq_hist_idx 328; slq_hist_idx 329; slq_hist_idx 330; slq_hist_idx 331; 201; slq_hist_idx 332; slq_hist_idx 333; slq_hist_idx 334; slq_hist_idx 335; slq_hist_idx 336; 202; slq_hist_idx 337; slq_hist_idx 338; slq_hist_idx 339; slq_hist_idx 340; slq_hist_idx 341; slq_hist_idx 342; 203; slq_hist_idx 343; slq_hist_idx 344; slq_hist_idx 345; slq_hist_idx 346; slq_hist_idx 347; slq_hist_idx 348; slq_hist_idx 349; 204; 205; 206; slq_hist_idx 350; 207; slq_hist_idx 351; slq_hist_idx 352; 208; slq_hist_idx 353; slq_hist_idx 354; slq_hist_idx 355; 209; slq_hist_idx 356; slq_hist_idx 357; slq_hist_idx 358; slq_hist_idx 359; 210; slq_hist_idx 360; slq_hist_idx 361; slq_hist_idx 362; slq_hist_idx 363; slq_hist_idx 364; 211; slq_hist_idx 365; slq_hist_idx 366; slq_hist_idx 367; slq_hist_idx 368; slq_hist_idx 369; slq_hist_idx 370; 212; slq_hist_idx 371; slq_hist_idx 372; slq_hist_idx 373; slq_hist_idx 374; slq_hist_idx 375; slq_hist_idx 376; slq_hist_idx 377; 213; slq_hist_idx 378; slq_hist_idx 379; slq_hist_idx 380; slq_hist_idx 381; slq_hist_idx 382; slq_hist_idx 383; slq_hist_idx 384; slq_hist_idx 385] };;
(* Lean: single979_1_1_checked *)
let C979EQC03_SINGLE979_1_1_CHECKED = sodt_checked `c979eqb_family` 1 c979eqc03_single979_1_1;;
