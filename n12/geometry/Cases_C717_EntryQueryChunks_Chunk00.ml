(* ========================================================================= *)
(* Port of Compact/Cases/C717/EntryQueryChunks/Chunk00.lean (namespace S12):*)
(* direct single-owner domains of the C717 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case717Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c717eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C717EQC00_.                     *)
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

(* Lean: single717_0_0 *)
let c717eqc00_single717_0_0 = { dmask = 1; dlower = 1; dupper = 1;
  dallowed = [[2]];
  dqueries = [0; 1; 5; 9; 14; 20; 27; 35; 44] };;
(* Lean: single717_0_0_checked *)
let C717EQC00_SINGLE717_0_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc00_single717_0_0;;
(* Lean: single717_0_1 *)
let c717eqc00_single717_0_1 = { dmask = 1; dlower = 1; dupper = 3;
  dallowed = [[2]; [0; 2]];
  dqueries = [54; 55; 56; 57; slq_hist_idx 146; 58; 59; 60; slq_hist_idx 147; 61; slq_hist_idx 148; slq_hist_idx 149; 62; 63; 64; slq_hist_idx 150; 65; slq_hist_idx 151; slq_hist_idx 152; 66; slq_hist_idx 153; slq_hist_idx 154; slq_hist_idx 155; 67; 68; 69; slq_hist_idx 156; 70; slq_hist_idx 157; slq_hist_idx 158; 71; slq_hist_idx 159; slq_hist_idx 160; slq_hist_idx 161; 72; slq_hist_idx 162; slq_hist_idx 163; slq_hist_idx 164; slq_hist_idx 165; 73; 74; 75; slq_hist_idx 166; 76; slq_hist_idx 167; slq_hist_idx 168; 77; slq_hist_idx 169; slq_hist_idx 170; slq_hist_idx 171; 78; slq_hist_idx 172; slq_hist_idx 173; slq_hist_idx 174; slq_hist_idx 175; 79; slq_hist_idx 176; slq_hist_idx 177; slq_hist_idx 178; slq_hist_idx 179; slq_hist_idx 180; 80; 81; 82; slq_hist_idx 181; 83; slq_hist_idx 182; slq_hist_idx 183; 84; slq_hist_idx 184; slq_hist_idx 185; slq_hist_idx 186; 85; slq_hist_idx 187; slq_hist_idx 188; slq_hist_idx 189; slq_hist_idx 190; 86; slq_hist_idx 191; slq_hist_idx 192; slq_hist_idx 193; slq_hist_idx 194; slq_hist_idx 195; 87; slq_hist_idx 196; slq_hist_idx 197; slq_hist_idx 198; slq_hist_idx 199; slq_hist_idx 200; slq_hist_idx 201; 88; 89; 90; slq_hist_idx 202; 91; slq_hist_idx 203; slq_hist_idx 204; 92; slq_hist_idx 205; slq_hist_idx 206; slq_hist_idx 207; 93; slq_hist_idx 208; slq_hist_idx 209; slq_hist_idx 210; slq_hist_idx 211; 94; slq_hist_idx 212; slq_hist_idx 213; slq_hist_idx 214; slq_hist_idx 215; slq_hist_idx 216; 95; slq_hist_idx 217; slq_hist_idx 218; slq_hist_idx 219; slq_hist_idx 220; slq_hist_idx 221; slq_hist_idx 222; 96; slq_hist_idx 223; slq_hist_idx 224; slq_hist_idx 225; slq_hist_idx 226; slq_hist_idx 227; slq_hist_idx 228; slq_hist_idx 229; 97; 98; 99; slq_hist_idx 230; 100; slq_hist_idx 231; slq_hist_idx 232; 101; slq_hist_idx 233; slq_hist_idx 234; slq_hist_idx 235; 102; slq_hist_idx 236; slq_hist_idx 237; slq_hist_idx 238; slq_hist_idx 239; 103; slq_hist_idx 240; slq_hist_idx 241; slq_hist_idx 242; slq_hist_idx 243; slq_hist_idx 244; 104; slq_hist_idx 245; slq_hist_idx 246; slq_hist_idx 247; slq_hist_idx 248; slq_hist_idx 249; slq_hist_idx 250; 105; slq_hist_idx 251; slq_hist_idx 252; slq_hist_idx 253; slq_hist_idx 254; slq_hist_idx 255; slq_hist_idx 256; slq_hist_idx 257; 106; slq_hist_idx 258; slq_hist_idx 259; slq_hist_idx 260; slq_hist_idx 261; slq_hist_idx 262; slq_hist_idx 263; slq_hist_idx 264; slq_hist_idx 265] };;
(* Lean: single717_0_1_checked *)
let C717EQC00_SINGLE717_0_1_CHECKED = sodt_checked `c717eqb_family` 1 c717eqc00_single717_0_1;;
(* Lean: single717_1_0 *)
let c717eqc00_single717_1_0 = { dmask = 2; dlower = 1; dupper = 1;
  dallowed = [[0]];
  dqueries = [107; 109; 111; 115; 120; 126; 133; 141; 150] };;
(* Lean: single717_1_0_checked *)
let C717EQC00_SINGLE717_1_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc00_single717_1_0;;
(* Lean: single717_1_1 *)
let c717eqc00_single717_1_1 = { dmask = 2; dlower = 1; dupper = 3;
  dallowed = [[0]];
  dqueries = [160; 161; 162; 163; 164; slq_hist_idx 266; 165; 166; 167; slq_hist_idx 267; 168; slq_hist_idx 268; slq_hist_idx 269; 169; 170; 171; slq_hist_idx 270; 172; slq_hist_idx 271; slq_hist_idx 272; 173; slq_hist_idx 273; slq_hist_idx 274; slq_hist_idx 275; 174; 175; 176; slq_hist_idx 276; 177; slq_hist_idx 277; slq_hist_idx 278; 178; slq_hist_idx 279; slq_hist_idx 280; slq_hist_idx 281; 179; slq_hist_idx 282; slq_hist_idx 283; slq_hist_idx 284; slq_hist_idx 285; 180; 181; 182; slq_hist_idx 286; 183; slq_hist_idx 287; slq_hist_idx 288; 184; slq_hist_idx 289; slq_hist_idx 290; slq_hist_idx 291; 185; slq_hist_idx 292; slq_hist_idx 293; slq_hist_idx 294; slq_hist_idx 295; 186; slq_hist_idx 296; slq_hist_idx 297; slq_hist_idx 298; slq_hist_idx 299; slq_hist_idx 300; 187; 188; 189; slq_hist_idx 301; 190; slq_hist_idx 302; slq_hist_idx 303; 191; slq_hist_idx 304; slq_hist_idx 305; slq_hist_idx 306; 192; slq_hist_idx 307; slq_hist_idx 308; slq_hist_idx 309; slq_hist_idx 310; 193; slq_hist_idx 311; slq_hist_idx 312; slq_hist_idx 313; slq_hist_idx 314; slq_hist_idx 315; 194; slq_hist_idx 316; slq_hist_idx 317; slq_hist_idx 318; slq_hist_idx 319; slq_hist_idx 320; slq_hist_idx 321; 195; 196; 197; slq_hist_idx 322; 198; slq_hist_idx 323; slq_hist_idx 324; 199; slq_hist_idx 325; slq_hist_idx 326; slq_hist_idx 327; 200; slq_hist_idx 328; slq_hist_idx 329; slq_hist_idx 330; slq_hist_idx 331; 201; slq_hist_idx 332; slq_hist_idx 333; slq_hist_idx 334; slq_hist_idx 335; slq_hist_idx 336; 202; slq_hist_idx 337; slq_hist_idx 338; slq_hist_idx 339; slq_hist_idx 340; slq_hist_idx 341; slq_hist_idx 342; 203; slq_hist_idx 343; slq_hist_idx 344; slq_hist_idx 345; slq_hist_idx 346; slq_hist_idx 347; slq_hist_idx 348; slq_hist_idx 349; 204; 205; 206; slq_hist_idx 350; 207; slq_hist_idx 351; slq_hist_idx 352; 208; slq_hist_idx 353; slq_hist_idx 354; slq_hist_idx 355; 209; slq_hist_idx 356; slq_hist_idx 357; slq_hist_idx 358; slq_hist_idx 359; 210; slq_hist_idx 360; slq_hist_idx 361; slq_hist_idx 362; slq_hist_idx 363; slq_hist_idx 364; 211; slq_hist_idx 365; slq_hist_idx 366; slq_hist_idx 367; slq_hist_idx 368; slq_hist_idx 369; slq_hist_idx 370; 212; slq_hist_idx 371; slq_hist_idx 372; slq_hist_idx 373; slq_hist_idx 374; slq_hist_idx 375; slq_hist_idx 376; slq_hist_idx 377; 213; slq_hist_idx 378; slq_hist_idx 379; slq_hist_idx 380; slq_hist_idx 381; slq_hist_idx 382; slq_hist_idx 383; slq_hist_idx 384; slq_hist_idx 385] };;
(* Lean: single717_1_1_checked *)
let C717EQC00_SINGLE717_1_1_CHECKED = sodt_checked `c717eqb_family` 1 c717eqc00_single717_1_1;;
(* Lean: single717_2_0 *)
let c717eqc00_single717_2_0 = { dmask = 12; dlower = 0; dupper = 0;
  dallowed = [[]];
  dqueries = [] };;
(* Lean: single717_2_0_checked *)
let C717EQC00_SINGLE717_2_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc00_single717_2_0;;
(* Lean: single717_2_1 *)
let c717eqc00_single717_2_1 = { dmask = 12; dlower = 0; dupper = 2;
  dallowed = [[]; [5]; [8]; [5; 8]];
  dqueries = [slq_hist_idx 386; slq_hist_idx 387; slq_hist_idx 388; slq_hist_idx 389; slq_hist_idx 390; slq_hist_idx 391; slq_hist_idx 392; slq_hist_idx 393; slq_hist_idx 394; slq_hist_idx 395; slq_hist_idx 396; slq_hist_idx 397; slq_hist_idx 398; slq_hist_idx 399; slq_hist_idx 400; slq_hist_idx 401; slq_hist_idx 402; slq_hist_idx 403; slq_hist_idx 404; slq_hist_idx 405; slq_hist_idx 406; slq_hist_idx 407; slq_hist_idx 408; slq_hist_idx 409; slq_hist_idx 410; slq_hist_idx 411; slq_hist_idx 412; slq_hist_idx 413; slq_hist_idx 414; slq_hist_idx 415; slq_hist_idx 416; slq_hist_idx 417; slq_hist_idx 418; slq_hist_idx 419; slq_hist_idx 420; slq_hist_idx 421; slq_hist_idx 422; slq_hist_idx 423; slq_hist_idx 424; slq_hist_idx 425; slq_hist_idx 426; slq_hist_idx 427; slq_hist_idx 428; slq_hist_idx 429; slq_hist_idx 430; slq_hist_idx 431; slq_hist_idx 432; slq_hist_idx 433; slq_hist_idx 434; slq_hist_idx 435; slq_hist_idx 436; slq_hist_idx 437] };;
(* Lean: single717_2_1_checked *)
let C717EQC00_SINGLE717_2_1_CHECKED = dsd_actual `c717eqb_family` 1 c717eqc00_single717_2_1;;
(* Lean: single717_3_0 *)
let c717eqc00_single717_3_0 = { dmask = 16; dlower = 1; dupper = 1;
  dallowed = [[7]];
  dqueries = [339; 340; 342; 345; 349; 354; 360; 374; 383] };;
(* Lean: single717_3_0_checked *)
let C717EQC00_SINGLE717_3_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc00_single717_3_0;;
(* Lean: single717_3_1 *)
let c717eqc00_single717_3_1 = { dmask = 16; dlower = 1; dupper = 3;
  dallowed = [[7]; [7; 9]];
  dqueries = [393; 394; slq_hist_idx 440; 395; slq_hist_idx 441; slq_hist_idx 442; slq_hist_idx 443; 396; slq_hist_idx 444; slq_hist_idx 445; slq_hist_idx 446; slq_hist_idx 447; slq_hist_idx 448; slq_hist_idx 449; 397; slq_hist_idx 450; slq_hist_idx 451; slq_hist_idx 452; slq_hist_idx 453; slq_hist_idx 454; slq_hist_idx 455; slq_hist_idx 456; slq_hist_idx 457; slq_hist_idx 458; slq_hist_idx 459; 398; slq_hist_idx 460; slq_hist_idx 461; slq_hist_idx 462; slq_hist_idx 463; slq_hist_idx 464; slq_hist_idx 465; slq_hist_idx 466; slq_hist_idx 467; slq_hist_idx 468; slq_hist_idx 469; slq_hist_idx 470; slq_hist_idx 471; slq_hist_idx 472; slq_hist_idx 473; slq_hist_idx 474; 399; slq_hist_idx 475; slq_hist_idx 476; slq_hist_idx 477; slq_hist_idx 478; slq_hist_idx 479; slq_hist_idx 480; slq_hist_idx 481; slq_hist_idx 482; slq_hist_idx 483; slq_hist_idx 484; slq_hist_idx 485; slq_hist_idx 486; slq_hist_idx 487; slq_hist_idx 488; slq_hist_idx 489; slq_hist_idx 490; slq_hist_idx 491; slq_hist_idx 492; slq_hist_idx 493; slq_hist_idx 494; slq_hist_idx 495; slq_hist_idx 496; slq_hist_idx 497; slq_hist_idx 498; slq_hist_idx 499; slq_hist_idx 500; slq_hist_idx 501; slq_hist_idx 502; slq_hist_idx 503; slq_hist_idx 504; slq_hist_idx 505; slq_hist_idx 506; slq_hist_idx 507; slq_hist_idx 508; slq_hist_idx 509; slq_hist_idx 510; slq_hist_idx 511; slq_hist_idx 512; slq_hist_idx 513; slq_hist_idx 514; slq_hist_idx 515; slq_hist_idx 516; slq_hist_idx 517; slq_hist_idx 518; slq_hist_idx 519; slq_hist_idx 520; slq_hist_idx 521; slq_hist_idx 522; slq_hist_idx 523; 400; slq_hist_idx 524; slq_hist_idx 525; slq_hist_idx 526; slq_hist_idx 527; slq_hist_idx 528; slq_hist_idx 529; slq_hist_idx 530; slq_hist_idx 531; slq_hist_idx 532; slq_hist_idx 533; slq_hist_idx 534; slq_hist_idx 535; slq_hist_idx 536; slq_hist_idx 537; slq_hist_idx 538; slq_hist_idx 539; slq_hist_idx 540; slq_hist_idx 541; slq_hist_idx 542; slq_hist_idx 543; slq_hist_idx 544; slq_hist_idx 545; slq_hist_idx 546; slq_hist_idx 547; slq_hist_idx 548; slq_hist_idx 549; slq_hist_idx 550; slq_hist_idx 551; slq_hist_idx 552; slq_hist_idx 553; slq_hist_idx 554; slq_hist_idx 555; slq_hist_idx 556; slq_hist_idx 557; slq_hist_idx 558; slq_hist_idx 559; 401; slq_hist_idx 560; slq_hist_idx 561; slq_hist_idx 562; slq_hist_idx 563; slq_hist_idx 564; slq_hist_idx 565; slq_hist_idx 566; slq_hist_idx 567; slq_hist_idx 568; slq_hist_idx 569; slq_hist_idx 570; slq_hist_idx 571; slq_hist_idx 572; slq_hist_idx 573; slq_hist_idx 574; slq_hist_idx 575; slq_hist_idx 576; slq_hist_idx 577; slq_hist_idx 578; slq_hist_idx 579; slq_hist_idx 580; slq_hist_idx 581; slq_hist_idx 582; slq_hist_idx 583; slq_hist_idx 584; slq_hist_idx 585; slq_hist_idx 586; slq_hist_idx 587; slq_hist_idx 588; slq_hist_idx 589; slq_hist_idx 590; slq_hist_idx 591; slq_hist_idx 592; slq_hist_idx 593; slq_hist_idx 594; slq_hist_idx 595; slq_hist_idx 596; slq_hist_idx 597; slq_hist_idx 598; slq_hist_idx 599; slq_hist_idx 600; slq_hist_idx 601; slq_hist_idx 602; slq_hist_idx 603] };;
(* Lean: single717_3_1_checked *)
let C717EQC00_SINGLE717_3_1_CHECKED = sodt_checked `c717eqb_family` 1 c717eqc00_single717_3_1;;
(* Lean: single717_4_0 *)
let c717eqc00_single717_4_0 = { dmask = 32; dlower = 1; dupper = 1;
  dallowed = [[9]];
  dqueries = [402; 403; 404; 405; 406; 407; 408; 409; 410] };;
(* Lean: single717_4_0_checked *)
let C717EQC00_SINGLE717_4_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc00_single717_4_0;;
(* Lean: single717_4_1 *)
let c717eqc00_single717_4_1 = { dmask = 32; dlower = 1; dupper = 3;
  dallowed = [[9]];
  dqueries = [411; 412; slq_hist_idx 604; 413; slq_hist_idx 605; slq_hist_idx 606; slq_hist_idx 607; 414; slq_hist_idx 608; slq_hist_idx 609; slq_hist_idx 610; slq_hist_idx 611; slq_hist_idx 612; slq_hist_idx 613; 415; slq_hist_idx 614; slq_hist_idx 615; slq_hist_idx 616; slq_hist_idx 617; slq_hist_idx 618; slq_hist_idx 619; slq_hist_idx 620; slq_hist_idx 621; slq_hist_idx 622; slq_hist_idx 623; 416; slq_hist_idx 624; slq_hist_idx 625; slq_hist_idx 626; slq_hist_idx 627; slq_hist_idx 628; slq_hist_idx 629; slq_hist_idx 630; slq_hist_idx 631; slq_hist_idx 632; slq_hist_idx 633; slq_hist_idx 634; slq_hist_idx 635; slq_hist_idx 636; slq_hist_idx 637; slq_hist_idx 638; 417; slq_hist_idx 639; slq_hist_idx 640; slq_hist_idx 641; slq_hist_idx 642; slq_hist_idx 643; slq_hist_idx 644; slq_hist_idx 645; slq_hist_idx 646; slq_hist_idx 647; slq_hist_idx 648; slq_hist_idx 649; slq_hist_idx 650; slq_hist_idx 651; slq_hist_idx 652; slq_hist_idx 653; slq_hist_idx 654; slq_hist_idx 655; slq_hist_idx 656; slq_hist_idx 657; slq_hist_idx 658; slq_hist_idx 659; 418; slq_hist_idx 660; slq_hist_idx 661; slq_hist_idx 662; slq_hist_idx 663; slq_hist_idx 664; slq_hist_idx 665; slq_hist_idx 666; slq_hist_idx 667; slq_hist_idx 668; slq_hist_idx 669; slq_hist_idx 670; slq_hist_idx 671; slq_hist_idx 672; slq_hist_idx 673; slq_hist_idx 674; slq_hist_idx 675; slq_hist_idx 676; slq_hist_idx 677; slq_hist_idx 678; slq_hist_idx 679; slq_hist_idx 680; slq_hist_idx 681; slq_hist_idx 682; slq_hist_idx 683; slq_hist_idx 684; slq_hist_idx 685; slq_hist_idx 686; slq_hist_idx 687; 419; slq_hist_idx 688; slq_hist_idx 689; slq_hist_idx 690; slq_hist_idx 691; slq_hist_idx 692; slq_hist_idx 693; slq_hist_idx 694; slq_hist_idx 695; slq_hist_idx 696; slq_hist_idx 697; slq_hist_idx 698; slq_hist_idx 699; slq_hist_idx 700; slq_hist_idx 701; slq_hist_idx 702; slq_hist_idx 703; slq_hist_idx 704; slq_hist_idx 705; slq_hist_idx 706; slq_hist_idx 707; slq_hist_idx 708; slq_hist_idx 709; slq_hist_idx 710; slq_hist_idx 711; slq_hist_idx 712; slq_hist_idx 713; slq_hist_idx 714; slq_hist_idx 715; slq_hist_idx 716; slq_hist_idx 717; slq_hist_idx 718; slq_hist_idx 719; slq_hist_idx 720; slq_hist_idx 721; slq_hist_idx 722; slq_hist_idx 723; slq_hist_idx 724; slq_hist_idx 725; slq_hist_idx 726; slq_hist_idx 727; slq_hist_idx 728; slq_hist_idx 729; slq_hist_idx 730; slq_hist_idx 731; slq_hist_idx 732; slq_hist_idx 733; slq_hist_idx 734; slq_hist_idx 735; slq_hist_idx 736; slq_hist_idx 737; slq_hist_idx 738; slq_hist_idx 739; slq_hist_idx 740; slq_hist_idx 741; slq_hist_idx 742; slq_hist_idx 743; slq_hist_idx 744; slq_hist_idx 745; slq_hist_idx 746; slq_hist_idx 747; slq_hist_idx 748; slq_hist_idx 749; slq_hist_idx 750; slq_hist_idx 751; slq_hist_idx 752; slq_hist_idx 753; slq_hist_idx 754; slq_hist_idx 755; slq_hist_idx 756; slq_hist_idx 757; slq_hist_idx 758; slq_hist_idx 759; slq_hist_idx 760; slq_hist_idx 761; slq_hist_idx 762; slq_hist_idx 763; slq_hist_idx 764; slq_hist_idx 765; slq_hist_idx 766; slq_hist_idx 767; slq_hist_idx 768] };;
(* Lean: single717_4_1_checked *)
let C717EQC00_SINGLE717_4_1_CHECKED = sodt_checked `c717eqb_family` 1 c717eqc00_single717_4_1;;
(* Lean: single717_5_0 *)
let c717eqc00_single717_5_0 = { dmask = 192; dlower = 0; dupper = 0;
  dallowed = [[]];
  dqueries = [] };;
(* Lean: single717_5_0_checked *)
let C717EQC00_SINGLE717_5_0_CHECKED = dsd_actual `c717eqb_family` 0 c717eqc00_single717_5_0;;
(* Lean: single717_5_1 *)
let c717eqc00_single717_5_1 = { dmask = 192; dlower = 0; dupper = 2;
  dallowed = [[]; [1]; [4]; [1; 4]];
  dqueries = [slq_hist_idx 769; slq_hist_idx 770; slq_hist_idx 771; slq_hist_idx 772; slq_hist_idx 773; slq_hist_idx 774; slq_hist_idx 775; slq_hist_idx 776; slq_hist_idx 777; slq_hist_idx 778; slq_hist_idx 779; slq_hist_idx 780; slq_hist_idx 781; slq_hist_idx 782; slq_hist_idx 783; slq_hist_idx 784; slq_hist_idx 785; slq_hist_idx 786; slq_hist_idx 787; slq_hist_idx 788; slq_hist_idx 789; slq_hist_idx 790; slq_hist_idx 791; slq_hist_idx 792; slq_hist_idx 793; slq_hist_idx 794; slq_hist_idx 795; slq_hist_idx 796; slq_hist_idx 797; slq_hist_idx 798; slq_hist_idx 799; slq_hist_idx 800; slq_hist_idx 801; slq_hist_idx 802; slq_hist_idx 803; slq_hist_idx 804; slq_hist_idx 805; slq_hist_idx 806; slq_hist_idx 807; slq_hist_idx 808; slq_hist_idx 809; slq_hist_idx 810; slq_hist_idx 811; slq_hist_idx 812; slq_hist_idx 813; slq_hist_idx 814; slq_hist_idx 815; slq_hist_idx 816; slq_hist_idx 817; slq_hist_idx 818; slq_hist_idx 819; slq_hist_idx 820] };;
(* Lean: single717_5_1_checked *)
let C717EQC00_SINGLE717_5_1_CHECKED = dsd_actual `c717eqb_family` 1 c717eqc00_single717_5_1;;
