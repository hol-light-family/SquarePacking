(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C896CentralPoints.lean.           *)
(* Further actual C896 geometry (northwest crosspoints, sharp point, top     *)
(* origin, wall-center signs).  owner p m is the 5-tuple (ooc .. m) (oos ..  *)
(* m) (oou .. m) (oov .. m) l.  The private  point  (auxiliary_exact at a    *)
(* compulsory point) is c896wb_aux, the private  foreign  is oo_excl, the    *)
(* structure Fixed is the predicate c896cp_fixed.  C896WallBars.bars:        *)
(* C896WB_BARS (points of the bars via c896cp_bar);                          *)
(* C981CompletionCrosspoint.point: C981CP_POINT; InwardPoint.strong_original:*)
(* CCIP_STRONG_ORIGINAL; C974976Central.top_origin: CC974O_TOP_ORIGIN;       *)
(* WallSignFromSingleton.original_left_center / original_bottom:             *)
(* wsfs_original_left_center / wsfs_original_bottom.  pullX / pullY /        *)
(* pullSwap: LINSIDE_PULLX/Y/SW (via C896WB_APPLY_TAC).  Tag C896CP_.        *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C896WallBars.ml";;
needs "n12/geometry/CP_CommonCases_C974976Origins.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_CommonCases_WallSignFromSingleton.ml";;

(* Lean: Fixed (structure) *)
let c896cp_fixed = new_definition
 `c896cp_fixed (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&33 / &20) (&47 / &20) /\
    linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l (&47 / &20) (&47 / &20) /\
    linside (ooc c1 c2 a b l 768) (oos c1 c2 a b l 768) (oou c1 c2 a b l 768) (oov c1 c2 a b l 768) l (&33 / &20) (&33 / &20) /\
    linside (ooc c1 c2 a b l 768) (oos c1 c2 a b l 768) (oou c1 c2 a b l 768) (oov c1 c2 a b l 768) l (&47 / &20) (&33 / &20) /\
    linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&2) (&113 / &50) /\
    linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&87 / &50) (&2) /\
    linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l (&2) (&1543 / &500) /\
    linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l (&8 / &5) (&3) /\
    linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096) (oov c1 c2 a b l 4096) l (&457 / &500) (&2) /\
    linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096) (oov c1 c2 a b l 4096) l (&1) (&12 / &5) /\
    linside (ooc c1 c2 a b l 192) (oos c1 c2 a b l 192) (oou c1 c2 a b l 192) (oov c1 c2 a b l 192) l (&1) (&1543 / &500) /\
    linside (ooc c1 c2 a b l 192) (oos c1 c2 a b l 192) (oou c1 c2 a b l 192) (oov c1 c2 a b l 192) l (&1) (&3)`;;

(* the individual Fixed facts (seeds and compulsory auxiliary points) *)
let C896CP_NW_MARKER = c896wb_seed 2048 (`&33 / &20`, `&47 / &20`);;
let C896CP_NE_MARKER = c896wb_seed 1024 (`&47 / &20`, `&47 / &20`);;
let C896CP_SW_MARKER = c896wb_seed 768 (`&33 / &20`, `&33 / &20`);;
let C896CP_SE_MARKER = c896wb_seed 768 (`&47 / &20`, `&33 / &20`);;
let C896CP_NW_F5 = c896wb_aux 2048 5;;
let C896CP_NW_G3 = c896wb_aux 2048 13;;
let C896CP_TOP_MARKER = c896wb_seed 32768 (`&2`, `&1543 / &500`);;
let C896CP_TOP_F3 = c896wb_aux 32768 3;;
let C896CP_LEFT_MARKER = c896wb_seed 4096 (`&457 / &500`, `&2`);;
let C896CP_LEFT_G1 = c896wb_aux 4096 11;;
let C896CP_NWC_MARKER = c896wb_seed 192 (`&1`, `&1543 / &500`);;
let C896CP_NWC = c896wb_seed 192 (`&1`, `&3`);;

(* Lean: fixed *)
let C896CP_FIXED = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c896d_family
     ==> c896cp_fixed c1 c2 a b l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c896cp_fixed] THEN
  ASM_SIMP_TAC[C896CP_NW_MARKER; C896CP_NE_MARKER; C896CP_SW_MARKER; C896CP_SE_MARKER;
               C896CP_NW_F5; C896CP_NW_G3; C896CP_TOP_MARKER; C896CP_TOP_F3;
               C896CP_LEFT_MARKER; C896CP_LEFT_G1; C896CP_NWC_MARKER; C896CP_NWC]);;

(* a point of one of the bars of C896WB_BARS *)
let c896cp_bar m x y =
  prove(c896wb_stmt (c896wb_own m x y),
    REPEAT STRIP_TAC THEN MP_TAC(SPEC_ALL C896WB_BARS) THEN
    ASM_REWRITE_TAC[c896wb_bars; IMP_IMP] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC));;

let c896cp_ex m n th = oo_excl C896D_F m n th;;

(* Lean: northwest_north *)
let C896CP_NORTHWEST_NORTH = prove
 (c896wb_stmt (c896wb_own 2048 `&2` `&5 / &2`),
  C896WB_APPLY_TAC C981CP_POINT (c896wb_pullx (c896wb_q 2048))
   [C896CP_NW_F5; C896CP_NW_G3; C896CP_NW_MARKER;
    c896cp_ex 2048 768 C896CP_SW_MARKER; c896cp_ex 2048 1024 C896CP_NE_MARKER;
    c896cp_ex 2048 4096 (c896cp_bar 4096 `&1` `&12 / &5`);
    c896cp_ex 2048 4096 (c896cp_bar 4096 `&1` `&5 / &2`)]);;

(* Lean: northwest_west *)
let C896CP_NORTHWEST_WEST = prove
 (c896wb_stmt (c896wb_own 2048 `&3 / &2` `&2`),
  C896WB_APPLY_TAC C981CP_POINT (c896wb_pullsw (c896wb_pullx (c896wb_q 2048)))
   [C896CP_NW_F5; C896CP_NW_G3; C896CP_NW_MARKER;
    c896cp_ex 2048 1024 C896CP_NE_MARKER; c896cp_ex 2048 768 C896CP_SW_MARKER;
    c896cp_ex 2048 32768 (c896cp_bar 32768 `&8 / &5` `&3`);
    c896cp_ex 2048 32768 (c896cp_bar 32768 `&3 / &2` `&3`)]);;

(* Lean: northwest_sharp *)
let C896CP_NORTHWEST_SHARP = prove
 (c896wb_stmt (c896wb_own 2048 `&73 / &50` `&201 / &100`),
  C896WB_APPLY_TAC CCIP_STRONG_ORIGINAL (c896wb_pully (c896wb_pullx (c896wb_q 2048)))
   [C896CP_NW_MARKER; C896CP_NW_F5; C896CP_NW_G3;
    c896cp_ex 2048 1024 C896CP_NE_MARKER; c896cp_ex 2048 768 C896CP_SW_MARKER;
    c896cp_ex 2048 32768 C896CP_TOP_F3]);;

(* Lean: top_origin *)
let C896CP_TOP_ORIGIN = prove
 (c896wb_stmt (c896wb_own 32768 `&2` `&3`),
  C896WB_APPLY_TAC CC974O_TOP_ORIGIN (c896wb_q 4096 @ c896wb_q 32768 @ c896wb_q 192)
   [C896CP_LEFT_MARKER; C896CP_LEFT_G1;
    c896cp_ex 4096 2 (c896wb_seed 2 (`&1`, `&87 / &50`));
    c896cp_ex 4096 2048 C896CP_NW_G3;
    C896CP_TOP_MARKER; C896CP_TOP_F3; C896CP_NWC_MARKER; C896CP_NWC;
    oo_apart C896D_F 192 4096; oo_apart C896D_F 192 32768]);;

let C896CP_V5 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let c896cp_wsfs th ms first =
  let th1 = SPECL (C896CP_V5 @ [C896D_F]) th in
  let c = rand (concl th1) in
  prove(c896wb_stmt (if first then lhand c else c),
    REPEAT STRIP_TAC THEN MP_TAC th1 THEN
    ASM_REWRITE_TAC(map (fun m -> in_fam m C896D_F) ms) THEN
    (if first then DISCH_THEN(ACCEPT_TAC o CONJUNCT1) else DISCH_THEN ACCEPT_TAC));;

(* Lean: left_center *)
let C896CP_LEFT_CENTER = c896cp_wsfs (wsfs_original_left_center 4096) [4096; 2] false;;

(* Lean: bottom_center *)
let C896CP_BOTTOM_CENTER = c896cp_wsfs (wsfs_original_bottom 8192) [8192; 1] true;;
