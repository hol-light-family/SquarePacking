(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976/EarlyGeometry.lean             *)
(* (namespace N12Compact.Completion.OtherCases.C976.OriginalData).          *)
(* owners p i is the owner of mask EL i c976od_masks, written with the      *)
(* literal mask (owners 0..11 = masks 1,2,12,48,192,256,512,1024,6144,8192,  *)
(* 16384,32768).  The structure Fixed (extends Compulsory = c976e_compulsory)*)
(* is the predicate c976eg_fixed.  foreign / apart are C976E_CLASH_TAC /    *)
(* oo_apart; seed = c976od_seed; side/box = OO_SIDE / OO_BOX (unit normal    *)
(* OO_UNIT).  C981CompletionCrosspoint.point = C981CP_POINT,                 *)
(* C1089.ContinuousBottom.reach = C1089CB_REACH, WallUpperMissingReach.point *)
(* = WUMR_POINT, vertical_segment = OO_VERTICAL_SEGMENT, C974976Central =    *)
(* CC974C_* (Input = cc974c_input).  Tag C976EG_.                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C976_Entrance.ml";;
needs "n12/geometry/CP_CommonCases_C974976Central.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;

(* Lean: Fixed (structure, extends Compulsory) *)
let c976eg_fixed = new_definition
 `c976eg_fixed (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    c976e_compulsory c1 c2 a b l /\
    linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256) (oov c1 c2 a b l 256) l (&33 / &20) (&33 / &20) /\
    linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l (&47 / &20) (&33 / &20) /\
    linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l (&47 / &20) (&47 / &20) /\
    linside (ooc c1 c2 a b l 6144) (oos c1 c2 a b l 6144) (oou c1 c2 a b l 6144) (oov c1 c2 a b l 6144) l (&33 / &20) (&47 / &20) /\
    linside (ooc c1 c2 a b l 6144) (oos c1 c2 a b l 6144) (oou c1 c2 a b l 6144) (oov c1 c2 a b l 6144) l (&457 / &500) (&2) /\
    linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l (&2) (&457 / &500) /\
    linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&1543 / &500) (&2) /\
    linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l (&2) (&1543 / &500) /\
    linside (ooc c1 c2 a b l 192) (oos c1 c2 a b l 192) (oou c1 c2 a b l 192) (oov c1 c2 a b l 192) l (&1) (&1543 / &500) /\
    linside (ooc c1 c2 a b l 192) (oos c1 c2 a b l 192) (oou c1 c2 a b l 192) (oov c1 c2 a b l 192) l (&1) (&3) /\
    linside (ooc c1 c2 a b l 48) (oos c1 c2 a b l 48) (oou c1 c2 a b l 48) (oov c1 c2 a b l 48) l (&3) (&3) /\
    linside (ooc c1 c2 a b l 12) (oos c1 c2 a b l 12) (oou c1 c2 a b l 12) (oov c1 c2 a b l 12) l (&3) (&1) /\
    linside (ooc c1 c2 a b l 12) (oos c1 c2 a b l 12) (oou c1 c2 a b l 12) (oov c1 c2 a b l 12) l (&3) (&457 / &500) /\
    linside (ooc c1 c2 a b l 12) (oos c1 c2 a b l 12) (oou c1 c2 a b l 12) (oov c1 c2 a b l 12) l (&1543 / &500) (&1) /\
    linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l (&187 / &100) (&19 / &25) /\
    linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l (&19 / &25) (&187 / &100)`;;

(* Lean: fixed *)
let C976EG_FIXED = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> c976eg_fixed c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c976eg_fixed] THEN
  ASM_SIMP_TAC[C976E_COMPULSORY] THEN
  ASM_SIMP_TAC[c976od_seed 5 (`&33 / &20`, `&33 / &20`); c976od_seed 6 (`&47 / &20`, `&33 / &20`); c976od_seed 7 (`&47 / &20`, `&47 / &20`); c976od_seed 8 (`&33 / &20`, `&47 / &20`); c976od_seed 8 (`&457 / &500`, `&2`); c976od_seed 9 (`&2`, `&457 / &500`); c976od_seed 10 (`&1543 / &500`, `&2`); c976od_seed 11 (`&2`, `&1543 / &500`); c976od_seed 4 (`&1`, `&1543 / &500`); c976od_seed 4 (`&1`, `&3`); c976od_seed 3 (`&3`, `&3`); c976od_seed 2 (`&3`, `&1`); c976od_seed 2 (`&3`, `&457 / &500`); c976od_seed 2 (`&1543 / &500`, `&1`); c976od_seed 0 (`&187 / &100`, `&19 / &25`); c976od_seed 1 (`&19 / &25`, `&187 / &100`)]);;

(* all Fixed fields (and unit / side / box facts of the used owners) as assumptions *)
let C976EG_FIXED_TAC =
  MP_TAC(SPEC_ALL C976EG_FIXED) THEN ASM_REWRITE_TAC[c976eg_fixed; c976e_compulsory] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let C976EG_OWNER_TAC m =
  let mt = mk_small_numeral m in
  let sp th = SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; mt] th in
  MP_TAC(sp OO_UNIT) THEN MP_TAC(sp OO_BOX) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC;;

let C976EG_SV y = MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                            `l:real`; y] C976OD_SINGLETON_VERTICAL) THEN
             ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC;;
let C976EG_SH x = MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                            `l:real`; x] C976OD_SINGLETON_HORIZONTAL) THEN
             ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC;;

let C976EG_APART m n =
  MP_TAC(SPEC_ALL (oo_apart `c976od_family` m n)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* side conditions of a lemma instance *)
let C976EG_SIDE_TAC =
  REWRITE_TAC[REAL_NEG_MUL2] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC LCONT_PULLX THEN FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C976E_CLASH_TAC;
         RASM_ARITH_TAC];;

(* Lean: southwest_south *)
let C976EG_SOUTHWEST_SOUTH = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256) (oov c1 c2 a b l 256) l (&2) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN C976EG_OWNER_TAC 256 THEN
  C976EG_SV `&8 / &5` THEN C976EG_SV `&3 / &2` THEN
  MP_TAC(SPECL [`--(ooc c1 c2 a b l 256)`; `--(oos c1 c2 a b l 256)`; `((oou c1 c2 a b l 256) - &4 * (ooc c1 c2 a b l 256)) - &4 * (oos c1 c2 a b l 256)`; `&4 * (--(ooc c1 c2 a b l 256)) - (--(oov c1 c2 a b l 256) - l:real - &4 * (oos c1 c2 a b l 256)) - l:real`; `l:real`] C981CP_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLY] THEN REWRITE_TAC[LINSIDE_PULLX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN C976EG_SIDE_TAC);;

(* Lean: southwest_west *)
let C976EG_SOUTHWEST_WEST = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256) (oov c1 c2 a b l 256) l (&3 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN C976EG_OWNER_TAC 256 THEN
  C976EG_SH `&8 / &5` THEN C976EG_SH `&3 / &2` THEN
  MP_TAC(SPECL [`--(oos c1 c2 a b l 256)`; `--(ooc c1 c2 a b l 256)`; `((oou c1 c2 a b l 256) - &4 * (ooc c1 c2 a b l 256)) - &4 * (oos c1 c2 a b l 256)`; `--(&4 * (--(ooc c1 c2 a b l 256)) - (--(oov c1 c2 a b l 256) - l:real - &4 * (oos c1 c2 a b l 256)) - l:real) - l:real`; `l:real`] C981CP_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLSW] THEN REWRITE_TAC[LINSIDE_PULLY] THEN REWRITE_TAC[LINSIDE_PULLX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN C976EG_SIDE_TAC);;

(* Lean: southeast_g8 *)
let C976EG_SOUTHEAST_G8 = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l (&3) (&8 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C976EG_SOUTHWEST_SOUTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C976EG_FIXED_TAC THEN C976EG_OWNER_TAC 512 THEN C976EG_OWNER_TAC 1024 THEN
  C976EG_APART 512 1024 THEN
  MP_TAC(SPECL ([`ooc c1 c2 a b l 512`; `oos c1 c2 a b l 512`; `oou c1 c2 a b l 512`; `oov c1 c2 a b l 512`; `l:real`; `ooc c1 c2 a b l 1024`; `oos c1 c2 a b l 1024`; `oou c1 c2 a b l 1024`; `oov c1 c2 a b l 1024`; `l:real`]) CC974C_SOUTHEAST_G8) THEN
  DISCH_THEN MATCH_MP_TAC THEN C976EG_SIDE_TAC);;

(* Lean: bottom_reach *)
let C976EG_BOTTOM_REACH = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l (&14 / &5) (&1) /\
         (forall x. &113 / &50 <= x ==> x <= &14 / &5 ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l (x) (&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN C976EG_OWNER_TAC 8192 THEN
  C976EG_SH `&87 / &50` THEN
  MP_TAC(SPECL [`ooc c1 c2 a b l 8192`; `oos c1 c2 a b l 8192`; `oou c1 c2 a b l 8192`; `oov c1 c2 a b l 8192`; `l:real`] C1089CB_REACH) THEN
  ANTS_TAC THENL [C976EG_SIDE_TAC; ALL_TAC] THEN
  MESON_TAC[]);;

(* Lean: right_reach *)
let C976EG_RIGHT_REACH = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&3) (&64 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C976EG_FIXED_TAC THEN C976EG_OWNER_TAC 16384 THEN
  MP_TAC(SPECL [`--(ooc c1 c2 a b l 16384)`; `oos c1 c2 a b l 16384`; `(oou c1 c2 a b l 16384) - &4 * (ooc c1 c2 a b l 16384)`; `--(oov c1 c2 a b l 16384) - l:real - &4 * (oos c1 c2 a b l 16384)`; `l:real`] WUMR_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN C976EG_SIDE_TAC);;

(* Lean: right_bar *)
let C976EG_RIGHT_BAR = prove
 (`forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family /\
     &113 / &50 <= y /\ y <= &64 / &25
     ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&3) (y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C976EG_RIGHT_REACH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C976EG_FIXED_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&64 / &25`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: selection_input *)
let C976EG_SELECTION_INPUT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> cc974c_input (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C976EG_SOUTHWEST_SOUTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C976EG_SOUTHEAST_G8) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C976EG_BOTTOM_REACH) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C976EG_FIXED_TAC THEN C976EG_APART 512 1024 THEN
  REWRITE_TAC[cc974c_input; occ1090nes_input] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(DISCH_TAC THEN C976E_CLASH_TAC) THEN
  X_GEN_TAC `x:real` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l (x) (&1)` ASSUME_TAC THENL [ASM_MESON_TAC[]; C976E_CLASH_TAC]);;

(* Lean: northeast_g7 *)
let C976EG_NORTHEAST_G7 = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CC974C_NORTHEAST_G7 THEN
  MAP_EVERY EXISTS_TAC [`ooc c1 c2 a b l 512`; `oos c1 c2 a b l 512`; `oou c1 c2 a b l 512`; `oov c1 c2 a b l 512`; `l:real`] THEN
  ASM_SIMP_TAC[C976EG_SELECTION_INPUT; OO_UNIT] THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: northeast_f7 *)
let C976EG_NORTHEAST_F7 = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l (&12 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CC974C_NORTHEAST_F7 THEN
  MAP_EVERY EXISTS_TAC [`ooc c1 c2 a b l 512`; `oos c1 c2 a b l 512`; `oou c1 c2 a b l 512`; `oov c1 c2 a b l 512`; `l:real`] THEN
  ASM_SIMP_TAC[C976EG_SELECTION_INPUT; OO_UNIT] THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: top_pair *)
let C976EG_TOP_PAIR = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c976od_family
     ==> linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l (&8 / &5) (&3) /\ linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l (&87 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C976EG_SELECTION_INPUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C976EG_FIXED_TAC THEN C976EG_APART 1024 32768 THEN
  MATCH_MP_TAC CC974C_TOP_PAIR THEN
  MAP_EVERY EXISTS_TAC ([`ooc c1 c2 a b l 512`; `oos c1 c2 a b l 512`; `oou c1 c2 a b l 512`; `oov c1 c2 a b l 512`; `l:real`; `ooc c1 c2 a b l 1024`; `oos c1 c2 a b l 1024`; `oou c1 c2 a b l 1024`; `oov c1 c2 a b l 1024`; `l:real`]) THEN
  ASM_SIMP_TAC[OO_UNIT] THEN RASM_ARITH_TAC);;
