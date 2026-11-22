(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C972CentralSelection.lean          *)
(* (namespace N12Compact.FiniteCases.C972).  C972's continuous central       *)
(* selection.  owners p i is the owner of mask EL i c972o_masks, written    *)
(* with the literal mask (owners 0..11 = masks 1,2,12,48,192,256,512,1024,   *)
(* 2048,4096,8192,16384).  missing_top = oo_missing m 15.                    *)
(* The structure Fixed (extends Points = c972e_points)                       *)
(* is the predicate c972cs_fixed.  foreign / apart are C972CS_CLASH_TAC /    *)
(* oo_apart; seed = c972o_seed; side/box = OO_SIDE / OO_BOX (unit normal    *)
(* OO_UNIT).  C981CompletionCrosspoint.point = C981CP_POINT,                 *)
(* C1089.ContinuousBottom.reach = C1089CB_REACH, WallUpperMissingReach.point *)
(* = WUMR_POINT, vertical_segment = OO_VERTICAL_SEGMENT, C974976Central =    *)
(* CC974C_* (Input = cc974c_input).  Tag C972CS_.                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C972Entrance.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_CommonCases_C974976Central.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;

(* Lean: Fixed (structure, extends Compulsory) *)
let c972cs_fixed = new_definition
 `c972cs_fixed (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    c972e_points c1 c2 a b l /\
    linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256) (oov c1 c2 a b l 256) l (&33 / &20) (&33 / &20) /\
    linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l (&47 / &20) (&33 / &20) /\
    linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l (&47 / &20) (&47 / &20) /\
    linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&33 / &20) (&47 / &20) /\
    linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096) (oov c1 c2 a b l 4096) l (&457 / &500) (&2) /\
    linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l (&2) (&457 / &500) /\
    linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&1543 / &500) (&2) /\
    linside (ooc c1 c2 a b l 12) (oos c1 c2 a b l 12) (oou c1 c2 a b l 12) (oov c1 c2 a b l 12) l (&3) (&1) /\
    linside (ooc c1 c2 a b l 12) (oos c1 c2 a b l 12) (oou c1 c2 a b l 12) (oov c1 c2 a b l 12) l (&1543 / &500) (&1) /\
    linside (ooc c1 c2 a b l 48) (oos c1 c2 a b l 48) (oou c1 c2 a b l 48) (oov c1 c2 a b l 48) l (&3) (&3) /\
    linside (ooc c1 c2 a b l 192) (oos c1 c2 a b l 192) (oou c1 c2 a b l 192) (oov c1 c2 a b l 192) l (&1) (&3) /\
    linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l (&187 / &100) (&19 / &25) /\
    linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l (&19 / &25) (&187 / &100)`;;

(* Lean: fixed *)
let C972CS_FIXED = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> c972cs_fixed c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c972cs_fixed] THEN
  ASM_SIMP_TAC[C972E_POINTS] THEN
  ASM_SIMP_TAC[c972o_seed 5 (`&33 / &20`, `&33 / &20`); c972o_seed 6 (`&47 / &20`, `&33 / &20`); c972o_seed 7 (`&47 / &20`, `&47 / &20`); c972o_seed 8 (`&33 / &20`, `&47 / &20`); c972o_seed 9 (`&457 / &500`, `&2`); c972o_seed 10 (`&2`, `&457 / &500`); c972o_seed 11 (`&1543 / &500`, `&2`); c972o_seed 2 (`&3`, `&1`); c972o_seed 2 (`&1543 / &500`, `&1`); c972o_seed 3 (`&3`, `&3`); c972o_seed 4 (`&1`, `&3`); c972o_seed 0 (`&187 / &100`, `&19 / &25`); c972o_seed 1 (`&19 / &25`, `&187 / &100`)]);;

(* all Fixed fields (and unit / side / box facts of the used owners) as assumptions *)
let C972CS_FIXED_TAC =
  MP_TAC(SPEC_ALL C972CS_FIXED) THEN ASM_REWRITE_TAC[c972cs_fixed; c972e_points] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY (fun m -> MP_TAC(SPEC_ALL (oo_inst `c972d_family` (oo_missing m 15))) THEN
                      ASM_REWRITE_TAC[] THEN DISCH_TAC) [1024; 2048];;

(* a contradiction from two distinct owners containing the same point *)
let C972CS_CLASH_TAC (asl, w as g) =
  let owned = List.filter_map (fun (_, th) ->
     let t = concl th in
     try let f, args = strip_comb t in
         if f <> `linside` then failwith "" else
         let m = dest_small_numeral (rand (hd args)) in
         Some (m, (el 5 args, el 6 args), th)
     with _ -> None) asl in
  let pairs = flat (map (fun (m, p, th) -> List.filter_map (fun (n, q, th') ->
     if m < n && aconv (fst p) (fst q) && aconv (snd p) (snd q) then Some (m, n, p) else None) owned)
     owned) in
  if pairs = [] then failwith "C972CS_CLASH_TAC" else
  let (m, n, (x, y)) = hd pairs in
  let fam = `c972d_family` in
  (MP_TAC(SPECL [x; y] (REWRITE_RULE[ldisj]
     (MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                 fam; mk_small_numeral m; mk_small_numeral n] OO_APART)
         (end_itlist CONJ [ASSUME `NPACK c1 c2 a b l`;
                           ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = c972d_family`;
                           in_fam m fam; in_fam n fam;
                           EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n)))]))))
   THEN ASM_REWRITE_TAC[]) g;;

let C972CS_OWNER_TAC m =
  let mt = mk_small_numeral m in
  let sp th = SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; mt] th in
  MP_TAC(sp OO_UNIT) THEN MP_TAC(sp OO_BOX) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC;;

let C972CS_SV y = MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                            `l:real`; y] C972O_SINGLETON_VERTICAL) THEN
             ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC;;
let C972CS_SH x = MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                            `l:real`; x] C972O_SINGLETON_HORIZONTAL) THEN
             ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC;;

let C972CS_APART m n =
  MP_TAC(SPEC_ALL (oo_apart `c972d_family` m n)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* side conditions of a lemma instance *)
let C972CS_SIDE_TAC =
  REWRITE_TAC[REAL_NEG_MUL2] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC LCONT_PULLX THEN FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C972CS_CLASH_TAC;
         RASM_ARITH_TAC];;

(* Lean: southwest_south *)
let C972CS_SOUTHWEST_SOUTH = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256) (oov c1 c2 a b l 256) l (&2) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 256 THEN
  C972CS_SV `&8 / &5` THEN C972CS_SV `&3 / &2` THEN
  MP_TAC(SPECL [`--(ooc c1 c2 a b l 256)`; `--(oos c1 c2 a b l 256)`; `((oou c1 c2 a b l 256) - &4 * (ooc c1 c2 a b l 256)) - &4 * (oos c1 c2 a b l 256)`; `&4 * (--(ooc c1 c2 a b l 256)) - (--(oov c1 c2 a b l 256) - l:real - &4 * (oos c1 c2 a b l 256)) - l:real`; `l:real`] C981CP_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLY] THEN REWRITE_TAC[LINSIDE_PULLX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN C972CS_SIDE_TAC);;

(* Lean: southwest_west *)
let C972CS_SOUTHWEST_WEST = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256) (oov c1 c2 a b l 256) l (&3 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 256 THEN
  C972CS_SH `&8 / &5` THEN C972CS_SH `&3 / &2` THEN
  MP_TAC(SPECL [`--(oos c1 c2 a b l 256)`; `--(ooc c1 c2 a b l 256)`; `((oou c1 c2 a b l 256) - &4 * (ooc c1 c2 a b l 256)) - &4 * (oos c1 c2 a b l 256)`; `--(&4 * (--(ooc c1 c2 a b l 256)) - (--(oov c1 c2 a b l 256) - l:real - &4 * (oos c1 c2 a b l 256)) - l:real) - l:real`; `l:real`] C981CP_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLSW] THEN REWRITE_TAC[LINSIDE_PULLY] THEN REWRITE_TAC[LINSIDE_PULLX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN C972CS_SIDE_TAC);;

(* Lean: southeast_g8 *)
let C972CS_SOUTHEAST_G8 = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l (&3) (&8 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHWEST_SOUTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 512 THEN C972CS_OWNER_TAC 1024 THEN
  C972CS_APART 512 1024 THEN
  MP_TAC(SPECL ([`ooc c1 c2 a b l 512`; `oos c1 c2 a b l 512`; `oou c1 c2 a b l 512`; `oov c1 c2 a b l 512`; `l:real`; `ooc c1 c2 a b l 1024`; `oos c1 c2 a b l 1024`; `oou c1 c2 a b l 1024`; `oov c1 c2 a b l 1024`; `l:real`]) CC974C_SOUTHEAST_G8) THEN
  DISCH_THEN MATCH_MP_TAC THEN C972CS_SIDE_TAC);;

(* Lean: bottom_reach *)
let C972CS_BOTTOM_REACH = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l (&14 / &5) (&1) /\
         (forall x. &113 / &50 <= x ==> x <= &14 / &5 ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l (x) (&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 8192 THEN
  C972CS_SH `&87 / &50` THEN
  MP_TAC(SPECL [`ooc c1 c2 a b l 8192`; `oos c1 c2 a b l 8192`; `oou c1 c2 a b l 8192`; `oov c1 c2 a b l 8192`; `l:real`] C1089CB_REACH) THEN
  ANTS_TAC THENL [C972CS_SIDE_TAC; ALL_TAC] THEN
  MESON_TAC[]);;

(* Lean: right_reach *)
let C972CS_RIGHT_REACH = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&3) (&64 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 16384 THEN
  MP_TAC(SPECL [`--(ooc c1 c2 a b l 16384)`; `oos c1 c2 a b l 16384`; `(oou c1 c2 a b l 16384) - &4 * (ooc c1 c2 a b l 16384)`; `--(oov c1 c2 a b l 16384) - l:real - &4 * (oos c1 c2 a b l 16384)`; `l:real`] WUMR_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN C972CS_SIDE_TAC);;

(* Lean: right_bar *)
let C972CS_RIGHT_BAR = prove
 (`forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family /\
     &113 / &50 <= y /\ y <= &64 / &25
     ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&3) (y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_RIGHT_REACH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&64 / &25`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: selection_input *)
let C972CS_SELECTION_INPUT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> cc974c_input (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512) (oov c1 c2 a b l 512) l (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHWEST_SOUTH) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHEAST_G8) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C972CS_BOTTOM_REACH) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_APART 512 1024 THEN
  REWRITE_TAC[cc974c_input; occ1090nes_input] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(DISCH_TAC THEN C972CS_CLASH_TAC) THEN
  X_GEN_TAC `x:real` THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l (x) (&1)` ASSUME_TAC THENL [ASM_MESON_TAC[]; C972CS_CLASH_TAC]);;

(* Lean: northeast_g7 *)
let C972CS_NORTHEAST_G7 = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l (&113 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CC974C_NORTHEAST_G7 THEN
  MAP_EVERY EXISTS_TAC [`ooc c1 c2 a b l 512`; `oos c1 c2 a b l 512`; `oou c1 c2 a b l 512`; `oov c1 c2 a b l 512`; `l:real`] THEN
  ASM_SIMP_TAC[C972CS_SELECTION_INPUT; OO_UNIT] THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: northeast_f7 *)
let C972CS_NORTHEAST_F7 = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 1024) (oos c1 c2 a b l 1024) (oou c1 c2 a b l 1024) (oov c1 c2 a b l 1024) l (&12 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CC974C_NORTHEAST_F7 THEN
  MAP_EVERY EXISTS_TAC [`ooc c1 c2 a b l 512`; `oos c1 c2 a b l 512`; `oou c1 c2 a b l 512`; `oov c1 c2 a b l 512`; `l:real`] THEN
  ASM_SIMP_TAC[C972CS_SELECTION_INPUT; OO_UNIT] THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


(* Lean: northwest_component *)
let C972CS_NORTHWEST_COMPONENT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> (linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&8 / &5) (&3) \/ linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&2) (&113 / &50)) /\
         linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&87 / &50) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972E_COMPULSORY) THEN ASM_REWRITE_TAC[c972e_compulsory] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPEC_ALL C972CS_NORTHEAST_F7) THEN MP_TAC(SPEC_ALL C972CS_NORTHEAST_G7) THEN
  ASM_REWRITE_TAC[oo_aux_point 7; oo_aux_point 17] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[oo_aux_point 3; oo_aux_point 5; oo_aux_point 14] THEN
  OO_EXCLUDE_ALL_TAC C972D_F 2048 THEN OO_DOMAIN_CASES_TAC C972D_NORTHWEST);;

(* Lean: northwest_f3 *)
let C972CS_NORTHWEST_F3 = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&8 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C972CS_NORTHWEST_COMPONENT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPEC_ALL C972CS_SOUTHWEST_WEST) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C972CS_FIXED_TAC THEN C972CS_OWNER_TAC 2048 THEN
  REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN `linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048)
                  (oov c1 c2 a b l 2048) l (&2) (&113 / &50)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[LINSIDE_PULLSW] (SPECL [`oos c1 c2 a b l 2048`; `ooc c1 c2 a b l 2048`; `oou c1 c2 a b l 2048`; `--(oov c1 c2 a b l 2048) - l`; `l:real`] OCEP_POINTS_ORIGINAL)) THEN
  ANTS_TAC THENL [C972CS_SIDE_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN C972CS_CLASH_TAC);;

(* Lean: northwest_pair *)
let C972CS_NORTHWEST_PAIR = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c972d_family
     ==> linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&8 / &5) (&3) /\ linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048) (oov c1 c2 a b l 2048) l (&87 / &50) (&3)`,
  MESON_TAC[C972CS_NORTHWEST_F3; C972CS_NORTHWEST_COMPONENT]);;
