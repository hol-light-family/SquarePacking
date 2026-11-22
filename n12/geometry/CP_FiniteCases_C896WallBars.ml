(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C896WallBars.lean.                *)
(* Genuine wall segments after the original C896 entrance.                  *)
(* owner p m is the 5-tuple (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l.   *)
(* The private  foreign_seed  is oo_excl (seed of another owner) and the    *)
(* private  auxiliary  is c896wb_aux (OO_AUX_EXACT at a compulsory point of *)
(* C896E_COMPULSORY).  pullX / pullY / pullSwap: LINSIDE_PULLX/Y/SW.         *)
(* C981CompletionWallAdvance.point: C981WA_POINT; WallUpperMissingReach.     *)
(* point: WUMR_POINT.  The structure Bars is the predicate c896wb_bars.     *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C896Entrance.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;

let c896wb_stmt concl = mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`,
  mk_forall(`b:num->real`, mk_forall(`l:real`,
    mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c896d_family`, concl))))));;

let c896wb_own m x y = list_mk_comb(`linside`,
  map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                                 mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`; x; y]);;

let c896wb_seed m p = oo_inst C896D_F (oo_seed m p);;

(* Lean: auxiliary (private), at the compulsory points of C896Entrance.compulsory *)
let c896wb_aux m j =
  let th = SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  mk_small_numeral m] (oo_aux_point j) in
  prove(c896wb_stmt (lhs (concl th)),
    REPEAT STRIP_TAC THEN REWRITE_TAC[th] THEN
    MP_TAC (SPEC_ALL C896E_COMPULSORY) THEN ASM_REWRITE_TAC[c896e_compulsory] THEN SIMP_TAC[]);;

let c896wb_q m = map (fun f -> if f = `l:real` then f else
    list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; mk_small_numeral m]))
  [`ooc`; `oos`; `oou`; `oov`; `l:real`];;
let c896wb_pull tms [c; s; u; v; a] =
  map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms;;
let c896wb_pullx = c896wb_pull [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;
let c896wb_pully = c896wb_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let c896wb_pullsw = c896wb_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* apply a wall lemma to a transformed owner; side goals from ths and the owner facts *)
let C896WB_APPLY_TAC th tp ths =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
                       REAL_RAT_REDUCE_CONV) (SPECL tp th) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th' THEN REPEAT CONJ_TAC THEN
  FIRST [ASM_SIMP_TAC (ths @ [OO_BOX]) THEN NO_TAC;
         REPEAT (FIRST [MATCH_MP_TAC LCONT_PULLSW; MATCH_MP_TAC LCONT_PULLX; MATCH_MP_TAC LCONT_PULLY]) THEN
         ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
         FIRST [ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC;
                ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC];
         MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];;

(* Lean: left_high *)
let C896WB_LEFT_HIGH = prove
 (c896wb_stmt (c896wb_own 4096 `&1` `&14 / &5`),
  C896WB_APPLY_TAC C981WA_POINT (c896wb_q 4096)
   [c896wb_seed 4096 (`&457 / &500`, `&2`); c896wb_aux 4096 11;
    oo_excl C896D_F 4096 2 (c896wb_seed 2 (`&1`, `&87 / &50`));
    oo_excl C896D_F 4096 2 (c896wb_seed 2 (`&19 / &25`, `&187 / &100`));
    oo_excl C896D_F 4096 2048 (c896wb_seed 2048 (`&33 / &20`, `&47 / &20`))]);;

(* Lean: bottom_right *)
let C896WB_BOTTOM_RIGHT = prove
 (c896wb_stmt (c896wb_own 8192 `&14 / &5` `&1`),
  C896WB_APPLY_TAC C981WA_POINT (c896wb_pullsw (c896wb_q 8192))
   [c896wb_seed 8192 (`&2`, `&457 / &500`); c896wb_aux 8192 6;
    oo_excl C896D_F 8192 1 (c896wb_seed 1 (`&87 / &50`, `&1`));
    oo_excl C896D_F 8192 1 (c896wb_seed 1 (`&187 / &100`, `&19 / &25`));
    oo_excl C896D_F 8192 768 (c896wb_seed 768 (`&47 / &20`, `&33 / &20`))]);;

(* Lean: top_left *)
let C896WB_TOP_LEFT = prove
 (c896wb_stmt (c896wb_own 32768 `&6 / &5` `&3`),
  C896WB_APPLY_TAC C981WA_POINT (c896wb_pullsw (c896wb_pullx (c896wb_pully (c896wb_q 32768))))
   [c896wb_seed 32768 (`&2`, `&1543 / &500`); c896wb_aux 32768 3;
    oo_excl C896D_F 32768 16 (c896wb_seed 16 (`&113 / &50`, `&3`));
    oo_excl C896D_F 32768 16 (c896wb_seed 16 (`&213 / &100`, `&81 / &25`));
    oo_excl C896D_F 32768 2048 (c896wb_seed 2048 (`&33 / &20`, `&47 / &20`))]);;

(* Lean: right_low *)
let C896WB_RIGHT_LOW = prove
 (c896wb_stmt (c896wb_own 16384 `&3` `&36 / &25`),
  C896WB_APPLY_TAC WUMR_POINT (c896wb_pullx (c896wb_pully (c896wb_q 16384)))
   [c896wb_seed 16384 (`&1543 / &500`, `&2`); c896wb_aux 16384 18;
    oo_excl C896D_F 16384 1024 (c896wb_aux 1024 9);
    oo_excl C896D_F 16384 768 (c896wb_seed 768 (`&47 / &20`, `&33 / &20`))]);;

(* Lean: Bars (structure) *)
let c896wb_bars = new_definition
 `c896wb_bars (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    (forall y. &113 / &50 <= y ==> y <= &14 / &5 ==>
         linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096) (oov c1 c2 a b l 4096) l (&1) y) /\
    (forall x. &113 / &50 <= x ==> x <= &14 / &5 ==>
         linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l x (&1)) /\
    (forall x. &6 / &5 <= x ==> x <= &87 / &50 ==>
         linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768) (oov c1 c2 a b l 32768) l x (&3)) /\
    (forall y. &36 / &25 <= y ==> y <= &87 / &50 ==>
         linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&3) y)`;;

(* Lean: bars *)
let C896WB_BARS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c896d_family
     ==> c896wb_bars c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c896wb_bars] THEN REPEAT CONJ_TAC THEN
  GEN_TAC THEN REPEAT DISCH_TAC THENL
   [MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`];
    MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`];
    MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&6 / &5`; `&87 / &50`];
    MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&87 / &50`]] THEN
  ASM_SIMP_TAC[c896wb_aux 4096 1; C896WB_LEFT_HIGH; c896wb_aux 8192 15; C896WB_BOTTOM_RIGHT;
               C896WB_TOP_LEFT; c896wb_aux 32768 14; C896WB_RIGHT_LOW; c896wb_aux 16384 8] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
