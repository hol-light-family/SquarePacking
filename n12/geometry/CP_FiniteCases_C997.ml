(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C997.lean                          *)
(* (N12Compact.FiniteCases.C997).  Whole original C997 exclusion by one     *)
(* reflected continuous two-square obstruction (CentralPair.impossible =     *)
(* CCCPAIR_IMPOSSIBLE on pullY of the owners 1024 and 512).                  *)
(* Lean own / foreign (local haves) are oo_seed / oo_excl; auxiliary_inside  *)
(* is oo_aux_point on C997PT_COMPULSORY; C981CompletionWallAdvance.point is  *)
(* C981WA_POINT (on pullSwap, LINSIDE_PULLSW); horizontal_segment is        *)
(* OO_HORIZONTAL_SEGMENT; row_checked / excludes via RowIdentity (row 528).  *)
(* Tag C997C_.                                                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C997Points.ml";;
needs "n12/geometry/CP_CommonCases_CentralPair.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/RowIdentity.ml";;

let C997C_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C997C_H = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c997e_family`;;
let c997c_mp th = MP (SPECL C997C_VARS th) (ASSUME C997C_H);;
let c997c_gen th = GENL C997C_VARS (DISCH C997C_H th);;
let c997c_own m =
  map (fun f -> list_mk_comb(f, C997C_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

(* Lean: own (seed at a literal point of seedPoints (maskSupport mask)) *)
let c997c_seed m p = c997c_mp (oo_inst C997E_F (oo_seed m p));;

(* Lean: foreign *)
let c997c_foreign m n thn = c997c_mp (oo_excl C997E_F m n (c997c_gen thn));;

(* Lean: auxiliary_inside on the compulsory memberships *)
let C997C_COMP = CONJUNCTS (REWRITE_RULE[GSYM CONJ_ASSOC] (c997c_mp C997PT_COMPULSORY));;
let c997c_aux m j =
  let mem = find (fun th -> concl th = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j),
                     list_mk_comb(`ooaux`, C997C_VARS @ [mk_small_numeral m]))) C997C_COMP in
  EQ_MP (SYM (SPECL (C997C_VARS @ [mk_small_numeral m]) (oo_aux_point j))) mem;;

let C997C_MARK_NE = c997c_seed 1024 (`&47 / &20`, `&47 / &20`);;
let C997C_MARK_SE = c997c_seed 512 (`&47 / &20`, `&33 / &20`);;
let C997C_NE_F = c997c_aux 1024 5;;
let C997C_NE_G = c997c_aux 1024 16;;
let C997C_SE_F = c997c_aux 512 8;;
let C997C_SE_G = c997c_aux 512 18;;
let C997C_BOTTOM_MARKER = c997c_seed 8192 (`&2`, `&457 / &500`);;
let C997C_BOTTOM_OUTER = c997c_aux 8192 6;;
let C997C_BOTTOM_ELBOW = c997c_aux 8192 15;;
let C997C_TOP_OUTER = c997c_aux 32768 7;;
let C997C_SW_TIP = c997c_seed 1 (`&87 / &50`, `&1`);;
let C997C_SW_SEED = c997c_seed 1 (`&187 / &100`, `&19 / &25`);;
let C997C_MARK_NW = c997c_seed 2240 (`&33 / &20`, `&47 / &20`);;
let C997C_RIGHT_MARKER = c997c_seed 16384 (`&1543 / &500`, `&2`);;
let C997C_CORNER = c997c_seed 12 (`&3`, `&1`);;
let C997C_CORNER_MARKER = c997c_seed 12 (`&1543 / &500`, `&1`);;

let c997c_sub x y = mk_comb(mk_comb(`(-):real->real->real`, x), y);;
let c997c_mul x y = mk_comb(mk_comb(`(*):real->real->real`, x), y);;
let c997c_neg x = mk_comb(`(--):real->real`, x);;

let C997C_NP = CONJUNCT1 (ASSUME C997C_H);;
let c997c_unit m = MP (SPECL (C997C_VARS @ [mk_small_numeral m]) OO_UNIT) C997C_NP;;
let C997C_SIDE = MP (SPECL C997C_VARS OO_SIDE) C997C_NP;;

(* Lean: bottomFar  (C981CompletionWallAdvance.point on pullSwap (owner 8192)) *)
let C997C_BOTTOM_FAR =
  let [c; s; u; v; a] = c997c_own 8192 in
  let th = REWRITE_RULE[LINSIDE_PULLSW] (SPECL [s; c; u; c997c_sub (c997c_neg v) a; a] C981WA_POINT) in
  let box = MATCH_MP LCONT_PULLSW (MP (SPECL (C997C_VARS @ [`8192`]) OO_BOX) C997C_NP) in
  let unit = ONCE_REWRITE_RULE[REAL_ADD_SYM] (c997c_unit 8192) in
  let side = C997C_SIDE in
  let pos = MP (REAL_ARITH `&1 < l ==> &0 < l`) side in
  MP th (end_itlist CONJ
    [unit; pos; side; box; C997C_BOTTOM_MARKER; C997C_BOTTOM_OUTER;
     c997c_foreign 8192 1 C997C_SW_TIP; c997c_foreign 8192 1 C997C_SW_SEED;
     c997c_foreign 8192 512 C997C_MARK_SE]);;

(* Lean: bottomBar *)
let C997C_BOTTOM_BAR =
  let [c; s; u; v; a] = c997c_own 8192 in
  let th = SPECL [c; s; u; v; a; `&113 / &50`; `&14 / &5`; `&1`; `z:real`] OO_HORIZONTAL_SEGMENT in
  let lt = REAL_ARITH `&113 / &50 < &14 / &5` in
  GEN `z:real` (DISCH `&113 / &50 <= z /\ z <= &14 / &5`
    (MP th (end_itlist CONJ [C997C_BOTTOM_ELBOW; C997C_BOTTOM_FAR; lt;
                             ASSUME `&113 / &50 <= z /\ z <= &14 / &5`])));;

(* ~ owner 512 on the bottom bar (the last premise of CentralPair.impossible) *)
let C997C_BAR_FOREIGN =
  let d = REWRITE_RULE[ldisj] (c997c_mp (oo_apart C997E_F 512 8192)) in
  GEN `z:real` (DISCH `&113 / &50 <= z /\ z <= &14 / &5`
    (NOT_INTRO (DISCH (list_mk_comb(`linside`, c997c_own 512 @ [`z:real`; `&1`]))
      (MP (NOT_ELIM (SPECL [`z:real`; `&1`] d))
          (CONJ (ASSUME (list_mk_comb(`linside`, c997c_own 512 @ [`z:real`; `&1`])))
                (UNDISCH (SPEC `z:real` C997C_BOTTOM_BAR)))))));;

let C997C_APART = REWRITE_RULE[ldisj] (c997c_mp (oo_apart C997E_F 1024 512));;

(* Lean: family_impossible *)
let C997C_FAMILY_IMPOSSIBLE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c997e_family ==> false`,
  let facts =
    [C997C_MARK_NE; C997C_NE_F; C997C_NE_G;
     c997c_foreign 1024 2240 C997C_MARK_NW; c997c_foreign 1024 32768 C997C_TOP_OUTER;
     C997C_MARK_SE; C997C_SE_F; C997C_SE_G;
     c997c_foreign 512 16384 C997C_RIGHT_MARKER; c997c_foreign 512 12 C997C_CORNER;
     c997c_foreign 512 12 C997C_CORNER_MARKER;
     c997c_unit 1024; c997c_unit 512; C997C_SIDE] in
  let [cA; sA; uA; vA; aA] = c997c_own 1024 and [cN; sN; uN; vN; aN] = c997c_own 512 in
  let pully c s u v a = [c; c997c_neg s; c997c_sub u (c997c_mul `&4` s); c997c_sub (c997c_sub (c997c_mul `&4` c) v) a; a] in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY ASSUME_TAC facts THEN
  ASSUME_TAC C997C_APART THEN
  MATCH_MP_TAC CCCPAIR_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC (pully cA sA uA vA aA @ pully cN sN uN vN aN) THEN
  REWRITE_TAC[LINSIDE_PULLY; ldisj; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPEC `z:real` C997C_BAR_FOREIGN) THEN ASM_REWRITE_TAC[]);;

(* Lean: row_checked (private) / excludes *)
let C997C_EXCLUDES = prove
 (`excl_case 997`,
  REWRITE_TAC[ri_excludes_case_iff 528 `c997e_family`; excl_fam] THEN
  MESON_TAC[C997C_FAMILY_IMPOSSIBLE]);;

(* for the assembly: |- EXCLUDED_ROW 528 *)
let C997C_EXCLUDED_ROW = ri_excluded_row 528 C997C_EXCLUDES;;
