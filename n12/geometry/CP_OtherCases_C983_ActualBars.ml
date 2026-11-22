(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/ActualBars.lean.              *)
(* Unconditional actual C983 left and bottom wall bars.  owners p i is the  *)
(* OriginalOwners 5-tuple at the literal mask EL i c983ri_owner_code:       *)
(*   owners p 0 = owner 1, owners p 1 = owner 2, owners p 5 = owner 512,     *)
(*   owners p 7 = owner 2304, owners p 8 = owner 4096, owners p 9 = owner 8192. *)
(* Statements: !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) =          *)
(* c983ri_family ==> ... (Lean p, hf).  seed_inside = c983e_seed_inside,     *)
(* C981CompletionWallAdvance.point = C981WA_POINT (pullSwap via              *)
(* LINSIDE_PULLSW / LCONT_PULLSW), vertical/horizontal_segment =             *)
(* OO_VERTICAL_SEGMENT / OO_HORIZONTAL_SEGMENT.  Tag C983AB_.                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_Entrance.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

let C983AB_H = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family`;;
let c983ab_own m =
  map (fun f -> list_mk_comb(f, C983E_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c983ab_in m x y = list_mk_comb(`linside`, c983ab_own m @ [x; y]);;
let c983ab_mp th = MP (SPECL C983E_VARS th) (ASSUME C983AB_H);;
let c983ab_gen th = GENL C983E_VARS (DISCH C983AB_H th);;

(* Lean: left_labels (private) *)
let C983AB_LEFT_LABELS = prove
 (`forall s. MEM s (EL 8 c983e_original_components) ==> 1 IN s /\ 11 IN s`,
  REWRITE_TAC[c983e_original_components] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* Lean: bottom_labels (private) *)
let C983AB_BOTTOM_LABELS = prove
 (`forall s. MEM s (EL 9 c983e_original_components) ==> 6 IN s /\ 15 IN s`,
  REWRITE_TAC[c983e_original_components] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* the labels at the actual owner set: |- H ==> j IN ooaux c1 c2 a b l m (m = EL i ownerCode) *)
let c983ab_labels i lab =
  let ith = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral i) `12`)) in
  let mem = MP (SPECL (C983E_VARS @ [mk_small_numeral i]) C983E_ORIGINAL_ACTUAL_MEM)
               (CONJ (CONJUNCT1 (ASSUME C983AB_H)) (CONJ (CONJUNCT2 (ASSUME C983AB_H)) ith)) in
  CONV_RULE (REWRITE_CONV[c983e_actual; c983ri_owner_code] THENC ONCE_DEPTH_CONV EL_CONV)
            (MATCH_MP lab mem);;

let c983ab_point j th =
  EQ_MP (SYM (SPECL (C983E_VARS @ [rand (rand (concl th))]) (oo_aux_point j))) th;;

(* Lean: left_aux *)
let C983AB_LEFT_AUX =
  let th = c983ab_labels 8 C983AB_LEFT_LABELS in
  let th = CONJ (c983ab_point 1 (CONJUNCT1 th)) (c983ab_point 11 (CONJUNCT2 th)) in
  let want = mk_conj(c983ab_in 4096 `&1` `&113 / &50`, c983ab_in 4096 `&1` `&12 / &5`) in
  c983ab_gen (EQ_MP (prove(mk_eq(concl th, want),
                            CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[])) th);;

(* Lean: bottom_aux *)
let C983AB_BOTTOM_AUX =
  let th = c983ab_labels 9 C983AB_BOTTOM_LABELS in
  let th = CONJ (c983ab_point 6 (CONJUNCT1 th)) (c983ab_point 15 (CONJUNCT2 th)) in
  let want = mk_conj(c983ab_in 8192 `&12 / &5` `&1`, c983ab_in 8192 `&113 / &50` `&1`) in
  c983ab_gen (EQ_MP (prove(mk_eq(concl th, want),
                            CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[])) th);;

let c983ab_seed i x y = c983ab_mp (c983e_seed_inside i (x, y));;
let c983ab_excl m n i x y = c983ab_mp (oo_excl C983E_F m n (c983e_seed_inside i (x, y)));;
let c983ab_basics m =
  let np = CONJUNCT1 (ASSUME C983AB_H) in
  let side = MP (SPECL C983E_VARS OO_SIDE) np in
  (MP (SPECL (C983E_VARS @ [mk_small_numeral m]) OO_UNIT) np,
   MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side, side,
   MP (SPECL (C983E_VARS @ [mk_small_numeral m]) OO_BOX) np);;

(* Lean: left_advance *)
let C983AB_LEFT_ADVANCE =
  let unit, pos, side, box = c983ab_basics 4096 in
  let marker = c983ab_seed 8 `&457 / &500` `&2` in
  let aux = CONJUNCT2 (c983ab_mp C983AB_LEFT_AUX) in
  let e1 = c983ab_excl 4096 2 1 `&1` `&87 / &50` in
  let e2 = c983ab_excl 4096 2 1 `&19 / &25` `&187 / &100` in
  let e3 = c983ab_excl 4096 2304 7 `&33 / &20` `&47 / &20` in
  c983ab_gen (MP (SPECL (c983ab_own 4096) C981WA_POINT)
                 (end_itlist CONJ [unit; pos; side; box; marker; aux; e1; e2; e3]));;

(* Lean: bottom_advance *)
let C983AB_BOTTOM_ADVANCE =
  let unit, pos, side, box = c983ab_basics 8192 in
  let marker = c983ab_seed 9 `&2` `&457 / &500` in
  let aux = CONJUNCT1 (c983ab_mp C983AB_BOTTOM_AUX) in
  let e1 = c983ab_excl 8192 1 0 `&87 / &50` `&1` in
  let e2 = c983ab_excl 8192 1 0 `&187 / &100` `&19 / &25` in
  let e3 = c983ab_excl 8192 512 5 `&47 / &20` `&33 / &20` in
  let psw = match c983ab_own 8192 with
      [c; s; u; v; a] -> [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
    | _ -> failwith "psw" in
  let th = REWRITE_RULE[LINSIDE_PULLSW] (SPECL psw C981WA_POINT) in
  let unit' = ONCE_REWRITE_RULE[REAL_ADD_SYM] unit in
  let box' = MATCH_MP LCONT_PULLSW box in
  c983ab_gen (MP th (end_itlist CONJ [unit'; pos; side; box'; marker; aux; e1; e2; e3]));;

(* Lean: left_bar *)
let C983AB_LEFT_BAR = prove
 (list_mk_forall(C983E_VARS, mk_imp(C983AB_H,
    mk_forall(`y:real`, mk_imp(`&113 / &50 <= y`, mk_imp(`y <= &14 / &5`, c983ab_in 4096 `&1` `y:real`))))),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`] THEN
  ASM_SIMP_TAC[C983AB_LEFT_AUX; C983AB_LEFT_ADVANCE] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: bottom_bar *)
let C983AB_BOTTOM_BAR = prove
 (list_mk_forall(C983E_VARS, mk_imp(C983AB_H,
    mk_forall(`x:real`, mk_imp(`&113 / &50 <= x`, mk_imp(`x <= &14 / &5`, c983ab_in 8192 `x:real` `&1`))))),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`] THEN
  ASM_SIMP_TAC[C983AB_BOTTOM_AUX; C983AB_BOTTOM_ADVANCE] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
