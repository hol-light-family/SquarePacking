(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974LocalData.lean             *)
(* (N12Compact.Completion.OtherCases.C983.C974LocalData).  Exact raw input   *)
(* of C974-THREE-SQUARE-ENDING Theorem 1 and the two actual-owner ledgers.   *)
(* Input K W C is c983ld_input (K) (W) (C) over three 5-tuples (the          *)
(* OpenSquare invariants are not part of the Lean structure); apartness      *)
(* fields are ldisj.  Conventions of CP_OtherCases_C983_LeftOrigin.ml /      *)
(* ActualBars.ml: owners p 0 / 1 / 2 / 4 / 5 / 7 / 8 / 9 / 11 = owner        *)
(* 1 / 2 / 12 / 192 / 512 / 2304 / 4096 / 8192 / 32768, actual p i =         *)
(* c983e_actual c1 c2 a b l i.  q.translated 1 1 is the tuple                *)
(* (c, s, u - (c * &1 + s * &1), v - (--s * &1 + c * &1), a)                  *)
(* (CCIP_INSIDE_TRANSLATED), pullSwap that of LINSIDE_PULLSW.  seed_inside = *)
(* c983e_seed_inside, bottom_advance / left_advance = C983AB_BOTTOM_ADVANCE /*)
(* C983AB_LEFT_ADVANCE, f4_top C983F4F_F4_TOP, f4_northeast_g7               *)
(* C983F4CE_F4_NORTHEAST_G7, left_origin_of_top_g7 /  top_left_advance =     *)
(* C983LO_*, merged_horizontal_point C983TOP_MERGED_HORIZONTAL_POINT,        *)
(* auxiliary_inside = c983f4f_point.  Tag C983LD_.                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4BottomMidpointOriginal.ml";;
needs "n12/geometry/CP_OtherCases_C983_LeftOrigin.ml";;
needs "n12/geometry/CP_OtherCases_C983_TopOnlyPoints.ml";;

(* Lean: Input *)
let c983ld_input = new_definition
 `c983ld_input (cK:real) (sK:real) (uK:real) (vK:real) (aK:real)
               (cW:real) (sW:real) (uW:real) (vW:real) (aW:real)
               (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) <=>
    &1 < aK /\ aK = aW /\ aK = aC /\
    (forall x y. linside cK sK uK vK aK x y ==> --(&1) <= y) /\
    linside cK sK uK vK aK (&0) (--(&43 / &500)) /\
    linside cK sK uK vK aK (&41 / &50) (&0) /\
    linside cK sK uK vK aK (&24 / &25) (--(&6 / &25)) /\
    ~linside cK sK uK vK aK (&0) (&0) /\
    linside cW sW uW vW aW (&1) (&0) /\
    linside cW sW uW vW aW (&1) (--(&43 / &500)) /\
    linside cW sW uW vW aW (&9 / &5) (&0) /\
    ~linside cW sW uW vW aW (&27 / &20) (&13 / &20) /\
    ~linside cW sW uW vW aW (&1) (&1 / &2) /\
    ~linside cW sW uW vW aW (&2) (&1 / &2) /\
    (forall x y. linside cC sC uC vC aC x y ==> x <= &3 /\ --(&1) <= y) /\
    linside cC sC uC vC aC (&2) (&0) /\
    ~linside cC sC uC vC aC (&2) (&1 / &2) /\
    ldisj cK sK uK vK aK cW sW uW vW aW /\
    ldisj cK sK uK vK aK cC sC uC vC aC /\
    ldisj cW sW uW vW aW cC sC uC vC aC`;;

(* (q).translated 1 1 and (pullSwap q).translated 1 1 as tuples *)
let c983ld_tr t = match t with
    [c; s; u; v; a] ->
      let mul x y = mk_binop `( * ):real->real->real` x y
      and add x y = mk_binop `(+):real->real->real` x y
      and sub x y = mk_binop `(-):real->real->real` x y in
      [c; s; sub u (add (mul c `&1`) (mul s `&1`));
       sub v (add (mul (mk_comb(`(--):real->real`, s)) `&1`) (mul c `&1`)); a]
  | _ -> failwith "c983ld_tr";;
let c983ld_sw t = match t with
    [c; s; u; v; a] -> [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
  | _ -> failwith "c983ld_sw";;
let c983ld_concl tK tW tC = list_mk_comb(`c983ld_input`, tK @ tW @ tC);;

(* closes the unfolded Input from point facts, boxes and apartness facts *)
let C983LD_CLOSE_TAC facts boxes =
  REWRITE_TAC[c983ld_input; ldisj; CCIP_INSIDE_TRANSLATED; LINSIDE_PULLSW] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  FIRST ([FIRST_ASSUM ACCEPT_TAC; REFL_TAC; REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC] @
         map (fun b -> REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP b) THEN REAL_ARITH_TAC) boxes);;

(* Lean: bottom_input *)
let C983LD_BOTTOM_INPUT =
  let o0 = c983ab_own 1 and o9 = c983ab_own 8192 and o2 = c983ab_own 12 in
  let hyps = [mk_neg (c983ab_in 1 `&1` `&1`); c983ab_in 1 `&91 / &50` `&1`;
              c983ab_in 1 `&49 / &25` `&19 / &25`; c983ab_in 8192 `&2` `&1`;
              mk_neg (c983ab_in 8192 `&2` `&3 / &2`); c983ab_in 512 `&3` `&3 / &2`] in
  prove
   (c983sa_stmt hyps (c983ld_concl (c983ld_tr o0) (c983ld_tr o9) (c983ld_tr o2)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
    let outer = ASSUME (c983ab_in 512 `&3` `&3 / &2`) in
    let facts = [side; seed 0 `&1` `&457 / &500`; seed 9 `&2` `&457 / &500`;
                 c983lo_use C983AB_BOTTOM_ADVANCE [];
                 excl 8192 512 (seed 5 `&47 / &20` `&33 / &20`);
                 excl 8192 512 outer; seed 2 `&3` `&1`; excl 12 512 outer;
                 apart 1 8192; apart 1 12; apart 8192 12] in
    C983LD_CLOSE_TAC facts [REWRITE_RULE[lcont] (box 1); REWRITE_RULE[lcont] (box 12)]);;

(* Lean: left_input *)
let C983LD_LEFT_INPUT =
  let o1 = c983ab_own 2 and o8 = c983ab_own 4096 and o4 = c983ab_own 192 in
  let f4tm = c983f4f_mem 4 7 in
  let hyps = [f4tm; mk_neg (c983ab_in 2 `&1` `&1`); c983ab_in 2 `&1` `&91 / &50`;
              c983ab_in 2 `&19 / &25` `&49 / &25`] in
  let tr t = c983ld_tr (c983ld_sw t) in
  prove
   (c983sa_stmt hyps (c983ld_concl (tr o1) (tr o8) (tr o4)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
    let f4 = ASSUME f4tm in
    let f3 = CONJUNCT1 (c983lo_use C983F4F_F4_TOP [f4]) in
    let g7 = c983lo_use C983F4CE_F4_NORTHEAST_G7 [f4] in
    let origin = c983lo_use C983LO_LEFT_ORIGIN_OF_TOP_G7 [f3; g7] in
    let middle = c983lo_use C983TOP_MERGED_HORIZONTAL_POINT [] in
    let anchor = c983f4f_point f3 in
    let top =
      MP (SPECL (c983ab_own 32768 @ [`&36 / &25`; `&8 / &5`; `&3`; `&3 / &2`]) OO_HORIZONTAL_SEGMENT)
         (end_itlist CONJ [c983lo_use C983LO_TOP_LEFT_ADVANCE [f3; g7]; anchor;
                           EQT_ELIM (REAL_RAT_REDUCE_CONV `&36 / &25 < &8 / &5`);
                           EQT_ELIM (REAL_RAT_REDUCE_CONV `&36 / &25 <= &3 / &2`);
                           EQT_ELIM (REAL_RAT_REDUCE_CONV `&3 / &2 <= &8 / &5`)]) in
    let facts = [side; seed 1 `&457 / &500` `&1`; origin; seed 8 `&457 / &500` `&2`;
                 c983lo_use C983AB_LEFT_ADVANCE [];
                 excl 4096 2304 (seed 7 `&33 / &20` `&47 / &20`);
                 excl 4096 2304 middle; excl 4096 32768 top;
                 seed 4 `&1` `&3`; excl 192 32768 top;
                 apart 2 4096; apart 2 192; apart 4096 192] in
    C983LD_CLOSE_TAC facts [REWRITE_RULE[lcont] (box 2); REWRITE_RULE[lcont] (box 192)]);;
