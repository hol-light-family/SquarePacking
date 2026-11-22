(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974ReducedEnding.lean         *)
(* (N12Compact.Completion.OtherCases.C983.C974ReducedEnding).  Join of       *)
(* C974-THREE-SQUARE-ENDING sections 2-4.  Squares K W C are 5-tuples with   *)
(* their OpenSquare invariants as explicit hypotheses.  C974LowerFace.Input  *)
(* is oc983lf_input (K) (W), lower_face OC983LF_LOWER_FACE; C974WallReach.   *)
(* Data is oc983wr_data; C974CornerEnding.impossible OC983CE_IMPOSSIBLE;     *)
(* C974LocalData.Input is c983ld_input.  q.translated 1 0 is the tuple       *)
(* (c, s, u - (c * &1 + s * &0), v - (--s * &1 + c * &0), a)                  *)
(* (CCIP_INSIDE_TRANSLATED).  Tag C983RE_.                                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974LowerFace.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974CornerEnding.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LocalData.ml";;

let C983RE_K = [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`];;
let C983RE_W = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;
let C983RE_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let c983re_tr10 t = match t with
    [c; s; u; v; a] ->
      let mul x y = mk_binop `( * ):real->real->real` x y
      and add x y = mk_binop `(+):real->real->real` x y
      and sub x y = mk_binop `(-):real->real->real` x y in
      [c; s; sub u (add (mul c `&1`) (mul s `&0`));
       sub v (add (mul (mk_comb(`(--):real->real`, s)) `&1`) (mul c `&0`)); a]
  | _ -> failwith "c983re_tr10";;

let C983RE_WALLS = `forall x y. linside cC sC uC vC aC x y ==> x <= &3 /\ --(&1) <= y`;;
let C983RE_APART = `ldisj cW sW uW vW aW cC sC uC vC aC`;;

(* Lean: impossible *)
let C983RE_IMPOSSIBLE = prove
 (`forall cK sK uK vK aK cW sW uW vW aW cC sC uC vC aC.
     cK * cK + sK * sK = &1 /\ &0 < aK /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC * cC + sC * sC = &1 /\ &0 < aC /\
     oc983lf_input cK sK uK vK aK cW sW uW vW aW /\
     linside cW sW uW vW aW (&9 / &5) (&0) /\ aW = aC /\
     (forall x y. linside cC sC uC vC aC x y ==> x <= &3 /\ --(&1) <= y) /\
     linside cC sC uC vC aC (&2) (&0) /\ ~linside cC sC uC vC aC (&2) (&1 / &2) /\
     ldisj cW sW uW vW aW cC sC uC vC aC
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C983RE_K @ C983RE_W) OC983LF_LOWER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[oc983lf_input] o
    check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `oc983lf_input`)) THEN
  let walls = ASSUME C983RE_WALLS and apart = REWRITE_RULE[ldisj] (ASSUME C983RE_APART) in
  MATCH_MP_TAC (SPECL (c983re_tr10 C983RE_W @ c983re_tr10 C983RE_C) OC983CE_IMPOSSIBLE) THEN
  REWRITE_TAC[oc983wr_data; ldisj; CCIP_INSIDE_TRANSLATED; REAL_ADD_LID] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC apart;
         REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP walls) THEN REAL_ARITH_TAC;
         RASM_ARITH_TAC]);;

(* Lean: of_raw_and_reductions *)
let C983RE_OF_RAW_AND_REDUCTIONS = prove
 (`forall cK sK uK vK aK cW sW uW vW aW cC sC uC vC aC.
     cK * cK + sK * sK = &1 /\ &0 < aK /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC * cC + sC * sC = &1 /\ &0 < aC /\
     c983ld_input cK sK uK vK aK cW sW uW vW aW cC sC uC vC aC /\
     oc983lf_input cK sK uK vK aK cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c983ld_input] THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C983RE_K @ C983RE_W @ C983RE_C) C983RE_IMPOSSIBLE) THEN
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC]);;
