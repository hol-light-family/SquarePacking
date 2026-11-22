(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/ResidualNoTopG4.lean          *)
(* (namespace N12Compact.Completion.OtherCases.C1091.Residual).             *)
(* C1091-complete-proof section 3: the actual top owner omits G4.           *)
(* q : Fin 12 -> OpenSquare is  qc qs qu qv qa : num -> real  (see           *)
(* CP_OtherCases_C1091_ResidualInput.ml); the OpenSquare field unit_normal   *)
(* is the separate hypothesis  !i. i < 12 ==> qc i * qc i + qs i * qs i = &1 *)
(* (side_pos follows from the side field).  pullY / pullSwap:               *)
(* LINSIDE_PULLY / LINSIDE_PULLSW.  WallUpperMissingReach.point: WUMR_POINT; *)
(* C981CompletionCommonCycle.impossible: C981CC_IMPOSSIBLE;                  *)
(* horizontal_segment: OO_HORIZONTAL_SEGMENT.                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1091_ResidualInput.ml";;
needs "n12/geometry/CP_C981_CommonCycle.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

let c1091rn_q i = map (fun f -> mk_comb(f, mk_small_numeral i))
  [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;
let c1091rn_pull tms [c; s; u; v; a] =
  map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms;;
let c1091rn_pully = c1091rn_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let c1091rn_pullsw = c1091rn_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

let C1091RN_UNFOLD_TAC =
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[c1091ri_input] o
    check (can (term_match [] `c1091ri_input qc qs qu qv qa`) o concl));;

(* unit normal, side facts and box of q i as assumptions *)
let C1091RN_SQUARE_TAC i =
  let n = mk_small_numeral i in
  let lt = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` n `12`)) in
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `( * ):real->real->real`)) (concl th)
     && not (can (find_term ((=) `linside`)) (concl th))
     then let u = MP (SPEC n th) lt in
          ASSUME_TAC u THEN ASSUME_TAC (ONCE_REWRITE_RULE[REAL_ADD_SYM] u) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `c1091ri_input qc qs qu qv qa`) (concl th) then
     let cs = CONJUNCTS (REWRITE_RULE[c1091ri_input] th) in
     let side = MP (SPEC n (el 0 cs)) lt and box = MP (SPEC n (el 3 cs)) lt in
     ASSUME_TAC side THEN ASSUME_TAC box THEN
     ASSUME_TAC (MATCH_MP (REAL_ARITH `&1 < x ==> &0 < x`) side) else NO_TAC);;

(* a negated point of q i from a point of q j *)
let C1091RN_FOREIGN_TAC js =
  TRY (GEN_TAC THEN DISCH_TAC THEN DISCH_TAC) THEN
  MATCH_MP_TAC C1091RI_FOREIGN THEN
  FIRST (map (fun j -> EXISTS_TAC (mk_small_numeral j) THEN ASM_SIMP_TAC[] THEN
                       CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) js);;

(* apply a geometry lemma th to transformed tuples; side goals from the assumptions *)
let C1091RN_APPLY_TAC th tp js =
  let th' = CONV_RULE (REWRITE_CONV[ldisj] THENC
                       REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
                       REWRITE_CONV[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THENC
                       REAL_RAT_REDUCE_CONV) (SPECL tp th) in
  let th' = if is_neg (concl th') then MATCH_MP (TAUT `~p ==> p ==> false`) th' else th' in
  MATCH_MP_TAC th' THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_SIMP_TAC[LCONT_PULLX; LCONT_PULLY; LCONT_PULLSW] THEN NO_TAC;
         REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
         C1091RN_FOREIGN_TAC js];;

(* Lean: top_advance *)
let C1091RN_TOP_ADVANCE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1091ri_input qc qs qu qv qa /\
     ~linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)
     ==> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&64 / &25) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091RN_SQUARE_TAC 11 THEN C1091RN_UNFOLD_TAC THEN
  C1091RN_APPLY_TAC WUMR_POINT (c1091rn_pullsw (c1091rn_pully (c1091rn_q 11))) [6]);;

(* Lean: no_top_g4_impossible *)
let C1091RN_NO_TOP_G4_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1091ri_input qc qs qu qv qa /\
     ~linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C1091RN_TOP_ADVANCE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPEC_ALL C1091RI_SOUTHEAST_CUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1091RN_SQUARE_TAC 5 THEN C1091RN_SQUARE_TAC 6 THEN C1091RN_UNFOLD_TAC THEN
  SUBGOAL_THEN `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&5 / &2) (&3)` ASSUME_TAC THENL
   [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`&12 / &5`; `&64 / &25`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&2)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `&36 / &25`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(qa:num->real) 5 = qa 6` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (term_match [] `forall i j. i < 12 /\ j < 12 ==> (qa:num->real) i = qa j`) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `forall x y. ~(linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) x y /\
                        linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) x y)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `~(i:num = j)`)) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  C1091RN_APPLY_TAC C981CC_IMPOSSIBLE (c1091rn_pullsw (c1091rn_q 5) @ c1091rn_pullsw (c1091rn_q 6))
    [4; 9; 5; 10; 11; 2]);;
