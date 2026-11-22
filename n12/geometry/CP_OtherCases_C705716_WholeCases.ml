(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C705716/WholeCases.lean.          *)
(* Complete original-case proofs of C705 (b = false, family                 *)
(* c705716ri_family_f, retained row 386) and C716 (b = true,                *)
(* c705716ri_family_t, row 397).  owners b p i is the OriginalOwners        *)
(* 5-tuple at the literal mask EL i (ownerCode b) (c705716wc_own);          *)
(* Bool-indexed theorems are OCaml pairs (b = false, b = true).            *)
(* ThreeCentral.impossible = OC3CTS_IMPOSSIBLE, pullX = LINSIDE_PULLX,      *)
(* ExcludesFamily = excl_fam, ExcludesCase = excl_case, excludes_case =     *)
(* C705716RI_EXCLUDES_CASE.  Tag C705716WC_.                                *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C705716_Entrance.ml";;
needs "n12/geometry/CP_OtherCases_ThreeCentral_TwoSquares.ml";;

let C705716WC_V = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let c705716wc_fam bb = c705716e_sel bb C705716E_FAMS;;
let c705716wc_mask bb i = el i (c705716e_masks bb);;
let c705716wc_hyp bb = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, c705716wc_fam bb));;

(* Lean: owners *)
let c705716wc_own bb i =
  let mt = mk_small_numeral (c705716wc_mask bb i) in
  map (fun f -> list_mk_comb(f, C705716WC_V @ [mt])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

let c705716wc_close bb concl th =
  prove(list_mk_forall(C705716WC_V, mk_imp(c705716wc_hyp bb, concl)),
        REPEAT GEN_TAC THEN DISCH_THEN(fun h -> ACCEPT_TAC (PROVE_HYP h th)));;

(* Lean: owner_code *)
let C705716WC_OWNER_CODE = (fun f -> (f false, f true)) (fun bb ->
  map (fun i -> let m = mk_small_numeral (c705716wc_mask bb i) in
    let th = MP (SPECL (C705716WC_V @ [c705716wc_fam bb; m]) OO_CODE)
                (CONJ (CONJUNCT1 (ASSUME (c705716wc_hyp bb)))
                  (CONJ (CONJUNCT2 (ASSUME (c705716wc_hyp bb))) (in_fam (c705716wc_mask bb i) (c705716wc_fam bb)))) in
    c705716wc_close bb (concl th) th) (0--11));;

(* Lean: owners_side, owners_same  (every owner has side l) *)
let C705716WC_OWNERS_SIDE = OO_SIDE;;
let C705716WC_OWNERS_SAME = REFL `l:real`;;

(* Lean: owners_markers *)
let C705716WC_OWNERS_MARKERS = (fun f -> (f false, f true)) (fun bb ->
  map (fun i -> let h = ASSUME (c705716wc_hyp bb) in
                MATCH_MP OO_MARKERS (CONJ (CONJUNCT1 h) (CONJ (CONJUNCT2 h)
                  (in_fam (c705716wc_mask bb i) (c705716wc_fam bb)))) |> fun th ->
                c705716wc_close bb (concl th) th) (0--11)) ;;

(* Lean: owners_apart  (at literal distinct masks) *)
let c705716wc_apart bb i j =
  MP (SPECL C705716WC_V (oo_apart (c705716wc_fam bb) (c705716wc_mask bb i) (c705716wc_mask bb j)))
     (ASSUME (c705716wc_hyp bb));;

(* the twelve actual auxiliary sets: |- ooaux .. m_i = S_i (hyp NPACK /\ IMAGE) *)
let c705716wc_entries bb =
  let cover = UNDISCH (SPEC_ALL (c705716e_sel bb C705716E_ACTUAL_COVER)) in
  CONJUNCTS (REWRITE_RULE[c705716e_actual_vector; c705716e_expected_vector; MAP; CONS_11] cover);;

(* Lean: auxiliary_inside, at literal i, j: |- linside (owners b p i) x_j y_j *)
let c705716wc_aux bb i j =
  let m = mk_small_numeral (c705716wc_mask bb i) in
  let e = find (fun th -> rand (lhs (concl th)) = m) (c705716wc_entries bb) in
  let mt = mk_binop `(IN):num->(num->bool)->bool` (mk_small_numeral j) (lhs (concl e)) in
  let mem = EQT_ELIM ((REWRITE_CONV[e; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[]) mt) in
  CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (EQ_MP (SYM (SPECL (C705716WC_V @ [m]) (oo_aux_point j))) mem);;

(* the general statement of auxiliary_inside *)
let C705716WC_AUXILIARY_INSIDE = (fun f -> (f false, f true)) (fun bb ->
  let bt = c705716e_bool bb in
  let stmt = list_mk_forall(C705716WC_V @ [`i:num`; `j:num`],
    mk_imp(list_mk_conj [c705716wc_hyp bb; `i < 12`; `j < 20`;
                         mk_binop `(IN):num->(num->bool)->bool` `j:num`
                           (mk_comb(mk_comb(`EL:num->(num->bool)list->num->bool`, `i:num`),
                                    mk_comb(`c705716e_expected_vector`, bt)))],
      list_mk_comb(`linside`,
        map (fun f -> list_mk_comb(f, C705716WC_V @ [mk_comb(mk_comb(`EL:num->num list->num`, `i:num`),
                                                    mk_comb(`c705716ri_owner_code`, bt))]))
            [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`; `EL j (AUXPTS 2)$1`; `EL j (AUXPTS 2)$2`]))) in
  prove(stmt, REPEAT STRIP_TAC THEN
    MP_TAC(SPECL C705716WC_V (c705716e_sel bb C705716E_ACTUAL_COVER)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `EL (i:num):(num->bool)list->num->bool`) THEN
    ASM_SIMP_TAC[C705716E_ACTUAL_ENTRY] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[OO_AUX_EXACT]));;

(* Lean: marker_inside, at a literal owner and marker point *)
let c705716wc_marker bb i (x, y) =
  MP (SPECL C705716WC_V (oo_inst (c705716wc_fam bb) (oo_seed (c705716wc_mask bb i) (x, y))))
     (ASSUME (c705716wc_hyp bb));;

let c705716wc_excl bb i j pt =
  let d = REWRITE_RULE[ldisj] (c705716wc_apart bb i j) in
  let args = snd (strip_comb (concl pt)) in
  let d2 = SPECL [el 5 args; el 6 args] d in
  let a = lhand (rand (concl d2)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) pt)));;

let c705716wc_apply conv spec facts =
  let nf = map (CONV_RULE conv) facts in
  let pa t =
    try find (fun f -> aconv (concl f) t) facts with Failure _ ->
    let eq = conv t in
    if rhs (concl eq) = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) (rhs (concl eq))) nf)
    with Failure _ -> failwith ("c705716wc_apply: " ^ string_of_term t) in
  MP spec (end_itlist CONJ (map pa (conjuncts (lhand (concl spec)))));;

let c705716wc_basic bb =
  let np = CONJUNCT1 (ASSUME (c705716wc_hyp bb)) in
  let side = MP (SPECL C705716WC_V OO_SIDE) np in
  let unit i = MP (SPECL (C705716WC_V @ [mk_small_numeral (c705716wc_mask bb i)]) OO_UNIT) np in
  (side, MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side, unit);;

(* Lean: family705_excluded *)
let C705716WC_FAMILY705_EXCLUDED =
  let bb = false in
  let side, pos, unit = c705716wc_basic bb in
  let facts = [unit 6; unit 7; side; pos; REFL `l:real`;
               c705716wc_marker bb 6 (`&33 / &20`, `&33 / &20`);
               c705716wc_aux bb 6 4; c705716wc_aux bb 6 13;
               c705716wc_excl bb 6 0 (c705716wc_aux bb 0 2);
               c705716wc_excl bb 6 1 (c705716wc_aux bb 1 10);
               c705716wc_marker bb 7 (`&47 / &20`, `&33 / &20`);
               c705716wc_marker bb 7 (`&47 / &20`, `&47 / &20`);
               c705716wc_marker bb 7 (`&33 / &20`, `&47 / &20`);
               c705716wc_apart bb 6 7] in
  let f = c705716wc_apply REFL (SPECL (c705716wc_own bb 6 @ c705716wc_own bb 7) OC3CTS_IMPOSSIBLE) facts in
  prove(`excl_fam c705716ri_family_f`,
        REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN DISCH_THEN(fun h -> ACCEPT_TAC (PROVE_HYP h f)));;

(* Lean: family716_excluded *)
let C705716WC_FAMILY716_EXCLUDED =
  let bb = true in
  let side, pos, unit = c705716wc_basic bb in
  let pullx q = let t = SPECL (q @ [`x:real`; `y:real`]) LINSIDE_PULLX in
                let args = snd (strip_comb (lhs (concl t))) in
                [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args] in
  let pa = pullx (c705716wc_own bb 6) and ph = pullx (c705716wc_own bb 7) in
  let dj =
    let tm = list_mk_comb(`ldisj`, pa @ ph) in
    let d = REWRITE_RULE[ldisj] (c705716wc_apart bb 6 7) in
    EQ_MP (SYM (REWRITE_CONV[ldisj; LINSIDE_PULLX] tm))
          (GEN `x:real` (GEN `y:real` (SPECL [`&4 - x`; `y:real`] d))) in
  let conv = REWRITE_CONV[LINSIDE_PULLX; REAL_NEG_MUL2] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let facts = [unit 6; unit 7; side; pos; REFL `l:real`; dj;
               c705716wc_marker bb 6 (`&47 / &20`, `&33 / &20`);
               c705716wc_aux bb 6 4; c705716wc_aux bb 6 16;
               c705716wc_excl bb 6 9 (c705716wc_aux bb 9 6);
               c705716wc_excl bb 6 10 (c705716wc_aux bb 10 18);
               c705716wc_marker bb 7 (`&33 / &20`, `&33 / &20`);
               c705716wc_marker bb 7 (`&33 / &20`, `&47 / &20`);
               c705716wc_marker bb 7 (`&47 / &20`, `&47 / &20`)] in
  let f = c705716wc_apply conv (SPECL (pa @ ph) OC3CTS_IMPOSSIBLE) facts in
  prove(`excl_fam c705716ri_family_t`,
        REWRITE_TAC[excl_fam] THEN REPEAT GEN_TAC THEN DISCH_THEN(fun h -> ACCEPT_TAC (PROVE_HYP h f)));;

(* Lean: case705_excluded, case716_excluded *)
let C705716WC_CASE705_EXCLUDED = MP (fst C705716RI_EXCLUDES_CASE) C705716WC_FAMILY705_EXCLUDED;;
let C705716WC_CASE716_EXCLUDED = MP (snd C705716RI_EXCLUDES_CASE) C705716WC_FAMILY716_EXCLUDED;;

(* for the assembly: |- EXCLUDED_ROW 386, |- EXCLUDED_ROW 397 *)
let C705716WC_EXCLUDED_ROW705 = ri_excluded_row 386 C705716WC_CASE705_EXCLUDED;;
let C705716WC_EXCLUDED_ROW716 = ri_excluded_row 397 C705716WC_CASE716_EXCLUDED;;
