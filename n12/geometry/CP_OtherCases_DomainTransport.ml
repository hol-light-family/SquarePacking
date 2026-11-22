(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/DomainTransport.lean, with S12     *)
(* DomainRefinement (refineAgainst, enlarge) and DomainEnumeration           *)
(* (domain_cases_sound).                                                     *)
(*   Lean NamedDomain family    an OCaml pair (|- cdom fam m al, |- m IN fam) *)
(*   Lean rebase / restrictUpper  dt_rebase / dt_restrict_upper on dsd records *)
(*   Lean trim d queries          dt_trim th [query indices]                 *)
(*   Lean hullSingleton           dt_hull_singleton fam m k idx tri          *)
(*   Lean refineAgainst / refine / sweep   PK_REFINE_AGAINST, dt_refine_against, *)
(*                                         dt_refine, dt_sweep               *)
(*   Lean enlarge                 cdom_cache                                 *)
(*   Lean domain_cases_sound      pk_domain_cases fam [domains] cases        *)
(* actual_vector_eq_of_masks / sweep_masks / refine_mask are list facts about *)
(* the mask fields; in HOL the masks are numerals of the theorems.           *)
(* ========================================================================= *)

needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: rebase  (the same record checked against the new family) *)
let dt_rebase newfam k w = dsd_actual newfam k w;;

(* Lean: restrictUpper / restrictUpper_checked *)
let dt_restrict_upper w upper =
  if upper > w.dupper then failwith "dt_restrict_upper: larger upper" else
  { w with dupper = upper; dallowed = filter (fun s -> length s <= upper) w.dallowed };;

(* Lean: trim (exact combined owners refuted by certified queries) *)
let dt_trim th qidxs =
  List.fold_left (fun th n ->
      let (m, k, ow, _) = slq_select n in
      if m <> cdom_mask th || k <> 2 then failwith "dt_trim: query mask / kind" else
      pk_remove th (mk_numset ow)) th qidxs;;

(* Lean: hullSingleton (budget upper exactly one; lower may be zero) *)
let dt_hull_singleton fam m k idx tri =
  if pk_num (pkup_thm fam m k) <> 1 then failwith "dt_hull_singleton: budget" else
  ro_small_budget_seed fam m k idx tri;;

(* Lean: S12.CertifiedDomain.refineAgainst *)
let PK_REFINE_AGAINST = prove
 (`forall fam m n al bl. cdom fam m al /\ cdom fam n bl /\ n IN fam /\ ~(m = n)
     ==> cdom fam m (FILTER (\x. EX (\y. DISJOINT x y) bl) al)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `cdom fam m al` THEN REWRITE_TAC[cdom; MEM_FILTER] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN BETA_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[GSYM EX_MEM] THEN EXISTS_TAC `ooaux c1 c2 a b l n` THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC CDOM_OWNER THEN EXISTS_TAC `fam:num->bool` THEN ASM_REWRITE_TAC[]] THEN
   (REWRITE_TAC[ooaux] THEN MATCH_MP_TAC PK_COMBINED_DISJOINT THEN ASM_REWRITE_TAC[OIDX_LT] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(m:num = n)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) && rhs (concl th) = `m:num`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OIDX_SPEC THEN ASM_MESON_TAC[]));;

let disjoint_lit_conv t =
  (LAND_CONV setlit_conv THENC RAND_CONV setlit_conv THENC disjoint_conv) t;;

(* refineAgainst evaluated:  (|- cdom fam m al) (|- cdom fam n bl)  |- cdom fam m [filtered] *)
let dt_refine_against tha thb =
  let (fam, m, _) = cdom_parts tha and (_, n, _) = cdom_parts thb in
  let inb = in_fam n fam in
  let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n))) in
  let th = MATCH_MP PK_REFINE_AGAINST (end_itlist CONJ [tha; thb; inb; ne]) in
  let cc t = (REWRITE_CONV[EX] THENC DEPTH_CONV BETA_CONV THENC
              ONCE_DEPTH_CONV (fun u -> if is_comb u && is_comb (rator u) &&
                                           rator (rator u) = `DISJOINT:(num->bool)->(num->bool)->bool`
                                        then disjoint_lit_conv u else failwith "") THENC
              REWRITE_CONV[]) t in
  CONV_RULE (RAND_CONV (filter_by_conv cc)) th;;

(* Lean: NamedDomain.refine and sweep *)
let dt_refine (a, ia) (b, ib) =
  if cdom_mask a = cdom_mask b then (a, ia) else (dt_refine_against a b, ia);;
let dt_sweep ds = map (fun d -> List.fold_left dt_refine d ds) ds;;
let dt_named th = (th, in_fam (cdom_mask th) (cdom_fam th));;

(* Lean: S12.domain_cases_sound: the actual owner sets of the listed domains form
   one of the cases (cases: a HOL list of lists of literal sets):
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = fam
        ==> MEM [ooaux c1 c2 a b l m_1; ..; ooaux c1 c2 a b l m_k] cases *)
let pk_domain_cases fam doms cases =
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let masks = map cdom_mask doms in
  if length (setify masks) <> length masks then failwith "pk_domain_cases: repeated masks" else
  let vec = mk_list(map ooaux_tm masks, `:num->bool`) in
  let goal = list_mk_comb(`MEM:((num->bool)list)->((num->bool)list)list->bool`, [vec; cases]) in
  let mems = map (fun d -> CONV_RULE (REWRITE_CONV (fam_defs (rand (concl d)) @ [MEM]))
      (MATCH_MP CDOM_OWNER (CONJ d (CONJ hnp (CONJ hrow (in_fam (cdom_mask d) fam)))))) doms in
  let da = Array.of_list (List.combine masks mems) in
  let n = Array.length da in
  let disj mi mj =
    let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral mi, mk_small_numeral mj))) in
    MATCH_MP OO_AUX_DISJOINT (end_itlist CONJ [hnp; hrow; in_fam mi fam; in_fam mj fam; ne]) in
  let caselist = dest_list cases in
  let leaf chosen =
    let eqs = rev (map (fun (_, e, _) -> e) chosen) in
    let lits = map (fun e -> rhs (concl e)) eqs in
    let target = try find (fun c -> let es = dest_list c in length es = length lits &&
                                    forall2 (fun x y -> numset_of x = numset_of y) es lits) caselist
                 with Failure _ -> failwith "pk_domain_cases: feasible assignment not among the cases" in
    let eqs2 = map2 (fun e t -> TRANS e (setlit_eq (rhs (concl e)) t)) eqs (dest_list target) in
    let rec mklist es = match es with
        [] -> REFL `[]:(num->bool)list`
      | e :: rest -> MK_COMB (AP_TERM `CONS:(num->bool)->(num->bool)list->(num->bool)list` e, mklist rest) in
    let leq = mklist eqs2 in
    let memt = EQT_ELIM (REWRITE_CONV[MEM] (list_mk_comb(`MEM:((num->bool)list)->((num->bool)list)list->bool`, [target; cases]))) in
    EQ_MP (SYM (AP_THM (AP_TERM `MEM:((num->bool)list)->((num->bool)list)list->bool` leq) cases)) memt in
  let rec dfs j chosen =
    if j = n then leaf chosen else
    let (mj, dj) = da.(j) in
    let rec cases_of th =
      if is_disj (concl th) then
        let p, q = dest_disj (concl th) in DISJ_CASES th (pick (ASSUME p)) (cases_of (ASSUME q))
      else if concl th = `false` then CONTR goal th else pick th
    and pick eqj =
      let s = rhs (concl eqj) in
      let ls = numset_of s in
      let rec conflict ch = match ch with
          [] -> None
        | (mt, eqt, lt) :: rest ->
            if exists (fun x -> mem x ls) lt then
              let d1 = SUBS [eqt; eqj] (disj mt mj) in
              Some (CONV_RULE (LAND_CONV setlit_conv THENC RAND_CONV setlit_conv THENC disjoint_conv) d1)
            else conflict rest in
      match conflict chosen with
        Some f -> CONTR goal f
      | None -> dfs (j + 1) ((mj, eqj, ls) :: chosen) in
    cases_of dj in
  GENL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] (DISCH hyp (dfs 0 []));;
