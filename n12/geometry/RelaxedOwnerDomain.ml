(* ========================================================================= *)
(* Phase 2: Compact/Bridge/RelaxedOwnerDomain.lean (and the parts of        *)
(* OwnerBudget / SmallOwnerDomain it uses).  Owner domains of a packing     *)
(* with the actual F/G budget; see PackingContext.ml for the vocabulary.    *)
(*                                                                           *)
(*   Lean lower mask k            pklow m k                                  *)
(*   Lean upper family mask k     pkup fam m k                               *)
(*   Lean Bounds family mask w k  robounds fam m lo hi k  (lo, hi = w's      *)
(*                                lower / upper)                             *)
(*   Lean firstHalf / secondHalf  rofirst / rosecond                         *)
(*   Lean SetBounds               rosetb                                     *)
(*   Lean extend / pushOwners     roext / ropush  (a permutation of Fin 10   *)
(*                                is the num list of its values)             *)
(* Lean defs producing domains are OCaml producers returning                 *)
(*   |- cdom fam m al   or   |- hdom fam m k al                              *)
(* (ro_single, ro_combined, ro_small_budget, ro_small_budget_seed,           *)
(*  ro_transformed, ro_restrict_budget, ro_restrict_f1).                     *)
(* ========================================================================= *)

needs "n12/geometry/PackingContext.ml";;

(* Lean: Bounds *)
let robounds = new_definition
 `robounds fam m lo hi k <=> lo <= pklow m k /\ pkup fam m k <= hi`;;

(* Lean: actual_bounds *)
let RO_ACTUAL_BOUNDS = prove
 (`forall fam m lo hi k c1 c2 a b l i. robounds fam m lo hi k /\ k < 2 /\
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ i < 12 /\
     ownmask (c1 i) (c2 i) (a i) (b i) l = m
     ==> lo <= CARD (auxown k (c1 i) (c2 i) (a i) (b i) l) /\
         CARD (auxown k (c1 i) (c2 i) (a i) (b i) l) <= hi`,
  REWRITE_TAC[robounds] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `k:num`; `i:num`] PK_BUDGET) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_TRANS]);;

let rofirst = new_definition `rofirst s = {n:num | n IN s /\ n < 10}`;;
let rosecond = new_definition `rosecond s = {n:num | n IN s /\ 10 <= n}`;;

(* Lean: firstHalf_combined *)
let RO_FIRST_COMBINED = prove
 (`forall x y. x SUBSET {n | n < 10} ==> rofirst (combown x y) = x`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; rofirst; combown; IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN
  X_GEN_TAC `n:num` THEN ASM_MESON_TAC[ARITH_RULE `~((m:num) + 10 < 10)`]);;

(* Lean: secondHalf_combined *)
let RO_SECOND_COMBINED = prove
 (`forall x y. x SUBSET {n | n < 10} ==> rosecond (combown x y) = IMAGE (\n. n + 10) y`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; rosecond; combown; IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN
  X_GEN_TAC `n:num` THEN
  ASM_MESON_TAC[ARITH_RULE `10 <= (m:num) + 10`; ARITH_RULE `(n:num) < 10 ==> ~(10 <= n)`]);;

let RO_HALVES = prove
 (`forall c1 c2 a b l. rofirst (auxown 2 c1 c2 a b l) = auxown 0 c1 c2 a b l /\
                 CARD (rosecond (auxown 2 c1 c2 a b l)) = CARD (auxown 1 c1 c2 a b l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[AUXOWN2_COMBOWN] THEN
  SIMP_TAC[RO_FIRST_COMBINED; RO_SECOND_COMBINED; AUXOWN_SUBSET10; ARITH_RULE `0 < 2`] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_AUXOWN] THEN SIMP_TAC[EQ_ADD_RCANCEL]);;

(* Lean: SetBounds *)
let rosetb = new_definition
 `rosetb fam m s <=>
    (pklow m 0 <= CARD (rofirst s) /\ CARD (rofirst s) <= pkup fam m 0) /\
    (pklow m 1 <= CARD (rosecond s) /\ CARD (rosecond s) <= pkup fam m 1)`;;

(* Lean: restrictByBudget *)
let RO_RESTRICT_BUDGET = prove
 (`forall fam m al. cdom fam m al ==> cdom fam m (FILTER (rosetb fam m) al)`,
  REWRITE_TAC[cdom; MEM_FILTER] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[rosetb; RO_HALVES] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `fam:num->bool`; `0`; `i:num`] PK_BUDGET) THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `fam:num->bool`; `1`; `i:num`] PK_BUDGET) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 2 /\ 1 < 2`] THEN SIMP_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: restrictFCardOne  (owned.filter (fun n => n < 10) is rofirst) *)
let RO_RESTRICT_F1 = prove
 (`forall fam m al. cdom fam m al /\ CARD (fam INTER auxex 0) = 2 /\ ~(m IN auxex 0)
     ==> cdom fam m (FILTER (\s. CARD (rofirst s) = 1) al)`,
  REWRITE_TAC[cdom; MEM_FILTER] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[RO_HALVES] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `fam:num->bool`; `0`; `i:num`] PK_BUDGET) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 2`; pkup; pklow] THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: extend / pushOwners (perm given by its list of values) *)
let roext = new_definition `roext (p:num list) n = if n < 10 then EL n p else n`;;
let ropush = new_definition `ropush (p:num list) s = IMAGE (roext p) s`;;

(* Lean: reflectXF, reflectXG, halfTurnPerm (as value lists) *)
let RO_REFLECTXF = [8;9;6;7;4;5;2;3;0;1];;
let RO_REFLECTXG = [8;9;5;6;7;2;3;4;0;1];;
let RO_HALFTURN = [9;8;7;6;5;4;3;2;1;0];;

(* ------------------------------------------------------------------------- *)
(* Literal evaluation of the budget filters.                                  *)
(* ------------------------------------------------------------------------- *)

let RO_FIRST_SOL = prove
 (`forall l. rofirst (set_of_list l) = set_of_list (FILTER (\n. n < 10) l)`,
  REWRITE_TAC[rofirst; EXTENSION; IN_ELIM_THM; IN_SET_OF_LIST; MEM_FILTER] THEN MESON_TAC[]);;
let RO_SECOND_SOL = prove
 (`forall l. rosecond (set_of_list l) = set_of_list (FILTER (\n. 10 <= n) l)`,
  REWRITE_TAC[rosecond; EXTENSION; IN_ELIM_THM; IN_SET_OF_LIST; MEM_FILTER] THEN MESON_TAC[]);;

(* |- CARD (rofirst S) = n  /  |- CARD (rosecond S) = n  for literal S *)
let ro_card_conv tm =
  let th = (RAND_CONV (RAND_CONV setlit_conv) THENC
            RAND_CONV (REWRITE_CONV[RO_FIRST_SOL; RO_SECOND_SOL]) THENC
            RAND_CONV (RAND_CONV (filter_by_conv NUM_REDUCE_CONV))) tm in
  TRANS th (CARD_LIST_CONV (rhs (concl th)));;
let ro_card_dconv tm =
  if is_comb tm && rator tm = `CARD:(num->bool)->num` && is_comb (rand tm) &&
     (rator (rand tm) = `rofirst` || rator (rand tm) = `rosecond`) && is_numset (rand (rand tm))
  then ro_card_conv tm else failwith "ro_card_dconv";;

(* evaluate FILTER P al for the budget predicates above (fam, m literal) *)
let ro_filter_conv fam m tm =
  let ths = [pklow_thm m 0; pklow_thm m 1; pkup_thm fam m 0; pkup_thm fam m 1] in
  filter_by_conv (REWRITE_CONV[rosetb] THENC ONCE_DEPTH_CONV ro_card_dconv THENC REWRITE_CONV ths THENC
                  NUM_REDUCE_CONV THENC REWRITE_CONV[]) tm;;

let cdom_parts th =
  let c = concl th in
  (rand(rator(rator c)), dest_small_numeral (rand(rator c)), rand c);;

(* Lean: restrictByBudget, evaluated:  |- cdom fam m [filtered literal list] *)
let ro_restrict_budget th =
  let (fam, m, _) = cdom_parts th in
  CONV_RULE (RAND_CONV (ro_filter_conv fam m)) (MATCH_MP RO_RESTRICT_BUDGET th);;

(* Lean: restrictFCardOne, evaluated *)
let ro_restrict_f1 th =
  let (fam, m, _) = cdom_parts th in
  let c = EQT_ELIM ((REWRITE_CONV[card_exempt fam 0]) (mk_eq(mk_comb(`CARD:(num->bool)->num`,
             mk_binop `(INTER):(num->bool)->(num->bool)->(num->bool)` fam `auxex 0`), `2`))) in
  let ne = EQF_ELIM (AUXEX_CONV (mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral m), `auxex 0`))) in
  CONV_RULE (RAND_CONV (ro_filter_conv fam m)) (MATCH_MP RO_RESTRICT_F1 (end_itlist CONJ [th; c; ne]));;

(* ------------------------------------------------------------------------- *)
(* Producers for the Lean defs.                                              *)
(* ------------------------------------------------------------------------- *)

(* Lean: ofSingle (single_actual):  |- hdom fam m k al  for single spec n.
   Fails unless Bounds holds (the budget interval lies in the spec's). *)
let ro_single fam n = pk_single fam n;;
let ro_single_x fam n al = pk_single_x fam n (Some al);;

(* Lean: ofCombined:  |- cdom fam m al  for combined spec n *)
let ro_combined fam n = pk_combined fam n;;
let ro_combined_x fam n al = pk_combined_x fam n (Some al);;

(* Lean: SmallOwnerDomain.smallSubsets, in Lean's order *)
let RO_SMALL = [[]] @ map (fun i -> [i]) (0--9) @
  List.concat (map (fun i -> map (fun j -> [i; j]) (filter (fun j -> i < j) (0--9))) (0--9));;

let ro_small_lists fam m k =
  let lo = pk_num (pklow_thm m k) and hi = pk_num (pkup_thm fam m k) in
  if hi > 2 then failwith "ro_small_budget: upper > 2" else
  filter (fun s -> lo <= length s && length s <= hi) RO_SMALL;;

(* Lean: ofSmallBudget:  |- hdom fam m k [smallSubsets filtered by the budget] *)
let ro_small_budget fam m k = pk_budget_hdom fam m k (ro_small_lists fam m k);;

(* Lean: ofSmallBudgetWithSeed: the small budget list filtered by idx IN owned,
   tri = (points, target, s, t): a triangle certificate on seed points of m
   whose target is EL idx (AUXPTS k) (Lean: TriangleCertificate) *)
let ro_small_budget_seed fam m k idx tri =
  let base = ro_small_lists fam m k in
  let keep = filter (mem idx) base in
  let lo = pk_num (pklow_thm m k) and hi = pk_num (pkup_thm fam m k) in
  let sth = spec_theorem m k lo hi base in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let (hl, hh) = bound_tms k lo hi in
  let hyps = LQ_HYPS @ [ownp; hl; hh] in
  let d = List.fold_left MP (SPECL SPEC5 sth) (map ASSUME hyps) in
  let seeds = pk_seeds SPEC5 (map ASSUME LQ_HYPS) (marker_facts (ASSUME ownp)) (bits m) in
  let tp = tri_point seeds tri in
  let elth = (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV)
               (mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral idx),
                        mk_comb(`AUXPTS`, mk_small_numeral k))) in
  let tp' = EQ_MP (SYM (AP_THM (AP_TERM `(IN):real^2->(real^2->bool)->bool` elth) (rand(concl tp)))) tp in
  let ltth = EQT_ELIM((REWRITE_CONV[LEN_AUX.(k)] THENC NUM_REDUCE_CONV)
               (mk_binop `(<):num->num->bool` (mk_small_numeral idx)
                  (mk_comb(`LENGTH:(real^2)list->num`, mk_comb(`AUXPTS`, mk_small_numeral k))))) in
  let memth = MATCH_MP AUXMEM (CONJ ltth tp') in
  let a = auxown_tm k in
  let goal = if keep = [] then `false` else list_mk_disj (map (fun s -> mk_eq(a, set_tm s)) keep) in
  let rec go th =
    if is_disj (concl th) then
      let p, q = dest_disj (concl th) in DISJ_CASES th (go (ASSUME p)) (go (ASSUME q))
    else if concl th = `false` then CONTR goal th
    else
      let s = map dest_small_numeral (dest_list (rand (rhs (concl th)))) in
      if mem idx s then
        let ds = disjuncts goal in
        let i = index (concl th) ds in
        let rec build ds j = match ds with
            [_] -> th
          | x::rest -> if j = 0 then DISJ1 th (list_mk_disj rest) else DISJ2 x (build rest (j-1))
          | [] -> failwith "build" in
        build ds i
      else
        let m' = EQ_MP (AP_TERM (mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral idx)) th) memth in
        let f = EQ_MP ((REWRITE_CONV[IN_SET_OF_LIST; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
                         (concl m')) m' in
        CONTR goal f in
  let th = go d in
  pk_hdom_local fam m k lo hi hyps th (mk_list(map mk_numset keep, `:num->bool`));;

(* Lean: ofTransformedCombined.  Source combined spec n (mask w.mask) under the
   transform trf = (swap, reflectX, reflectY) with point permutations permF,
   permG (value lists); the target mask is t.maskAction w.mask.  Every local
   query of the source is re-proved for the target with mapped points and
   owner indices; the result is weakened to the list al (Lean's hallowed). *)
let RO_NEXT_ID = ref 7000;;
let ro_fresh_id () =
  let used i = exists (fun (j,_,_,_,_,_) -> j = i) (SINGLE_SPECS @ !EXTRA_SINGLE) ||
               exists (fun (j,_,_,_,_) -> j = i) (COMBINED_SPECS @ !EXTRA_COMBINED) in
  while used !RO_NEXT_ID do incr RO_NEXT_ID done;
  let i = !RO_NEXT_ID in incr RO_NEXT_ID; i;;

let aux_q k j =
  let th = (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV)
             (mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral j), mk_comb(`AUXPTS`, mk_small_numeral k))) in
  match dest_list (rand (rhs (concl th))) with [x; y] -> (rat_of_term x, rat_of_term y) | _ -> failwith "aux_q";;

let check_perm trf k perm =
  List.iter (fun j -> if not (qeq (tr_q trf (aux_q k j)) (aux_q k (el j perm))) then
     failwith (Printf.sprintf "ro_transformed: permutation %d does not match point %d" k j)) (0--9);;

let mask_action trf m = itlist (fun i acc -> acc + (1 lsl (marker_action trf i))) (bits m) 0;;

let ro_transformed fam tmask trf n permF permG al =
  check_perm trf 0 permF; check_perm trf 1 permG;
  let (_, sm, f, g, allowed) = pk_comb_row n in
  if mask_action trf sm <> tmask then failwith "ro_transformed: mask action" else
  let tp (x, y) = let (x1, y1) = tr_point trf (term_of_rat x, term_of_rat y) in (rat_of_term x1, rat_of_term y1) in
  let p20 j = if j < 10 then el j permF else el (j - 10) permG + 10 in
  let idF = ro_fresh_id () in transformed_spec idF f tmask 0 trf permF;
  let idG = ro_fresh_id () in transformed_spec idG g tmask 1 trf permG;
  List.iter (fun (_, m, k, ow, uin, uout) ->
      if m = sm && k = 2 then
        Hashtbl.replace PK_XQ (tmask, 2, List.sort compare (map p20 ow)) (map tp uin, map tp uout))
    LOCAL_QUERIES;
  let idC = ro_fresh_id () in
  EXTRA_COMBINED := (idC, tmask, idF, idG, map (fun s -> List.sort compare (map p20 s)) allowed) :: !EXTRA_COMBINED;
  pk_combined_x fam idC (Some al);;

(* Lean: OwnerBudget.HalfDomain.ofSeedHull (budget exactly one point, and a
   triangle certificate on seeds of m for the point idx):  |- hdom fam m k [{idx}].
   tri = ([p0; p1; p2], target, s, t), rationals (Lean TriangleCertificate fields). *)
let pk_hdom_seedhull fam m k idx tri =
  if pk_num (pklow_thm m k) <> 1 || pk_num (pkup_thm fam m k) <> 1 then
    failwith "pk_hdom_seedhull: budget is not exactly one" else
  ro_small_budget_seed fam m k idx tri;;
