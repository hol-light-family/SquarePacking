(* ========================================================================= *)
(* Phase 2: bridge extensions for the template cases (new domain kinds).     *)
(*  - promoted owner budgets (Jatloe Bridge/PromotedOwnerBudget:             *)
(*    Promotion.{combined, ofSpec, ownDomain, singleton});                   *)
(*  - removal of owner sets by local queries (S12 CertifiedDomain.remove);   *)
(*  - the upper-middle domain of mask 33792 (Bridge/UpperMidDomain): the    *)
(*    half-turn image of single spec 72, re-proved from mapped local queries *)
(*    (as in cornerpair.ml), times spec 101, minus three hull queries;       *)
(*  - gen_case_thm_y: gen_case_thm_x with a pluggable domain function.       *)
(* ========================================================================= *)

needs "n12/geometry/gen_bridge.ml";;
needs "n12/geometry/cornerpair.ml";;
needs "n12/geometry/promote.ml";;

type phalf = Ph of half | Phspec of int * int | Phsing of int | Phown of int
           | Prspec of int * int
           | Prsmall of int * int * ((num * num) list * (num * num) * num * num);;
type xdom = Xd of dom | Xpcomb of int | Xpprod of phalf * phalf | Xrem of xdom * int list list
          | Xrcomb of int | Xrtr of int * (bool * bool * bool);;

let IN_NONEMPTY_X = prove
 (`forall x:num s. x IN s ==> ~(s = {})`, SET_TAC[]);;

let CARD_LE1_MEMBER = prove
 (`forall S j:num. FINITE S /\ CARD S <= 1 /\ j IN S ==> S = set_of_list [j]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD1_MEMBER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `n <= 1 /\ ~(n = 0) ==> n = 1`) THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
  ASM SET_TAC[]);;

(* split a disjunction of equations, continue with k on each *)
let over_disj th k =
  let rec go th = if is_disj (concl th) then
      let a, b = dest_disj (concl th) in DISJ_CASES th (k (ASSUME a)) (go (ASSUME b))
    else k th in
  go th;;

let inject_disj goal th =
  let ds = disjuncts goal in
  let i = index (concl th) ds in
  let rec build ds j = match ds with
      [_] -> th
    | d::rest -> if j = 0 then DISJ1 th (list_mk_disj rest) else DISJ2 d (build rest (j-1))
    | [] -> failwith "inject_disj" in
  build ds i;;

(* |- idx IN auxown k (square sq) from a triangle certificate over its seeds *)
let promo_owns sq k idx tri =
  let (m, iv, lt, own, sqth) = sq in
  let sp = sq_params iv in
  let seeds = seeds_at sp sqth (marker_facts own) (bits m) in
  let tp = try tri_point seeds tri with Failure msg -> failwith ("promo tri_point: " ^ msg) in
  let elth = (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV)
               (mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral idx),
                        mk_comb(`AUXPTS`, mk_small_numeral k))) in
  let tp' = EQ_MP (SYM (AP_THM (AP_TERM `(IN):real^2->(real^2->bool)->bool` elth) (rand(concl tp)))) tp in
  let ltth = EQT_ELIM((REWRITE_CONV[LEN_AUX.(k)] THENC NUM_REDUCE_CONV)
             (mk_binop `(<):num->num->bool` (mk_small_numeral idx)
                (mk_comb(`LENGTH:(real^2)list->num`, mk_comb(`AUXPTS`, mk_small_numeral k))))) in
  MATCH_MP AUXMEM (CONJ ltth tp');;

(* promoted budget of square sq for kind k:  |- CARD (auxown k sq) <= hi  (hi computed) *)
let promo_budget pctx hnp hrow sq k =
  let (sq0, owns) = pctx in
  let (_, iv, lt, own, _) = sq and (_, iv0, lt0, own0, _) = sq0 in
  let kth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let ne = MATCH_MP IN_NONEMPTY_X (owns k) in
  let bud = MATCH_MP SQUARE_BUDGET_P (end_itlist CONJ [hnp; hrow; kth; lt; own; lt0; ne; own0]) in
  let bud' = CONV_RULE (LAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV filter_conv) THENC CARD_LIST_CONV))) bud in
  let atm = list_mk_comb(`auxown`, mk_small_numeral k :: sq_params iv) in
  let n = dest_small_numeral (rand(lhand(concl bud'))) in
  if n > 10 then failwith "promo_budget" else
  MP (ARITH_RULE (mk_imp(concl bud', mk_binop `(<=):num->num->bool`
        (mk_comb(`CARD:(num->bool)->num`, atm)) (mk_small_numeral (10 - n))))) bud';;

(* the ordinary budget  |- CARD (auxown k sq) <= hi  (OwnerBudget / nat_aux_budget) *)
let std_budget hnp hrow sq k =
  let (_, iv, lt, own, _) = sq in
  let kth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let bud = MATCH_MP SQUARE_BUDGET (end_itlist CONJ [hnp; hrow; kth; lt; own]) in
  let bud' = CONV_RULE (LAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV filter_conv) THENC CARD_LIST_CONV))) bud in
  let atm = list_mk_comb(`auxown`, mk_small_numeral k :: sq_params iv) in
  let n = dest_small_numeral (rand(lhand(concl bud'))) in
  if n > 10 then failwith "std_budget" else
  MP (ARITH_RULE (mk_imp(concl bud', mk_binop `(<=):num->num->bool`
        (mk_comb(`CARD:(num->bool)->num`, atm)) (mk_small_numeral (10 - n))))) bud';;

(* lower bound 1 <= CARD (auxown k sq) when the mask is not exempt *)
let nonexempt_lower hnp sq k =
  let (m, iv, lt, own, _) = sq in
  let kth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let pk = pk_is k (bits m) in
  if rhs(concl pk) <> `false` then None else
  let np = EQF_ELIM (TRANS (AP_TERM (rator(lhs(concl pk))) own) pk) in
  Some (MATCH_MP SQUARE_NONEMPTY (end_itlist CONJ [hnp; kth; lt; np]));;

(* drop the disjuncts  auxown k sq = set_of_list s  of th whose size violates the budget
   (RelaxedOwnerDomain.restrictByBudget / restrictFCardOne) *)
let restrict_card th hb hl =
  let bnd = dest_small_numeral (rand(concl hb)) in
  let okc c = c <= bnd && (match hl with None -> true | Some _ -> c >= 1) in
  let ds = filter (fun t -> okc (List.length (dest_list (rand(rand t))))) (disjuncts (concl th)) in
  if length ds = length (disjuncts (concl th)) then th else
  let goal = if ds = [] then `false` else list_mk_disj ds in
  over_disj th (fun e ->
    let c = List.length (dest_list (rand(rand(concl e)))) in
    if okc c then inject_disj goal e else
    let cth = TRANS (AP_TERM `CARD:(num->bool)->num` e) (CARD_LIST_CONV (card_tm (rhs(concl e)))) in
    let bad = if c > bnd then hb else (match hl with Some h -> h | None -> failwith "restrict_card") in
    let f = EQ_MP (NUM_REDUCE_CONV (concl (REWRITE_RULE[cth] bad))) (REWRITE_RULE[cth] bad) in
    CONTR goal f);;

(* single spec n on square sq, budget hb (|- CARD <= B); spec bounds may be relaxed
   (RelaxedOwnerDomain.Bounds: lo <= lower, B <= hi); the result is restricted to the budget *)
let single_domain_g budget hnp hrow r sq n =
  let (m, iv, lt, own, sqth) = sq in
  let (_,m',k,lo,hi,_) = find (fun (i,_,_,_,_,_) -> i = n) (SINGLE_SPECS @ !EXTRA_SINGLE) in
  if m' <> m then failwith "single_domain_g: mask mismatch" else
  let sp = sq_params iv in
  let atm = list_mk_comb(`auxown`, mk_small_numeral k :: sp) in
  let hl = nonexempt_lower hnp sq k in
  let hlo = if lo = 0 then SPEC (mk_comb(`CARD:(num->bool)->num`, atm)) LE_0 else
    match hl with Some h when lo = 1 -> h | _ -> failwith "single_domain_g: lower bound" in
  let hb = budget sq k in
  let hhi = try MP (ARITH_RULE (mk_imp(concl hb, mk_binop `(<=):num->num->bool`
                 (mk_comb(`CARD:(num->bool)->num`, atm)) (mk_small_numeral hi)))) hb
            with Failure _ -> failwith "single_domain_g: upper bound" in
  let sth = try Hashtbl.find SPEC_TBL n with Not_found ->
    let (_,m0,k0,lo0,hi0,al0) = find (fun (i,_,_,_,_,_) -> i = n) (SINGLE_SPECS @ !EXTRA_SINGLE) in
    let th = spec_theorem m0 k0 lo0 hi0 al0 in Hashtbl.replace SPEC_TBL n th; th in
  let th = List.fold_left (fun th h -> MP th h) (SPECL sp sth) (sqth @ [own; hlo; hhi]) in
  restrict_card th hb hl;;

(* Promotion.ofSpec: single spec n on square sq with the promoted budget *)
let single_domain_p pctx hnp hrow r sq n = single_domain_g (promo_budget pctx hnp hrow) hnp hrow r sq n;;

(* RelaxedOwnerDomain.ofSmallBudgetWithSeed: CARD <= 2 and a seed-hull point owned *)
let SMALL2_SETS = prove
 (`forall S j:num. FINITE S /\ CARD S <= 2 /\ j IN S ==> S = {j} \/ exists k. ~(k = j) /\ S = {j, k}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `S = {j:num}` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exists k:num. k IN S /\ ~(k = j)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{j:num, k} SUBSET S` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(GSYM CARD_SUBSET_LE) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_ARITH_TAC);;

let SMALL2_TBL = Hashtbl.create 10;;
let small2_lemma j =
  try Hashtbl.find SMALL2_TBL j with Not_found ->
  let sets = [j] :: map (fun v -> List.sort compare [j; v]) (filter (fun v -> v <> j) (0--9)) in
  let goal = list_mk_disj (map (fun s -> mk_eq(`S:num->bool`, set_tm s)) sets) in
  let jt = mk_small_numeral j in
  let th = prove(mk_forall(`S:num->bool`, mk_imp(list_mk_conj [`S SUBSET {x:num | x < 10}`; `FINITE (S:num->bool)`;
                   `CARD (S:num->bool) <= 2`; mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, jt), `S:num->bool`)], goal)),
    GEN_TAC THEN STRIP_TAC THEN MP_TAC(SPECL [`S:num->bool`; jt] SMALL2_SETS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th; set_of_list]) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `k < 10` ASSUME_TAC THENL
     [UNDISCH_TAC `S SUBSET {x:num | x < 10}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `k:num` (concl th) && concl th <> `k < 10`))) THEN
    UNDISCH_TAC `k < 10` THEN
    SPEC_TAC(`k:num`,`k:num`) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[set_of_list] THEN
    MESON_TAC[INSERT_COMM]) in
  Hashtbl.add SMALL2_TBL j th; th;;

let small_seed_domain hnp hrow sq k idx tri =
  let (m, iv, lt, own, sqth) = sq in
  let hb = std_budget hnp hrow sq k in
  if dest_small_numeral (rand(concl hb)) > 2 then failwith "Prsmall: budget > 2" else
  let kth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let sub = MATCH_MP AUXOWN_SUBSET10 kth |> SPECL (sq_params iv) in
  let fin = SPECL (mk_small_numeral k :: sq_params iv) FINITE_AUXOWN in
  let hb2 = MP (ARITH_RULE (mk_imp(concl hb, mk_binop `(<=):num->num->bool` (lhand(concl hb)) `2`))) hb in
  let mem = promo_owns sq k idx tri in
  let th = MATCH_MP (small2_lemma idx) (end_itlist CONJ [sub; fin; hb2; mem]) in
  restrict_card th hb (nonexempt_lower hnp sq k);;

(* half domains, promoted (pctx) or relaxed *)
let half_domain_p pctx hnp hrow r sq h =
  let (m, iv, lt, own, sqth) = sq in
  let need () = match pctx with Some p -> p | None -> failwith "promoted half: no promotion" in
  match h with
    Ph h -> half_domain hnp hrow r sq h
  | Prspec(n, _) -> single_domain_g (std_budget hnp hrow) hnp hrow r sq n
  | Prsmall(k, idx, tri) -> small_seed_domain hnp hrow sq k idx tri
  | Phspec(n, _) -> single_domain_p (need ()) hnp hrow r sq n
  | Phown k ->
      let pctx = need () in
      let (sq0, owns) = pctx in
      let (m0, _, _, _, _) = sq0 in
      if m0 <> m then failwith "Phown: not the promoted mask" else
      let mem = owns k in
      let hb = promo_budget pctx hnp hrow sq k in
      let fin = SPECL (mk_small_numeral k :: sq_params iv) FINITE_AUXOWN in
      MATCH_MP CARD_LE1_MEMBER (end_itlist CONJ [fin; hb; mem])
  | Phsing k ->
      let pctx = need () in
      let kth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
      let pk = pk_is k (bits m) in
      let np = EQF_ELIM (TRANS (AP_TERM (rator(lhs(concl pk))) own) pk) in
      let lo = MATCH_MP SQUARE_NONEMPTY (end_itlist CONJ [hnp; kth; lt; np]) in
      let hb = promo_budget pctx hnp hrow sq k in
      let atm = list_mk_comb(`auxown`, mk_small_numeral k :: sq_params iv) in
      let eq = MP (ARITH_RULE (mk_imp(mk_conj(concl lo, concl hb),
                 mk_eq(mk_comb(`CARD:(num->bool)->num`, atm), `1`)))) (CONJ lo hb) in
      let sub = MATCH_MP AUXOWN_SUBSET10 kth |> SPECL (sq_params iv) in
      MATCH_MP CARD1_ENUM (CONJ sub eq);;

let list_of_set_eq th = map dest_small_numeral (dest_list (rand(rand(concl th))));;

(* kind-2 domain from two half domains (OwnerBudget.product / CombinedSpec.sound);
   sets not in `allowed` (if given) are refuted by registered local queries *)
let product_domain sq allowed d0 d1 =
  let (m, iv, lt, own, sqth) = sq in
  let a2 = list_mk_comb(`auxown`, `2` :: sq_params iv) in
  let lists th = map (fun t -> map dest_small_numeral (dest_list (rand(rand t)))) (disjuncts (concl th)) in
  let prods = if concl d0 = `false` || concl d1 = `false` then [] else
    setify (List.concat (map (fun x -> map (fun y -> set_merge x y) (lists d1)) (lists d0))) in
  let merged = match allowed with Some al -> filter (fun s -> mem s prods) al | None -> prods in
  let goal = if merged = [] then `false` else list_mk_disj (map (fun d -> mk_eq(a2, set_tm d)) merged) in
  let fin thx thy =
    let th = MATCH_MP AUXOWN2_LIST (CONJ thx thy) in
    let th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV[APPEND; MAP] THENC DEPTH_CONV BETA_CONV THENC
                                               NUM_REDUCE_CONV))) th in
    let s = list_of_set_eq th in
    if mem s merged then inject_disj goal th else
    let q = lq_thm (m, 2, s) in
    CONTR goal (List.fold_left (fun th h -> MP th h) (SPECL (sq_params iv) q) (sqth @ [own; th])) in
  let k0 th k = if concl th = `false` then CONTR goal th else over_disj th k in
  k0 d0 (fun thx -> k0 d1 (fun thy -> fin thx thy));;

(* remove owner sets from a kind-2 domain by local queries (CertifiedDomain.remove) *)
let remove_domain sq dth rem =
  let (m, iv, lt, own, sqth) = sq in
  let ds = filter (fun t -> not (mem (map dest_small_numeral (dest_list (rand(rand t)))) rem)) (disjuncts (concl dth)) in
  let goal = if ds = [] then `false` else list_mk_disj ds in
  over_disj dth (fun th ->
    let s = list_of_set_eq th in
    if mem s rem then
      let q = lq_thm (m, 2, s) in
      CONTR goal (List.fold_left (fun th h -> MP th h) (SPECL (sq_params iv) q) (sqth @ [own; th]))
    else inject_disj goal th);;

(* promotion context of a case: the promoted square and its two forced memberships *)
let promo_ctx sq_of promo =
  match promo with
    None -> None
  | Some (pm, wl) ->
      let sq0 = sq_of pm in
      let tbl = Array.of_list (map (fun (k, (idx, tri)) -> promo_owns sq0 k idx tri) (zip [0; 1] wl)) in
      Some (sq0, (fun k -> tbl.(k)));;

(* RelaxedOwnerDomain.ofTransformedCombined: the image of combined spec srcid under a
   symmetry, registered as a new combined spec whose queries are the mapped source
   queries (each re-proved for the image marker set) *)
let REFLECTXG = [8;9;5;6;7;2;3;4;0;1];;
let HALFTURNF = [9;8;7;6;5;4;3;2;1;0];;
let tr_perms trf = match trf with
    (false, true, false) -> (REFLECTXF, REFLECTXG)
  | (false, true, true) -> (HALFTURNF, HALFTURNF)
  | _ -> failwith "tr_perms: transform not supported";;
let TR_COUNTER = ref 3000;;
let TRC_TBL = Hashtbl.create 10;;
let transformed_combined srcid tmask trf =
  try Hashtbl.find TRC_TBL (srcid, tmask, trf) with Not_found ->
  let (permF, permG) = tr_perms trf in
  let (_, sm, f, g, allowed) = find (fun (i,_,_,_,_) -> i = srcid) COMBINED_SPECS in
  let fid = !TR_COUNTER and gid = !TR_COUNTER + 1 and nid = !TR_COUNTER + 2 in
  TR_COUNTER := !TR_COUNTER + 3;
  transformed_spec fid f tmask 0 trf permF;
  transformed_spec gid g tmask 1 trf permG;
  let p20 j = if j < 10 then el j permF else el (j - 10) permG + 10 in
  let tp (x, y) = let (x1, y1) = tr_point trf (term_of_rat x, term_of_rat y) in
                  (rat_of_term x1, rat_of_term y1) in
  List.iter (fun (_, m, k, ow, uin, uout) ->
      if m = sm && k = 2 then add_query (tmask, 2, List.sort compare (map p20 ow), map tp uin, map tp uout))
    LOCAL_QUERIES;
  EXTRA_COMBINED := (nid, tmask, fid, gid, map (fun s -> List.sort compare (map p20 s)) allowed) :: !EXTRA_COMBINED;
  List.iter (fun (i, m, k, lo, hi, al) ->
    if not (Hashtbl.mem SPEC_TBL i) then Hashtbl.replace SPEC_TBL i (spec_theorem m k lo hi al))
    !EXTRA_SINGLE;
  Hashtbl.add TRC_TBL (srcid, tmask, trf) nid; nid;;

let rec xdomain_thm pctx hnp hrow r sq d =
  match d with
    Xd d -> domain_thm hnp hrow r sq d
  | Xpcomb n ->
      let pc = match pctx with Some p -> p | None -> failwith "Xpcomb: no promotion" in
      let (_,m',f,g,allowed) = find (fun (i,_,_,_,_) -> i = n) (COMBINED_SPECS @ !EXTRA_COMBINED) in
      let (m, _, _, _, _) = sq in
      if m' <> m then failwith "Xpcomb: mask mismatch" else
      product_domain sq (Some allowed) (single_domain_p pc hnp hrow r sq f) (single_domain_p pc hnp hrow r sq g)
  | Xpprod(h0, h1) ->
      product_domain sq None (half_domain_p pctx hnp hrow r sq h0) (half_domain_p pctx hnp hrow r sq h1)
  | Xrem(d, rem) -> remove_domain sq (xdomain_thm pctx hnp hrow r sq d) rem
  | Xrtr(n, trf) ->
      let (m, _, _, _, _) = sq in
      xdomain_thm pctx hnp hrow r sq (Xrcomb (transformed_combined n m trf))
  | Xrcomb n ->
      let (_,m',f,g,allowed) = find (fun (i,_,_,_,_) -> i = n) (COMBINED_SPECS @ !EXTRA_COMBINED) in
      let (m, _, _, _, _) = sq in
      if m' <> m then failwith "Xrcomb: mask mismatch" else
      let sd = single_domain_g (std_budget hnp hrow) hnp hrow r sq in
      product_domain sq (Some allowed) (sd f) (sd g);;

(* the domain function for gen_case_thm_y; promotion contexts are memoised per case *)
let xdfun promo =
  let ctx = ref None in
  fun sq_of hnp hrow r sq d ->
    let pc = match !ctx with Some c -> c | None -> let c = promo_ctx sq_of promo in ctx := Some c; c in
    xdomain_thm pc hnp hrow r sq d;;

(* ------------------------------------------------------------------------- *)
(* UpperMidDomain.domain33792: registered as combined spec 2002.             *)
(* ------------------------------------------------------------------------- *)

let () =
  transformed_spec 1004 72 33792 0 (false, true, true) HALFTURNF;
  let hull = map q2 [("8/5","3"); ("2","1543/500"); ("47/20","47/20")] and tgt = [q2 ("87/50","3")] in
  List.iter (fun j -> add_query (33792, 2, [3; j + 10], hull, tgt)) [6; 7; 9];
  let prod = List.concat (map (fun x -> map (fun y -> set_merge [x] [y]) [6; 7; 9]) [7; 5; 3]) in
  EXTRA_COMBINED := (2002, 33792, 1004, 101,
      filter (fun s -> not (mem s [[3;16]; [3;17]; [3;19]])) prod) :: !EXTRA_COMBINED;
  List.iter (fun (i, m, k, lo, hi, al) ->
    if not (Hashtbl.mem SPEC_TBL i) then Hashtbl.replace SPEC_TBL i (spec_theorem m k lo hi al))
  !EXTRA_SINGLE;;

(* Seeds: corner extras (Lean S12.Seeds.cornerExtras, CornerForcing.corner_pair_forces);
   copied from geometry/PackingContext.ml under the BX_ prefix *)
let BX_CORNER_POS = prove
 (`forall c1 c2 a b l bb. &1 < l /\ &0 <= a /\ &0 <= b /\
     (a + b) * l / &2 <= c1 /\ (a + b) * l / &2 <= c2 /\ bb <= &1 /\
     vector[&1; bb] IN osq c1 c2 a b l /\ vector[bb; &1] IN osq c1 c2 a b l
     ==> vector[&1; &1] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_OSQ_BANDS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= a * (c1 - (a + b) * l / &2) /\ &0 <= b * (c2 - (a + b) * l / &2) /\
                &0 < (l - &1) * (&1 + (a + b) * (a + b)) /\ &0 <= (a + b - &1) * (a + b - &1) /\
                &0 <= a * (&1 - bb) /\ &0 <= b * (&1 - bb)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC(SPEC `a + b:real` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_SQUARE];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC]);;

let BX_CORNER = prove
 (`forall c1 c2 a b l bb. &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\ bb <= &1 /\
     vector[&1; bb] IN osq c1 c2 a b l /\ vector[bb; &1] IN osq c1 c2 a b l
     ==> vector[&1; &1] IN osq c1 c2 a b l`,
  let CASE_TAC (ea,eb) (a',b') =
    SUBGOAL_THEN (mk_conj(mk_eq(`abs a`,ea), mk_eq(`abs b`,eb)))
     (CONJUNCTS_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c1:real`; `c2:real`; a'; b'; `l:real`; `bb:real`] BX_CORNER_POS) THEN
    REWRITE_TAC[OSQ_ROT; OSQ_NEG; OSQ_ROT3] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC in
  REPEAT GEN_TAC THEN REWRITE_TAC[owalls] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= a` THEN ASM_CASES_TAC `&0 <= b` THENL
   [CASE_TAC (`a:real`,`b:real`) (`a:real`,`b:real`);
    CASE_TAC (`a:real`,`--b`) (`--b`,`a:real`);
    CASE_TAC (`--a`,`b:real`) (`b:real`,`--a`);
    CASE_TAC (`--a`,`--b`) (`--a`,`--b`)]);;

let BX_CORNER0 =
  let hyps = [`&1 < l`; `a * a + b * b = &1`; `owalls c1 c2 a b l`;
              `vector[&1; &457 / &500] IN osq c1 c2 a b l`;
              `vector[&457 / &500; &1] IN osq c1 c2 a b l`] in
  prove(list_mk_forall(SPEC5, mk_imp(list_mk_conj hyps, `vector[&1; &1] IN osq c1 c2 a b l`)),
    REPEAT STRIP_TAC THEN MATCH_MP_TAC BX_CORNER THEN EXISTS_TAC `&457 / &500` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let BX_CORNER_EXPL = D4_FORMS BX_CORNER0;;

let bx_corner_seeds sp sqhyps facts =
  let use th =
    let th = SPECL sp th in
    let hs = conjuncts(lhand(concl th)) in
    let prove_h h =
      try find (fun f -> aconv (concl f) h) (facts @ sqhyps)
      with Failure _ ->
        let rels = filter (fun f -> is_real_rel (concl f)) sqhyps in
        if is_real_rel h then
          MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), h))) (end_itlist CONJ rels)
        else failwith "no" in
    try CONJUNCTS (MP th (end_itlist CONJ (map prove_h hs))) with Failure _ -> [] in
  List.concat (map use BX_CORNER_EXPL);;

(* ------------------------------------------------------------------------- *)
(* The case engine (gen_case_thm_x split into reusable parts).               *)
(*  case_ctx: the squares of all masks, their domains (dfun);                *)
(*  forced_eq: certified_domain_forced;                                      *)
(*  apply_tmpl: discharge every premise of a template theorem instance from *)
(*    the packing, given owner-set equations of some squares;               *)
(*  enum_leaves: the domain enumeration (DomainEnumeration /                 *)
(*    certified_domain_assignments_mem), a leaf prover gets the assignment;  *)
(*  close_case: |- EXCLUDED_ROW ri from a proof of F under the row hyps.     *)
(* ------------------------------------------------------------------------- *)

type cctx = { cid : int; ri : int; rw : term; chyp : term; hnp : thm; hrow : thm;
              sqs : (int * (thm * (int * term * thm * thm * thm list))) list;
              dths : (int * thm) list;
              seeds_tbl : (int, thm list * thm list) Hashtbl.t };;

let case_ctx dfun xmasks (cid, fam, doms) =
  let fam = List.sort compare fam in
  let ri = try index fam (map row_masks (0--576)) with Failure _ -> failwith "case: row not found" in
  let r = ROW_LIST ri in
  let hyp = mk_conj(`NPACK c1 c2 a b l`,
              mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, mk_comb(`set_of_list:(num)list->num->bool`, r))) in
  let hnp = CONJUNCT1 (ASSUME hyp) and hrow = CONJUNCT2 (ASSUME hyp) in
  let allmasks = setify (fam @ map fst doms @ xmasks) in
  let sqs = map (fun m ->
      let iv = mk_var("i" ^ string_of_int m, `:num`) in
      let (_, ex) = mask_square_thm ri m in
      let ex' = CONV_RULE (GEN_ALPHA_CONV iv) ex in
      let body = snd(dest_exists(concl ex')) in
      let hb = ASSUME body in
      let lt = CONJUNCT1 hb and own = CONJUNCT2 hb in
      let sqth = CONJUNCTS (MATCH_MP NPACK_SQ (CONJ hnp lt)) in
      (m, (ex', (m, iv, lt, own, sqth)))) allmasks in
  let sq_of m = snd (assoc m sqs) in
  let dths = map (fun (m, d) -> (m, try dfun sq_of hnp hrow r (sq_of m) d
                   with Failure msg -> failwith (Printf.sprintf "domain %d: %s" m msg))) doms in
  { cid = cid; ri = ri; rw = r; chyp = hyp; hnp = hnp; hrow = hrow; sqs = sqs; dths = dths;
    seeds_tbl = Hashtbl.create 20 };;

let csq ctx m = try snd (assoc m ctx.sqs) with Failure _ -> failwith (Printf.sprintf "no square for mask %d" m);;

let cneq_sq (mj, ivj, ltj, ownj, _) (mt, ivt, ltt, ownt, _) =
  let eq = ASSUME (mk_eq(ivj, ivt)) in
  let ownj' = CONV_RULE (LAND_CONV (REWRITE_CONV[eq])) ownj in
  let sets = TRANS (SYM ownj') ownt in
  NOT_INTRO (DISCH (concl eq) (MP (NOT_ELIM (set_neq (bits mj) (bits mt))) sets));;

let cdisj2 ctx sa sb =
  let (_, _, lta, _, _) = sa and (_, _, ltb, _, _) = sb in
  MATCH_MP (SPEC `2` (SPECL SPECV AUXOWN_DISJ)) (end_itlist CONJ [ctx.hnp; lta; ltb; cneq_sq sa sb]);;

(* depth-first search over the domain disjunctions with pairwise disjointness;
   leaf chosen goal : the proof at a consistent full assignment *)
let enum_dfs ctx goal leaf =
  let da = Array.of_list ctx.dths in
  let n = Array.length da in
  let nleaves = ref 0 in
  let rec dfs j chosen =
    if j = n then (incr nleaves; leaf chosen) else
    let (mj, dth) = da.(j) in
    let rec cases th =
      if is_disj (concl th) then
        let a, b = dest_disj (concl th) in DISJ_CASES th (pick (ASSUME a)) (cases (ASSUME b))
      else if concl th = `false` then CONTR goal th
      else pick th
    and pick eqj =
      let rec check ch = match ch with
          [] -> None
        | (mt, eqt)::rest ->
            let dth = cdisj2 ctx (csq ctx mt) (csq ctx mj) in
            let dth' = REWRITE_RULE[eqt; eqj] dth in
            let v = disjoint_conv (concl dth') in
            if rhs(concl v) = `false` then Some (CONTR goal (EQ_MP v dth')) else check rest in
      match check chosen with
        Some f -> f
      | None -> dfs (j+1) ((mj, eqj) :: chosen) in
    cases dth in
  let th = dfs 0 [] in
  (th, !nleaves);;

let forced_eq ctx m value =
  let (_, iv, _, _, _) = csq ctx m in
  let goal = mk_eq(list_mk_comb(`auxown`, `2` :: sq_params iv), set_tm value) in
  fst (enum_dfs ctx goal (fun chosen ->
    let eqm = try assoc m chosen with Failure _ -> failwith (Printf.sprintf "case %d: no domain for %d" ctx.cid m) in
    if aconv (concl eqm) goal then eqm else failwith (Printf.sprintf "case %d: %d not forced" ctx.cid m)));;

(* owner set of a square in an assignment *)
let eq_set th = map dest_small_numeral (dest_list (rand(rand(concl th))));;

(* apply a template: tmpl |- !params. premises ==> concl, for the k squares of masksk
   (pulled by trf); eqs: (mask, |- auxown 2 sq = set_of_list s) known owner sets;
   returns |- concl instance (hyps: row hyps, square hyps, eqs) *)
let APPLY_TRACE = ref false;;
let APPLY_EXTRA_FACTS = ref ([] : (int * thm list) list);;
let apply_tmpl ctx eqs tmpl trf masksk =
  let cid = ctx.cid in
  let sq_of = csq ctx in
  let allmasks = map fst ctx.sqs in
  let seeds_of m =
    try Hashtbl.find ctx.seeds_tbl m with Not_found ->
    let (_, iv, lt, own, sqth) = sq_of m in
    let mf = marker_facts own in
    let sd = seeds_at (sq_params iv) sqth mf (bits m) in
    let res = (sd @ bx_corner_seeds (sq_params iv) sqth (filter (fun f -> not (is_neg (concl f))) mf),
               filter (fun f -> is_neg (concl f)) mf) in
    Hashtbl.add ctx.seeds_tbl m res; res in
  let facts_tbl = Hashtbl.create 20 in
  let facts_of m =
    try Hashtbl.find facts_tbl m with Not_found ->
    let (seeds, mneg) = seeds_of m in
    let af = (try aux_facts 2 (assoc m eqs) with Failure _ -> []) @
             (try assoc m !APPLY_EXTRA_FACTS with Failure _ -> []) in
    let res = (seeds @ filter (fun f -> not (is_neg (concl f))) af,
               mneg @ filter (fun f -> is_neg (concl f)) af) in
    Hashtbl.add facts_tbl m res; res in
  let k = List.length masksk in
  let base_params j = let (_, iv, _, _, _) = sq_of (el j masksk) in
    let [c1t; c2t; at; bt; lt] = sq_params iv in lsq_params c1t c2t at bt lt in
  let params = Array.init k (fun j -> pull_params trf (base_params j)) in
  let nv = List.length (fst (strip_forall (concl tmpl))) in
  if nv <> 5 * k then failwith "apply_tmpl: template arity" else
  let tmpl_i = SPECL (List.concat (Array.to_list params)) tmpl in
  let prems = conjuncts (lhand (concl tmpl_i)) in
  let which ps = try find (fun j -> params.(j) = ps) (0 -- (k-1)) with Failure _ -> failwith "which" in
  let sqj j = sq_of (el j masksk) in
  let to_l th = REWRITE_RULE[OSQ_LSQ] th in
  let vec (x, y) = mk_comb(`vector:(real)list->real^2`, mk_list([x; y], `:real`)) in
  let find_pos j p =
    let ptm = vec (tr_point trf p) in
    let facts = fst (facts_of (el j masksk)) in
    try find (fun th -> aconv (lhand(concl th)) ptm) facts
    with Failure _ -> derive_point facts (tr_point trf p) in
  let gens = gens_of trf in
  let prove_prem t =
    let (hd, args) = strip_comb t in
    match t with
      Comb(Const("~",_), u) ->
        let (_, uargs) = strip_comb u in
        let j = which (fst(chop_list 5 uargs)) in
        let p = (el 5 uargs, el 6 uargs) in
        let peq = pull_point_eq trf (base_params j) p in
        let ptm = vec (tr_point trf p) in
        let base_neg =
          try to_l (find (fun th -> aconv (lhand(rand(concl th))) ptm) (snd (facts_of (el j masksk))))
          with Failure _ ->
            let (_, jiv, jlt, _, _) = sqj j in
            let owner = find (fun m -> m <> el j masksk &&
                          exists (fun th -> aconv (lhand(concl th)) ptm) (fst (facts_of m))) allmasks in
            let (_, biv, blt, _, _) = sq_of owner in
            let bth = find (fun th -> aconv (lhand(concl th)) ptm) (fst (facts_of owner)) in
            let asm = ASSUME (mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, ptm),
                                     list_mk_comb(`osq`, sq_params jiv))) in
            let eqi = MATCH_MP NPACK_DISJ (end_itlist CONJ [ctx.hnp; jlt; blt; asm; bth]) in
            let nq = cneq_sq (sqj j) (sq_of owner) in
            to_l (NOT_INTRO (DISCH (concl asm) (MP (NOT_ELIM nq) eqi))) in
        EQ_MP (SYM (AP_TERM `(~)` peq)) base_neg
    | _ ->
    (match fst(dest_const hd) with
      "lclosed" ->
        let j = which (fst(chop_list 5 args)) in
        let p = (el 5 args, el 6 args) in
        let peq = lclosed_of_linside_eq (pull_point_eq trf (base_params j) p) in
        let th = MATCH_MP LINSIDE_CLOSED (to_l (find_pos j p)) in
        EQ_MP (SYM peq) th
    | "linside" ->
        let j = which (fst(chop_list 5 args)) in
        let p = (el 5 args, el 6 args) in
        EQ_MP (SYM (pull_point_eq trf (base_params j) p)) (to_l (find_pos j p))
    | "lsquare" ->
        let j = which args in
        let (_, _, _, _, [h1; _; h3; _]) = sqj j in
        MP (MP (prove(mk_imp(concl h1, mk_imp(concl h3, t)), REWRITE_TAC[lsquare] THEN REAL_ARITH_TAC)) h1) h3
    | "lcont" ->
        let j = which args in
        let (_, _, _, _, [h1; _; h3; h4]) = sqj j in
        let th = MATCH_MP OWALLS_LCONT (end_itlist CONJ [h3; MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) h1; h4]) in
        itlist (fun g th -> MATCH_MP (LCONT_PULL g) th) (rev gens) th
    | "ldisj" ->
        let j = which (fst(chop_list 5 args)) and kk = which (snd(chop_list 5 args)) in
        let (_, ivj, ltj, _, _) = sqj j and (_, ivk, ltk, _, _) = sqj kk in
        let th = MATCH_MP NPACK_LDISJ (end_itlist CONJ [ctx.hnp; ltj; ltk; cneq_sq (sqj j) (sqj kk)]) in
        itlist (fun g th -> MATCH_MP (LDISJ_PULL g) th) (rev gens) th
    | _ ->
        let (_, _, _, _, [h1; h2; _; _]) = sqj 0 in
        try MP (MP (prove(mk_imp(concl h1, mk_imp(concl h2, t)), REAL_ARITH_TAC)) h1) h2
        with Failure _ ->
          (* unit normals etc.: use the real facts of all template squares *)
          let rels = List.concat (map (fun j -> let (_, _, _, _, [h1; h2; h3; _]) = sqj j in [h1; h2; h3])
                                      (0 -- (k-1))) in
          MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), t))) (end_itlist CONJ rels)) in
  let prove_prem t = let t0 = Sys.time() in
    let r = prove_prem t in
    (if !APPLY_TRACE then Printf.printf "  prem %.1fs: %s\n%!" (Sys.time() -. t0) (string_of_term t)); r in
  let prove_prem t = (try let th = prove_prem t in
      if aconv (concl th) t then th else failwith ("got " ^ string_of_term (concl th))
    with Failure msg ->
    failwith (Printf.sprintf "case %d premise %s: %s" cid (string_of_term t) msg)) in
  MP tmpl_i (end_itlist CONJ (map prove_prem prems));;

let close_case ctx f =
  let f = itlist (fun (_, (ex, _)) th -> CHOOSE (fst(dest_exists(concl ex)), ex) th) ctx.sqs f in
  let th = GENL ROWVARS (NOT_INTRO (DISCH ctx.chyp f)) in
  (ctx.ri, EQ_MP (SYM (REWRITE_CONV[NOT_EXISTS_THM] (EXCLUDED_ROW ctx.ri))) th);;

(* gen_case_thm_x with a pluggable domain function and extra masks *)
let gen_case_thm_y dfun xmasks extra tmpl (cid, fam, doms, trf, masksk, ownedk) =
  let ctx = case_ctx dfun xmasks (cid, fam, doms @ []) in
  let fmasks = masksk @ map fst extra and fowned = ownedk @ map snd extra in
  let eqs = map2 (fun m v -> (m, forced_eq ctx m v)) fmasks fowned in
  close_case ctx (apply_tmpl ctx eqs tmpl trf masksk);;

(* enumeration cases (FourSquareVectorCover, Endpoint684 patterns): every consistent
   assignment of the domains is closed by the first recipe (tmpl, trf, masks, owned)
   whose owner sets it contains *)
let gen_enum_thm dfun xmasks recipes (cid, fam, doms) =
  let ctx = case_ctx dfun xmasks (cid, fam, doms) in
  let leaf chosen =
    let sets = map (fun (m, th) -> (m, eq_set th)) chosen in
    let ok (_, _, masks, owned) =
      forall2 (fun m ow -> try assoc m sets = ow with Failure _ -> false) masks owned in
    let cands = filter ok recipes in
    if cands = [] then failwith (Printf.sprintf "case %d: no recipe for %s" cid
        (String.concat " " (map (fun (m, s) -> Printf.sprintf "%d:{%s}" m
            (String.concat "," (map string_of_int s))) (rev sets)))) else
    tryfind (fun (tmpl, trf, masks, _) -> apply_tmpl ctx chosen tmpl trf masks) cands in
  let (f, n) = enum_dfs ctx `false` leaf in
  Printf.printf "case %d: %d leaves\n%!" cid n;
  close_case ctx f;;
