(* ========================================================================= *)
(* Port, layer 11: from 577 rows to the 117 retained cases (Jatloe: To117,   *)
(* Diagonal, CoreExclusion, DomainSpecs, SpecPacking, Budget).               *)
(* ========================================================================= *)

needs "n12/phase1/transport.ml";;
needs "n12/phase1/localq.ml";;

(* the square that owns a given mask of the row *)
let ROW_MASK_SQUARE = prove
 (`forall c1 c2 a b l r L. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r /\
       MEM (binarysum (set_of_list L)) r
       ==> exists i. i < 12 /\ owned (c1 i) (c2 i) (a i) (b i) l = set_of_list L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `MEM (binarysum (set_of_list L)) r` THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:num->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BINARYSUM_INJ THEN REWRITE_TAC[FINITE_OWNED; FINITE_SET_OF_LIST] THEN
  ASM_MESON_TAC[]);;

(* |- binarysum (set_of_list (bits m)) = m *)
let binarysum_bits m =
  let l = numlist (bits m) in
  let th = MATCH_MP BINARYSUM_LIST (EQT_ELIM((REWRITE_CONV[sorted_lt; HD; NOT_CONS_NIL] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
             (mk_comb(`sorted_lt`, l)))) in
  CONV_RULE (RAND_CONV (REWRITE_CONV[ITLIST] THENC NUM_REDUCE_CONV)) th;;

let ROW_LIST i = rand(concl ROW_LOOKUP.(i));;
let row_masks i = map dest_small_numeral (dest_list (ROW_LIST i));;

(* given the row hypothesis for row index ri and a mask m in it, the owning square *)
let mask_square_thm ri m =
  let bth = binarysum_bits m in
  let memth = EQT_ELIM((REWRITE_CONV[bth; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
                 (mk_comb(mk_comb(`MEM:num->(num)list->bool`, lhand(concl bth)), ROW_LIST ri))) in
  let hyp = mk_conj(`NPACK c1 c2 a b l`,
              mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, mk_comb(`set_of_list:(num)list->num->bool`, ROW_LIST ri))) in
  let th = MATCH_MP ROW_MASK_SQUARE (CONJ (ASSUME hyp) memth |> fun t ->
             CONJ (CONJUNCT1 (ASSUME hyp)) (CONJ (CONJUNCT2 (ASSUME hyp)) memth)) in
  (hyp, th);;

(* ------------------------------------------------------------------------- *)
(* The diagonal rows.                                                        *)
(* ------------------------------------------------------------------------- *)

let DIAG_810 = short_lemma [(q"&33 / &20",q"&33 / &20"); (q"&47 / &20",q"&47 / &20")]
  [(q"&47 / &20",q"&33 / &20"); (q"&33 / &20",q"&47 / &20")];;
let DIAG_911 = short_lemma [(q"&47 / &20",q"&33 / &20"); (q"&33 / &20",q"&47 / &20")]
  [(q"&33 / &20",q"&33 / &20"); (q"&47 / &20",q"&47 / &20")];;

let diag_bad m =
  let b k = (m lsr k) land 1 = 1 in
  (b 8 && b 10 && not (b 9) && not (b 11)) || (b 9 && b 11 && not (b 8) && not (b 10));;

let EXCLUDED_ROW ri =
  mk_neg(list_mk_exists([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
    mk_conj(`NPACK c1 c2 a b l`,
      mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, mk_comb(`set_of_list:(num)list->num->bool`, ROW_LIST ri)))));;

let ROWVARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* turn  hyp |- F  into the exclusion theorem for row ri *)
let excluded_of_false ri hyp f =
  let th = GENL ROWVARS (NOT_INTRO (DISCH hyp f)) in
  prove(EXCLUDED_ROW ri, REWRITE_TAC[NOT_EXISTS_THM] THEN ACCEPT_TAC th);;

(* the facts about square i of the row hypothesis owning the mask m *)
let square_facts ri m =
  let (hyp, ex) = mask_square_thm ri m in
  let body = snd(dest_exists(concl ex)) in
  let hb = ASSUME body in
  let lt = CONJUNCT1 hb and own = CONJUNCT2 hb in
  let sqth = MATCH_MP NPACK_SQ (CONJ (CONJUNCT1 (ASSUME hyp)) lt) in
  (hyp, ex, lt, CONJUNCTS sqth, own);;

let kill_disj outs th =
  let rec kill th =
    if is_disj (concl th) then
      let a, b = dest_disj (concl th) in DISJ_CASES th (kill (ASSUME a)) (kill (ASSUME b))
    else let n = find (fun f -> aconv (rand(concl f)) (concl th)) outs in MP (NOT_ELIM n) th in
  kill th;;

let diagonal_row_thm ri =
  let m = find diag_bad (row_masks ri) in
  let (hyp, ex, lt, [h1; _; h3; _], own) = square_facts ri m in
  let facts = marker_facts own in
  let lemma = if (m lsr 8) land 1 = 1 then DIAG_810 else DIAG_911 in
  let spec = [`(c1:num->real) i`; `(c2:num->real) i`; `(a:num->real) i`; `(b:num->real) i`; `l:real`] in
  let lth = SPECL spec lemma in
  let ants = conjuncts(lhand(concl lth)) in
  let prove_a t = try find (fun f -> aconv (concl f) t) (h1 :: h3 :: facts)
                  with Failure _ -> failwith ("diagonal: " ^ string_of_term t) in
  let disj = MP lth (end_itlist CONJ (map prove_a ants)) in
  let f = kill_disj (filter (fun f -> is_neg (concl f)) facts) disj in
  excluded_of_false ri hyp (CHOOSE (`i:num`, ex) f);;

(* ------------------------------------------------------------------------- *)
(* Domain specs: the auxiliary owner set of a square with a given marker set *)
(* lies in an explicit list, by local-query refutation of all other sets.    *)
(* ------------------------------------------------------------------------- *)

loadt "n12/phase1/core_data.ml";;

let LQ_TABLE = Hashtbl.create 2000;;
let lq_thm (m, kind, owned) =
  try Hashtbl.find LQ_TABLE (m, kind, owned) with Not_found ->
  let q = try find (fun (_,m',k',o',_,_) -> m' = m && k' = kind && o' = owned) LOCAL_QUERIES
          with Failure _ -> failwith (Printf.sprintf "no local query for %d %d" m kind) in
  let th = query_theorem q in
  Hashtbl.add LQ_TABLE (m, kind, owned) th; th;;

let AUXOWN_FILTER = prove
 (`forall k c1 c2 a b l. auxown k c1 c2 a b l =
     set_of_list (FILTER (\j. EL j (AUXPTS k) IN osq c1 c2 a b l) (rangelist 0 (LENGTH (AUXPTS k))))`,
  REWRITE_TAC[auxown; EXTENSION; IN_ELIM_THM; IN_SET_OF_LIST; MEM_FILTER; MEM_RANGELIST;
              LE_0; ADD_CLAUSES] THEN MESON_TAC[]);;

(* explicit form for kind k: auxown k c1 c2 a b l = set_of_list (FILTER (\j. ...) [0;..]) *)
let RANGE_EXPL n = Compute.CBV_CONV (fam_cs ()) (mk_comb(mk_comb(`rangelist`, `0`), mk_small_numeral n));;
let AUXOWN_EXPL = Array.init 3 (fun k ->
  let th = SPECL [mk_small_numeral k; `c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] AUXOWN_FILTER in
  REWRITE_RULE[LEN_AUX.(k); RANGE_EXPL AUX_LEN.(k)] th);;

let FINITE_AUXOWN = prove
 (`forall k c1 c2 a b l. FINITE (auxown k c1 c2 a b l)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{j:num | j < LENGTH (AUXPTS k)}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; auxown] THEN SET_TAC[]);;

let AUXOWN_LOWER = prove
 (`forall k c1 c2 a b l J. ALL (\j. j < LENGTH (AUXPTS k) /\ EL j (AUXPTS k) IN osq c1 c2 a b l) J
       ==> CARD (set_of_list J) <= CARD (auxown k c1 c2 a b l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CARD_SUBSET THEN
  REWRITE_TAC[FINITE_AUXOWN] THEN
  UNDISCH_TAC `ALL (\j. j < LENGTH (AUXPTS k) /\ EL j (AUXPTS k) IN osq c1 c2 a b l) J` THEN
  REWRITE_TAC[GSYM ALL_MEM; SUBSET; IN_SET_OF_LIST; auxown; IN_ELIM_THM] THEN MESON_TAC[]);;

let SPEC_TBL = Hashtbl.create 200;;

let CARD_SOL_DISTINCT = prove
 (`forall l:num list. PAIRWISE (\x y. ~(x = y)) l ==> CARD (set_of_list l) = LENGTH l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[set_of_list; LENGTH; CARD_CLAUSES; PAIRWISE] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `ALL (\y. ~(h = y)) (t:num list)` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[]);;

let CARD_LIST_CONV tm =
  let l = rand(rand tm) in
  let pw = EQT_ELIM((REWRITE_CONV[PAIRWISE; ALL] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
             (list_mk_comb(`PAIRWISE:(num->num->bool)->(num)list->bool`, [`\x y:num. ~(x = y)`; l]))) in
  CONV_RULE (RAND_CONV (REWRITE_CONV[LENGTH] THENC NUM_REDUCE_CONV)) (MATCH_MP CARD_SOL_DISTINCT pw);;

let set_tm s = mk_comb(`set_of_list:(num)list->num->bool`, numlist s);;
let auxown_tm k = list_mk_comb(`auxown`, [mk_small_numeral k; `c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`]);;
let card_tm t = mk_comb(`CARD:(num->bool)->num`, t);;

(* prove  hyps |- auxown k .. = set_of_list d1 \/ ... (or F if allowed = [])        *)
let spec_theorem m k lo hi allowed =
  let n = AUX_LEN.(k) in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let hlo = mk_binop `(<=):num->num->bool` (mk_small_numeral lo) (card_tm (auxown_tm k))
  and hhi = mk_binop `(<=):num->num->bool` (card_tm (auxown_tm k)) (mk_small_numeral hi) in
  let goal = if allowed = [] then `false` else
             list_mk_disj (map (fun d -> mk_eq(auxown_tm k, set_tm d)) allowed) in
  let pj j = mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`,
               mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral j),
                       mk_comb(`AUXPTS`, mk_small_numeral k))), `osq c1 c2 a b l`) in
  let leaf assigns =
    (* assigns: list of (j, bool) for j = 0..n-1 *)
    let eqs = map (fun (j,b) -> if b then EQT_INTRO (ASSUME (pj j)) else EQF_INTRO (ASSUME (mk_neg (pj j)))) assigns in
    let th = CONV_RULE (RAND_CONV (REWRITE_CONV (FILTER :: eqs))) AUXOWN_EXPL.(k) in
    let s = map dest_small_numeral (dest_list (rand(rand(concl th)))) in
    if mem s allowed then
      let ds = disjuncts goal in
      let i = index (mk_eq(auxown_tm k, set_tm s)) ds in
      let rec build ds j = match ds with
          [_] -> th
        | d::rest -> if j = 0 then DISJ1 th (list_mk_disj rest) else DISJ2 d (build rest (j-1))
        | [] -> failwith "build" in
      build ds i
    else
      let c = List.length s in
      if lo <= c && c <= hi then
        let q = lq_thm (m, k, s) in
        let f = MP (MP (MP (MP (MP (MP (SPECL SPEC5 q) (ASSUME `&1 < l`)) (ASSUME `l <= &1001 / &1000`))
                  (ASSUME `a * a + b * b = &1`)) (ASSUME `owalls c1 c2 a b l`)) (ASSUME ownp)) th in
        CONTR goal f
      else
        let cth = TRANS (AP_TERM `CARD:(num->bool)->num` th) (CARD_LIST_CONV (card_tm (set_tm s))) in
        let bad = if c < lo then ASSUME hlo else ASSUME hhi in
        let f = EQ_MP (NUM_REDUCE_CONV (concl (REWRITE_RULE[cth] bad))) (REWRITE_RULE[cth] bad) in
        CONTR goal f in
  let lenth = LEN_AUX.(k) in
  let prune_hi ins =
    (* ins: indices j with P_j assumed; |ins| > hi *)
    let alls = map (fun j -> CONJ (EQT_ELIM((REWRITE_CONV[lenth] THENC NUM_REDUCE_CONV)
                 (mk_binop `(<):num->num->bool` (mk_small_numeral j)
                    (mk_comb(`LENGTH:(real^2)list->num`, mk_comb(`AUXPTS`, mk_small_numeral k))))))
                 (ASSUME (pj j))) ins in
    let lenk = mk_comb(`LENGTH:(real^2)list->num`, mk_comb(`AUXPTS`, mk_small_numeral k)) in
    let absf = mk_abs(`j:num`, mk_conj(mk_binop `(<):num->num->bool` `j:num` lenk,
                 mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`,
                   mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, `j:num`), mk_comb(`AUXPTS`, mk_small_numeral k))),
                   `osq c1 c2 a b l`))) in
    let alltm = list_mk_comb(`ALL:(num->bool)->(num)list->bool`, [absf; numlist ins]) in
    let eqth = (REWRITE_CONV[ALL] THENC DEPTH_CONV BETA_CONV THENC REWRITE_CONV[]) alltm in
    let allth = EQ_MP (SYM eqth) (end_itlist CONJ alls) in
    let le = MATCH_MP AUXOWN_LOWER allth in
    let le' = CONV_RULE (LAND_CONV CARD_LIST_CONV) le in
    let f = EQ_MP (NUM_REDUCE_CONV (mk_binop `(<=):num->num->bool` (lhand(concl le')) (mk_small_numeral hi)))
              (MATCH_MP LE_TRANS (CONJ le' (ASSUME hhi))) in
    CONTR goal f in
  let rec dfs j assigns =
    let ins = map fst (filter snd (rev assigns)) in
    if List.length ins > hi then prune_hi ins else
    if j = n then leaf (rev assigns) else
    let p = pj j in
    let t1 = dfs (j+1) ((j,true)::assigns) and t2 = dfs (j+1) ((j,false)::assigns) in
    DISJ_CASES (SPEC p EXCLUDED_MIDDLE) t1 t2 in
  let th = dfs 0 [] in
  GENL SPEC5 (itlist DISCH (LQ_HYPS @ [ownp; hlo; hhi]) th);;

(* ------------------------------------------------------------------------- *)
(* Individual budgets (Jatloe: Budget.individual_budget).                    *)
(* ------------------------------------------------------------------------- *)

let BUDGET_INDIV = prove
 (`forall (own:num->num->bool) (E:num->bool) i.
     (forall j. j < 12 ==> own j SUBSET {x | x < 10}) /\
     (forall j j'. j < 12 /\ j' < 12 /\ ~(j = j') ==> DISJOINT (own j) (own j')) /\
     (forall j. j < 12 /\ ~(j IN E) ==> ~(own j = {})) /\ i < 12
     ==> CARD (own i) + CARD {j | j < 12 /\ ~(j IN E) /\ ~(j = i)} <= 10`,
  let DISJ2_TAC v w =
    FIRST_X_ASSUM(MP_TAC o SPECL [v; w] o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `exists f. forall j. j < 12 /\ ~(j IN E) ==> f j IN (own:num->num->bool) j` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `j < 12 /\ ~(j IN E)` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  ABBREV_TAC `N = {j | j < 12 /\ ~(j IN E) /\ ~(j = i)}` THEN
  SUBGOAL_THEN `FINITE (N:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < 12}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE ((own:num->num->bool) i)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < 10}` THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (IMAGE (f:num->num) N) = CARD (N:num->bool)` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "N" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    DISJ2_TAC `x:num` `y:num` THEN
    DISCH_THEN(MP_TAC o SPEC `(f:num->num) y`) THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN ASM_SIMP_TAC[];
                    ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD ((own:num->num->bool) i) + CARD (IMAGE (f:num->num) N) =
                CARD (own i UNION IMAGE f N)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN EXPAND_TAC "N" THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    DISJ2_TAC `i:num` `x':num` THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x = (f:num->num) x'` THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM (SPEC `10` CARD_NUMSEG_LT)] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    EXPAND_TAC "N" THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':num` o check (fun th -> is_forall(concl th) &&
       length(fst(strip_forall(concl th))) = 1 && is_imp(snd(dest_forall(concl th))) &&
       is_binop `(IN):num->(num->bool)->bool` (rand(snd(dest_forall(concl th)))))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x':num` o check (fun th -> is_forall(concl th) &&
       length(fst(strip_forall(concl th))) = 1 && is_imp(snd(dest_forall(concl th))) &&
       is_comb(rand(snd(dest_forall(concl th)))) &&
       fst(strip_comb(rand(snd(dest_forall(concl th))))) = `(SUBSET):(num->bool)->(num->bool)->bool`)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let AUXOWN_SUBSET10 = prove
 (`forall k c1 c2 a b l. k < 2 ==> auxown k c1 c2 a b l SUBSET {x | x < 10}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH (AUXPTS k) = 10` ASSUME_TAC THENL
   [UNDISCH_TAC `k < 2` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[LEN_AUX.(0); LEN_AUX.(1)];
    ASM_REWRITE_TAC[auxown; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let AUXOWN_DISJ = prove
 (`forall c1 c2 a b l k i j. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> DISJOINT (auxown k (c1 i) (c2 i) (a i) (b i) l) (auxown k (c1 j) (c2 j) (a j) (b j) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; auxown; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC NPACK_DISJ THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`;
                        `l:real`; `EL x (AUXPTS k)`] THEN ASM_REWRITE_TAC[]);;

(* a square with empty kind-k owner set is exempt *)
let EMPTY_EXEMPT k =
  let pairs = if k = 0 then `FPAIRS` else `GPAIRS` in
  let avoid = if k = 0 then AVOIDF_FORCES_PAIR else AVOIDG_FORCES_PAIR in
  let pex = if k = 0 then PAIRIN_F_EXPLICIT else PAIRIN_G_EXPLICIT in
  prove(mk_forall(`c1:real`, mk_forall(`c2:real`, mk_forall(`a:real`, mk_forall(`b:real`, mk_forall(`l:real`,
    mk_imp(list_mk_conj [`&1 < l`; `a * a + b * b = &1`; `owalls c1 c2 a b l`;
                         mk_eq(auxown_tm k, `{}:num->bool`)],
           list_mk_comb(`pairin`, [pairs; `owned c1 c2 a b l`]))))))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pex] THEN MATCH_MP_TAC avoid THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC (mk_eq(auxown_tm k, `{}:num->bool`)) THEN
    REWRITE_TAC[AUXOWN_EXPL.(k); FILTER] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[AUXPTS_EXPL.(k)] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[set_of_list; NOT_INSERT_EMPTY]));;
let EMPTY_EXEMPT_F = EMPTY_EXEMPT 0 and EMPTY_EXEMPT_G = EMPTY_EXEMPT 1;;

(* counting squares by a property of their owned set, through the row *)
let FFP_BITSET = prove
 (`forall c1 c2 a b l r. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r
     ==> FFP c1 c2 a b l = IMAGE bitset (set_of_list r)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:num->bool. x) (FFP c1 c2 a b l)` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[IMAGE_ID]] THEN
  MATCH_MP_TAC IMAGE_EQ_ON THEN REWRITE_TAC[FFP; IN_IMAGE; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC BITSET_BINARYSUM THEN REWRITE_TAC[FINITE_OWNED]);;

let COUNT_SQUARES = prove
 (`forall c1 c2 a b l (Q:(num->bool)->bool). NPACK c1 c2 a b l
     ==> CARD {j | j < 12 /\ Q (owned (c1 j) (c2 j) (a j) (b j) l)} =
         CARD {G | G IN FFP c1 c2 a b l /\ Q G}`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  SUBGOAL_THEN `{G | G IN FFP c1 c2 a b l /\ (Q:(num->bool)->bool) G} =
                IMAGE (\i. owned (c1 i) (c2 i) (a i) (b i) l)
                      {j | j < 12 /\ Q (owned (c1 j) (c2 j) (a j) (b j) l)}` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `G:num->bool` THEN
    REWRITE_TAC[FFP; IN_ELIM_THM; IN_IMAGE] THEN
    EQ_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[];
      CONJ_TAC THENL [EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[OWNED_INJ];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < 12}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]]]);;

let BITSET_INJ = prove
 (`forall m n. bitset m = bitset n ==> m = n`,
  MESON_TAC[BINARYSUM_BITSET]);;

let COUNT_ROW = prove
 (`forall c1 c2 a b l r (Q:(num->bool)->bool). NPACK c1 c2 a b l /\
     IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r
     ==> CARD {j | j < 12 /\ Q (owned (c1 j) (c2 j) (a j) (b j) l)} =
         CARD (set_of_list (FILTER (\m. Q (bitset m)) r))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COUNT_SQUARES] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FFP_BITSET (CONJ (ASSUME `NPACK c1 c2 a b l`) th)]) THEN
  SUBGOAL_THEN `{G | G IN IMAGE bitset (set_of_list r) /\ (Q:(num->bool)->bool) G} =
                IMAGE bitset (set_of_list (FILTER (\m. Q (bitset m)) r))` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_SET_OF_LIST; MEM_FILTER] THEN
    X_GEN_TAC `G:num->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `m:num` THEN UNDISCH_TAC `(Q:(num->bool)->bool) G` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_SET_OF_LIST] THEN MESON_TAC[BITSET_INJ]]);;

let AUXOWN2 = prove
 (`forall c1 c2 a b l. auxown 2 c1 c2 a b l =
                 auxown 0 c1 c2 a b l UNION IMAGE (\j. j + 10) (auxown 1 c1 c2 a b l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[auxown; LEN_AUX.(0); LEN_AUX.(1); LEN_AUX.(2)] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN
  SUBGOAL_THEN `AUXPTS 2 = APPEND (AUXPTS 0) (AUXPTS 1)` SUBST1_TAC THENL
   [REWRITE_TAC[AUXPTS] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[EL_APPEND; LEN_AUX.(0)] THEN ASM_CASES_TAC `j < 10` THEN ASM_REWRITE_TAC[] THENL
   [EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_ARITH_TAC; MATCH_MP_TAC(TAUT `false ==> p`) THEN ASM_ARITH_TAC]];
    EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `j - 10` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `(x + 10) - 10 = x`] THEN ASM_ARITH_TAC]]);;

let DISJOINT_SOL = prove
 (`forall l l':num list. DISJOINT (set_of_list l) (set_of_list l') <=> ALL (\x. ~MEM x l') l`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SET_OF_LIST; GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let disjoint_conv tm =
  (REWRITE_CONV[DISJOINT_SOL; ALL; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[]) tm;;

(* |- bitset m = set_of_list (bits m) *)
let bitset_bits m =
  let b = binarysum_bits m in
  let th = MATCH_MP BITSET_BINARYSUM (ISPEC (rand(rand(lhand(concl b)))) FINITE_SET_OF_LIST) in
  TRANS (SYM (AP_TERM `bitset` b)) th;;

let PKS = new_definition `PKS k = if k = 0 then FPAIRS else GPAIRS`;;

let EMPTY_EXEMPT_K = prove
 (`forall k c1 c2 a b l. k < 2 /\ &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
                   auxown k c1 c2 a b l = {} ==> pairin (PKS k) (owned c1 c2 a b l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[PKS] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM IMP_CONJ] THEN STRIP_TAC THENL
   [MATCH_MP_TAC EMPTY_EXEMPT_F; MATCH_MP_TAC EMPTY_EXEMPT_G] THEN ASM_REWRITE_TAC[]);;

let SQUARE_NONEMPTY = prove
 (`forall c1 c2 a b l k i. NPACK c1 c2 a b l /\ k < 2 /\ i < 12 /\
       ~pairin (PKS k) (owned (c1 i) (c2 i) (a i) (b i) l)
       ==> 1 <= CARD (auxown k (c1 i) (c2 i) (a i) (b i) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  SIMP_TAC[CARD_EQ_0; FINITE_AUXOWN] THEN DISCH_TAC THEN
  UNDISCH_TAC `~pairin (PKS k) (owned (c1 (i:num)) (c2 i) (a i) (b i) l)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC EMPTY_EXEMPT_K THEN ASM_MESON_TAC[NPACK_SQ]);;

let SQUARE_BUDGET = prove
 (`forall c1 c2 a b l r k i L. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r /\
       k < 2 /\ i < 12 /\ owned (c1 i) (c2 i) (a i) (b i) l = set_of_list L
       ==> CARD (auxown k (c1 i) (c2 i) (a i) (b i) l) +
           CARD (set_of_list (FILTER (\m. ~pairin (PKS k) (bitset m) /\ ~(bitset m = set_of_list L)) r))
           <= 10`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\j. auxown k ((c1:num->real) j) (c2 j) (a j) (b j) l`;
                 `{j | pairin (PKS k) (owned ((c1:num->real) j) (c2 j) (a j) (b j) l)}`; `i:num`]
                BUDGET_INDIV) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[AUXOWN_SUBSET10; AUXOWN_DISJ] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `k:num`; `j:num`] SQUARE_NONEMPTY) THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `y = z ==> x + y <= 10 ==> x + z <= 10`) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `r:num list`;
                `\G. ~pairin (PKS k) G /\ ~(G = set_of_list L)`] COUNT_ROW) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN
  ASM_CASES_TAC `j < 12` THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     is_comb(lhs(concl th)) && fst(strip_comb(lhs(concl th))) = `owned`)) THEN
  EQ_TAC THENL [DISCH_THEN SUBST1_TAC THEN REFL_TAC;
     DISCH_TAC THEN MATCH_MP_TAC OWNED_INJ THEN
     MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
     ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* One core proof.                                                           *)
(* ------------------------------------------------------------------------- *)

let pk_is k L =
  (REWRITE_CONV[PKS] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC
   REWRITE_CONV[PAIRIN_SET; HASPAIR_ALT; FPAIRS; GPAIRS; EX; MEM] THENC NUM_REDUCE_CONV THENC
   REWRITE_CONV[]) (list_mk_comb(`pairin`, [mk_comb(`PKS`, mk_small_numeral k); set_tm L]));;

let sol_eq_conv tm =
  let l1 = map dest_small_numeral (dest_list(rand(lhs tm))) and l2 = map dest_small_numeral (dest_list(rand(rhs tm))) in
  if l1 = l2 then EQT_INTRO (REFL (lhs tm)) else EQF_INTRO (set_neq l1 l2);;

let filter_conv tm =
  (* tm: FILTER (\m. ~pairin (PKS k) (bitset m) /\ ~(bitset m = set_of_list L)) r, r explicit *)
  let ms = map dest_small_numeral (dest_list (rand tm)) in
  (REWRITE_CONV (FILTER :: map bitset_bits ms) THENC DEPTH_CONV BETA_CONV THENC
   REWRITE_CONV(map bitset_bits ms) THENC
   ONCE_DEPTH_CONV (fun t -> if is_eq t && is_comb(lhs t) && rator(lhs t) = `set_of_list:(num)list->num->bool` &&
                                 is_comb(rhs t) && rator(rhs t) = `set_of_list:(num)list->num->bool`
                              then sol_eq_conv t else failwith "") THENC
   REWRITE_CONV[PKS] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[] THENC
   REWRITE_CONV[PAIRIN_SET; HASPAIR_ALT; FPAIRS; GPAIRS; EX; MEM] THENC NUM_REDUCE_CONV THENC
   REWRITE_CONV[]) tm;;

let SPECV = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* card bounds and the domain disjunction for one single spec on square iv *)
(* extension tables for Phase 2 (derived specs, e.g. under symmetry) *)
let EXTRA_SINGLE = ref ([] : (int * int * int * int * int * int list list) list);;
let EXTRA_COMBINED = ref ([] : (int * int * int * int * int list list) list);;

let single_domain hnp hrow r (m, iv, lt, own, sqth) n =
  let (_,m',k,lo,hi,_) = find (fun (i,_,_,_,_,_) -> i = n) (SINGLE_SPECS @ !EXTRA_SINGLE) in
  if m' <> m then failwith "single_domain: mask mismatch" else
  let L = bits m in
  let sp = [mk_comb(`c1:num->real`, iv); mk_comb(`c2:num->real`, iv); mk_comb(`a:num->real`, iv);
            mk_comb(`b:num->real`, iv); `l:real`] in
  let atm = list_mk_comb(`auxown`, mk_small_numeral k :: sp) in
  let kth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let hlo = if lo = 0 then SPEC (mk_comb(`CARD:(num->bool)->num`, atm)) LE_0 else
    let pk = pk_is k L in
    let np = EQF_ELIM (TRANS (AP_TERM (rator(lhs(concl pk))) own) pk) in
    MATCH_MP SQUARE_NONEMPTY (end_itlist CONJ [hnp; kth; lt; np]) in
  let bud = MATCH_MP SQUARE_BUDGET (end_itlist CONJ [hnp; hrow; kth; lt; own]) in
  let bud' = CONV_RULE (LAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV filter_conv) THENC CARD_LIST_CONV))) bud in
  let hhi = MP (ARITH_RULE (mk_imp(concl bud', mk_binop `(<=):num->num->bool`
                 (mk_comb(`CARD:(num->bool)->num`, atm)) (mk_small_numeral hi)))) bud' in
  let sth = try Hashtbl.find SPEC_TBL n with Not_found ->
    let (_,m0,k0,lo0,hi0,al0) = find (fun (i,_,_,_,_,_) -> i = n) (SINGLE_SPECS @ !EXTRA_SINGLE) in
    let th = spec_theorem m0 k0 lo0 hi0 al0 in Hashtbl.replace SPEC_TBL n th; th in
  List.fold_left (fun th h -> MP th h) (SPECL sp sth) (sqth @ [own; hlo; hhi]);;

let set_merge x y = List.sort compare (x @ map (fun j -> j + 10) y);;

let AUXOWN2_LIST = prove
 (`forall c1 c2 a b l x y. auxown 0 c1 c2 a b l = set_of_list x /\ auxown 1 c1 c2 a b l = set_of_list y
     ==> auxown 2 c1 c2 a b l = set_of_list (APPEND x (MAP (\j. j + 10) y))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[AUXOWN2; SET_OF_LIST_APPEND; SET_OF_LIST_MAP]);;

(* combined domain on square iv from the two single domains *)
let combined_domain hnp hrow r sq n =
  let (m, iv, lt, own, sqth) = sq in
  let (_,m',f,g,allowed) = find (fun (i,_,_,_,_) -> i = n) (COMBINED_SPECS @ !EXTRA_COMBINED) in
  let d0 = single_domain hnp hrow r sq f and d1 = single_domain hnp hrow r sq g in
  let sp = [mk_comb(`c1:num->real`, iv); mk_comb(`c2:num->real`, iv); mk_comb(`a:num->real`, iv);
            mk_comb(`b:num->real`, iv); `l:real`] in
  let a2 = list_mk_comb(`auxown`, `2` :: sp) in
  let goal = if allowed = [] then `false` else list_mk_disj (map (fun d -> mk_eq(a2, set_tm d)) allowed) in
  let sqhyps = sqth in
  let qcase x y thx thy =
    let th = MATCH_MP AUXOWN2_LIST (CONJ thx thy) in
    let th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV[APPEND; MAP] THENC DEPTH_CONV BETA_CONV THENC
                                               NUM_REDUCE_CONV))) th in
    let s = map dest_small_numeral (dest_list (rand(rand(concl th)))) in
    if mem s allowed then
      let ds = disjuncts goal in
      let i = index (mk_eq(a2, set_tm s)) ds in
      let rec build ds j = match ds with
          [_] -> th
        | d::rest -> if j = 0 then DISJ1 th (list_mk_disj rest) else DISJ2 d (build rest (j-1))
        | [] -> failwith "build" in
      build ds i
    else
      let q = lq_thm (m, 2, s) in
      let f = List.fold_left (fun th h -> MP th h) (SPECL sp q) (sqhyps @ [own; th]) in
      CONTR goal f in
  let cases dth k =
    let rec go th = if is_disj (concl th) then
        let a, b = dest_disj (concl th) in DISJ_CASES th (k (ASSUME a)) (go (ASSUME b))
      else if concl th = `false` then CONTR goal th else k th in
    go dth in
  cases d0 (fun thx -> cases d1 (fun thy ->
    let x = map dest_small_numeral (dest_list (rand(rand(concl thx))))
    and y = map dest_small_numeral (dest_list (rand(rand(concl thy)))) in
    qcase x y thx thy));;

let core_theorem (cid, fam, mode, specs) =
  let fam = List.sort compare fam in
  let ri = try index fam (map row_masks (0--576)) with Failure _ -> failwith "core: row not found" in
  let r = ROW_LIST ri in
  let hyp = mk_conj(`NPACK c1 c2 a b l`,
              mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, mk_comb(`set_of_list:(num)list->num->bool`, r))) in
  let hnp = CONJUNCT1 (ASSUME hyp) and hrow = CONJUNCT2 (ASSUME hyp) in
  let nsp = List.length specs in
  let masks = map (fun (typ,_,n) ->
      if typ = 0 then let (_,m,_,_,_,_) = find (fun (i,_,_,_,_,_) -> i = n) SINGLE_SPECS in m
      else let (_,m,_,_,_) = find (fun (i,_,_,_,_) -> i = n) COMBINED_SPECS in m) specs in
  let ivars = List.init nsp (fun j -> mk_var("i" ^ string_of_int j, `:num`)) in
  let sqs = map2 (fun m iv ->
      let (_, ex) = mask_square_thm ri m in
      let ex' = CONV_RULE (GEN_ALPHA_CONV iv) ex in
      let body = snd(dest_exists(concl ex')) in
      let hb = ASSUME body in
      let lt = CONJUNCT1 hb and own = CONJUNCT2 hb in
      let sqth = CONJUNCTS (MATCH_MP NPACK_SQ (CONJ hnp lt)) in
      (ex', (m, iv, lt, own, sqth))) masks ivars in
  let doms = map2 (fun (typ,_,n) (_, sq) ->
      if typ = 0 then single_domain hnp hrow r sq n else combined_domain hnp hrow r sq n) specs sqs in
  let kd = mode in
  (* disjointness of the owner sets of two spec squares *)
  let disj (_, (mj, ivj, ltj, ownj, _)) (_, (mt, ivt, ltt, ownt, _)) =
    let eq = ASSUME (mk_eq(ivj, ivt)) in
    let ownj' = CONV_RULE (LAND_CONV (REWRITE_CONV[eq])) ownj in
    let sets = TRANS (SYM ownj') ownt in
    let neq = NOT_INTRO (DISCH (concl eq) (MP (NOT_ELIM (set_neq (bits mj) (bits mt))) sets)) in
    MATCH_MP (SPEC (mk_small_numeral kd) (SPECL SPECV AUXOWN_DISJ)) (end_itlist CONJ [hnp; ltj; ltt; neq]) in
  let sqa = Array.of_list sqs and da = Array.of_list doms in
  let rec dfs j chosen =
    if j = nsp then failwith (Printf.sprintf "core %d: feasible assignment" cid) else
    let rec cases th =
      if is_disj (concl th) then
        let a, b = dest_disj (concl th) in DISJ_CASES th (pick (ASSUME a)) (cases (ASSUME b))
      else if concl th = `false` then th
      else pick th
    and pick eqj =
      (* eqj: |- A_j = set_of_list d *)
      let rec check ch = match ch with
          [] -> None
        | (t, eqt)::rest ->
            let dth = disj sqa.(t) sqa.(j) in
            let dth' = REWRITE_RULE[eqt; eqj] dth in
            let v = disjoint_conv (concl dth') in
            if rhs(concl v) = `false` then Some (EQ_MP v dth') else check rest in
      match check chosen with
        Some f -> f
      | None -> dfs (j+1) ((j, eqj) :: chosen) in
    cases da.(j) in
  let f = dfs 0 [] in
  let f = itlist (fun (ex, _) th -> CHOOSE (fst(dest_exists(concl ex)), ex) th) sqs f in
  excluded_of_false ri hyp f;;

(* ------------------------------------------------------------------------- *)
(* Assembly: every packing reduces to one of the 117 retained rows.          *)
(* ------------------------------------------------------------------------- *)

loadt "n12/phase1/retained_data.ml";;

let RETAINED = new_definition (mk_eq(`RETAINED:((num)list)list`,
  mk_list(map ROW_LIST RETAINED_IDX, `:(num)list`)));;

let reduction_117 diag_rows core_tbl =
  let excl = Array.make 577 TRUTH in
  List.iter (fun (ri, th) -> excl.(ri) <- th) diag_rows;
  Hashtbl.iter (fun _ th ->
    let r = rand(rand(rand(snd(strip_exists(rand(concl th)))))) in
    let ri = index r (map ROW_LIST (0--576)) in excl.(ri) <- th) core_tbl;
  let missing = filter (fun i -> excl.(i) = TRUTH && not (mem i RETAINED_IDX)) (0--576) in
  if missing <> [] then failwith (Printf.sprintf "reduction_117: %d rows not excluded" (length missing)) else
  let goal = `forall c1 c2 a b l. NPACK c1 c2 a b l
     ==> exists c1' c2' a' b' r. NPACK c1' c2' a' b' l /\ MEM r RETAINED /\
                           IMAGE binarysum (FFP c1' c2' a' b' l) = set_of_list r` in
  let memret = Array.init 577 (fun i -> if mem i RETAINED_IDX then
      Some (EQT_ELIM((REWRITE_CONV[RETAINED; MEM] THENC REWRITE_CONV[]) (mk_comb(mk_comb(`MEM:(num)list->((num)list)list->bool`, ROW_LIST i), `RETAINED`))))
      else None) in
  prove(goal,
    REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP PACKING_ROW) THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:num->real` (X_CHOOSE_THEN `d2:num->real` (X_CHOOSE_THEN `e1:num->real`
      (X_CHOOSE_THEN `e2:num->real` (X_CHOOSE_THEN `r:num list` STRIP_ASSUME_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `r:num list`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `MEM (r:num list) ROWS` THEN REWRITE_TAC[ROWS; MEM] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    W(fun (asl,w) ->
      let ri = index (lhand w) (map ROW_LIST (0--576)) in
      match memret.(ri) with
        Some th -> ACCEPT_TAC th
      | None -> MP_TAC excl.(ri) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
                DISCH_THEN(MP_TAC o SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]) THEN
                ASM_REWRITE_TAC[]));;
