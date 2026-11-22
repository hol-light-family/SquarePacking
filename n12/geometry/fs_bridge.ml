(* ========================================================================= *)
(* Phase 2: the four-square cases, packing side (Jatloe: Compact/Bridge/     *)
(* FourSquareCase, OwnerBudget, S12/CertifiedDomain).  Forced auxiliary     *)
(* owners and the template's point premises, derived from a packing.        *)
(* ========================================================================= *)

needs "n12/phase1/step6.ml";;
needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/fst_stmt.ml";;

let CARD1_EXISTS = prove
 (`forall S:num->bool. FINITE S /\ CARD S = 1 ==> exists x. S = {x}`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(S:num->bool) HAS_SIZE 1` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC[]]);;

let CARD1_ENUM = prove
 (`forall S. S SUBSET {x:num | x < 10} /\ CARD S = 1
       ==> S = set_of_list [0] \/ S = set_of_list [1] \/ S = set_of_list [2] \/
           S = set_of_list [3] \/ S = set_of_list [4] \/ S = set_of_list [5] \/
           S = set_of_list [6] \/ S = set_of_list [7] \/ S = set_of_list [8] \/
           S = set_of_list [9]`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (S:num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < 10}` THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `S:num->bool` CARD1_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `x < 10` MP_TAC THENL
   [UNDISCH_TAC `{x:num} SUBSET {x | x < 10}` THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LT10_CASES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[set_of_list]);;

let CARD1_MEMBER = prove
 (`forall S j:num. FINITE S /\ CARD S = 1 /\ j IN S ==> S = set_of_list [j]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `S:num->bool` CARD1_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `j IN {x:num}` THEN REWRITE_TAC[IN_SING; set_of_list] THEN MESON_TAC[]);;

loadt "n12/geometry/fs_data.ml";;

(* seed theorems for a square given by arbitrary parameter terms sp *)
let seeds_at sp sqhyps facts clist =
  let base = filter (fun f -> not (is_neg (concl f))) facts in
  let try_use th =
    let th = SPECL sp th in
    let hs = conjuncts(lhand(concl th)) in
    let prove_h h =
      try find (fun f -> aconv (concl f) h) (facts @ sqhyps)
      with Failure _ ->
        let rels = filter (fun f -> is_real_rel (concl f)) sqhyps in
        if is_real_rel h then
          MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), h))) (end_itlist CONJ rels)
        else failwith "no" in
    try CONJUNCTS (MP th (end_itlist CONJ (map prove_h hs)))
    with Failure _ -> [] in
  let sing = match clist with [k] when k < 8 -> try_use SING_EXPL.(k) | _ -> [] in
  base @ sing @ List.concat (map try_use WALL_EXPL);;

let sq_params iv = [mk_comb(`c1:num->real`, iv); mk_comb(`c2:num->real`, iv);
                    mk_comb(`a:num->real`, iv); mk_comb(`b:num->real`, iv); `l:real`];;

(* exact card 1 for a non-exempt square when the row has two exempt masks *)
let card_one hnp hrow r (m, iv, lt, own, sqth) k =
  let sp = sq_params iv in
  let atm = list_mk_comb(`auxown`, mk_small_numeral k :: sp) in
  let kth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let pk = pk_is k (bits m) in
  let np = EQF_ELIM (TRANS (AP_TERM (rator(lhs(concl pk))) own) pk) in
  let lo = MATCH_MP SQUARE_NONEMPTY (end_itlist CONJ [hnp; kth; lt; np]) in
  let bud = MATCH_MP SQUARE_BUDGET (end_itlist CONJ [hnp; hrow; kth; lt; own]) in
  let bud' = CONV_RULE (LAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV filter_conv) THENC CARD_LIST_CONV))) bud in
  let eq = MP (ARITH_RULE (mk_imp(mk_conj(concl lo, concl bud'),
             mk_eq(mk_comb(`CARD:(num->bool)->num`, atm), `1`)))) (CONJ lo bud') in
  (atm, kth, eq);;

let AUXMEM = prove
 (`forall k j c1 c2 a b l. j < LENGTH (AUXPTS k) /\ EL j (AUXPTS k) IN osq c1 c2 a b l
                     ==> j IN auxown k c1 c2 a b l`,
  SIMP_TAC[auxown; IN_ELIM_THM]);;

let half_domain hnp hrow r sq h =
  let (m, iv, lt, own, sqth) = sq in
  match h with
    Hspec(n, _) -> single_domain hnp hrow r sq n
  | Hsing k ->
      let (atm, kth, eq) = card_one hnp hrow r sq k in
      let sub = MATCH_MP AUXOWN_SUBSET10 kth |> SPECL (sq_params iv) in
      MATCH_MP CARD1_ENUM (CONJ sub eq)
  | Hhull(k, idx, tri) ->
      let (atm, kth, eq) = try card_one hnp hrow r sq k with Failure msg -> failwith ("card_one: " ^ msg) in
      let sp = sq_params iv in
      let facts = marker_facts own in
      let seeds = seeds_at sp sqth facts (bits m) in
      let tp = try tri_point seeds tri with Failure msg -> failwith ("tri_point: " ^ msg) in
      (* idx IN auxown k ... *)
      let elth = (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV)
                   (mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral idx),
                            mk_comb(`AUXPTS`, mk_small_numeral k))) in
      let tp' = EQ_MP (SYM (AP_THM (AP_TERM `(IN):real^2->(real^2->bool)->bool` elth)
                         (rand(concl tp)))) tp in
      let lt = EQT_ELIM((REWRITE_CONV[LEN_AUX.(k)] THENC NUM_REDUCE_CONV)
                 (mk_binop `(<):num->num->bool` (mk_small_numeral idx)
                    (mk_comb(`LENGTH:(real^2)list->num`, mk_comb(`AUXPTS`, mk_small_numeral k))))) in
      let memth = MATCH_MP AUXMEM (CONJ lt tp') in
      MATCH_MP CARD1_MEMBER (end_itlist CONJ [SPECL (mk_small_numeral k :: sp) FINITE_AUXOWN; eq; memth]);;

(* the combined (kind 2) domain of a square *)
let domain_thm hnp hrow r sq d =
  let (m, iv, lt, own, sqth) = sq in
  match d with
    Dcomb n -> combined_domain hnp hrow r sq n
  | Dprod(h0, h1) ->
      let d0 = half_domain hnp hrow r sq h0 and d1 = half_domain hnp hrow r sq h1 in
      let lists th = map (fun t -> map dest_small_numeral (dest_list (rand(rand t)))) (disjuncts (concl th)) in
      let a2 = list_mk_comb(`auxown`, `2` :: sq_params iv) in
      let merged = setify (List.concat (map (fun x -> map (fun y -> set_merge x y) (lists d1)) (lists d0))) in
      let goal = list_mk_disj (map (fun d -> mk_eq(a2, set_tm d)) merged) in
      let fin thx thy =
        let th = MATCH_MP AUXOWN2_LIST (CONJ thx thy) in
        let th = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV[APPEND; MAP] THENC DEPTH_CONV BETA_CONV THENC
                                                   NUM_REDUCE_CONV))) th in
        let ds = disjuncts goal in
        let i = index (concl th) ds in
        let rec bd ds j = match ds with
            [_] -> th
          | x::rest -> if j = 0 then DISJ1 th (list_mk_disj rest) else DISJ2 x (bd rest (j-1))
          | [] -> failwith "bd" in
        bd ds i in
      let rec over th k =
        if is_disj (concl th) then
          let a, b = dest_disj (concl th) in DISJ_CASES th (k (ASSUME a)) (over (ASSUME b) k)
        else k th in
      over d0 (fun thx -> over d1 (fun thy -> fin thx thy));;

(* ------------------------------------------------------------------------- *)
(* From the centred representation to the template's.                        *)
(* ------------------------------------------------------------------------- *)

let lsq_params c1 c2 a b l =
  (* the same shape as the parse of  a * c1 + b * c2 - l / &2  (right associative) *)
  let th = SPECL [`x:real`; `y:real`; c1; c2; a; b; l] OSQ_LSQ in
  let args = snd(strip_comb(rhs(concl th))) in
  fst(chop_list 5 args);;

let OWALLS_LCONT = prove
 (`forall c1 c2 a b l. a * a + b * b = &1 /\ &0 < l /\ owalls c1 c2 a b l
     ==> lcont a b (a * c1 + b * c2 - l / &2) (--b * c1 + a * c2 - l / &2) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[owalls; lcont; GSYM OSQ_LSQ] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN STRIP_TAC THEN
  ABBREV_TAC `U = (x - c1) * a + (y - c2) * b` THEN
  ABBREV_TAC `V = (y - c2) * a - (x - c1) * b` THEN
  SUBGOAL_THEN `x = c1 + a * U - b * V /\ y = c2 + b * U + a * V` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "V"] THEN CONJ_TAC THEN
    UNDISCH_TAC `a * a + b * b = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 <= a` THEN ASM_CASES_TAC `&0 <= b` THEN
  FIRST_ASSUM(fun tha -> FIRST_ASSUM(fun thb ->
    let ea = if concl tha = `&0 <= a` then `abs a = a` else if concl tha = `~(&0 <= a)` then `abs a = --a` else failwith ""
    and eb = if concl thb = `&0 <= b` then `abs b = b` else if concl thb = `~(&0 <= b)` then `abs b = --b` else failwith "" in
    SUBGOAL_THEN (mk_conj(ea, eb)) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC])) THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

let NPACK_LDISJ = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (a i) (b i) (a i * c1 i + b i * c2 i - l / &2) (--b i * c1 i + a i * c2 i - l / &2) l
               (a j) (b j) (a j * c1 j + b j * c2 j - l / &2) (--b j * c1 j + a j * c2 j - l / &2) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ldisj; GSYM OSQ_LSQ] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN MATCH_MP_TAC NPACK_DISJ THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                        `vector[x; y]:real^2`] THEN ASM_REWRITE_TAC[]);;

let LDISJ_PULLX = prove
 (`forall c s u v a c' s' u' v' a'. ldisj c s u v a c' s' u' v' a'
     ==> ldisj (--c) s (u - &4 * c) (--v - a - &4 * s) a (--c') s' (u' - &4 * c') (--v' - a' - &4 * s') a'`,
  REWRITE_TAC[ldisj; LINSIDE_PULLX] THEN MESON_TAC[]);;

let LDISJ_PULLSW = prove
 (`forall c s u v a c' s' u' v' a'. ldisj c s u v a c' s' u' v' a'
     ==> ldisj s c u (--v - a) a s' c' u' (--v' - a') a'`,
  REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN MESON_TAC[]);;

loadt "n12/geometry/fst_stmt.ml";;

(* ------------------------------------------------------------------------- *)
(* One four-square case:  FST_STMT ==> no packing has this row.              *)
(* ------------------------------------------------------------------------- *)

(* template points (FourSquareCase.insidePoints / outsidePoints) *)
let FS_INSIDE = [|[("&2","&113 / &50"); ("&113 / &50","&2"); ("&47 / &20","&47 / &20")];
                  [("&33 / &20","&47 / &20"); ("&8 / &5","&3"); ("&87 / &50","&3")];
                  [("&457 / &500","&2"); ("&1","&12 / &5")];
                  [("&3","&12 / &5"); ("&1543 / &500","&2")]|];;
let FS_OUTSIDE = [|[("&33 / &20","&33 / &20"); ("&47 / &20","&33 / &20")];
                   [("&1","&1543 / &500"); ("&2","&1543 / &500")];
                   [("&33 / &20","&33 / &20")];
                   []|];;

let fs_case_thm (cid, fam, doms, (sw, rx, ry), masks4, owned4, lb, rb) =
  if ry || (sw && rx) then failwith "fs_case_thm: transform not implemented" else
  let fam = List.sort compare fam in
  let ri = try index fam (map row_masks (0--576)) with Failure _ -> failwith "case: row not found" in
  let r = ROW_LIST ri in
  let hyp = mk_conj(`NPACK c1 c2 a b l`,
              mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, mk_comb(`set_of_list:(num)list->num->bool`, r))) in
  let hnp = CONJUNCT1 (ASSUME hyp) and hrow = CONJUNCT2 (ASSUME hyp) in
  let dmasks = map fst doms in
  let allmasks = setify (dmasks @ masks4 @ [lb; rb]) in
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
  let neq_sq (mj, ivj, ltj, ownj, _) (mt, ivt, ltt, ownt, _) =
    let eq = ASSUME (mk_eq(ivj, ivt)) in
    let ownj' = CONV_RULE (LAND_CONV (REWRITE_CONV[eq])) ownj in
    let sets = TRANS (SYM ownj') ownt in
    NOT_INTRO (DISCH (concl eq) (MP (NOT_ELIM (set_neq (bits mj) (bits mt))) sets)) in
  (* domains and the forced owners *)
  let dths = map (fun (m, d) -> (m, try domain_thm hnp hrow r (sq_of m) d
                   with Failure msg -> failwith (Printf.sprintf "domain %d: %s" m msg))) doms in
  let disj2 sa sb =
    let (_, _, lta, _, _) = sa and (_, _, ltb, _, _) = sb in
    MATCH_MP (SPEC `2` (SPECL SPECV AUXOWN_DISJ)) (end_itlist CONJ [hnp; lta; ltb; neq_sq sa sb]) in
  let forced m value =
    let goal = mk_eq(list_mk_comb(`auxown`, `2` :: sq_params (let (_,iv,_,_,_) = sq_of m in iv)), set_tm value) in
    let n = List.length dths in
    let da = Array.of_list dths in
    let rec dfs j chosen =
      if j = n then
        let eqm = assoc m chosen in
        if aconv (concl eqm) goal then eqm else failwith (Printf.sprintf "case %d: not forced" cid)
      else
        let (mj, dth) = da.(j) in
        let rec cases th =
          if is_disj (concl th) then
            let a, b = dest_disj (concl th) in DISJ_CASES th (pick (ASSUME a)) (cases (ASSUME b))
          else pick th
        and pick eqj =
          let rec check ch = match ch with
              [] -> None
            | (mt, eqt)::rest ->
                let dth = disj2 (sq_of mt) (sq_of mj) in
                let dth' = REWRITE_RULE[eqt; eqj] dth in
                let v = disjoint_conv (concl dth') in
                if rhs(concl v) = `false` then Some (CONTR goal (EQ_MP v dth')) else check rest in
          match check chosen with
            Some f -> f
          | None -> dfs (j+1) ((mj, eqj) :: chosen) in
        cases dth in
    dfs 0 [] in
  let forced4 = map2 forced masks4 owned4 in
  (* membership facts for the four template squares, in original coordinates *)
  let four_minus x = term_of_rat (num 4 -/ rat_of_term x) in
  let tr (x,y) = if sw then (y,x) else if rx then (four_minus x, y) else (x,y) in
  let mem_facts j =
    let (m, iv, lt, own, sqth) = sq_of (el j masks4) in
    let sp = sq_params iv in
    let mf = marker_facts own in
    let seeds = seeds_at sp sqth mf (bits m) in
    let af = aux_facts 2 (el j forced4) in
    (seeds @ filter (fun f -> not (is_neg (concl f))) af,
     filter (fun f -> is_neg (concl f)) (mf @ af)) in
  let find_mem ths (x,y) =
    let pt = mk_comb(`vector:(real)list->real^2`, mk_list([parse_term x; parse_term y], `:real`)) in
    let pt = rand(concl(REAL_RAT_REDUCE_CONV pt)) |> fun _ -> pt in
    try find (fun th -> let t = if is_neg (concl th) then rand(concl th) else concl th in
                        aconv (lhand t) pt) ths
    with Failure _ -> failwith (Printf.sprintf "case %d: point %s,%s not available" cid x y) in
  (* the template squares' parameters *)
  let base_params j = let (_, iv, _, _, _) = sq_of (el j masks4) in
    let [c1t; c2t; at; bt; lt] = sq_params iv in lsq_params c1t c2t at bt lt in
  let pulled ps =
    let [c;s;u;v;a] = ps in
    if sw then fst(chop_list 5 (snd(strip_comb(lhs(concl(SPECL [c;s;u;v;a;`x:real`;`y:real`] LINSIDE_PULLSW))))))
    else if rx then fst(chop_list 5 (snd(strip_comb(lhs(concl(SPECL [c;s;u;v;a;`x:real`;`y:real`] LINSIDE_PULLX))))))
    else ps in
  let params = Array.init 4 (fun j -> pulled (base_params j)) in
  let tmpl = SPECL (List.concat (Array.to_list params)) (ASSUME FST_STMT) in
  let prems = conjuncts (lhand (concl tmpl)) in
  let which ps = try (0 -- 3) |> find (fun j -> params.(j) = ps) with Failure _ -> failwith "which" in
  let mf = Array.init 4 mem_facts in
  let sqj j = sq_of (el j masks4) in
  (* th: |- linside base X Y at the transformed point; result at the template point *)
  let pull_eq args x y =
    let [c;s;u;v;a] = args in
    if sw then SPECL [c;s;u;v;a;x;y] LINSIDE_PULLSW
    else let th = SPECL [c;s;u;v;a;x;y] LINSIDE_PULLX in
         CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV REAL_RAT_REDUCE_CONV))) th in
  let base_of j = base_params j in
  let pull_in j x y th = if not (sw || rx) then th else EQ_MP (SYM (pull_eq (base_of j) x y)) th in
  let pull_out j x y th = if not (sw || rx) then th else
    EQ_MP (SYM (AP_TERM `(~)` (pull_eq (base_of j) x y))) th in
  let point_of t = let args = snd(strip_comb t) in (el 5 args, el 6 args) in
  let to_l th = REWRITE_RULE[OSQ_LSQ] th in
  let prove_prem t =
    let (hd, args) = strip_comb t in
    match t with
      Comb(Const("~",_), u) ->
        let (_, uargs) = strip_comb u in
        let j = which (fst(chop_list 5 uargs)) in
        let (x, y) = point_of u in
        let (ox, oy) = tr (x, y) in
        let ptm = mk_comb(`vector:(real)list->real^2`, mk_list([ox; oy], `:real`)) in
        let cands = snd mf.(j) in
        (try pull_out j x y (to_l (find (fun th -> aconv (lhand(rand(concl th))) ptm) cands))
         with Failure _ ->
           (* a barrier point: owned by the barrier square *)
           let bm = if j = 2 then lb else rb in
           let (bmask, biv, blt, bown, bsqth) = sq_of bm in
           let bseeds = seeds_at (sq_params biv) bsqth (marker_facts bown) (bits bm) in
           let bth = find (fun th -> aconv (lhand(concl th)) ptm) bseeds in
           let (_, jiv, jlt, _, _) = sqj j in
           let nq = neq_sq (sqj j) (sq_of bm) in
           let asm = ASSUME (mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, ptm),
                                     list_mk_comb(`osq`, sq_params jiv))) in
           let eqi = MATCH_MP NPACK_DISJ (end_itlist CONJ [hnp; jlt; blt; asm; bth]) in
           let nth = NOT_INTRO (DISCH (concl asm) (MP (NOT_ELIM nq) eqi)) in
           pull_out j x y (to_l nth))
    | _ ->
    (match fst(dest_const hd) with
      "lclosed" ->
        let j = which (fst(chop_list 5 args)) in
        let (x, y) = point_of t in
        let (ox, oy) = tr (x, y) in
        let ptm = mk_comb(`vector:(real)list->real^2`, mk_list([ox; oy], `:real`)) in
        let th = find (fun th -> aconv (lhand(concl th)) ptm) (fst mf.(j)) in
        MATCH_MP LINSIDE_CLOSED (pull_in j x y (to_l th))
    | "lsquare" ->
        let j = which args in
        let (_, _, _, _, [h1; _; h3; _]) = sqj j in
        MP (MP (prove(mk_imp(concl h1, mk_imp(concl h3, t)), REWRITE_TAC[lsquare] THEN REAL_ARITH_TAC)) h1) h3
    | "lcont" ->
        let j = which args in
        let (_, _, _, _, [h1; _; h3; h4]) = sqj j in
        let th = MATCH_MP OWALLS_LCONT (end_itlist CONJ [h3; MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) h1; h4]) in
        if sw then MATCH_MP LCONT_PULLSW th else if rx then MATCH_MP LCONT_PULLX th else th
    | "ldisj" ->
        let j = which (fst(chop_list 5 args)) and k = which (snd(chop_list 5 args)) in
        let (_, ivj, ltj, _, _) = sqj j and (_, ivk, ltk, _, _) = sqj k in
        let th = MATCH_MP NPACK_LDISJ (end_itlist CONJ [hnp; ltj; ltk; neq_sq (sqj j) (sqj k)]) in
        if sw then MATCH_MP LDISJ_PULLSW th else if rx then MATCH_MP LDISJ_PULLX th else th
    | _ ->
        let (_, _, _, _, [h1; h2; _; _]) = sqj 0 in
        MP (MP (prove(mk_imp(concl h1, mk_imp(concl h2, t)), REAL_ARITH_TAC)) h1) h2) in
  let prove_prem t = (try let th = prove_prem t in
      if aconv (concl th) t then th else failwith ("got " ^ string_of_term (concl th))
    with Failure msg ->
    failwith (Printf.sprintf "case %d premise %s: %s" cid (string_of_term t) msg)) in
  let mfs = try Array.init 4 mem_facts with Failure msg -> failwith ("mem_facts: " ^ msg) in
  ignore mfs;
  let f = MP tmpl (end_itlist CONJ (map prove_prem prems)) in
  let f = itlist (fun (_, (ex, _)) th -> CHOOSE (fst(dest_exists(concl ex)), ex) th) sqs f in
  let th = GENL ROWVARS (NOT_INTRO (DISCH hyp f)) in
  let ex = EQ_MP (SYM (REWRITE_CONV[NOT_EXISTS_THM] (EXCLUDED_ROW ri))) th in
  (ri, DISCH FST_STMT ex);;
