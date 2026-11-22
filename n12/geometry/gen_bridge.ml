(* ========================================================================= *)
(* Phase 2: a generic packing-side bridge for template cases.                *)
(*                                                                           *)
(* Given a template theorem  |- !sq_1 .. sq_k. premises ==> F  (each square  *)
(* five reals, in the representation of p2_base.ml) and a case (row, owner   *)
(* domains, symmetry, masks and forced owner sets of the k squares), prove   *)
(*      |- ~(?packing. NPACK .. /\ family = row).                           *)
(* Premises are discharged by kind: lsquare, lcont, ldisj, side relations,  *)
(* lclosed / linside at points owned (markers, seeds, auxiliary points), and *)
(* ~linside at points either excluded for the square or owned by another    *)
(* square of the family.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/fs_bridge.ml";;

(* the symmetry: Lean Transform (swap, reflectX, reflectY) pulls the square
   by reflectX, then reflectY, then swap; a pulled square at P is the original
   square at T(P) = reflect(swap P). *)
let tr_point (sw, rx, ry) (x, y) =
  let four_minus t = term_of_rat (num 4 -/ rat_of_term t) in
  let (u, v) = if sw then (y, x) else (x, y) in
  ((if rx then four_minus u else u), (if ry then four_minus v else v));;

type pgen = Gx | Gy | Gs;;

(* params after one generator, and the equivalence at a point *)
let gen_step gen ps x y =
  let [c;s;u;v;a] = ps in
  let th = SPECL [c;s;u;v;a;x;y] (match gen with
      Gx -> LINSIDE_PULLX | Gy -> LINSIDE_PULLY | Gs -> LINSIDE_PULLSW) in
  let th = CONV_RULE (RAND_CONV (DEPTH_CONV (fun t ->
             if is_binop `(-):real->real->real` t && lhand t = `&4` && is_ratconst (rand t)
             then REAL_RAT_REDUCE_CONV t else failwith ""))) th in
  (fst(chop_list 5 (snd(strip_comb(lhs(concl th))))), th);;

let gens_of (sw, rx, ry) = (if rx then [Gx] else []) @ (if ry then [Gy] else []) @ (if sw then [Gs] else []);;

(* pulled params of a base square *)
let pull_params trf ps =
  itlist (fun g ps -> fst (gen_step g ps `x:real` `y:real`)) (rev (gens_of trf)) ps;;

(* |- linside pulled P <=> linside base T(P) *)
let pull_point_eq trf ps (x, y) =
  let gens = gens_of trf in
  (* apply generators in order; at each step the point moves *)
  (* simple implementation: build from the base outwards *)
  let rec build ps gs (x, y) =
    match gs with
      [] -> REFL (list_mk_comb(`linside`, ps @ [x; y]))
    | _ ->
        let g = last gs and inner = butlast gs in
        let inner_ps = pull_params_list ps inner in
        let (_, th) = gen_step g inner_ps x y in
        let args = snd(strip_comb(rand(concl th))) in
        let x' = el 5 args and y' = el 6 args in
        TRANS th (build ps inner (x', y'))
  and pull_params_list ps gs = itlist (fun g ps -> fst (gen_step g ps `x:real` `y:real`)) (rev gs) ps in
  build ps gens (x, y);;

let lclosed_of_linside_eq th =
  (* from |- linside p x y <=> linside q x' y' get the lclosed analogue *)
  let l = lhs(concl th) and r = rhs(concl th) in
  let mk t = let (_, args) = strip_comb t in list_mk_comb(`lclosed`, args) in
  prove(mk_eq(mk l, mk r), REWRITE_TAC[lclosed] THEN
    MP_TAC th THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let LCONT_PULL g = match g with Gx -> LCONT_PULLX | Gy -> LCONT_PULLY | Gs -> LCONT_PULLSW;;
let LDISJ_PULLY = prove
 (`forall c s u v a c' s' u' v' a'. ldisj c s u v a c' s' u' v' a'
     ==> ldisj c (--s) (u - &4 * s) (&4 * c - v - a) a c' (--s') (u' - &4 * s') (&4 * c' - v' - a') a'`,
  REWRITE_TAC[ldisj; LINSIDE_PULLY] THEN MESON_TAC[]);;
let LDISJ_PULL g = match g with Gx -> LDISJ_PULLX | Gy -> LDISJ_PULLY | Gs -> LDISJ_PULLSW;;

(* derive membership of point p from owned points by convexity *)
let pt_of_th th = match dest_list(rand(lhand(concl th))) with
    [x;y] -> (rat_of_term x, rat_of_term y) | _ -> failwith "pt_of_th";;

let derive_point facts (px, py) =
  let pts = mapfilter (fun th -> (pt_of_th th, th)) facts in
  let p = (rat_of_term px, rat_of_term py) in
  try snd (find (fun (q, _) -> q = p) pts) with Failure _ ->
  let seg ((x0,y0),th0) ((x1,y1),th1) =
    (* p = (1-t) p0 + t p1 *)
    let dx = x1 -/ x0 and dy = y1 -/ y0 in
    let t = if dx <>/ num 0 then (fst p -/ x0) // dx
            else if dy <>/ num 0 then (snd p -/ y0) // dy else failwith "" in
    if t </ num 0 || t >/ num 1 then failwith "" else
    if x0 +/ t */ dx <>/ fst p || y0 +/ t */ dy <>/ snd p then failwith "" else
    tri_point [th0; th1] ([(x0,y0); (x1,y1); (x1,y1)], p, t, num 0) in
  let rec pairs l = match l with [] -> [] | h::t -> map (fun x -> (h,x)) t @ pairs t in
  try tryfind (fun (a, b) -> seg a b) (pairs pts) with Failure _ ->
  let tri ((x0,y0),th0) ((x1,y1),th1) ((x2,y2),th2) =
    (* barycentric coordinates *)
    let det = (x1 -/ x0) */ (y2 -/ y0) -/ (x2 -/ x0) */ (y1 -/ y0) in
    if det =/ num 0 then failwith "" else
    let l1 = ((fst p -/ x0) */ (y2 -/ y0) -/ (x2 -/ x0) */ (snd p -/ y0)) // det
    and l2 = ((x1 -/ x0) */ (snd p -/ y0) -/ (fst p -/ x0) */ (y1 -/ y0)) // det in
    let l0 = num 1 -/ l1 -/ l2 in
    if l0 </ num 0 || l1 </ num 0 || l2 </ num 0 then failwith "" else
    let t = l2 in
    let s = if l0 +/ l1 =/ num 0 then num 0 else l1 // (l0 +/ l1) in
    tri_point [th0; th1; th2] ([(x0,y0); (x1,y1); (x2,y2)], p, s, t) in
  let rec triples l = match l with
      [] -> [] | h::t -> map (fun (a,b) -> (h,a,b)) (pairs t) @ triples t in
  tryfind (fun (a, b, c) -> tri a b c) (triples pts);;

let gen_case_thm_x extra tmpl (cid, fam, doms, trf, masksk, ownedk) =
  let fam = List.sort compare fam in
  let ri = try index fam (map row_masks (0--576)) with Failure _ -> failwith "case: row not found" in
  let r = ROW_LIST ri in
  let hyp = mk_conj(`NPACK c1 c2 a b l`,
              mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, mk_comb(`set_of_list:(num)list->num->bool`, r))) in
  let hnp = CONJUNCT1 (ASSUME hyp) and hrow = CONJUNCT2 (ASSUME hyp) in
  let allmasks = setify (fam @ map fst doms @ masksk) in
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
  (* forced owners for the k template squares *)
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
  let k = List.length masksk in
  let fmasks = masksk @ map fst extra and fowned = ownedk @ map snd extra in
  let forcedk = Array.of_list (map2 forced fmasks fowned) in
  (* membership facts of a square (given its forced owners when known) *)
  let facts_tbl = Hashtbl.create 20 in
  let facts_of m =
    try Hashtbl.find facts_tbl m with Not_found ->
    let (_, iv, lt, own, sqth) = sq_of m in
    let mf = marker_facts own in
    let seeds = seeds_at (sq_params iv) sqth mf (bits m) in
    let af = try let j = index m fmasks in aux_facts 2 forcedk.(j) with Failure _ -> [] in
    let res = (seeds @ filter (fun f -> not (is_neg (concl f))) af,
               filter (fun f -> is_neg (concl f)) (mf @ af)) in
    Hashtbl.add facts_tbl m res; res in
  (* template parameters *)
  let base_params j = let (_, iv, _, _, _) = sq_of (el j masksk) in
    let [c1t; c2t; at; bt; lt] = sq_params iv in lsq_params c1t c2t at bt lt in
  let params = Array.init k (fun j -> pull_params trf (base_params j)) in
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
            (* owned strictly by another square of the family *)
            let (_, jiv, jlt, _, _) = sqj j in
            let owner = find (fun m -> m <> el j masksk &&
                          exists (fun th -> aconv (lhand(concl th)) ptm) (fst (facts_of m))) allmasks in
            let (_, biv, blt, _, _) = sq_of owner in
            let bth = find (fun th -> aconv (lhand(concl th)) ptm) (fst (facts_of owner)) in
            let asm = ASSUME (mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, ptm),
                                     list_mk_comb(`osq`, sq_params jiv))) in
            let eqi = MATCH_MP NPACK_DISJ (end_itlist CONJ [hnp; jlt; blt; asm; bth]) in
            let nq = neq_sq (sqj j) (sq_of owner) in
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
        let th = MATCH_MP NPACK_LDISJ (end_itlist CONJ [hnp; ltj; ltk; neq_sq (sqj j) (sqj kk)]) in
        itlist (fun g th -> MATCH_MP (LDISJ_PULL g) th) (rev gens) th
    | _ ->
        let (_, _, _, _, [h1; h2; _; _]) = sqj 0 in
        MP (MP (prove(mk_imp(concl h1, mk_imp(concl h2, t)), REAL_ARITH_TAC)) h1) h2) in
  let prove_prem t = (try let th = prove_prem t in
      if aconv (concl th) t then th else failwith ("got " ^ string_of_term (concl th))
    with Failure msg ->
    failwith (Printf.sprintf "case %d premise %s: %s" cid (string_of_term t) msg)) in
  let f = MP tmpl_i (end_itlist CONJ (map prove_prem prems)) in
  let f = itlist (fun (_, (ex, _)) th -> CHOOSE (fst(dest_exists(concl ex)), ex) th) sqs f in
  let th = GENL ROWVARS (NOT_INTRO (DISCH hyp f)) in
  (ri, EQ_MP (SYM (REWRITE_CONV[NOT_EXISTS_THM] (EXCLUDED_ROW ri))) th);;
let gen_case_thm tmpl c = gen_case_thm_x [] tmpl c;;
