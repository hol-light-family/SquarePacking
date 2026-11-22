(* ========================================================================= *)
(* Port, layer 9: the 1703 local queries (Jatloe: LocalQuery, LocalRejection, *)
(* LocalQueryData).  Each query says that no square owns exactly a given     *)
(* marker group together with a given set of auxiliary points.  Every       *)
(* Lean certificate (hull, short template, four-point) is re-checked here as *)
(* one linear contradiction over the square's parameters, split over the    *)
(* faces of the outside points it uses.                                      *)
(* ========================================================================= *)

needs "n12/phase1/localq_geom.ml";;
needs "n12/phase1/hull.ml";;
loadt "n12/phase1/localq_data.ml";;

(* Auxiliary point lists in Lean's order: F, G (sorted), and F ++ G. *)
let GPT_LIST = `[vector[&1; &8 / &5]; vector[&1; &12 / &5]; vector[&87 / &50; &1];
                 vector[&87 / &50; &2]; vector[&87 / &50; &3]; vector[&113 / &50; &1];
                 vector[&113 / &50; &2]; vector[&113 / &50; &3]; vector[&3; &8 / &5];
                 vector[&3; &12 / &5]]:(real^2)list`;;

let AUXPTS = new_definition (mk_eq(`AUXPTS (k:num):(real^2)list`,
  mk_cond(`k = 0`, FPT_LIST, mk_cond(`k = 1`, GPT_LIST,
    mk_comb(mk_comb(`APPEND:(real^2)list->(real^2)list->(real^2)list`, FPT_LIST), GPT_LIST)))));;

let auxown = new_definition
 `auxown k c1 c2 a b l = {j | j < LENGTH (AUXPTS k) /\ EL j (AUXPTS k) IN osq c1 c2 a b l}`;;

let AUXPTS_CONV k =
  (REWRITE_CONV[AUXPTS] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[APPEND])
    (mk_comb(`AUXPTS`, mk_small_numeral k));;
let AUXPTS_EXPL = Array.init 3 AUXPTS_CONV;;
let AUX_LEN = [|10; 10; 20|];;

let AUXOWN_MEMBER = prove
 (`forall k c1 c2 a b l s j. auxown k c1 c2 a b l = set_of_list s /\ j < LENGTH (AUXPTS k)
     ==> (EL j (AUXPTS k) IN osq c1 c2 a b l <=> MEM j s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[EXTENSION; auxown; IN_ELIM_THM; IN_SET_OF_LIST] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]);;

let LEN_AUX = Array.init 3 (fun k ->
  (REWRITE_CONV[AUXPTS_EXPL.(k); LENGTH] THENC NUM_REDUCE_CONV)
    (mk_comb(`LENGTH:(real^2)list->num`, mk_comb(`AUXPTS`, mk_small_numeral k))));;

(* facts for an aux-owner hypothesis  th: |- auxown k c1 c2 a b l = set_of_list s *)
let aux_facts k th =
  map (fun j ->
    let lt = EQT_ELIM((REWRITE_CONV[LEN_AUX.(k)] THENC NUM_REDUCE_CONV)
       (mk_binop `(<):num->num->bool` (mk_small_numeral j)
          (mk_comb(`LENGTH:(real^2)list->num`, mk_comb(`AUXPTS`, mk_small_numeral k))))) in
    let th1 = MATCH_MP AUXOWN_MEMBER (CONJ th lt) in
    let th2 = CONV_RULE (RAND_CONV (REWRITE_CONV[MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])) th1 in
    CONV_RULE (ONCE_DEPTH_CONV EL_CONV) (REWRITE_RULE[AUXPTS_EXPL.(k)] th2))
   (0 -- (AUX_LEN.(k) - 1));;

(* ------------------------------------------------------------------------- *)
(* Wall-bridge seeds in all eight orientations.                              *)
(* ------------------------------------------------------------------------- *)

let WALL0_EXPL =
  let hyps = [`&1 < l`; `a * a + b * b = &1`; `owalls c1 c2 a b l`;
              `vector[&457 / &500; &1] IN osq c1 c2 a b l`;
              `vector[&457 / &500; &2] IN osq c1 c2 a b l`] in
  let h = list_mk_conj hyps in
  prove(list_mk_forall(SPEC5, mk_imp(h,
          mk_conj(mem_osq `vector[&1; &5 / &4]:real^2`, mem_osq `vector[&1; &7 / &4]:real^2`))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC WALL_BRIDGE_FORCES THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let D4_FORMS th =
  [th; T_SW th; T_RX th; T_RX (T_SW th); T_RY th; T_RY (T_SW th);
   T_RX (T_RY th); T_RX (T_RY (T_SW th))];;
let WALL_EXPL = D4_FORMS WALL0_EXPL;;

(* all seed theorems for a square: markers owned, singleton and wall extras *)
let all_seeds sqhyps facts clist =
  let base = filter (fun f -> not (is_neg (concl f))) facts in
  let try_use th =
    let hs = conjuncts(lhand(snd(strip_forall(concl th)))) in
    let prove_h h =
      try find (fun f -> aconv (concl f) h) (facts @ sqhyps)
      with Failure _ ->
        let rels = filter (fun f -> is_real_rel (concl f)) sqhyps in
        if is_real_rel h then
          MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), h))) (end_itlist CONJ rels)
        else failwith "no" in
    try CONJUNCTS (MP (SPECL SPEC5 th) (end_itlist CONJ (map prove_h hs)))
    with Failure _ -> [] in
  let sing = match clist with [k] when k < 8 -> try_use SING_EXPL.(k) | _ -> [] in
  base @ sing @ List.concat (map try_use WALL_EXPL);;

(* ------------------------------------------------------------------------- *)
(* The linear contradiction.                                                 *)
(* ------------------------------------------------------------------------- *)

let IN_OSQ_BANDS = prove
 (`forall x y c1 c2 a b l. vector[x; y] IN osq c1 c2 a b l <=>
     --(l / &2) < (x - c1) * a + (y - c2) * b /\ (x - c1) * a + (y - c2) * b < l / &2 /\
     --(l / &2) < (y - c2) * a - (x - c1) * b /\ (y - c2) * a - (x - c1) * b < l / &2`,
  REWRITE_TAC[IN_OSQ; ABS_LT_BANDS; CONJ_ASSOC]);;

let NOT_IN_OSQ_FACES = prove
 (`forall x y c1 c2 a b l. ~(vector[x; y] IN osq c1 c2 a b l) <=>
     (x - c1) * a + (y - c2) * b <= --(l / &2) \/ l / &2 <= (x - c1) * a + (y - c2) * b \/
     (y - c2) * a - (x - c1) * b <= --(l / &2) \/ l / &2 <= (y - c2) * a - (x - c1) * b`,
  REWRITE_TAC[IN_OSQ_BANDS] THEN REAL_ARITH_TAC);;

let pt_of_mem th =
  let v = lhand(if is_neg (concl th) then rand(concl th) else concl th) in
  match dest_list(rand v) with [x;y] -> (rat_of_term x, rat_of_term y) | _ -> failwith "pt_of_mem";;

let lin_refute sqhyps ins outs =
  let infacts = List.concat (map (fun th -> CONJUNCTS (REWRITE_RULE[IN_OSQ_BANDS] th)) ins) in
  let outdisj = map (REWRITE_RULE[NOT_IN_OSQ_FACES]) outs in
  let rec pairs l = match l with [] -> [] | h::t -> map (fun x -> (h,x)) t @ pairs t in
  let ab = find (fun th -> concl th = `a * a + b * b = &1`) sqhyps in
  let cs = List.concat (mapfilter (fun (p,q) ->
      let (x0,y0) = pt_of_mem p and (x1,y1) = pt_of_mem q in
      let dx = x0 -/ x1 and dy = y0 -/ y1 in
      if dx */ dx +/ dy */ dy >/ num 1 then failwith "" else
      let th = MP (SPECL [`a:real`; `b:real`; term_of_rat dx; term_of_rat dy] CS_BOUND)
                  (CONJ ab (EQT_ELIM(REAL_RAT_REDUCE_CONV
                     (mk_binop `(<=):real->real->bool`
                        (mk_binop `(+):real->real->real`
                           (mk_binop `( * ):real->real->real` (term_of_rat dx) (term_of_rat dx))
                           (mk_binop `( * ):real->real->real` (term_of_rat dy) (term_of_rat dy))) `&1`)))) in
      CONJUNCTS (REWRITE_RULE[REAL_ARITH `abs x <= &1 <=> -- &1 <= x /\ x <= &1`] th))
    (pairs outs)) in
  let l1 = find (fun th -> concl th = `&1 < l`) sqhyps in
  let base = l1 :: infacts @ cs in
  (* split the outside disjunctions *)
  let rec split acc ds =
    match ds with
      [] -> NLIN_REFUTE ~deg2:false (acc @ base)
    | d::rest ->
        let rec cases th =
          if is_disj (concl th) then
            let a, b = dest_disj (concl th) in
            DISJ_CASES th (split (ASSUME a :: acc) rest) (cases (ASSUME b))
          else split (th :: acc) rest in
        cases d in
  split [] outdisj;;

(* ------------------------------------------------------------------------- *)
(* One query.                                                                *)
(* ------------------------------------------------------------------------- *)

let LQ_HYPS = [`&1 < l`; `l <= &1001 / &1000`; `a * a + b * b = &1`; `owalls c1 c2 a b l`];;

let query_theorem (i, m, kind, owned, uin, uout) =
  let cl = bits m in
  let ownp = mk_eq(`owned c1 c2 a b l`, mk_comb(`set_of_list:(num)list->num->bool`, numlist cl)) in
  let auxp = mk_eq(list_mk_comb(`auxown`, [mk_small_numeral kind; `c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`]),
                   mk_comb(`set_of_list:(num)list->num->bool`, numlist owned)) in
  let sqhyps = map ASSUME LQ_HYPS in
  let mfacts = marker_facts (ASSUME ownp) and afacts = aux_facts kind (ASSUME auxp) in
  let seeds = all_seeds sqhyps mfacts cl in
  let insides = seeds @ filter (fun f -> not (is_neg (concl f))) afacts in
  let outsides = filter (fun f -> is_neg (concl f)) (mfacts @ afacts) in
  let find_pt ths p =
    let pt = pt_term p in
    try find (fun th -> aconv (lhand(if is_neg(concl th) then rand(concl th) else concl th)) pt) ths
    with Failure _ -> failwith (Printf.sprintf "query %d: point %s not available" i (string_of_term pt)) in
  let ins = map (find_pt insides) uin and outs = map (find_pt outsides) uout in
  let th = lin_refute sqhyps ins outs in
  GENL SPEC5 (itlist DISCH (LQ_HYPS @ [ownp; auxp]) th);;
