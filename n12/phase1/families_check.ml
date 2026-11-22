(* ========================================================================= *)
(* Driver: proves  VALIDF FF ==> GOALF FF  by walking the marker search tree. *)
(* ========================================================================= *)

needs "n12/phase1/families.ml";;
needs "n12/bounds/cert_check.ml";;
#load "unix.cma";;

(* EL with a numeral index on an explicit list.                              *)
let rec EL_NUM_CONV tm =
  match tm with
    Comb(Comb(Const("EL",_),n),l) when is_numeral n ->
      if dest_small_numeral n = 0 then REWRITE_CONV[EL; HD] tm
      else
        let th1 = AP_THM (AP_TERM (rator(rator tm)) (num_CONV n)) l in
        let th2 = TRANS th1 (REWRITE_CONV[CONJUNCT2 EL; TL] (rand(concl th1))) in
        TRANS th2 (EL_NUM_CONV (rand(concl th2)))
  | _ -> failwith "EL_NUM_CONV";;

let DPERM_TH = Array.init 8 (fun t -> Array.init 16 (fun k ->
  let tm = list_mk_comb(`dperm`,[mk_small_numeral t; mk_small_numeral k]) in
  (REWRITE_CONV[dperm; MPERMS] THENC ONCE_DEPTH_CONV EL_NUM_CONV THENC
   ONCE_DEPTH_CONV EL_NUM_CONV) tm));;

let ROW_LOOKUP = el_lookups ROWS;;
let LENGTH_ROWS = (REWRITE_CONV[ROWS; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH ROWS`;;
let MEM_EL_ROWS0 i =
  let th = MATCH_MP MEM_EL (EQT_ELIM((REWRITE_CONV[LENGTH_ROWS] THENC NUM_REDUCE_CONV)
                         (mk_comb(mk_comb(`(<):num->num->bool`, mk_small_numeral i),
                                  `LENGTH ROWS`)))) in
  REWRITE_RULE[ROW_LOOKUP.(i)] th;;
let MEM_EL_ROWS_TBL = Array.init (Array.length ROW_LOOKUP) MEM_EL_ROWS0;;
let MEM_EL_ROWS i = MEM_EL_ROWS_TBL.(i);;

let AVAIL_ALT = prove
 (`avail P k used = LENGTH (FILTER (\p. k <= FST p /\ k <= SND p /\
                                        ~MEM (FST p) used /\ ~MEM (SND p) used) P)`,
  REWRITE_TAC[avail] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let HASPAIR_ALT = prove
 (`haspair P c <=> EX (\p. MEM (FST p) c /\ MEM (SND p) c) P`,
  REWRITE_TAC[haspair] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let RANGELIST_NUM = prove
 (`forall k n. rangelist k n = if n = 0 then [] else CONS k (rangelist (k + 1) (n - 1))`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[rangelist; NOT_SUC; SUC_SUB1; ADD1]);;

(* A compset for the small list computations of the search.                  *)
let fam_convs =
   [`(+):num->num->num`,2,NUM_ADD_CONV; `(-):num->num->num`,2,NUM_SUB_CONV;
    `(<):num->num->bool`,2,NUM_LT_CONV; `(<=):num->num->bool`,2,NUM_LE_CONV;
    `(=):num->num->bool`,2,NUM_EQ_CONV; `SUC`,1,NUM_SUC_CONV;
    `(EXP):num->num->num`,2,NUM_EXP_CONV];;
let make_fam_cs () =
  let cs = Compute.bool_compset() in
  Compute.add_thms [FLATL; ITLIST; APPEND; MEM; ALL; EX; FILTER; LENGTH; MAP; HD; TL;
    PAIRWISE; RANGELIST_NUM; CONS_11; NOT_CONS_NIL; PAIR_EQ; FST; SND;
    freeN; AVAIL_ALT; HASPAIR_ALT; FPAIRS; GPAIRS; CONFL] cs;
  Compute.add_thms (List.concat (Array.to_list (Array.map Array.to_list DPERM_TH))) cs;
  List.iter (fun (t,n,c) -> Compute.add_conv (t,n,c) cs) fam_convs;
  cs;;

let fam_cs_tbl = Array.make 4096 None;;
let fam_cs () =
  let i = (Domain.self () :> int) land 4095 in
  match fam_cs_tbl.(i) with
    Some cs -> cs
  | None -> let cs = make_fam_cs () in fam_cs_tbl.(i) <- Some cs; cs;;
let fam_ev tm = EQT_ELIM(Compute.CBV_CONV (fam_cs ()) tm);;

(* For each k, the cliques with least marker k.                              *)
let CLQ_LISTS = map (map dest_small_numeral o dest_list) (dest_list(rand(concl CLQ)));;
let byk k = filter (fun c -> hd c = k) CLQ_LISTS;;
let ty_num = `:num` and ty_numl = `:num list` and nil_numll = `[]:(num list)list`;;
let numl l = mk_list(map mk_small_numeral l, ty_num);;
let numll ll = if ll = [] then nil_numll else mk_list(map numl ll, ty_numl);;

let BYK_THM = Array.init 16 (fun k ->
  let cs = byk k in
  let qv = `Q:num list->bool` in
  let concl = list_mk_disj(map (fun c -> mk_comb(qv, numl c)) cs) in
  prove(mk_forall(qv, mk_imp(
     subst [mk_small_numeral k, `kk:num`] `exists c. MEM c CLQ /\ HD c = kk /\ (Q:num list->bool) c`,
     concl)),
   GEN_TAC THEN REWRITE_TAC[CLQ; MEM; RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2;
                            GSYM CONJ_ASSOC] THEN
   REWRITE_TAC[HD] THEN CONV_TAC(DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* The tree walk.                                                            *)
(* ------------------------------------------------------------------------- *)

let FFv = `FF:(num->bool)->bool`;;
let VAL_TM = `VALIDF FF`;;
let GOAL_TM = `GOALF FF`;;
let INVF_C = `INVF`;;
let inv_tm k l = list_mk_comb(INVF_C, [FFv; mk_small_numeral k; numll l]);;
let suc_fix th = CONV_RULE (ONCE_DEPTH_CONV NUM_SUC_CONV) th;;

let VALID_BUDGETS =
  let th = UNDISCH(fst(EQ_IMP_RULE(SPEC FFv VALIDF))) in
  let cs = CONJUNCTS th in
  el 5 cs, el 6 cs;;

let early_cert =
  let tbl = Hashtbl.create 5000 in
  let ic = Stdlib.open_in "n12/data/early_cert.txt" in
  (try while true do
     match String.split_on_char ' ' (input_line ic) with
       [ms; t; r] -> Hashtbl.add tbl (List.map int_of_string (String.split_on_char ',' ms))
                                     (int_of_string t, int_of_string r)
     | _ -> ()
   done with End_of_file -> ());
  Stdlib.close_in ic; tbl;;

let mask_of c = List.fold_left (fun a k -> a + (1 lsl k)) 0 c;;
let fpairs = [0,1; 2,3; 4,5; 6,7; 8,11; 9,10] and gpairs = [0,1; 2,3; 4,5; 6,7; 8,9; 10,11];;
let haspair_ml p c = List.exists (fun (a,b) -> mem a c && mem b c) p;;
let conf_pairs = map (fun (a,b) -> (map dest_small_numeral (dest_list a),
                                    map dest_small_numeral (dest_list b)))
  (map dest_pair (dest_list(rand(concl CONFL))));;
let conflicts c d = mem (c,d) conf_pairs || mem (d,c) conf_pairs;;

let contra th = CONTR GOAL_TM th;;

(* Hoisted quotations: the tree walk runs in parallel domains, and the
   parser is not domain-safe. *)
let qt_0 = `ALL:(num->bool)->num list->bool`;;
let qt_1 = `x:num`;;
let qt_2 = `MEM:num->num list->bool`;;
let qt_3 = `MEM:num list->(num list)list->bool`;;
let qt_4 = `k:num`;;
let qt_5 = `L:(num list)list`;;
let qt_6 = `LENGTH (L:(num list)list) + freeN k (FLATL L) < 12`;;
let qt_7 = `(<=):num->num->bool`;;
let qt_8 = `16`;;
let qt_9 = `FPAIRS`;;
let qt_10 = `GPAIRS`;;
let qt_11 = `P:(num#num)list`;;
let qt_12 = `LENGTH (FILTER (haspair P) (L:(num list)list)) + avail P k (FLATL L) < 2`;;
let qt_13 = `MEM (k:num) (FLATL L)`;;
let qt_14 = `FLATL`;;
let qt_15 = `c:num list`;;
let qt_16 = `d:num list`;;
let qt_17 = `MEM ((c:num list),(d:num list)) CONFL \/ MEM (d,c) CONFL`;;
let qt_18 = `12 < LENGTH (L:(num list)list)`;;

let leaf_thm l hv hi =
  let key = List.sort compare (map mask_of l) in
  let (t, ri) = try Hashtbl.find early_cert key with Not_found -> failwith "leaf: no cert" in
  let tt = mk_small_numeral t in
  let r = rand(concl ROW_LOOKUP.(ri)) in
  let ltm = numll l in
  let lem = SPECL [FFv; ltm; tt; r] LEAF_GOAL in
  let ants = conjuncts(lhand(concl lem)) in
  let prove_ant a =
    if a = VAL_TM then hv else if a = concl hi then hi
    else if is_eq a then
      let l1 = rand(lhand a) and l2 = rand(rand a) in
      let allmem la lb = mk_comb(mk_comb(qt_0,
           mk_abs(qt_1, mk_comb(mk_comb(qt_2, qt_1), lb))), la) in
      MATCH_MP SET_OF_LIST_EQ_ALL (fam_ev(mk_conj(allmem l1 l2, allmem l2 l1)))
    else if fst(strip_comb a) = qt_3 then MEM_EL_ROWS ri
    else fam_ev a in
  MP lem (end_itlist CONJ (map prove_ant ants));;

let node_memo = Hashtbl.create 1000;;

let rec node k l =
  try Hashtbl.find node_memo (k,l) with Not_found ->
  let hv = ASSUME VAL_TM and hi = ASSUME (inv_tm k l) in
  let kt = mk_small_numeral k and ltm = numll l in
  let used = List.concat l in
  let free = List.length (filter (fun j -> not(mem j used)) (k--15)) in
  let favail = List.length (filter (fun (a,b) -> a >= k && b >= k && not(mem a used) && not(mem b used)) fpairs)
  and gavail = List.length (filter (fun (a,b) -> a >= k && b >= k && not(mem a used) && not(mem b used)) gpairs) in
  let nf = List.length (filter (haspair_ml fpairs) l) and ng = List.length (filter (haspair_ml gpairs) l) in
  if List.length l > 12 then
    let fact = fam_ev (subst [ltm,qt_5] qt_18) in
    contra (MP (SPECL [FFv; kt; ltm] P_TOOMANY) (end_itlist CONJ [hv; hi; fact]))
  else if List.length l + free < 12 then
    let fact = fam_ev (subst [kt,qt_4; ltm,qt_5]
                 qt_6) in
    let kle = EQT_ELIM(NUM_LE_CONV(mk_comb(mk_comb(qt_7,kt),qt_8))) in
    contra (MP (SPECL [FFv; kt; ltm] P_COUNT) (end_itlist CONJ [hv; hi; kle; fact]))
  else if nf + favail < 2 || ng + gavail < 2 then
    let (pl, bud) = if nf + favail < 2 then (qt_9, fst VALID_BUDGETS)
                    else (qt_10, snd VALID_BUDGETS) in
    let fact = fam_ev (subst [kt,qt_4; ltm,qt_5; pl,qt_11]
      qt_12) in
    contra (MP (SPECL [pl; FFv; kt; ltm] P_BUDGET) (end_itlist CONJ [hv; hi; bud; fact]))
  else if k = 16 then leaf_thm l hv hi
  else if mem k used then
    let mf = fam_ev (subst [kt,qt_4; ltm,qt_5] qt_13) in
    let th = suc_fix (MP (SPECL [FFv; kt; ltm] INVF_USED) (end_itlist CONJ [hv; hi; mf])) in
    PROVE_HYP th (node (k+1) l)
  else
    let st = suc_fix (MP (SPECL [FFv; kt; ltm] INVF_STEP) (CONJ hv hi)) in
    let d1, d2 = dest_disj (concl st) in
    let th1 = node (k+1) l in
    let cv, body = dest_exists d2 in
    let _, rest = dest_conj body in
    let _, q = dest_conj rest in
    let qlam = mk_abs(cv, q) in
    let bth = SPEC qlam BYK_THM.(k) in
    let ante = lhand(concl bth) in
    let d2th' = EQ_MP (SYM(DEPTH_CONV BETA_CONV ante)) (ASSUME d2) in
    let disj = CONV_RULE (DEPTH_CONV BETA_CONV) (MP bth d2th') in
    let cases = map (fun c ->
      let ctm = numl c in
      let qc = vsubst [ctm, cv] q in
      let hq = ASSUME qc in
      let [h_in; h_nb; h_inv] = CONJUNCTS hq in
      let th =
        match filter (fun x -> mem x used) c with
          x::_ ->
            let xt = mk_small_numeral x in
            let m1 = fam_ev (mk_comb(mk_comb(qt_2, xt), ctm)) in
            let m2 = fam_ev (mk_comb(mk_comb(qt_2, xt),
                                     mk_comb(qt_14, ltm))) in
            contra (MP (SPECL [FFv; kt; ltm; ctm; xt] P_DISJ)
                       (end_itlist CONJ [hv; hi; h_in; h_nb; m1; m2]))
        | [] ->
          match filter (conflicts c) l with
            d::_ ->
              let dt = numl d in
              let m1 = fam_ev (mk_comb(mk_comb(qt_3, dt), ltm)) in
              let m2 = fam_ev (subst [ctm,qt_15; dt,qt_16]
                         qt_17) in
              contra (MP (SPECL [FFv; kt; ltm; ctm; dt] P_CONF)
                         (end_itlist CONJ [hv; hi; h_in; m1; m2]))
          | [] -> PROVE_HYP h_inv (node (k+1) (c::l)) in
      qc, th) (byk k) in
    let rec combine dth cs =
      match cs with
        [qc, th] -> PROVE_HYP dth th
      | (qc, th)::rest ->
          let a, b = dest_disj (concl dth) in
          DISJ_CASES dth th (combine (ASSUME b) rest)
      | [] -> failwith "combine" in
    let th2 = combine disj cases in
    DISJ_CASES st th1 th2;;

(* Parallel driver: prove all states at marker level kf in parallel.        *)
let frontier kf =
  let acc = ref [] in
  let rec walk k l =
    let used = List.concat l in
    if k = kf then acc := (k,l) :: !acc else
    let free = List.length (filter (fun j -> not(mem j used)) (k--15)) in
    let fa p = List.length (filter (fun (a,b) -> a >= k && b >= k && not(mem a used) &&
                                                not(mem b used)) p) in
    let nf = List.length (filter (haspair_ml fpairs) l)
    and ng = List.length (filter (haspair_ml gpairs) l) in
    if List.length l > 12 || List.length l + free < 12 || nf + fa fpairs < 2 || ng + fa gpairs < 2 then () else
    if mem k used then walk (k+1) l else
    (walk (k+1) l;
     List.iter (fun c -> if exists (fun x -> mem x used) c || exists (conflicts c) l
                         then () else walk (k+1) (c::l)) (byk k)) in
  walk 0 []; List.rev !acc;;

let families_theorem ndom kf =
  let tasks = Array.of_list (frontier kf) in
  let n = Array.length tasks in
  let res = Array.make n None in
  let next = Atomic.make 0 in
  let failed = Atomic.make "" in
  let css = Array.init ndom (fun _ -> make_fam_cs ()) in
  let worker i () =
    fam_cs_tbl.((Domain.self () :> int) land 4095) <- Some css.(i);
    let rec loop () =
      let j = Atomic.fetch_and_add next 1 in
      if j < n && Atomic.get failed = "" then begin
        let (k,l) = tasks.(j) in
        (try res.(j) <- Some(node k l)
         with Failure s -> Atomic.set failed s | e -> Atomic.set failed (Printexc.to_string e));
        loop () end in
    loop () in
  let doms = List.init ndom (fun i -> Domain.spawn (worker i)) in
  List.iter Domain.join doms;
  if Atomic.get failed <> "" then failwith ("families_theorem: " ^ Atomic.get failed);
  Array.iteri (fun j (k,l) -> match res.(j) with
      Some th -> Hashtbl.replace node_memo (k,l) th | None -> failwith "missing") tasks;
  let th = node 0 [] in
  (* discharge INVF FF 0 [] *)
  let th0 = PROVE_HYP (ISPEC FFv INVF_0) th in
  GEN FFv (DISCH VAL_TM th0);;
