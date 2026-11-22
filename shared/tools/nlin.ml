(* ========================================================================= *)
(* NLIN_TAC: an nlinarith-style prover for real polynomial inequalities.     *)
(*                                                                           *)
(* Hypotheses p >= 0, p > 0, p = 0 (from the assumptions, the hint theorems  *)
(* and the negated goal) are multiplied in pairs.  An external LP (untrusted, *)
(* shared/tools/nlin_lp.py) picks a subset that has a linear contradiction, and   *)
(* REAL_ARITH proves the contradiction from that subset.                     *)
(* ========================================================================= *)

#load "unix.cma";;

(* Polynomials over rational numbers, with atoms numbered by first occurrence. *)

let nlin_atoms = ref ([] : term list);;

let nlin_atom t =
  let rec find i l = match l with
      [] -> nlin_atoms := !nlin_atoms @ [t]; i
    | h::r -> if aconv h t then i else find (i+1) r in
  find 0 !nlin_atoms;;

(* monomial: sorted (atom, power) list; poly: (monomial * num) list *)
let pnorm p =
  let p = List.sort (fun (m1,_) (m2,_) -> compare m1 m2) p in
  let rec merge l = match l with
      (m1,c1)::(m2,c2)::r when m1 = m2 -> merge ((m1, c1 +/ c2)::r)
    | (m,c)::r -> if c =/ num 0 then merge r else (m,c)::merge r
    | [] -> [] in
  merge p;;

let padd p q = pnorm (p @ q);;
let pscale c p = pnorm (map (fun (m,d) -> (m, c */ d)) p);;
let mmul m1 m2 =
  let rec go a b = match a,b with
      [],_ -> b | _,[] -> a
    | (x,i)::r, (y,j)::s ->
        if x = y then (x,i+j)::go r s
        else if x < y then (x,i)::go r b else (y,j)::go a s in
  go m1 m2;;
let pmul p q = pnorm (List.concat (map (fun (m1,c1) -> map (fun (m2,c2) -> (mmul m1 m2, c1 */ c2)) q) p));;
let pconst c = if c =/ num 0 then [] else [[], c];;

let rec poly_of_term t =
  try pconst (rat_of_term t) with Failure _ ->
  match t with
    Comb(Comb(Const("real_add",_),a),b) -> padd (poly_of_term a) (poly_of_term b)
  | Comb(Comb(Const("real_sub",_),a),b) -> padd (poly_of_term a) (pscale (num(-1)) (poly_of_term b))
  | Comb(Const("real_neg",_),a) -> pscale (num(-1)) (poly_of_term a)
  | Comb(Comb(Const("real_mul",_),a),b) -> pmul (poly_of_term a) (poly_of_term b)
  | Comb(Comb(Const("real_div",_),a),b) when (try ignore(rat_of_term b); true with Failure _ -> false) ->
      let c = rat_of_term b in
      if c =/ num 0 then failwith "poly_of_term: division by zero"
      else pscale (num 1 // c) (poly_of_term a)
  | Comb(Comb(Const("real_pow",_),a),n) when is_numeral n ->
      let k = dest_small_numeral n in
      let pa = poly_of_term a in
      let rec pw i = if i = 0 then pconst (num 1) else pmul pa (pw (i-1)) in pw k
  | _ -> [[nlin_atom t, 1], num 1];;

(* Facts: theorems |- &0 <= p, |- &0 < p, |- p = &0.                          *)

type nkind = Nge | Ngt | Neq;;

let REAL_SUB_LE' = REAL_ARITH `forall a b. a <= b ==> &0 <= b - a`;;
let REAL_SUB_LT' = REAL_ARITH `forall a b. a < b ==> &0 < b - a`;;
let REAL_SUB_EQ' = REAL_ARITH `forall a b. a = b ==> a - b = &0`;;
let REAL_NOT_LE' = REAL_ARITH `forall a b. ~(a <= b) ==> &0 < a - b`;;
let REAL_NOT_LT' = REAL_ARITH `forall a b. ~(a < b) ==> &0 <= a - b`;;
let REAL_GE' = REAL_ARITH `forall a b. a >= b ==> &0 <= a - b`;;
let REAL_GT' = REAL_ARITH `forall a b. a > b ==> &0 < a - b`;;
let REAL_EQ_MUL0 = prove(`forall x y. x = &0 ==> x * y = &0`, SIMP_TAC[REAL_MUL_LZERO]);;
let REAL_LE_MUL' = prove(`forall x y. &0 <= x /\ &0 <= y ==> &0 <= x * y`, SIMP_TAC[REAL_LE_MUL]);;
let REAL_LT_MUL' = prove(`forall x y. &0 < x /\ &0 < y ==> &0 < x * y`, SIMP_TAC[REAL_LT_MUL]);;
let REAL_LTLE_MUL = prove(`forall x y. &0 < x /\ &0 <= y ==> &0 <= x * y`,
  SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]);;
let REAL_LELT_MUL = prove(`forall x y. &0 <= x /\ &0 < y ==> &0 <= x * y`,
  SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]);;
let real_ty = `:real`;;
let real_zero = `&0`;;

let is_real_rel t =
  match t with
    Comb(Comb(Const(("real_le"|"real_lt"|"real_ge"|"real_gt"),_),_),_) -> true
  | Comb(Comb(Const("=",Tyapp("fun",[ty;_])),_),_) -> ty = real_ty
  | _ -> false;;

(* normalise a theorem to a fact, or fail *)
let fact_of_thm th =
  let t = concl th in
  let fix c = if is_comb c && is_comb(rator c) && rand(rator c) = real_zero then c else c in
  ignore fix;
  match t with
    Comb(Comb(Const("real_le",_),z),p) when z = real_zero -> (Nge, th)
  | Comb(Comb(Const("real_lt",_),z),p) when z = real_zero -> (Ngt, th)
  | Comb(Comb(Const("=",_),p),z) when z = real_zero && type_of p = real_ty -> (Neq, th)
  | Comb(Comb(Const("real_le",_),a),b) -> (Nge, MATCH_MP REAL_SUB_LE' th)
  | Comb(Comb(Const("real_lt",_),a),b) -> (Ngt, MATCH_MP REAL_SUB_LT' th)
  | Comb(Comb(Const("real_ge",_),a),b) -> (Nge, MATCH_MP REAL_GE' th)
  | Comb(Comb(Const("real_gt",_),a),b) -> (Ngt, MATCH_MP REAL_GT' th)
  | Comb(Comb(Const("=",_),a),b) when type_of a = real_ty -> (Neq, MATCH_MP REAL_SUB_EQ' th)
  | Comb(Const("~",_),Comb(Comb(Const("real_le",_),a),b)) -> (Ngt, MATCH_MP REAL_NOT_LE' th)
  | Comb(Const("~",_),Comb(Comb(Const("real_lt",_),a),b)) -> (Nge, MATCH_MP REAL_NOT_LT' th)
  | _ -> failwith "fact_of_thm";;

let fact_poly (k,th) =
  let t = concl th in
  match k with Neq -> poly_of_term (lhand t) | _ -> poly_of_term (rand t);;

let fact_term (k,th) = let t = concl th in match k with Neq -> lhand t | _ -> rand t;;

let mul_facts (k1,t1) (k2,t2) =
  let c = CONJ t1 t2 in
  match k1,k2 with
    Neq,_ -> Some(Neq, SPEC (fact_term (k2,t2)) (MATCH_MP REAL_EQ_MUL0 t1))
  | _,Neq -> Some(Neq, SPEC (fact_term (k1,t1)) (MATCH_MP REAL_EQ_MUL0 t2))
  | Nge,Nge -> Some(Nge, MATCH_MP REAL_LE_MUL' c)
  | Ngt,Ngt -> Some(Ngt, MATCH_MP REAL_LT_MUL' c)
  | Ngt,Nge -> Some(Nge, MATCH_MP REAL_LTLE_MUL c)
  | Nge,Ngt -> Some(Nge, MATCH_MP REAL_LELT_MUL c);;

let nlin_counter = ref 0;;

let nlin_rat s =
  match String.split_on_char '/' s with
    [a] -> Num.num_of_string a
  | [a;b] -> Num.num_of_string a // Num.num_of_string b
  | _ -> failwith "nlin_rat";;

(* The Python interpreter for the untrusted oracles (needs SciPy): $SQ_PYTHON, else
   .venv/bin/python under the project root if present, else python3.  Paths are relative to the
   project root, from which every build is run (shared/build.sh). *)
let sq_python () =
  match Sys.getenv_opt "SQ_PYTHON" with
    Some p when p <> "" -> p
  | _ -> if Sys.file_exists ".venv/bin/python" then ".venv/bin/python" else "python3";;

let lp_proc = ref (None : (in_channel * out_channel) option);;
let lp_server () =
  match !lp_proc with
    Some p -> p
  | None ->
      let py = sq_python () in
      let p = Unix.open_process_args py
                [|py; "shared/tools/nlin_lp.py"; "--server"|] in
      lp_proc := Some p; p;;

let run_lp facts =
  let polys = map fact_poly facts in
  let monos = Hashtbl.create 64 and nmon = ref 1 in
  Hashtbl.add monos [] 0;
  let midx m = try Hashtbl.find monos m with Not_found ->
    let i = !nmon in Hashtbl.add monos m i; incr nmon; i in
  let rows = map (fun p -> map (fun (m,c) -> (midx m, c)) p) polys in
  let buf = Buffer.create 4096 in
  Printf.bprintf buf "%d %d\n" (List.length facts) !nmon;
  Buffer.add_string buf (String.concat " "
    (map (fun (k,_) -> match k with Nge -> "ge" | Ngt -> "gt" | Neq -> "eq") facts) ^ "\n");
  List.iter (fun r ->
    Buffer.add_string buf (string_of_int (List.length r));
    List.iter (fun (m,c) -> Printf.bprintf buf " %d %s" m (string_of_num c)) r;
    Buffer.add_string buf "\n") rows;
  let (ic,oc) = lp_server () in
  output_string oc (Buffer.contents buf); flush oc;
  let line = input_line ic in
  if line = "FAIL" then failwith "nlin: no certificate" else
  let toks = filter (fun s -> s <> "") (String.split_on_char ' ' line) in
  let rec pairs l = match l with
      i::c::r -> (int_of_string i, nlin_rat c) :: pairs r
    | _ -> [] in
  pairs toks;;

let NLIN_SCALE_GE = prove(`forall k p. &0 <= k /\ &0 <= p ==> &0 <= k * p`, SIMP_TAC[REAL_LE_MUL]);;
let NLIN_SCALE_GT = prove(`forall k p. &0 < k /\ &0 < p ==> &0 < k * p`, SIMP_TAC[REAL_LT_MUL]);;
let NLIN_SCALE_EQ = prove(`forall k p. p = &0 ==> k * p = &0`, SIMP_TAC[REAL_MUL_RZERO]);;
let NLIN_ADD_GE = prove(`forall x y. &0 <= x /\ &0 <= y ==> &0 <= x + y`, SIMP_TAC[REAL_LE_ADD]);;
let NLIN_ADD_GT = REAL_ARITH `forall x y. &0 < x /\ &0 <= y ==> &0 < x + y`;;
let NLIN_ADD_GT2 = REAL_ARITH `forall x y. &0 <= x /\ &0 < y ==> &0 < x + y`;;
let NLIN_ADD_EQ = REAL_ARITH `forall x y. &0 <= x /\ y = &0 ==> &0 <= x + y`;;
let NLIN_ADD_EQ2 = REAL_ARITH `forall x y. &0 < x /\ y = &0 ==> &0 < x + y`;;
let NLIN_EQ_EQ = REAL_ARITH `forall x y. x = &0 /\ y = &0 ==> x + y = &0`;;

(* Combine scaled facts and normalise to a false numeric relation. *)
let nlin_check facts cert =
  let scaled = map (fun (i,c) ->
    let (k,th) = el i facts in
    let ct = term_of_rat c in
    match k with
      Neq -> (Neq, SPEC ct (MATCH_MP NLIN_SCALE_EQ th))
    | Nge -> let pos = EQT_ELIM(REAL_RAT_REDUCE_CONV(mk_binop `(<=):real->real->bool` real_zero ct)) in
             (Nge, MATCH_MP NLIN_SCALE_GE (CONJ pos th))
    | Ngt -> let pos = EQT_ELIM(REAL_RAT_REDUCE_CONV(mk_binop `(<):real->real->bool` real_zero ct)) in
             (Ngt, MATCH_MP NLIN_SCALE_GT (CONJ pos th))) cert in
  let add (k1,t1) (k2,t2) =
    let c = CONJ t1 t2 in
    match k1,k2 with
      Nge,Nge -> (Nge, MATCH_MP NLIN_ADD_GE c)
    | Ngt,Nge -> (Ngt, MATCH_MP NLIN_ADD_GT c)
    | Nge,Ngt -> (Ngt, MATCH_MP NLIN_ADD_GT2 c)
    | Ngt,Ngt -> (Ngt, MATCH_MP NLIN_ADD_GT (CONJ t1 (MATCH_MP REAL_LT_IMP_LE t2)))
    | Nge,Neq -> (Nge, MATCH_MP NLIN_ADD_EQ c)
    | Ngt,Neq -> (Ngt, MATCH_MP NLIN_ADD_EQ2 c)
    | Neq,Nge -> (Nge, MATCH_MP NLIN_ADD_EQ (CONJ t2 t1))
    | Neq,Ngt -> (Ngt, MATCH_MP NLIN_ADD_EQ2 (CONJ t2 t1))
    | Neq,Neq -> (Neq, MATCH_MP NLIN_EQ_EQ c) in
  let (k,th) = end_itlist add scaled in
  let th' = CONV_RULE (RAND_CONV REAL_POLY_CONV) (if k = Neq then
              CONV_RULE (LAND_CONV REAL_POLY_CONV) th else th) in
  EQ_MP (REAL_RAT_REDUCE_CONV (concl th')) th';;

(* Prove F from a list of theorems (facts) using pairwise products and hints. *)
let NLIN_REFUTE ?(deg2=true) ths =
  nlin_atoms := [];
  let base = mapfilter fact_of_thm ths in
  let prods =
    if not deg2 then [] else
    let rec pairs l = match l with
        [] -> []
      | h::t -> map (fun x -> (h,x)) l @ pairs t in
    mapfilter (fun (a,b) -> match mul_facts a b with Some f -> f | None -> failwith "")
      (pairs base) in
  let facts = base @ prods in
  let cert = run_lp facts in
  nlin_check facts cert;;

(* The tactic: uses real-relation assumptions, hint theorems and the negated
   goal (when the goal is a real relation or F). *)
let NLIN_TAC ?(deg2=true) hints (asl,w as g) =
  let ahyps = filter (fun th -> is_real_rel (concl th) ||
                         (is_neg (concl th) && is_real_rel (rand(concl th))))
                     (List.concat (map (fun (_,th) -> CONJUNCTS th) asl)) in
  if w = `false` then
    ACCEPT_TAC (NLIN_REFUTE ~deg2 (hints @ ahyps)) g
  else
    (REFUTE_THEN (fun nth ->
       let nths = match concl nth with
           Comb(Const("~",_),Comb(Comb(Const("=",_),a),b)) ->
             failwith "NLIN_TAC: equality goals are not supported"
         | _ -> [nth] in
       ACCEPT_TAC (NLIN_REFUTE ~deg2 (nths @ hints @ ahyps)))) g;;

(* Hint helpers in the style of nlinarith's arguments. *)
let SQ_NONNEG t = SPEC t REAL_LE_SQUARE;;
let MUL_NONNEG th1 th2 = MATCH_MP REAL_LE_MUL' (CONJ (snd(fact_of_thm th1)) (snd(fact_of_thm th2)));;

(* Goals that are disjunctions of conjunctions of real relations: prove the
   atoms that follow outright, then split on the rest and refute each branch. *)
let rec disj_atoms t =
  if is_disj t then disj_atoms (lhand t) @ disj_atoms (rand t)
  else if is_conj t then disj_atoms (lhand t) @ disj_atoms (rand t)
  else [t];;

let NLIN_TRY hints t (asl,w) =
  try let th = TAC_PROOF((asl,t), NLIN_TAC hints) in
      Some th
  with Failure _ -> None;;

let DISJ_NLIN_TAC ?(split=true) hints (asl,w as g) =
  let atoms = setify (disj_atoms w) in
  let proved = mapfilter (fun t -> match NLIN_TRY hints t g with
                             Some th -> th | None -> failwith "") atoms in
  let rest = filter (fun t -> not (exists (fun th -> aconv (concl th) t) proved)) atoms in
  (MAP_EVERY ASSUME_TAC proved THEN
   MAP_EVERY (fun t -> ASM_CASES_TAC t) rest THEN
   ASM_REWRITE_TAC[] THEN
   (NLIN_TAC hints ORELSE (fun (asl,w) -> failwith ("DISJ_NLIN_TAC branch: " ^
       String.concat "; " (map (fun (_,th) -> string_of_term (concl th)) asl) ^ " |- " ^ string_of_term w)))) g;;

(* Prove a list of facts in order, each added as an assumption for the next. *)
let NLIN_FACTS_TAC hints tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [NLIN_TAC hints ORELSE (fun g -> failwith ("NLIN_FACTS_TAC: " ^ string_of_term t)); ALL_TAC]) tms;;

(* REAL_ARITH on the goal using only the real (in)equality assumptions *)
let RASM_ARITH_TAC (asl,w as g) =
  let hs = filter (fun th -> let t = concl th in
                     is_real_rel t || (is_neg t && is_real_rel (rand t))) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;
