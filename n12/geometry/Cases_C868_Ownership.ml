(* ========================================================================= *)
(* Port of Compact/Cases/C868/Ownership.lean (N12Compact.C868, Jatloe).      *)
(* Nine original ownership domains of the C868 family; seven forced          *)
(* auxiliary memberships (ForcedAuxiliary.contains = fa_contains).           *)
(* Lean private domain1 .. domain512 are the cdom theorems C868OW_DOMAIN*:   *)
(*   MergedLower.direct = mlh_direct, MergedLower.halfturned = mlh_halfturned,*)
(*   OwnerBudget.product = pk_product, HalfDomain.ofSeedHull =               *)
(*   pk_hdom_seedhull, ofSmallBudgetWithSeed = ro_small_budget_seed.         *)
(* Lean  owner p mask := p.square (ownerIndex p mask)  is the OriginalOwners *)
(* 5-tuple (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l.                    *)
(* Lean statements indexed by i : Fin 7 are OCaml arrays (index i) of        *)
(* theorems.  domains_members / domains_distinct are checked by fa_search    *)
(* (in_fam, distinct masks) and stated as C868OW_DOMAINS_MEMBERS.            *)
(* Tag C868OW_ / c868ow_.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/Helpers.ml";;
needs "n12/geometry/ForcedAuxiliary.ml";;

let C868OW_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* Lean: family *)
let c868_family = new_definition
 `c868_family = {1,2,12,16,192,256,512,3072,4096,8192,16416,32768}`;;
let C868OW_F = `c868_family`;;

let c868ow_rat s = nlin_rat s;;

(* Lean: domain1, domain2, domain16, domain4096, domain8192, domain16416,
   domain32768, domain256, domain512 (private) *)
let C868OW_DOMAIN1 = mlh_direct C868OW_F 1;;
let C868OW_DOMAIN2 = mlh_direct C868OW_F 3;;
let C868OW_DOMAIN16 = mlh_halfturned C868OW_F 16 1;;
let C868OW_DOMAIN4096 = mlh_direct C868OW_F 17;;
let C868OW_DOMAIN8192 = mlh_direct C868OW_F 19;;
let C868OW_DOMAIN16416 =
  pk_product
    (pk_hdom_seedhull C868OW_F 16416 0 9
       ([(num 3, c868ow_rat "9/4"); (num 3, c868ow_rat "11/4"); (num 3, c868ow_rat "9/4")],
        (num 3, c868ow_rat "113/50"), c868ow_rat "1/50", num 0))
    (ro_small_budget_seed C868OW_F 16416 1 9
       ([(num 3, c868ow_rat "9/4"); (num 3, c868ow_rat "11/4"); (num 3, c868ow_rat "9/4")],
        (num 3, c868ow_rat "12/5"), c868ow_rat "3/10", num 0));;
let C868OW_DOMAIN32768 = mlh_direct C868OW_F 24;;
let C868OW_DOMAIN256 = mlh_direct C868OW_F 6;;
let C868OW_DOMAIN512 = mlh_direct C868OW_F 8;;

(* Lean: domains *)
let C868OW_DOMAINS =
  [C868OW_DOMAIN1; C868OW_DOMAIN2; C868OW_DOMAIN16; C868OW_DOMAIN4096; C868OW_DOMAIN8192;
   C868OW_DOMAIN16416; C868OW_DOMAIN32768; C868OW_DOMAIN256; C868OW_DOMAIN512];;

(* Lean: domains_members, domains_distinct *)
let C868OW_DOMAINS_MEMBERS =
  let ms = map cdom_mask C868OW_DOMAINS in
  if length (setify ms) <> length ms then failwith "C868OW: domains not distinct" else
  end_itlist CONJ (map (fun m -> in_fam m C868OW_F) ms);;

(* Lean: pointClaims *)
let C868OW_POINT_CLAIMS = [(256,4); (256,13); (32768,14); (1,2); (2,10); (1,12); (2,0)];;

(* Lean: pointClaims_checked + forced_point  (index i of pointClaims):
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = c868_family
        ==> j IN ooaux c1 c2 a b l m *)
let C868OW_FORCED_POINT =
  Array.of_list (map (fun (m, j) -> fa_contains C868OW_F C868OW_DOMAINS m j) C868OW_POINT_CLAIMS);;

(* Lean: seed_inside (at a literal mask and literal seed point):
   |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = c868_family ==> linside (owner m) x y *)
let c868_seed m p = oo_inst C868OW_F (oo_seed m p);;

(* Lean: apart (literal masks):  |- !c1 .. l. NPACK .. /\ IMAGE .. = c868_family ==> ldisj (owner m) (owner n) *)
let c868_apart m n = oo_apart C868OW_F m n;;

(* a point owned by n is not inside owner m (Lean: apart applied to an owned point) *)
let c868_excl m n thn = oo_excl C868OW_F m n thn;;

(* owner point from a membership  |- !c1 .. l. H ==> j IN ooaux c1 c2 a b l m *)
let c868_point_of_mem th =
  let th1 = SPECL C868OW_VARS th in
  let hyp = lhand (concl th1) in
  let mem = MP th1 (ASSUME hyp) in
  let j = lhand (concl mem) and m = rand (rand (concl mem)) in
  let pt = SPECL (C868OW_VARS @ [m]) (oo_aux_point (dest_small_numeral j)) in
  GENL C868OW_VARS (DISCH hyp (EQ_MP (SYM pt) mem));;

(* Lean: forced_inside  (index i of pointClaims):
   |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = c868_family ==> linside (owner m) x_j y_j *)
let C868OW_FORCED_INSIDE = Array.map c868_point_of_mem C868OW_FORCED_POINT;;

(* ------------------------------------------------------------------------- *)
(* Toolkit for the C868 packing-level files: facts are theorems with the     *)
(* single hypothesis C868_H; c868_gen discharges and generalises.            *)
(* ------------------------------------------------------------------------- *)

let C868_H = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family`;;
let c868_mp th = MP (SPECL C868OW_VARS th) (ASSUME C868_H);;
let c868_gen th = GENL C868OW_VARS (DISCH C868_H th);;
let c868_own m =
  map (fun f -> list_mk_comb(f, C868OW_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let C868_NP = CONJUNCT1 (ASSUME C868_H);;
let C868_SIDE = MP (SPECL C868OW_VARS OO_SIDE) C868_NP;;
let C868_POS = MP (REAL_ARITH `&1 < l ==> &0 < l`) C868_SIDE;;
let C868_SIDE_LE = MP (SPECL C868OW_VARS OO_SIDE_LE) C868_NP;;
let c868_unit m = MP (SPECL (C868OW_VARS @ [mk_small_numeral m]) OO_UNIT) C868_NP;;
let c868_box m = MP (SPECL (C868OW_VARS @ [mk_small_numeral m]) OO_BOX) C868_NP;;

(* facts under C868_H *)
let c868_seed_f m p = c868_mp (c868_seed m p);;
let c868_apart_f m n = c868_mp (c868_apart m n);;
(* ~ point of owner m from a fact  linside (owner n) x y  (under C868_H) *)
let c868_excl_f m n thn = c868_mp (c868_excl m n (c868_gen thn));;
let c868_forced_f i = c868_mp C868OW_FORCED_INSIDE.(i);;

(* owner mask of a term (ooc c1 c2 a b l m) *)
let c868_mask_of t =
  match strip_comb t with (f, args) when length args = 6 -> dest_small_numeral (el 5 args)
  | _ -> failwith "c868_mask_of";;

(* automatic side conditions of geometry lemmas applied to owners *)
let c868_auto t =
  if t = `&0 < l` then C868_POS else
  if t = `&1 < l` then C868_SIDE else
  if t = `l <= &1001 / &1000` then C868_SIDE_LE else
  if is_eq t && lhs t = rhs t then REFL (lhs t) else
  match strip_comb t with
    (f, c :: _) when f = `lcont` -> c868_box (c868_mask_of c)
  | (f, args) when f = `ldisj` && length args = 10 ->
      c868_apart_f (c868_mask_of (el 0 args)) (c868_mask_of (el 5 args))
  | _ ->
      if is_eq t && rhs t = `&1` then
        let ot = find_term (fun u -> is_comb u && (fst (strip_comb u) = `ooc` || fst (strip_comb u) = `oos`)) t in
        let u = c868_unit (c868_mask_of ot) in
        MP (prove(mk_imp(concl u, t), CONV_TAC REAL_RING)) u
      else failwith "c868_auto";;

let is_ineq t = is_binop `(<):real->real->bool` t || is_binop `(<=):real->real->bool` t;;

(* MP a lemma (already specialised) against facts / automatic side conditions *)
let c868_discharge facts th =
  let ant = lhand (concl th) in
  let prove1 t =
    try find (fun f -> aconv (concl f) t) facts with Failure _ ->
    try c868_auto t with Failure _ ->
    try EQT_ELIM (REAL_RAT_REDUCE_CONV t) with Failure _ ->
    try (if is_eq t && rhs t = `&1` then
           tryfind (fun f -> if is_eq (concl f) && rhs (concl f) = `&1` then
                               MP (prove(mk_imp(concl f, t), CONV_TAC REAL_RING)) f else fail()) facts
         else fail()) with Failure _ ->
    try (if is_ineq t then
           let ls = filter (fun f -> is_ineq (concl f) || (is_eq (concl f) && type_of (lhand (concl f)) = `:real`)) facts in
           MP (REAL_ARITH (mk_imp(list_mk_conj (map concl ls), t))) (end_itlist CONJ ls)
         else fail()) with Failure _ ->
    failwith ("c868_discharge: " ^ string_of_term t) in
  let rec build t = if is_conj t then
      (try prove1 t with Failure _ -> CONJ (build (lhand t)) (build (rand t)))
    else prove1 t in
  MP th (build ant);;

(* apply a lemma to a list of terms (squares and points) *)
let c868_apply lemma args facts = c868_discharge facts (SPECL args lemma);;

(* |- !vars extra. NPACK .. /\ IMAGE .. = c868_family /\ h1 /\ .. /\ hk ==> concl
   from a fact th with hypotheses among C868_H, h1, .., hk *)
let c868_genx extra hs th =
  if hs = [] then GENL (C868OW_VARS @ extra) (DISCH C868_H th) else
  let ant = mk_conj(`NPACK c1 c2 a b l`, list_mk_conj (`IMAGE binarysum (FFP c1 c2 a b l) = c868_family` :: hs)) in
  let a = ASSUME ant in
  let hh = CONJ (CONJUNCT1 a) (CONJUNCT1 (CONJUNCT2 a)) in
  let rec parts a n = if n = 1 then [a] else CONJUNCT1 a :: parts (CONJUNCT2 a) (n - 1) in
  let ps = hh :: parts (CONJUNCT2 (CONJUNCT2 a)) (length hs) in
  GENL (C868OW_VARS @ extra) (DISCH ant (itlist PROVE_HYP ps th));;

(* the displayed (faithful) statement must be exactly the derived theorem *)
let c868_check stmt th =
  if aconv (concl th) stmt && hyp th = [] then th else
  (print_thm th; print_newline ();
   failwith ("c868_check: statement mismatch: " ^ string_of_term stmt));;

(* parameters of pullX / pullY / pullSwap of a square (LINSIDE_PULLX/Y/SW) *)
let c868_pull lth sq =
  let t = lhs (snd (strip_forall (concl (SPECL (sq @ [`x:real`; `y:real`]) lth)))) in
  let args = snd (strip_comb t) in
  [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args];;
let c868_pullx = c868_pull LINSIDE_PULLX;;
let c868_pully = c868_pull LINSIDE_PULLY;;
let c868_pullsw = c868_pull LINSIDE_PULLSW;;
(* rewrite pulled memberships back to the original square, numerals reduced *)
let C868_PULL_RULE = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) o
  REWRITE_RULE[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW];;

(* transfer through  iff : |- !x y. linside A x y <=> linside (owner m) x y  *)
let c868_xy t = let args = snd (strip_comb t) in (el 5 args, el 6 args);;
let c868_to iff th =
  let t = concl th in
  if is_neg t then let (x, y) = c868_xy (rand t) in
    EQ_MP (AP_TERM `(~)` (SYM (SPECL [x; y] iff))) th
  else let (x, y) = c868_xy t in EQ_MP (SYM (SPECL [x; y] iff)) th;;
let c868_back iff th =
  let t = concl th in
  if is_neg t then let (x, y) = c868_xy (rand t) in
    EQ_MP (AP_TERM `(~)` (SPECL [x; y] iff)) th
  else let (x, y) = c868_xy t in EQ_MP (SPECL [x; y] iff) th;;
(* prove goal from theorems ths (possibly with hypotheses): tac runs with their
   conclusions as assumptions *)
let c868_prove ths goal tac =
  let g = itlist (fun th t -> mk_imp(concl th, t)) ths goal in
  let pg = prove(g, REPEAT DISCH_TAC THEN tac) in
  rev_itlist (fun th acc -> MP acc th) ths pg;;
(* ldisj A B from ldisj of the owners, through the iffs (an iff may be absent: pass None) *)
let c868_disj_tr iffa iffb d goal =
  let rw = match iffa, iffb with Some p, Some q -> [p; q] | Some p, None -> [p] | None, Some q -> [q] | _ -> [] in
  c868_prove (rw @ [REWRITE_RULE[ldisj] d]) goal (REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[]);;
(* F from linside (owner m) x y and linside (owner n) x y *)
let c868_clash m n thm thn =
  let (x, y) = c868_xy (concl thm) in
  let d = SPECL [x; y] (REWRITE_RULE[ldisj] (c868_apart_f m n)) in
  MP (NOT_ELIM d) (CONJ thm thn);;
