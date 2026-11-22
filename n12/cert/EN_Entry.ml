(* ========================================================================= *)
(* W-ENTRY (n12/docs/cert_design.md §4.3, §9): ownership domains and point       *)
(* premises of the historical entries C701, C713, C717, C973, C978, C979.    *)
(*                                                                           *)
(* Lean (n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact):                         *)
(*   Cases/CK/EntryQueryBase (caseKFamily), EntryQueries / EntryQueryChunks  *)
(*   (DirectSingleDomain, SmallOwnerDomain(.Three).checked), EntryDomains    *)
(*   (CertifiedDomain.ofDirectProduct, SharedLocalQueries.remove /           *)
(*   CertifiedDomain.remove), EntryRefined (refineAgainst, enlarge),         *)
(*   EntryPoints (OwnedHullPoint, CertifiedPoint.ofDomainHull),              *)
(*   RecipeInitial/Inputs + Entry (PointPremises.Check / .sound);            *)
(*   HistoricalOwnership/Queries* (2,193 local queries), C713/EntryQuery*.   *)
(*                                                                           *)
(* Data: n12/data/cert/entry_queries.txt, n12/data/cert/entry_cases.txt, written by  *)
(* the untrusted n12/scripts/cert_extract_entry.py.  Every fact is re-proved:    *)
(* local queries by the Phase-1 checker (localq.ml query_theorem), domains   *)
(* by the PackingContext producers and the theorems below.                   *)
(*                                                                           *)
(* Vocabulary (n12/geometry/PackingContext.ml): the family of a     *)
(* case is the Phase-1 row literal  set_of_list (ROW_LIST ri)  (same set as   *)
(* Lean's caseKFamily), the owner of mask m is the 5-tuple                   *)
(*   (ooc c1 c2 a b l m) (oos ..) (oou ..) (oov ..) l.                       *)
(*                                                                           *)
(* Results (OCaml tables, filled by en_run_case / en_run_all):               *)
(*   en_dom (case, name)   |- cdom fam m al   (Lean CertifiedDomain name)     *)
(*   en_hdom (case, name)  |- hdom fam m k al (Lean DirectSingleDomain name)  *)
(*   en_point (case, name) |- !c1 c2 a b l. NPACK c1 c2 a b l /\              *)
(*                            IMAGE binarysum (FFP c1 c2 a b l) = fam         *)
(*                            ==> linside (owner m) x y   (CertifiedPoint)    *)
(*   en_premises (case, k) |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam        *)
(*                            ==> linside (owner m) P1 /\ .. /\               *)
(*                                ~linside (owner m) Q1 /\ ..                 *)
(*                            (Lean PointPremises.sound for owner k, the      *)
(*                             lists insideK / outsideK expanded in order)    *)
(*   en_entry (case, k)    the same with the owner's square facts in front:   *)
(*        c*c + s*s = &1 /\ &0 < l /\ &1 < l /\ l <= &1001 / &1000 /\        *)
(*        lcont (owner m) /\ <premises>       (the antecedent of §4.3         *)
(*                                             CK_INITIAL.(k), any order)     *)
(*   en_discharge (case, k) th   instantiates  th : |- !c s u v a. A ==> B    *)
(*        at the owner and discharges the conjuncts of A from en_entry:       *)
(*        |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> B[owner]            *)
(*   en_close case th      |- EXCLUDED_ROW ri  from                           *)
(*        th : |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> F              *)
(*                                                                           *)
(* Needs the Phase-1 chain (n12/cases/cs_load.ml: NPACK, step6, localq).     *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/certlib/Convex.ml";;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Lean: CertifiedDomain.refineAgainst, with any list containing the kept   *)
(* entries (the producer uses exactly Lean's filtered list)                  *)
let EN_CDOM_REFINE = prove
 (`forall fam m n al bl al'. cdom fam m al /\ cdom fam n bl /\ n IN fam /\ ~(m = n) /\
     (forall x. MEM x al /\ (exists y. MEM y bl /\ DISJOINT x y) ==> MEM x al')
     ==> cdom fam m al'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cdom] THEN
  DISCH_THEN(fun th -> match CONJUNCTS th with
    [ha; hb; hn; hne; hs] ->
      ASSUME_TAC hn THEN ASSUME_TAC hne THEN
      MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
      STRIP_TAC THEN MATCH_MP_TAC hs THEN CONJ_TAC THENL
       [MATCH_MP_TAC ha THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `auxown 2 ((c1:num->real) (oidx c1 c2 a b l n)) (c2 (oidx c1 c2 a b l n))
                             (a (oidx c1 c2 a b l n)) (b (oidx c1 c2 a b l n)) l` THEN
        SUBGOAL_THEN `ownmask ((c1:num->real) (oidx c1 c2 a b l n)) (c2 (oidx c1 c2 a b l n))
                        (a (oidx c1 c2 a b l n)) (b (oidx c1 c2 a b l n)) l = n` ASSUME_TAC THENL
         [MATCH_MP_TAC OIDX_SPEC THEN EXISTS_TAC `fam:num->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC hb THEN ASM_REWRITE_TAC[OIDX_LT];
          MATCH_MP_TAC PK_COMBINED_DISJOINT THEN ASM_REWRITE_TAC[OIDX_LT] THEN
          DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]]]
  | _ -> failwith "EN_CDOM_REFINE"));;

(* Lean: CertifiedDomain.refineAgainst, verbatim (FILTER form) *)
let EN_REFINE_AGAINST = prove
 (`forall fam m n al bl. cdom fam m al /\ cdom fam n bl /\ n IN fam /\ ~(m = n)
     ==> cdom fam m (FILTER (\x. EX (\y. DISJOINT x y) bl) al)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EN_CDOM_REFINE THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `al:(num->bool)list`; `bl:(num->bool)list`] THEN
  ASM_REWRITE_TAC[MEM_FILTER; GSYM EX_MEM] THEN MESON_TAC[]);;

(* Lean: CertifiedDomain.enlarge *)
let EN_ENLARGE = CDOM_MONO;;

let EN_NOT_DISJOINT = prove
 (`forall x y (e:num). e IN x /\ e IN y ==> ~DISJOINT x y`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Data.                                                                     *)
(* ------------------------------------------------------------------------- *)

let en_lines file =
  let ic = Stdlib.open_in file in
  let rec go acc = match (try Some (input_line ic) with End_of_file -> None) with
      Some l -> go (if String.trim l = "" then acc else String.trim l :: acc)
    | None -> close_in ic; rev acc in
  go [];;
let en_split c s = filter (fun x -> x <> "") (String.split_on_char c s);;
let en_q s = nlin_rat s;;
let en_pt s = match en_split ',' s with [x; y] -> (en_q x, en_q y) | _ -> failwith ("en_pt " ^ s);;
let en_pts s = if s = "-" then [] else map en_pt (en_split ';' s);;
let en_set s = if s = "e" || s = "-" then [] else List.sort compare (map int_of_string (en_split ',' s));;
let en_sets s = if s = "-" then [] else map en_set (en_split ';' s);;

(* the extra local queries, by signature (several certificates per signature allowed) *)
let EN_QDATA = Hashtbl.create 4000;;
let en_load_queries () =
  Hashtbl.reset EN_QDATA;
  List.iter (fun l -> match en_split ' ' l with
      [nm; m; k; ow; ins; outs] ->
        Hashtbl.add EN_QDATA (int_of_string m, int_of_string k, en_set ow) (nm, en_pts ins, en_pts outs)
    | _ -> failwith ("entry_queries: " ^ l)) (en_lines "n12/data/cert/entry_queries.txt");;
en_load_queries ();;

type en_rec =
    Rfam of int list
  | Rsingle of string * int * int * int * int * int list list
  | Rprod of string * string * string
  | Rremove of string * string * int list
  | Rrefine of string * string * string
  | Renlarge of string * string * int list list
  | Rpoint of string * string * (num * num) * (int * int list * (num * num) list * num * num) list
  | Rknown of string list
  | Rowner of int * string * int * string * (num * num) list * (num * num) list;;

let en_witness s = match en_split ':' s with
    [m; ow; p0; p1; p2; tg; ss; tt] -> (int_of_string m, en_set ow, map en_pt [p0; p1; p2; tg], en_q ss, en_q tt)
  | _ -> failwith ("en_witness " ^ s);;

let EN_CASES = Hashtbl.create 10;;
let en_load_cases () =
  Hashtbl.reset EN_CASES;
  List.iter (fun l -> match en_split ' ' l with
      "F" :: c :: [ms] -> Hashtbl.add EN_CASES c (Rfam (map int_of_string (en_split ',' ms)))
    | ["S"; c; nm; m; k; lo; hi; al] ->
        Hashtbl.add EN_CASES c (Rsingle (nm, int_of_string m, int_of_string k, int_of_string lo, int_of_string hi, en_sets al))
    | ["P"; c; nm; a; b] -> Hashtbl.add EN_CASES c (Rprod (nm, a, b))
    | ["R"; c; nm; src; ow; _; _] -> Hashtbl.add EN_CASES c (Rremove (nm, src, en_set ow))
    | ["A"; c; nm; a; b] -> Hashtbl.add EN_CASES c (Rrefine (nm, a, b))
    | ["E"; c; nm; src; al] -> Hashtbl.add EN_CASES c (Renlarge (nm, src, en_sets al))
    | "C" :: c :: nm :: d :: p :: ws -> Hashtbl.add EN_CASES c (Rpoint (nm, d, en_pt p, map en_witness ws))
    | ["K"; c; l] -> Hashtbl.add EN_CASES c (Rknown (en_split ',' l))
    | ["O"; c; k; d; m; tgt; ins; outs] ->
        Hashtbl.add EN_CASES c (Rowner (int_of_string k, d, int_of_string m, tgt, en_pts ins, en_pts outs))
    | _ -> failwith ("entry_cases: " ^ l)) (en_lines "n12/data/cert/entry_cases.txt");;
en_load_cases ();;
(* records of a case, in file order *)
let en_recs c = rev (Hashtbl.find_all EN_CASES c);;

(* ------------------------------------------------------------------------- *)
(* Local queries (Lean: LocalQuery.Check by decide; here re-proved by the    *)
(* Phase-1 checker; the statement only depends on the signature).            *)
(* ------------------------------------------------------------------------- *)

let EN_QFAIL = ref ([] : (int * int * int list) list);;
let en_lq (m, k, owned) =
  try Hashtbl.find LQ_TABLE (m, k, owned) with Not_found ->
  let p1 = filter (fun (_, m', k', o', _, _) -> m' = m && k' = k && o' = owned) LOCAL_QUERIES in
  let ex = map (fun (_, uin, uout) -> (-1, m, k, owned, uin, uout)) (rev (Hashtbl.find_all EN_QDATA (m, k, owned))) in
  let rec go l = match l with
      [] -> EN_QFAIL := (m, k, owned) :: !EN_QFAIL;
            failwith (Printf.sprintf "en_lq: no checkable query for (%d, %d, {%s})" m k
                        (String.concat "," (map string_of_int owned)))
    | q :: r -> (try query_theorem q with Failure _ -> go r) in
  let th = go (p1 @ ex) in
  Hashtbl.replace LQ_TABLE (m, k, owned) th; th;;

let rec en_subsets lo hi l =       (* sorted subsets of l with lo <= size <= hi *)
  let rec all n l = if n = 0 then [[]] else match l with
      [] -> [] | h :: t -> map (fun s -> h :: s) (all (n - 1) t) @ all n t in
  List.concat (map (fun n -> all n l) (lo -- hi));;

(* ------------------------------------------------------------------------- *)
(* Domains.                                                                  *)
(* ------------------------------------------------------------------------- *)

let en_al ls = mk_list(map mk_numset ls, `:num->bool`);;
let en_lists al = map numset_of (dest_list al);;

(* Lean: DirectSingleDomain.Check family k  (SmallOwnerDomain(.Three).checked) and
   DirectSingleDomain.actual, as  |- hdom fam m k al *)
let en_single fam (m, k, lo, hi, allowed) =
  List.iter (fun s -> if not (mem s allowed) then ignore (en_lq (m, k, s))) (en_subsets lo (min hi 10) (0 -- 9));
  let th = spec_theorem m k lo hi allowed in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let (hl, hh) = bound_tms k lo hi in
  let hyps = LQ_HYPS @ [ownp; hl; hh] in
  let th = List.fold_left MP (SPECL SPEC5 th) (map ASSUME hyps) in
  pk_hdom_local fam m k lo hi hyps th (en_al allowed);;

(* |- DISJOINT x y <=> F  or  <=> T  for literal sets *)
let en_disjoint_conv tm =
  let x = lhand tm and y = rand tm in
  let lx = numset_of x and ly = numset_of y in
  match filter (fun e -> mem e ly) lx with
    e :: _ ->
      let ins s = in_fam e s in
      EQF_INTRO (MP (SPECL [x; y; mk_small_numeral e] EN_NOT_DISJOINT) (CONJ (ins x) (ins y)))
  | [] -> (RAND_CONV setlit_conv THENC LAND_CONV setlit_conv THENC disjoint_conv) tm;;

(* Lean: a.refineAgainst b:  |- cdom fam m al'  (al' = Lean's filtered list, in order) *)
let en_refine tha thb =
  let (fam, m, al) = cdom_parts tha and (_, n, bl) = cdom_parts thb in
  if m = n then failwith "en_refine: same mask" else
  let als = dest_list al and bls = dest_list bl in
  let keep x = exists (fun y -> intersect (numset_of x) (numset_of y) = []) bls in
  let al' = mk_list(filter keep als, `:num->bool`) in
  let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n))) in
  let xv = `x:num->bool` and yv = `y:num->bool` in
  let dj x y = mk_comb(mk_comb(`DISJOINT:(num->bool)->(num->bool)->bool`, x), y) in
  let ante x = mk_exists(yv, mk_conj(mk_comb(mk_comb(MEM_TM, yv), bl), dj x yv)) in
  let mem' x = mk_comb(mk_comb(MEM_TM, x), al') in
  (* |- ante x ==> MEM x al'  for a literal entry x of al *)
  let case_x x =
    if keep x then DISCH (ante x) (mem_lit x al') else
    let h = ASSUME (ante x) in
    let y0 = genvar `:num->bool` in
    let body = subst [y0, yv] (snd (dest_exists (ante x))) in
    let hb = ASSUME body in
    let memb = CONV_RULE (REWRITE_CONV[MEM]) (CONJUNCT1 hb) in
    let djb = CONJUNCT2 hb in
    (* cases y0 = b_j *)
    let rec cases th = if is_disj (concl th) then
        let p, q = dest_disj (concl th) in DISJ_CASES th (one (ASSUME p)) (cases (ASSUME q))
      else if concl th = `false` then CONTR (mem' x) th else one th
    and one eq =
      let yb = rhs (concl eq) in
      let f = EQ_MP (en_disjoint_conv (dj x yb)) (SUBS [eq] djb) in
      CONTR (mem' x) f in
    DISCH (ante x) (CHOOSE (y0, h) (cases memb)) in
  (* assemble  !x. MEM x al /\ ante x ==> MEM x al' *)
  let hx = ASSUME (mk_conj(mk_comb(mk_comb(MEM_TM, xv), al), ante xv)) in
  let memx = CONV_RULE (REWRITE_CONV[MEM]) (CONJUNCT1 hx) in
  let rec cases th = if is_disj (concl th) then
      let p, q = dest_disj (concl th) in DISJ_CASES th (one (ASSUME p)) (cases (ASSUME q))
    else if concl th = `false` then CONTR (mem' xv) th else one th
  and one eq =     (* eq: x = s *)
    let s = rhs (concl eq) in
    let th = MP (case_x s) (SUBS [eq] (CONJUNCT2 hx)) in
    EQ_MP (AP_THM (AP_TERM MEM_TM (SYM eq)) al') th in
  let side = GEN xv (DISCH (concl hx) (cases memx)) in
  let th = SPECL [fam; mk_small_numeral m; mk_small_numeral n; al; bl; al' ] EN_CDOM_REFINE in
  MP th (end_itlist CONJ [tha; thb; in_fam n fam; ne; side]);;

(* ------------------------------------------------------------------------- *)
(* Owner vocabulary at a family.                                             *)
(* ------------------------------------------------------------------------- *)

let EN_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let en_hyp fam = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam));;
let en_owner m =
  let mt = mk_small_numeral m in
  map (fun f -> list_mk_comb(f, EN_VARS @ [mt])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let en_lin m (x, y) = list_mk_comb(`linside`, en_owner m @ [term_of_rat x; term_of_rat y]);;

(* rewrite the point of a  [~]linside q x y  theorem to term_of_rat literals *)
let en_canon th =
  let cv t = if is_ratconst t then
      let t' = term_of_rat (rat_of_term t) in
      if t = t' then REFL t else EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_eq(t, t')))
    else failwith "en_canon" in
  let pc = RAND_CONV cv THENC LAND_CONV cv in
  CONV_RULE (if is_neg (concl th) then RAND_CONV pc else pc) th;;

(* the assumption context  hyp |- NPACK .., IMAGE .. = fam *)
let en_ctx fam = let h = ASSUME (en_hyp fam) in (CONJUNCT1 h, CONJUNCT2 h);;

(* split  A |- goal  over the allowed sets of a domain: k (|- ooaux .. m = S) gives
   A, ooaux .. m = S |- goal *)
let en_domain_cases fam dth goal k =
  let (_, m, al) = cdom_parts dth in
  let (hnp, hrow) = en_ctx fam in
  let mem = MATCH_MP CDOM_OWNER (end_itlist CONJ [dth; hnp; hrow; in_fam m fam]) in
  let dj = CONV_RULE (REWRITE_CONV[MEM]) mem in
  let rec cases th = if is_disj (concl th) then
      let p, q = dest_disj (concl th) in DISJ_CASES th (k (ASSUME p)) (cases (ASSUME q))
    else if concl th = `false` then CONTR goal th else k th in
  cases dj;;

(* Lean: query_inside_sound for kind 2 at an assumed owned set (eq: ooaux .. m = S):
   A, eq |- linside (owner m) x y   for P in queryInsidePoints m 2 S *)
let en_known fam m eq p =
  let s = rhs (concl eq) in
  let (hnp, hrow) = en_ctx fam in
  let th = SPECL (EN_VARS @ [fam]) (oo_known m s (term_of_rat (fst p), term_of_rat (snd p))) in
  en_canon (MP th (end_itlist CONJ [hnp; hrow; in_fam m fam; eq]));;

let en_in_query m s p =
  exists (fun q -> qeq p q) (seed_points m) ||
  exists (fun j -> mem j s && qeq (aux2_point j) p) (0 -- 19);;

(* Lean: query_outside_sound for kind 2 (markerOutsidePoints ++ auxOutsidePoints):
   A, eq |- ~linside (owner m) x y *)
let en_out_query fam m eq p =
  let s = numset_of (rhs (concl eq)) in
  let (hnp, hrow) = en_ctx fam in
  try let k = find (fun k -> not (mem k (bits m)) && qeq (marker_q k) p) (0 -- 15) in
      en_canon (MP (SPECL (EN_VARS @ [fam]) (oo_missing m k)) (end_itlist CONJ [hnp; hrow; in_fam m fam]))
  with Failure _ ->
    let j = find (fun j -> not (mem j s) && qeq (aux2_point j) p) (0 -- 19) in
    let ath = SPEC (mk_small_numeral m) (SPECL EN_VARS (oo_aux_point j)) in
    let nin = EQF_ELIM ((RAND_CONV (REWR_CONV eq) THENC RAND_CONV setlit_conv THENC
                         REWRITE_CONV[IN_SET_OF_LIST; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
                        (rand (concl ath))) in
    en_canon (EQ_MP (SYM (AP_TERM `(~)` ath)) nin);;

let en_out_ok m s p =
  exists (fun k -> not (mem k (bits m)) && qeq (marker_q k) p) (0 -- 15) ||
  exists (fun j -> not (mem j s) && qeq (aux2_point j) p) (0 -- 19);;

(* ------------------------------------------------------------------------- *)
(* Certified points (Lean: OwnedHullPoint.sound, CertifiedPoint.ofDomainHull, *)
(* DomainHullCheck).                                                         *)
(* ------------------------------------------------------------------------- *)

let en_pair (x, y) = mk_pair(term_of_rat x, term_of_rat y);;

(* Lean: TriangleCertificate.Check, decided *)
let en_tri_check (p0, p1, p2, tg, s, t) =
  let tm = mk_comb(`tri_cert_check`, list_mk_comb(`TriCert`, map en_pair [p0; p1; p2; tg] @ [term_of_rat s; term_of_rat t])) in
  EQT_ELIM ((REWRITE_CONV[tri_cert_check; FST; SND] THENC REAL_RAT_REDUCE_CONV) tm);;

(* A, eq |- linside (owner m) target  from an OwnedHullPoint witness for owned set S *)
let en_hull_point fam m eq (p0, p1, p2, tg, s, t) =
  let ins = map (en_known fam m eq) [p0; p1; p2] in
  let th = SPECL (map en_pair [p0; p1; p2; tg] @ [term_of_rat s; term_of_rat t] @ en_owner m)
             CVX_TRIANGLE_CERTIFICATE_SOUND in
  let th = CONV_RULE (PURE_REWRITE_CONV[FST; SND]) th in
  en_canon (MP th (end_itlist CONJ (en_tri_check (p0, p1, p2, tg, s, t) :: ins)));;

(* Lean: CertifiedPoint.ofDomainHull d hm point ws hc:
   |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> linside (owner m) x y *)
let en_cpoint fam dth p ws =
  let (_, m, _) = cdom_parts dth in
  let goal = en_lin m p in
  let th = en_domain_cases fam dth goal (fun eq ->
    let s = numset_of (rhs (concl eq)) in
    let (wm, _, pl, ss, tt) = try find (fun (wm, wo, pl, _, _) -> wm = m && wo = s && qeq (el 3 pl) p) ws
      with Failure _ -> failwith "en_cpoint: no witness (DomainHullCheck fails)" in
    let [p0; p1; p2; tg] = pl in
    en_hull_point fam m eq (p0, p1, p2, tg, ss, tt)) in
  if not (aconv (concl th) goal) then failwith "en_cpoint: point" else
  GENL EN_VARS (DISCH (en_hyp fam) th);;

(* ------------------------------------------------------------------------- *)
(* Point premises (Lean: PointPremises.Check d known inside outside and      *)
(* PointPremises.sound).                                                     *)
(*   known: (mask, point, |- !c1 .. l. NPACK .. /\ IMAGE .. = fam ==> linside (owner mask) P) *)
(* ------------------------------------------------------------------------- *)

let en_premises_thm fam dth known inside outside =
  let (_, m, _) = cdom_parts dth in
  let (hnp, hrow) = en_ctx fam in
  let h = CONJ hnp hrow in
  let concl_ins = map (en_lin m) inside and concl_outs = map (fun p -> mk_neg (en_lin m p)) outside in
  let goal = if concl_ins @ concl_outs = [] then `true` else list_mk_conj (concl_ins @ concl_outs) in
  let th = en_domain_cases fam dth goal (fun eq ->
    let s = numset_of (rhs (concl eq)) in
    let ins = map (fun p ->
        if en_in_query m s p then en_known fam m eq p else
        let (_, _, kth) = try find (fun (km, kp, _) -> km = m && qeq kp p) known
          with Failure _ -> failwith "en_premises: inside point not covered" in
        en_canon (MP (SPECL EN_VARS kth) h)) inside in
    let outs = map (fun p ->
        if en_out_ok m s p then en_out_query fam m eq p else
        let (n, _, kth) = try find (fun (km, kp, _) -> km <> m && qeq kp p) known
          with Failure _ -> failwith "en_premises: outside point not covered" in
        en_canon (MP (SPECL EN_VARS (oo_excl fam m n kth)) h)) outside in
    let all = ins @ outs in
    if all = [] then TRUTH else end_itlist CONJ all) in
  if not (aconv (concl th) goal) then failwith "en_premises: shape" else
  GENL EN_VARS (DISCH (en_hyp fam) th);;

(* the owner's square facts *)
let en_square_facts fam m =
  let (hnp, _) = en_ctx fam in
  let mt = mk_small_numeral m in
  let unit = MP (SPECL (EN_VARS @ [mt]) OO_UNIT) hnp in
  let s1 = MP (SPECL EN_VARS OO_SIDE) hnp in
  let s0 = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) s1 in
  let s2 = MP (SPECL EN_VARS OO_SIDE_LE) hnp in
  let box = MP (SPECL (EN_VARS @ [mt]) OO_BOX) hnp in
  [unit; s0; s1; s2; box];;

(* ------------------------------------------------------------------------- *)
(* A case.                                                                   *)
(* ------------------------------------------------------------------------- *)

let EN_DOM = Hashtbl.create 2000;;      (* (case, name) -> |- cdom fam m al *)
let EN_HDOM = Hashtbl.create 200;;      (* (case, name) -> |- hdom fam m k al *)
let EN_POINT = Hashtbl.create 300;;     (* (case, name) -> |- !.. hyp ==> linside (owner m) P *)
let EN_PREMISES = Hashtbl.create 100;;  (* (case, k) -> |- !.. hyp ==> premises *)
let EN_ENTRY = Hashtbl.create 100;;     (* (case, k) -> |- !.. hyp ==> square facts /\ premises *)
let EN_OWNERS = Hashtbl.create 100;;    (* (case, k) -> (mask, domain name, Lean target domain name) *)
let EN_FAMILY = Hashtbl.create 10;;     (* case -> (ri, fam term) *)
let EN_TIMES = Hashtbl.create 10;;

let en_dom k = Hashtbl.find EN_DOM k;;
let en_hdom k = Hashtbl.find EN_HDOM k;;
let en_point k = Hashtbl.find EN_POINT k;;
let en_premises k = Hashtbl.find EN_PREMISES k;;
let en_entry k = Hashtbl.find EN_ENTRY k;;

let en_family c =
  try Hashtbl.find EN_FAMILY c with Not_found ->
  let f = match find (fun r -> match r with Rfam _ -> true | _ -> false) (en_recs c) with
      Rfam f -> List.sort compare f | _ -> failwith "en_family" in
  let ri = try index f (map row_masks (0--576)) with Failure _ -> failwith "en_family: row not found" in
  let fam = mk_comb(`set_of_list:(num)list->num->bool`, ROW_LIST ri) in
  Hashtbl.replace EN_FAMILY c (ri, fam); (ri, fam);;

let en_log s = Printf.printf "%s\n%!" s;;

(* prove all queries a case needs (sequential: the LP oracle is a single process) *)
let en_case_queries c =
  let recs = en_recs c in
  let masks = Hashtbl.create 100 in
  List.iter (fun r -> match r with Rsingle (nm, m, _, _, _, _) -> Hashtbl.replace masks nm m | _ -> ()) recs;
  let sigs = ref [] in
  List.iter (fun r -> match r with
      Rsingle (_, m, k, lo, hi, al) ->
        List.iter (fun s -> if not (mem s al) then sigs := (m, k, s) :: !sigs) (en_subsets lo (min hi 10) (0 -- 9))
    | _ -> ()) recs;
  let sigs = setify !sigs in
  let t0 = Unix.gettimeofday () in
  let nf = ref 0 in
  List.iteri (fun i sg ->
    (try ignore (en_lq sg) with Failure msg -> (incr nf; en_log msg));
    if i mod 200 = 199 then en_log (Printf.sprintf "C%s queries %d/%d (%.0fs)" c (i + 1) (length sigs)
                                       (Unix.gettimeofday () -. t0))) sigs;
  en_log (Printf.sprintf "C%s: %d single-domain queries, %d failed, %.0fs" c (length sigs) !nf
            (Unix.gettimeofday () -. t0));;

let en_run_case c =
  let t0 = Unix.gettimeofday () in
  let (ri, fam) = en_family c in
  en_case_queries c;
  let t1 = Unix.gettimeofday () in
  let recs = en_recs c in
  let dom nm = try Hashtbl.find EN_DOM (c, nm) with Not_found -> failwith ("en: no domain " ^ nm) in
  let known = ref [] in
  let tk = Hashtbl.create 10 in
  let tag r = match r with Rsingle _ -> "single" | Rprod _ -> "product" | Rremove _ -> "remove"
    | Rrefine _ -> "refine" | Renlarge _ -> "enlarge" | Rpoint _ -> "point" | Rowner _ -> "premises"
    | _ -> "other" in
  let rname r = match r with Rsingle (nm, _, _, _, _, _) | Rprod (nm, _, _) | Rremove (nm, _, _)
    | Rrefine (nm, _, _) | Renlarge (nm, _, _) | Rpoint (nm, _, _, _) -> nm
    | Rowner (k, _, _, _, _, _) -> "owner" ^ string_of_int k | _ -> "-" in
  List.iter (fun r -> let ts = Unix.gettimeofday () in (try match r with
      Rsingle (nm, m, k, lo, hi, al) -> Hashtbl.replace EN_HDOM (c, nm) (en_single fam (m, k, lo, hi, al))
    | Rprod (nm, a, b) ->
        Hashtbl.replace EN_DOM (c, nm) (pk_product (Hashtbl.find EN_HDOM (c, a)) (Hashtbl.find EN_HDOM (c, b)))
    | Rremove (nm, src, ow) ->
        let th = dom src in
        let (_, m, _) = cdom_parts th in
        ignore (en_lq (m, 2, ow));
        Hashtbl.replace EN_DOM (c, nm) (pk_remove th (mk_numset ow))
    | Rrefine (nm, a, b) -> Hashtbl.replace EN_DOM (c, nm) (en_refine (dom a) (dom b))
    | Renlarge (nm, src, al) -> Hashtbl.replace EN_DOM (c, nm) (cdom_cache (dom src) (en_al al))
    | Rpoint (nm, d, p, ws) ->
        let th = en_cpoint fam (dom d) p ws in
        let (_, m, _) = cdom_parts (dom d) in
        Hashtbl.replace EN_POINT (c, nm) th;
        known := (m, p, th) :: !known
    | Rknown names ->
        List.iter (fun nm -> if not (Hashtbl.mem EN_POINT (c, nm)) then failwith ("en: known point " ^ nm)) names
    | Rowner (k, d, mask, tgt, ins, outs) ->
        let th = en_premises_thm fam (dom d) (rev !known) ins outs in
        let (_, m, _) = cdom_parts (dom d) in
        if m <> mask then failwith "en: owner mask" else
        Hashtbl.replace EN_PREMISES (c, k) th;
        Hashtbl.replace EN_OWNERS (c, k) (m, d, tgt);
        let (hnp, hrow) = en_ctx fam in
        let pr = MP (SPECL EN_VARS th) (CONJ hnp hrow) in
        let all = end_itlist CONJ (en_square_facts fam m @ [pr]) in
        Hashtbl.replace EN_ENTRY (c, k) (GENL EN_VARS (DISCH (en_hyp fam) all))
    | Rfam _ -> ()
    with Failure msg -> failwith (Printf.sprintf "C%s %s %s: %s" c (tag r) (rname r) msg));
    let (n, t) = try Hashtbl.find tk (tag r) with Not_found -> (0, 0.0) in
    let dt = Unix.gettimeofday () -. ts in
    if dt > 10.0 then en_log (Printf.sprintf "  C%s slow %s record %d: %.1fs" c (tag r) (n + 1) dt);
    Hashtbl.replace tk (tag r) (n + 1, t +. dt)) recs;
  Hashtbl.iter (fun k (n, t) -> en_log (Printf.sprintf "  C%s %s: %d in %.1fs" c k n t)) tk;
  let t2 = Unix.gettimeofday () in
  Hashtbl.replace EN_TIMES c (t1 -. t0, t2 -. t1);
  en_log (Printf.sprintf "C%s done: queries %.0fs, domains/points/premises %.0fs" c (t1 -. t0) (t2 -. t1));;

let EN_CASE_IDS = ["701"; "713"; "717"; "973"; "978"; "979"];;
let en_run_all () = List.iter en_run_case EN_CASE_IDS;;

(* ------------------------------------------------------------------------- *)
(* Composition helpers (the multi-set-domain extension of gen_bridge, in the *)
(* owner vocabulary).                                                        *)
(* ------------------------------------------------------------------------- *)

(* all facts of en_entry (case, k) under the hypothesis *)
let en_entry_facts key =
  let (_, fam) = en_family (fst key) in
  let th = en_entry key in
  let (hnp, hrow) = en_ctx fam in
  CONJUNCTS (MP (SPECL EN_VARS th) (CONJ hnp hrow));;

(* th : |- !c s u v a [more]. A1 /\ .. /\ An ==> B, quantifiers c s u v a first.
   Returns |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> B[owner of (case, k)],
   each Ai found among the entry facts (points compared as rationals) or proved
   by REAL_ARITH from the side facts. *)
let en_discharge key th =
  let (_, fam) = en_family (fst key) in
  let (m, _, _) = Hashtbl.find EN_OWNERS key in
  let facts = en_entry_facts key in
  let th1 = SPECL (en_owner m) th in
  let th1 = SPEC_ALL th1 in
  let ants = conjuncts (lhand (concl th1)) in
  let pt_of t = let args = snd (strip_comb t) in (rat_of_term (el 5 args), rat_of_term (el 6 args)) in
  let is_lin t = is_comb t && fst (strip_comb t) = `linside` in
  let prove_ant a =
    try find (fun f -> aconv (concl f) a) facts with Failure _ ->
    let neg = is_neg a in
    let core = if neg then rand a else a in
    if is_lin core then
      let f = find (fun f -> let c = concl f in
                     (is_neg c = neg) && (let cc = if neg then rand c else c in
                      is_lin cc && fst (chop_list 5 (snd (strip_comb cc))) = en_owner m &&
                      qeq (pt_of cc) (pt_of core))) facts in
      f
    else
      let rels = filter (fun f -> is_real_rel (concl f)) facts in
      MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), a))) (end_itlist CONJ rels) in
  let prove_ant a =
    let f = prove_ant a in
    if aconv (concl f) a then f else
    EQ_MP (EQT_ELIM ((REWRITE_CONV[] THENC REAL_RAT_REDUCE_CONV THENC REWRITE_CONV[]) (mk_eq(concl f, a)))) f in
  let r = MP th1 (end_itlist CONJ (map prove_ant ants)) in
  GENL EN_VARS (DISCH (en_hyp fam) r);;

(* |- EXCLUDED_ROW ri  from  |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> F *)
let en_close c th =
  let (ri, fam) = en_family c in
  let f = MP (SPECL EN_VARS th) (ASSUME (en_hyp fam)) in
  (ri, excluded_of_false ri (en_hyp fam) f);;

(* ------------------------------------------------------------------------- *)
(* gen_bridge for multi-set domains, in the owner vocabulary (§4.3, §4.5).    *)
(*   en_case_template c masks extras tmpl                                    *)
(* tmpl : |- !sq_1 .. sq_k. P1 /\ .. /\ Pn ==> F   (each square five reals,   *)
(*        in the order c s u v a; square j is instantiated with the owner of  *)
(*        masks_j).  Premises are discharged by kind:                         *)
(*   lsquare / lcont (OO_LSQUARE / OO_BOX), ldisj (oo_apart),                 *)
(*   linside at a point: an entry premise or certified point of that owner    *)
(*     (every allowed owned set of its domain was checked, en_premises_thm),  *)
(*   ~linside at a point: an entry premise of that owner, or a certified      *)
(*     point of another owner (oo_excl),                                      *)
(*   any other fact: one of  extras  (|- !c1 c2 a b l. hyp ==> P), or         *)
(*     REAL_ARITH from the owners' square facts (unit normals, side bounds).  *)
(* Result: |- EXCLUDED_ROW ri (with ri, as en_close).  en_case_bridge: the    *)
(* same for any conclusion B:  |- !c1 c2 a b l. hyp ==> B[owners].           *)
(* ------------------------------------------------------------------------- *)

let en_case_bridge c masks extras tmpl =
  let (ri, fam) = en_family c in
  let (hnp, hrow) = en_ctx fam in
  let h = CONJ hnp hrow in
  let under th = MP (SPECL EN_VARS th) h in
  let entries = Hashtbl.fold (fun (c', k) (m, _, _) acc -> if c' = c then (m, (c', k)) :: acc else acc) EN_OWNERS [] in
  let points = Hashtbl.fold (fun (c', nm) th acc -> if c' = c then th :: acc else acc) EN_POINT [] in
  let point_mask th = let t = snd (strip_forall (concl th)) in
    dest_small_numeral (last (snd (strip_comb (hd (snd (strip_comb (rand t))))))) in
  let pool = List.concat (map (fun (m, key) -> en_entry_facts key) entries) @ map under points @
             map under extras @ List.concat (map (en_square_facts fam) (setify masks)) in
  let inst = SPECL (List.concat (map en_owner masks)) tmpl in
  let ants = conjuncts (lhand (concl inst)) in
  let is_lin t = is_comb t && fst (strip_comb t) = `linside` in
  let lin_parts t = let args = snd (strip_comb t) in
    (fst (chop_list 5 args), (rat_of_term (el 5 args), rat_of_term (el 6 args))) in
  let mask_of q = try find (fun m -> en_owner m = q) (setify masks)
                  with Failure _ -> failwith "en_case_template: not an owner square" in
  let conv_to f a = if aconv (concl f) a then f else
    EQ_MP (EQT_ELIM ((REWRITE_CONV[] THENC REAL_RAT_REDUCE_CONV THENC REWRITE_CONV[]) (mk_eq(concl f, a)))) f in
  let find_lin neg q p = find (fun f -> let cc = concl f in is_neg cc = neg &&
      (let core = if neg then rand cc else cc in is_lin core &&
        (let (q', p') = lin_parts core in q' = q && qeq p p'))) pool in
  let prove_ant a =
    try find (fun f -> aconv (concl f) a) pool with Failure _ ->
    let neg = is_neg a in
    let core = if neg then rand a else a in
    let (hd, args) = strip_comb core in
    if is_lin core then
      let (q, p) = lin_parts core in
      (try conv_to (find_lin neg q p) a with Failure _ ->
       if not neg then failwith ("en_case_template: no fact " ^ string_of_term a) else
       let m = mask_of q in
       let pth = find (fun th -> let t = rand (snd (strip_forall (concl th))) in
                    let (_, p') = lin_parts t in qeq p p' && point_mask th <> m) points in
       conv_to (under (oo_excl fam m (point_mask pth) pth)) a)
    else if hd = `lsquare` then MP (SPECL (EN_VARS @ [mk_small_numeral (mask_of args)]) OO_LSQUARE) hnp
    else if hd = `lcont` then MP (SPECL (EN_VARS @ [mk_small_numeral (mask_of args)]) OO_BOX) hnp
    else if hd = `ldisj` then
      let (q1, q2) = chop_list 5 args in
      under (oo_apart fam (mask_of q1) (mask_of q2))
    else
      let rels = filter (fun f -> is_real_rel (concl f)) pool in
      MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), a))) (end_itlist CONJ rels) in
  let prove_ant a = try prove_ant a with Failure msg ->
    failwith (Printf.sprintf "en_case_template C%s premise %s: %s" c (string_of_term a) msg) in
  GENL EN_VARS (DISCH (en_hyp fam) (MP inst (end_itlist CONJ (map prove_ant ants))));;
let en_case_template c masks extras tmpl = en_close c (en_case_bridge c masks extras tmpl);;
