(* ========================================================================= *)
(* Phase 2 helper: original-packing entries of the Bridge case lemmas        *)
(* (Compact/Bridge/{FourSquareCaseHighRight, FourSquareConvexCase,           *)
(*  MidpointCase, EndpointHighRightCase, OwnerSegmentCrossing}.lean).        *)
(*                                                                           *)
(* Lean data  d : Data  (transform, masks i, owned i, ...) with a decidable  *)
(* Check  becomes OCaml data; the producers below re-check every Check       *)
(* condition while building the kernel proof (a failure = Lean decide fails) *)
(* and return                                                                *)
(*   |- !c1 c2 a b l. NPACK c1 c2 a b l /\                                  *)
(*        IMAGE binarysum (FFP c1 c2 a b l) = fam /\                        *)
(*        ooaux c1 c2 a b l m_0 = S_0 /\ .. /\ ooaux c1 c2 a b l m_k = S_k   *)
(*        ==> F                                                              *)
(* (ooaux c1 c2 a b l m = natCombinedOwners p (ownerIndex p m), by           *)
(* definition).  Lean  q i = d.transform.pull (p.square (ownerIndex p m_i))  *)
(* is pull_params trf (owner 5-tuple of m_i), trf = (swap, reflectX,         *)
(* reflectY) as in gen_bridge.ml.  Point facts are stated for the pulled     *)
(* squares at template coordinates P and proved at the base point T(P)       *)
(* (Lean rat_inside_transform):                                             *)
(*   ob_inside   T(P) in queryInsidePoints m 2 S   (query_inside_sound)     *)
(*   ob_outside  T(P) in queryOutsidePoints m 2 S  (query_outside_sound)    *)
(*   ob_barrier  T(P) in seedPoints (maskSupport n), n in fam, n <> m        *)
(*   ob_hull     a TriangleCertificate over queryInsidePoints (Convex.lean)  *)
(*   ob_segment  S12.inside_segment on a pulled square                       *)
(*   ob_foreign  a point inside another (apart) pulled square                *)
(* ob_apply discharges the premises of a template theorem from these facts   *)
(* (lsquare, side relations, lcont, ldisj, lclosed, linside, ~linside).      *)
(* Tag OB_.                                                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/gen_bridge.ml";;

let OB_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* Lean: S12.inside_segment *)
let OB_LINSIDE_SEGMENT = prove
 (`forall c s u v a x0 y0 x1 y1 t.
      linside c s u v a x0 y0 /\ linside c s u v a x1 y1 /\ &0 <= t /\ t <= &1
      ==> linside c s u v a ((&1 - t) * x0 + t * x1) ((&1 - t) * y0 + t * y1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c * ((&1 - t) * x0 + t * x1) + s * ((&1 - t) * y0 + t * y1) =
      (&1 - t) * (c * x0 + s * y0) + t * (c * x1 + s * y1) /\
    --s * ((&1 - t) * x0 + t * x1) + c * ((&1 - t) * y0 + t * y1) =
      (&1 - t) * (--s * x0 + c * y0) + t * (--s * x1 + c * y1)`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC REAL_CONVEX_BOUND_LT ORELSE MATCH_MP_TAC REAL_CONVEX_BOUND_GT) THEN
  ASM_REAL_ARITH_TAC);;

let ob_rat s = term_of_rat (nlin_rat s);;
let ob_pt (x, y) = (ob_rat x, ob_rat y);;

(* the owner 5-tuple of mask m *)
let ob_owner m = map (fun f -> list_mk_comb(f, OB_VARS @ [mk_small_numeral m]))
                   [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;

(* hypothesis  NPACK .. /\ IMAGE .. = fam /\ ooaux m_0 = S_0 /\ ..  *)
let ob_hyp fam owned =
  list_mk_conj ([`NPACK c1 c2 a b l`; mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)] @
                map (fun (m, s) -> mk_eq(ooaux_tm m, s)) owned);;

type obctx = { obfam : term; obhyp : term; obnp : thm; obrow : thm;
               obeqs : (int * thm) list; obtrf : bool * bool * bool };;

let ob_ctx fam trf owned =
  let hyp = ob_hyp fam owned in
  let cs = CONJUNCTS (ASSUME hyp) in
  { obfam = fam; obhyp = hyp; obnp = el 0 cs; obrow = el 1 cs;
    obeqs = map2 (fun (m, _) th -> (m, th)) owned (tl (tl cs)); obtrf = trf };;

let ob_eq ctx m = try assoc m ctx.obeqs with Failure _ -> failwith (Printf.sprintf "ob: no owned set for %d" m);;
let ob_inf ctx m = in_fam m ctx.obfam;;

(* rebuild  |- [~]linside p x' y'  at equal rational coordinates x y *)
let ob_align th (x, y) =
  let neg = is_neg (concl th) in
  let t = if neg then rand (concl th) else concl th in
  let x' = rand (rator t) and y' = rand t in
  let req a b = if a = b then REFL a else EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_eq(a, b))) in
  let eq = MK_COMB(AP_TERM (rator (rator t)) (req x' x), req y' y) in
  EQ_MP (if neg then AP_TERM `(~)` eq else eq) th;;

(* base point of a template point *)
let ob_base_eq ctx m (x, y) = pull_point_eq ctx.obtrf (ob_owner m) (x, y);;
let ob_base_pt peq = let args = snd (strip_comb (rand (concl peq))) in (el 5 args, el 6 args);;

(* base fact -> pulled fact at the template point (x, y) *)
let ob_pull ctx m (x, y) basef =
  let peq = ob_base_eq ctx m (x, y) in
  let bth = ob_align (basef (ob_base_pt peq)) (ob_base_pt peq) in
  if is_neg (concl bth) then EQ_MP (SYM (AP_TERM `(~)` peq)) bth else EQ_MP (SYM peq) bth;;

(* base: T(P) in queryInsidePoints m 2 S  ==>  linside (owner m) T(P) *)
let ob_known_base ctx m (bx, by) =
  let eq = ob_eq ctx m in
  let th = SPECL (OB_VARS @ [ctx.obfam]) (oo_known m (rand (concl eq)) (bx, by)) in
  MP th (end_itlist CONJ [ctx.obnp; ctx.obrow; ob_inf ctx m; eq]);;

(* base: T(P) in queryOutsidePoints m 2 S  ==>  ~linside (owner m) T(P) *)
let ob_outside_base ctx m (bx, by) =
  let p = (rat_of_term bx, rat_of_term by) in
  let eq = ob_eq ctx m in
  try let k = find (fun k -> not (mem k (bits m)) && qeq (marker_q k) p) (0 -- 15) in
      let th = SPECL (OB_VARS @ [ctx.obfam]) (oo_missing m k) in
      CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
        (MP th (end_itlist CONJ [ctx.obnp; ctx.obrow; ob_inf ctx m]))
  with Failure _ ->
  let s = numset_of (rand (concl eq)) in
  let j = try find (fun j -> not (mem j s) && qeq (aux2_point j) p) (0 -- 19)
          with Failure _ -> failwith (Printf.sprintf "ob_outside %d: (%s, %s) not in queryOutsidePoints"
                                        m (string_of_term bx) (string_of_term by)) in
  let ath = SPEC (mk_small_numeral m) (SPECL OB_VARS (oo_aux_point j)) in
  let nin = EQF_ELIM ((RAND_CONV (REWR_CONV eq) THENC RAND_CONV setlit_conv THENC
                       REWRITE_CONV[IN_SET_OF_LIST; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
                      (rand (concl ath))) in
  let th = EQ_MP (SYM (AP_TERM `(~)` ath)) nin in
  CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) th;;

(* base: T(P) in seedPoints (maskSupport n), n in fam, m <> n  ==>  ~linside (owner m) T(P) *)
let ob_barrier_base ctx m n (bx, by) =
  let th = oo_excl ctx.obfam m n (oo_inst ctx.obfam (oo_seed n (bx, by))) in
  MP (SPECL OB_VARS th) (CONJ ctx.obnp ctx.obrow);;

(* base: a triangle certificate (p0, p1, p2, target, s, t) over queryInsidePoints *)
let ob_hull_base ctx m (p0, p1, p2, tg, s, t) (bx, by) =
  let p0 = ob_pt p0 and p1 = ob_pt p1 and p2 = ob_pt p2 and tg = ob_pt tg in
  let s = ob_rat s and t = ob_rat t in
  if rat_of_term (fst tg) <>/ rat_of_term bx || rat_of_term (snd tg) <>/ rat_of_term by
  then failwith "ob_hull: target" else
  let k0 = ob_known_base ctx m p0 and k1 = ob_known_base ctx m p1 and k2 = ob_known_base ctx m p2 in
  let le a b = EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_binop `(<=):real->real->bool` a b)) in
  let seg th0 th1 w = MATCH_MP OB_LINSIDE_SEGMENT (end_itlist CONJ [th0; th1; le `&0` w; le w `&1`]) in
  let h = seg (seg k0 k1 s) k2 t in
  let h = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) h in
  ob_align h (bx, by);;

(* fact table: (pulled params, rational point, |- [~]linside pulled x y) *)
type obfacts = (term list * (num * num) * thm) list ref;;

let ob_params ctx m = pull_params ctx.obtrf (ob_owner m);;
let ob_add ctx (fs : obfacts) m th =
  let t = if is_neg (concl th) then rand (concl th) else concl th in
  let args = snd (strip_comb t) in
  fs := (ob_params ctx m, (rat_of_term (el 5 args), rat_of_term (el 6 args)), th) :: !fs;;

let ob_inside ctx fs m p = let (x, y) = ob_pt p in
  ob_add ctx fs m (ob_pull ctx m (x, y) (ob_known_base ctx m));;
let ob_outside ctx fs m p = let (x, y) = ob_pt p in
  ob_add ctx fs m (ob_pull ctx m (x, y) (ob_outside_base ctx m));;
let ob_barrier ctx fs m n p = let (x, y) = ob_pt p in
  ob_add ctx fs m (ob_pull ctx m (x, y) (ob_barrier_base ctx m n));;
(* Lean inside with a hull alternative: queryInsidePoints, else one of the certificates *)
let ob_inside_or_hull ctx fs m hulls p = let (x, y) = ob_pt p in
  ob_add ctx fs m (ob_pull ctx m (x, y) (fun bp ->
    try ob_known_base ctx m bp with Failure _ ->
    tryfind (fun w -> ob_hull_base ctx m w bp) hulls));;

let ob_find ctx (fs : obfacts) m neg p =
  let ps = ob_params ctx m in
  try let (_, _, th) = find (fun (ps', q, th) -> ps' = ps && qeq q p && is_neg (concl th) = neg) !fs in th
  with Failure _ -> failwith (Printf.sprintf "ob: no %sfact for mask %d at (%s, %s)"
                       (if neg then "negative " else "") m (string_of_num (fst p)) (string_of_num (snd p)));;

(* S12.inside_segment on the pulled square of m between two known points *)
let ob_segment ctx fs m p0 p1 t =
  let r (x, y) = (nlin_rat x, nlin_rat y) in
  let h0 = ob_find ctx fs m false (r p0) and h1 = ob_find ctx fs m false (r p1) in
  let tt = ob_rat t in
  let le a b = EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_binop `(<=):real->real->bool` a b)) in
  let h = MATCH_MP OB_LINSIDE_SEGMENT (end_itlist CONJ [h0; h1; le `&0` tt; le tt `&1`]) in
  let h = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) h in
  ob_add ctx fs m h;;

(* ldisj of the pulled squares of m and n (Lean apart; checks m <> n) *)
let ob_ldisj ctx m n =
  let th = MP (SPECL OB_VARS (oo_apart ctx.obfam m n)) (CONJ ctx.obnp ctx.obrow) in
  itlist (fun g th -> MATCH_MP (LDISJ_PULL g) th) (rev (gens_of ctx.obtrf)) th;;

(* ~linside (pulled m) P from linside (pulled n) P (Lean: apart m n) *)
let ob_foreign ctx fs m n p =
  let pn = ob_find ctx fs n false (let (x, y) = p in (nlin_rat x, nlin_rat y)) in
  let args = snd (strip_comb (concl pn)) in
  let d = SPECL [el 5 args; el 6 args] (REWRITE_RULE[ldisj] (ob_ldisj ctx m n)) in
  let a = lhand (rand (concl d)) in
  ob_add ctx fs m (NOT_INTRO (DISCH a (MP (NOT_ELIM d) (CONJ (ASSUME a) pn))));;

(* discharge the premises of  tmpl |- !sq_0 .. sq_k [extra]. prems ==> F  at the pulled
   squares of the role masks; returns  ctx.obhyp |- F *)
let ob_apply ctx fs tmpl roles extra =
  let params = map (ob_params ctx) roles in
  let tmpl_i = SPECL (List.concat params @ extra) tmpl in
  let prems = conjuncts (lhand (concl tmpl_i)) in
  let role ps = try find (fun m -> ob_params ctx m = ps) roles with Failure _ -> failwith "ob_apply: role" in
  let base_rel m = let np = ctx.obnp in
    let unit = MP (SPECL (OB_VARS @ [mk_small_numeral m]) OO_UNIT) np in
    [unit; MP (SPECL OB_VARS OO_SIDE) np; MP (SPECL OB_VARS OO_SIDE_LE) np] in
  let rels = List.concat (map base_rel (setify roles)) in
  let arith t = MP (REAL_ARITH (mk_imp(list_mk_conj (map concl rels), t))) (end_itlist CONJ rels) in
  let pt args = (rat_of_term (el 5 args), rat_of_term (el 6 args)) in
  let prove_prem t =
    let neg = is_neg t in
    let u = if neg then rand t else t in
    let (hd, args) = strip_comb u in
    let name = if is_const hd then fst (dest_const hd) else "" in
    match name with
      "linside" ->
        let m = role (fst (chop_list 5 args)) in
        ob_align (ob_find ctx fs m neg (pt args)) (el 5 args, el 6 args)
    | "lclosed" when not neg ->
        let m = role (fst (chop_list 5 args)) in
        MATCH_MP LINSIDE_CLOSED (ob_align (ob_find ctx fs m false (pt args)) (el 5 args, el 6 args))
    | "lsquare" ->
        let m = role args in
        let [u1; s1; _] = base_rel m in
        MP (prove(mk_imp(mk_conj(concl u1, concl s1), t), REWRITE_TAC[lsquare] THEN REAL_ARITH_TAC))
           (CONJ u1 s1)
    | "lcont" ->
        let m = role args in
        let th = MP (SPECL (OB_VARS @ [mk_small_numeral m]) OO_BOX) ctx.obnp in
        itlist (fun g th -> MATCH_MP (LCONT_PULL g) th) (rev (gens_of ctx.obtrf)) th
    | "ldisj" ->
        let m = role (fst (chop_list 5 args)) and n = role (snd (chop_list 5 args)) in
        ob_ldisj ctx m n
    | _ -> arith t in
  let prove_prem t = try let th = prove_prem t in
      if aconv (concl th) t then th else failwith ("got " ^ string_of_term (concl th))
    with Failure msg -> failwith (Printf.sprintf "ob_apply premise %s: %s" (string_of_term t) msg) in
  MP tmpl_i (end_itlist CONJ (map prove_prem prems));;

(* close:  |- !c1 c2 a b l. hyp ==> F *)
let ob_close ctx f = GENL OB_VARS (DISCH ctx.obhyp f);;

(* Lean impossible (forced form) from impossible_of_owned:
   th : |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam /\ E ==> F
   |- (!c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> E)
      ==> !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> F *)
let ob_forced th =
  let h = lhand (snd (strip_forall (concl th))) in
  let base = mk_conj(lhand h, lhand (rand h)) and e = rand (rand h) in
  let fa = list_mk_forall(OB_VARS, mk_imp(base, e)) in
  let hb = ASSUME base in
  let ev = MP (SPECL OB_VARS (ASSUME fa)) hb in
  let f = MP (SPECL OB_VARS th) (CONJ (CONJUNCT1 hb) (CONJ (CONJUNCT2 hb) ev)) in
  DISCH fa (GENL OB_VARS (DISCH base f));;
