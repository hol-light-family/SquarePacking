(* ========================================================================= *)
(* Checking a weighted point certificate inside HOL Light.                   *)
(*                                                                           *)
(* The data file (written by n12/scripts/gen_tree.py) lists the points on the    *)
(* integer grid of spacing 1/Q, their weights over W, the three D4           *)
(* permutations, and a box tree over pose space (centre, u = tan(theta/2)).  *)
(* Nothing in the data is trusted: every numeric fact is proved by HOL's     *)
(* numeral conversions, and every leaf is an instance of the lemmas of       *)
(* cover_lib.ml.  The result is a theorem                                    *)
(*     |- !t. t < m ==> ~packs n t.                                          *)
(* ========================================================================= *)

needs "n12/bounds/cover_lib.ml";;
#load "unix.cma";;

let VEC2_EQ = prove
 (`forall x1 x2 y1 y2. (vector[x1; x2]:real^2) = vector[y1; y2] <=> x1 = y1 /\ x2 = y2`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let DIV_EQ_SUB_DIV = prove
 (`forall a c M Q. 0 < Q ==> (&a / &Q = &M / &Q - &c / &Q <=> a + c = M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a / q - b / q = (a - b) / q`] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < q ==> (a / q = b / q <=> a = b)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let DIV_EQ_DIV = prove
 (`forall a b Q. 0 < Q ==> (&a / &Q = &b / &Q <=> a = b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < q ==> (a / q = b / q <=> a = b)`; REAL_OF_NUM_EQ]);;

let SUM_DIV_LT = prove
 (`forall S W n. 0 < W /\ S < n * W ==> &S / &W < &n`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; REAL_OF_NUM_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Numeral evaluation with a cache.                                          *)
(* ------------------------------------------------------------------------- *)

let cc_add_tm = `(+):num->num->num`
and cc_mul_tm = `( * ):num->num->num`
and cc_sub_tm = `(-):num->num->num`
and cc_le_tm = `(<=):num->num->bool`
and cc_lt_tm = `(<):num->num->bool`;;

let rec cc_ev cache tm =
  if is_numeral tm then REFL tm else
  try Hashtbl.find cache tm with Not_found ->
  let th =
    match tm with
      Comb(Comb(op,l),r) ->
        let tl = cc_ev cache l and tr = cc_ev cache r in
        let th1 = MK_COMB(AP_TERM op tl, tr) in
        let r1 = rand(concl th1) in
        let conv =
          if op = cc_add_tm then NUM_ADD_CONV
          else if op = cc_mul_tm then NUM_MULT_CONV
          else if op = cc_sub_tm then NUM_SUB_CONV
          else failwith ("cc_ev: operator "^string_of_term op) in
        TRANS th1 (conv r1)
    | _ -> failwith ("cc_ev: "^string_of_term tm) in
  Hashtbl.add cache tm th; th;;

let cc_prove_rel cache rel conv a b =
  let tha = cc_ev cache a and thb = cc_ev cache b in
  let th1 = MK_COMB(AP_TERM rel tha, thb) in
  EQT_ELIM(TRANS th1 (conv(rand(concl th1))));;

let cc_le cache a b = cc_prove_rel cache cc_le_tm NUM_LE_CONV a b;;
let cc_lt cache a b = cc_prove_rel cache cc_lt_tm NUM_LT_CONV a b;;

let cc_eqn cache v tm =
  (* |- v = tm where v is the numeral value of tm *)
  SYM(cc_ev cache tm);;

let mk_n (n:num) = mk_numeral n;;
let mk_add a b = mk_comb(mk_comb(cc_add_tm,a),b);;
let mk_mul a b = mk_comb(mk_comb(cc_mul_tm,a),b);;

(* ------------------------------------------------------------------------- *)
(* Reading the data file.                                                    *)
(* ------------------------------------------------------------------------- *)

type cert_data = {
  snum : num; sden : num; dd : num; ww : num; npts : int; ss : num; qq : num;
  mm : num; rr : num; umax : num; x1root : num;
  px : num array; py : num array; pw : num array;
  ppx : int array; ppy : int array; pps : int array;
  tree : string array };;

let read_cert_data fname =
  let ic = Stdlib.open_in fname in
  let words s = List.filter ((<>) "") (String.split_on_char ' ' (String.trim s)) in
  let hdr = Array.of_list (List.map num_of_string (words(input_line ic))) in
  let n = Num.int_of_num hdr.(4) in
  let px = Array.make n (Num.num_of_int 0) and py = Array.make n (Num.num_of_int 0)
  and pw = Array.make n (Num.num_of_int 0) in
  let ppx = Array.make n 0 and ppy = Array.make n 0 and pps = Array.make n 0 in
  for i = 0 to n - 1 do
    match words(input_line ic) with
      [a;b;c;d;e;f] ->
        px.(i) <- num_of_string a; py.(i) <- num_of_string b; pw.(i) <- num_of_string c;
        ppx.(i) <- int_of_string d; ppy.(i) <- int_of_string e; pps.(i) <- int_of_string f
    | _ -> failwith "read_cert_data: point line"
  done;
  let nt = int_of_string(String.trim(input_line ic)) in
  let tree = Array.init nt (fun _ -> String.trim(input_line ic)) in
  Stdlib.close_in ic;
  { snum = hdr.(0); sden = hdr.(1); dd = hdr.(2); ww = hdr.(3); npts = n; ss = hdr.(5);
    qq = hdr.(6); mm = hdr.(7); rr = hdr.(8); umax = hdr.(9); x1root = hdr.(10);
    px = px; py = py; pw = pw; ppx = ppx; ppy = ppy; pps = pps; tree = tree };;

(* ------------------------------------------------------------------------- *)
(* Lookup theorems |- EL k L = x_k for all k, in one linear pass.            *)
(* ------------------------------------------------------------------------- *)

let el_lookups (ldef:thm) =
  (* ldef : |- L = [x0; ...; x_{n-1}] *)
  let l = lhs(concl ldef) in
  let ty = hd(snd(dest_type(type_of l))) in
  let step = INST_TYPE [ty,`:A`] EL_STEP and head = INST_TYPE [ty,`:A`] EL_HEAD in
  let start = CONV_RULE (BINDER_CONV(RAND_CONV(RAND_CONV(K ldef))))
                (ISPEC l EL_START) in
  let rec go th k acc =
    (* th : |- !i. EL (i + k) L = EL i lst *)
    let lst = rand(rand(snd(dest_forall(concl th)))) in
    if is_const lst then List.rev acc else
    let h,t = dest_cons lst in
    let kt = rand(lhand(lhand(snd(dest_forall(concl th))))) in
    let el = MP (ISPECL [l;h;t;kt] head) th in
    let th' = MP (ISPECL [l;h;t;kt] step) th in
    let th'' = CONV_RULE (BINDER_CONV(LAND_CONV(LAND_CONV(RAND_CONV NUM_SUC_CONV)))) th' in
    go th'' (k+1) (el::acc) in
  Array.of_list (go start 0 []);;

(* ------------------------------------------------------------------------- *)
(* Setting up a certificate: definitions and global facts.                   *)
(* ------------------------------------------------------------------------- *)

type cert_ctx = {
  cd : cert_data;
  q_tm : term; r_tm : term; m_nat_tm : term; w_tm : term; n_tm : term;
  m_tm : term; pts_tm : term; wt_tm : term;
  px_tm : term; py_tm : term; ps_tm : term;
  qpos : thm; rpos : thm; wpos : thm;
  pt_th : thm array;       (* |- pts k = vector[&X/&Q; &Y/&Q] *)
  wt_th : thm array;       (* |- wt k = &w/&W *)
  wel_th : thm array;      (* |- EL k WS = w *)
  wnonneg : thm;           (* |- !k. k < N ==> &0 <= wt k *)
  claim_w : thm;           (* |- !ks. W <= ITLIST (\k a. EL k WS + a) ks 0
                                     ==> &1 <= ITLIST (\k a. wt k + a) ks (&0) *)
  ws_tm : term };;

let numlist_tm (a:num array) =
  mk_list(Array.to_list(Array.map mk_n a), `:num`);;
let intlist_tm (a:int array) =
  mk_list(Array.to_list(Array.map (fun i -> mk_small_numeral i) a), `:num`);;

let cert_setup prefix fname =
  let cd = read_cert_data fname in
  let def nm tm = new_definition(mk_eq(mk_var(prefix^"_"^nm, type_of tm), tm)) in
  let dX = def "X" (numlist_tm cd.px) and dY = def "Y" (numlist_tm cd.py)
  and dW = def "W" (numlist_tm cd.pw) and dPX = def "PX" (intlist_tm cd.ppx)
  and dPY = def "PY" (intlist_tm cd.ppy) and dPS = def "PS" (intlist_tm cd.pps) in
  let xl = lhs(concl dX) and yl = lhs(concl dY) and wl = lhs(concl dW) in
  let q_tm = mk_n cd.qq and r_tm = mk_n cd.rr and w_tm = mk_n cd.ww
  and m_nat_tm = mk_n cd.mm and n_tm = mk_small_numeral cd.npts in
  let dpts = def "pts" (subst [xl,`XL:num list`; yl,`YL:num list`; q_tm,`QQ:num`]
    `\k. vector[&(EL k XL) / &QQ; &(EL k YL) / &QQ]:real^2`) in
  let dwt = def "wt" (subst [wl,`WL:num list`; w_tm,`WW:num`] `\k. &(EL k WL) / &WW`) in
  let dpx = def "px" (subst [lhs(concl dPX),`L:num list`] `\k. EL k (L:num list)`)
  and dpy = def "py" (subst [lhs(concl dPY),`L:num list`] `\k. EL k (L:num list)`)
  and dps = def "ps" (subst [lhs(concl dPS),`L:num list`] `\k. EL k (L:num list)`) in
  let pts_tm = lhs(concl dpts) and wt_tm = lhs(concl dwt) in
  let m_tm = subst [m_nat_tm,`MM:num`; q_tm,`QQ:num`] `&MM / &QQ` in
  let lx = el_lookups dX and ly = el_lookups dY and lw = el_lookups dW
  and lpx = el_lookups dPX and lpy = el_lookups dPY and lps = el_lookups dPS in
  let n = cd.npts in
  let pt_th = Array.init n (fun k ->
    let th = BETA_RULE(AP_THM dpts (mk_small_numeral k)) in
    REWRITE_RULE[lx.(k); ly.(k)] th) in
  let wt_th = Array.init n (fun k ->
    REWRITE_RULE[lw.(k)] (BETA_RULE(AP_THM dwt (mk_small_numeral k)))) in
  let pos t = EQT_ELIM(NUM_LT_CONV(mk_comb(mk_comb(cc_lt_tm,`0`),t))) in
  let wpos = pos w_tm in
  let wnonneg = prove
   (subst [wt_tm,`wt:num->real`; n_tm,`N:num`] `forall k. k < (N:num) ==> &0 <= (wt:num->real) k`,
    REWRITE_TAC[dwt] THEN SIMP_TAC[REAL_LE_DIV; REAL_POS]) in
  let claim_w = prove
   (subst [wt_tm,`wt:num->real`; wl,`WS:num list`; w_tm,`W:num`]
     `forall ks. W <= ITLIST (\k a. EL k WS + a) ks 0
           ==> &1 <= ITLIST (\k a. wt k + a) ks (&0)`,
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[dwt] THEN
    REWRITE_TAC[BETA_RULE(ISPECL [`ks:num list`;
       subst [wl,`WS:num list`] `\k. EL k (WS:num list)`; w_tm] ITLIST_DIV)] THEN
    MATCH_MP_TAC LE_ONE_DIV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV) in
  { cd = cd; q_tm = q_tm; r_tm = r_tm; m_nat_tm = m_nat_tm; w_tm = w_tm; n_tm = n_tm;
    m_tm = m_tm; pts_tm = pts_tm; wt_tm = wt_tm;
    px_tm = lhs(concl dpx); py_tm = lhs(concl dpy); ps_tm = lhs(concl dps);
    qpos = pos q_tm; rpos = pos r_tm; wpos = wpos;
    pt_th = pt_th; wt_th = wt_th; wel_th = lw; wnonneg = wnonneg; claim_w = claim_w;
    ws_tm = wl },
  (dpx, dpy, dps, lpx, lpy, lps);;

(* ------------------------------------------------------------------------- *)
(* Global facts: D4 invariance and total weight.                             *)
(* ------------------------------------------------------------------------- *)

let forall_lt_build pk (bk : int -> thm) n =
  (* pk = \k. body; bk i : |- body[i]; result |- !k. k < n ==> pk k *)
  let th0 = ISPEC pk FORALL_LT_0 in
  let rec go i th =
    if i = n then th else
    let it = mk_small_numeral i in
    let b = EQ_MP (SYM(BETA_CONV(mk_comb(pk,it)))) (bk i) in
    let th1 = MP (ISPECL [pk; it] FORALL_LT_SUC) (CONJ th b) in
    let th2 = CONV_RULE (BINDER_CONV(LAND_CONV(RAND_CONV NUM_SUC_CONV))) th1 in
    go (i+1) th2 in
  go 0 th0;;

let prove_d4 ctx (dpx,dpy,dps,lpx,lpy,lps) =
  let cd = ctx.cd in
  let d4tm = list_mk_comb(`d4inv`, [ctx.pts_tm; ctx.wt_tm; ctx.n_tm; ctx.m_tm;
                                    ctx.px_tm; ctx.py_tm; ctx.ps_tm]) in
  let dth = REWRITE_CONV[d4inv] d4tm in
  let kv, imp = dest_forall(rand(concl dth)) in
  let body = rand imp in
  let pk = mk_abs(kv, body) in
  let bk k =
    let bt = vsubst [mk_small_numeral k, kv] body in
    let js = [cd.ppx.(k); cd.ppy.(k); cd.pps.(k)] in
    let rws = [dpx; dpy; dps; lpx.(k); lpy.(k); lps.(k)] @
              List.concat (map (fun j -> [lpx.(j); lpy.(j); lps.(j);
                                          ctx.pt_th.(j); ctx.wt_th.(j)]) js) @
              [ctx.pt_th.(k); ctx.wt_th.(k)] in
    EQT_ELIM((REWRITE_CONV rws THENC
              REWRITE_CONV[VECTOR_2; VEC2_EQ] THENC
              SIMP_CONV[DIV_EQ_SUB_DIV; DIV_EQ_DIV; ctx.qpos] THENC
              NUM_REDUCE_CONV) bt) in
  let th = forall_lt_build pk bk cd.npts in
  EQ_MP (SYM dth) (BETA_RULE th);;

let prove_total_weight ctx nsq =
  (* |- sum {k | k < N} wt < &nsq *)
  let cd = ctx.cd in
  let th0 = ISPECL [ctx.wt_tm; ctx.w_tm] SUM_LT_0 in
  let rec go i th =
    if i = cd.npts then th else
    let s = rand(lhand(rand(concl th))) in
    let th1 = MP (ISPECL [ctx.wt_tm; mk_small_numeral i; s; mk_n cd.pw.(i); ctx.w_tm]
                    SUM_LT_SUC_DIV) (CONJ th ctx.wt_th.(i)) in
    let th2 = CONV_RULE (LAND_CONV(ONCE_DEPTH_CONV NUM_SUC_CONV) THENC
                         RAND_CONV(LAND_CONV(RAND_CONV NUM_ADD_CONV))) th1 in
    go (i+1) th2 in
  let th = go 0 th0 in
  let s = rand(lhand(rand(concl th))) in
  let lt = MP (ISPECL [s; ctx.w_tm; mk_small_numeral nsq] SUM_DIV_LT)
              (CONJ ctx.wpos (EQT_ELIM(NUM_REDUCE_CONV
                 (mk_comb(mk_comb(cc_lt_tm,s),
                          mk_mul (mk_small_numeral nsq) ctx.w_tm))))) in
  EQ_MP (SYM(AP_THM (AP_TERM `(<):real->real->bool` th) (mk_comb(`&`,mk_small_numeral nsq)))) lt;;

(* ------------------------------------------------------------------------- *)
(* Leaves.                                                                   *)
(* ------------------------------------------------------------------------- *)

let nsub_num a b = if a >/ b then a -/ b else Num.num_of_int 0;;
let max_num a b = if a >=/ b then a else b;;
let min_num a b = if a <=/ b then a else b;;

let cc_c1 = `c1:real` and cc_c2 = `c2:real` and cc_t = `t:real`;;

let clip_tm ctx (xl,xh,yl,yh,u0,u1) =
  let q = ctx.q_tm and r = ctx.r_tm in
  subst [mk_n xl,`xl:num`; mk_n xh,`xh:num`; mk_n yl,`yl:num`; mk_n yh,`yh:num`;
         mk_n u0,`u0:num`; mk_n u1,`u1:num`; q,`Q:num`; r,`R:num`]
   `&xl / &Q <= c1 /\ c1 <= &xh / &Q /\ &yl / &Q <= c2 /\ c2 <= &yh / &Q /\
    &u0 / &R <= t /\ t <= &u1 / &R`;;

let tsq_tm = `tsq c1 c2 t`;;

let ITLIST_NIL_THM = prove
 (`forall f b. ITLIST (f:A->B->B) [] b = b`, REWRITE_TAC[ITLIST]);;

let ITLIST_CONS_THM = prove
 (`forall f h t b. ITLIST (f:A->B->B) (CONS h t) b = f h (ITLIST f t b)`,
  REWRITE_TAC[ITLIST]);;

let cc_k = `k:num` and cc_a = `a:num` and cc_EL = `EL:num->num list->num`
and cc_zero = `0` and cc_num_ty = `:num`;;

let itlist_w_thm ctx ks =
  (* |- ITLIST (\k a. EL k WS + a) ks 0 = n *)
  let f = mk_abs(cc_k, mk_abs(cc_a,
            mk_add (mk_comb(mk_comb(cc_EL,cc_k), ctx.ws_tm)) cc_a)) in
  let nil_th = ISPECL [f; cc_zero] ITLIST_NIL_THM in
  let rec go ks =
    match ks with
      [] -> nil_th
    | k::t ->
        let kt = mk_small_numeral k in
        let tl = mk_list(map mk_small_numeral t, cc_num_ty) in
        let th_t = go t in
        let th1 = ISPECL [f; kt; tl; cc_zero] ITLIST_CONS_THM in
        let th2 = CONV_RULE (RAND_CONV(RATOR_CONV BETA_CONV THENC BETA_CONV)) th1 in
        CONV_RULE (RAND_CONV(LAND_CONV(K ctx.wel_th.(k)) THENC
                             RAND_CONV(K th_t) THENC NUM_ADD_CONV)) th2 in
  go ks;;

let cc_prove_atom cache tm =
  if is_eq tm then
    let l,r = dest_eq tm in
    let th = cc_ev cache r in
    if rand(concl th) = l then SYM th else failwith "cc_prove_atom: wrong value"
  else
    let op,args = strip_comb tm in
    match args with
      [a;b] when op = cc_le_tm -> cc_le cache a b
    | [a;b] when op = cc_lt_tm -> cc_lt cache a b
    | _ -> failwith "cc_prove_atom";;

let cc_discharge cache th =
  (* th : |- A1 /\ ... /\ An ==> B ;  prove the Ai numerically *)
  let ants = conjuncts(lhand(concl th)) in
  MP th (end_itlist CONJ (map (cc_prove_atom cache) ants));;

let leaf_stats = Atomic.make 0;;
let claim_stats = Atomic.make 0;;

let cc_tmpl_a = `2 * ((R:num) * R - (s0:num) * s1)`
and cc_tmpl_b = `2 * (R:num) * ((s0:num) + s1)`
and cc_tmpl_g = `(R:num) * R + (s0:num) * s1`
and cc_R = `R:num` and cc_s0 = `s0:num` and cc_s1 = `s1:num`
and cc_in_tm = `(IN):real^2->(real^2->bool)->bool`
and cc_sorted_tm = `sorted_lt`;;

let cc_sorted_conv = REWRITE_CONV[sorted_lt; HD; NOT_CONS_NIL] THENC NUM_REDUCE_CONV;;
let cc_maxmin_conv = REWRITE_CONV[MAX; MIN] THENC NUM_REDUCE_CONV;;

let leaf_thm_gen ctx (x0,x1,y0,y1,u0,u1) rects indiv =
  let claims = List.sort compare (indiv @ List.concat (map snd rects)) in
  let cd = ctx.cd in
  let q = cd.qq and r = cd.rr and m = cd.mm in
  let two = Num.num_of_int 2 in
  let rr = r */ r in
  let wl = quo_num (q */ nsub_num (rr +/ two */ u0 */ r) (u1 */ u1))
                   (two */ (rr +/ u1 */ u1)) in
  let xl = max_num x0 wl and xh = min_num x1 (nsub_num m wl)
  and yl = max_num y0 wl and yh = min_num y1 (nsub_num m wl) in
  let cache = Hashtbl.create 97 in
  let pts = ctx.pts_tm and wt = ctx.wt_tm and nt = ctx.n_tm
  and qt = ctx.q_tm and rt = ctx.r_tm in
  let n = mk_n in
  let inner =
    if xh </ xl || yh </ yl then
      let d = if xh </ xl then DISJ1 (cc_lt cache (n xh) (n xl)) (mk_comb(mk_comb(cc_lt_tm,n yh),n yl))
              else DISJ2 (mk_comb(mk_comb(cc_lt_tm,n xh),n xl)) (cc_lt cache (n yh) (n yl)) in
      MP (ISPECL [pts; wt; nt; qt; rt; n u0; n u1; n xl; n xh; n yl; n yh] BOXCOV_LEAF_EMPTY)
         (CONJ ctx.qpos d)
    else begin
      let ev t = rand(concl(cc_ev cache t)) in
      let trip s0 s1 =
        let sb = [rt,cc_R; n s0,cc_s0; n s1,cc_s1] in
        let a = ev (subst sb cc_tmpl_a) and b = ev (subst sb cc_tmpl_b)
        and g = ev (subst sb cc_tmpl_g) in
        [a;b;g] in
      let abg = trip u0 u0 @ trip u1 u1 @ trip u0 u1 in
      let largs = [qt; rt; n u0; n u1; n xl; n xh; n yl; n yh] @ abg in
      let ptleaf = cc_discharge cache (ISPECL largs PT_NAT_LEAF) in
      let tbl = Hashtbl.create 64 in
      List.iter (fun k ->
        Hashtbl.replace tbl k (cc_discharge cache (SPECL [n cd.px.(k); n cd.py.(k)] ptleaf)))
        indiv;
      if rects <> [] then begin
        let rectleaf = cc_discharge cache (ISPECL largs PT_RECT_LEAF) in
        List.iter (fun ((xa,xb,ya,yb),ks) ->
          let rth = cc_discharge cache (SPECL [n xa; n xb; n ya; n yb] rectleaf) in
          List.iter (fun k ->
            Hashtbl.replace tbl k (cc_discharge cache (SPECL [n cd.px.(k); n cd.py.(k)] rth)))
            ks) rects
      end;
      let ptc = map (Hashtbl.find tbl) claims in
      let clip = lhand(snd(strip_forall(concl(hd ptc)))) in
      let hyp = ASSUME clip in
      let sq = tsq_tm in
      let in_th k th =
        let th1 = MP (SPECL [cc_c1; cc_c2; cc_t] th) hyp in
        EQ_MP (SYM(AP_THM (AP_TERM cc_in_tm ctx.pt_th.(k)) sq))
              th1 in
      let ins = map2 in_th claims ptc in
      let rec all_th ks ths =
        match ks, ths with
          [], [] -> ISPECL [nt; pts; sq] ALL_CLAIM_NIL
        | k::kt, th::tht ->
            let acc = all_th kt tht in
            let kn = mk_small_numeral k in
            let tl = mk_list(map mk_small_numeral kt, cc_num_ty) in
            MP (ISPECL [nt; pts; sq; kn; tl] ALL_CLAIM_CONS)
               (CONJ (CONJ (cc_lt cache kn nt) th) acc)
        | _ -> failwith "all_th" in
      let allth = all_th claims ins in
      let kst = mk_list(map mk_small_numeral claims, cc_num_ty) in
      let sorted = EQT_ELIM(cc_sorted_conv (mk_comb(cc_sorted_tm, kst))) in
      let itw = itlist_w_thm ctx claims in
      let le_n = cc_le cache ctx.w_tm (rand(concl itw)) in
      let le_it = EQ_MP (AP_TERM (mk_comb(cc_le_tm, ctx.w_tm)) (SYM itw)) le_n in
      let w1 = MP (SPEC kst ctx.claim_w) le_it in
      let capt_th = MP (ISPECL [pts; wt; nt; sq; kst] CLAIM_CAPT_GE1)
                       (end_itlist CONJ [ctx.wnonneg; allth; sorted; w1]) in
      GENL [cc_c1; cc_c2; cc_t] (DISCH clip capt_th)
    end in
  let bl = ISPECL [pts; wt; nt; ctx.m_tm; qt; rt; ctx.m_nat_tm; n x0; n x1; n y0; n y1;
                   n u0; n u1; n wl; n xl; n xh; n yl; n yh] BOXCOV_LEAF in
  let ants = conjuncts(lhand(concl bl)) in
  let prove_ant tm =
    if is_forall tm then inner
    else if is_eq tm && is_comb(rand tm) && is_const(fst(strip_comb(rand tm))) &&
            (fst(dest_const(fst(strip_comb(rand tm)))) = "MAX" ||
             fst(dest_const(fst(strip_comb(rand tm)))) = "MIN") then
      SYM(cc_maxmin_conv (rand tm))
    else if is_eq tm && lhs tm = ctx.m_tm then REFL ctx.m_tm
    else cc_prove_atom cache tm in
  Atomic.incr leaf_stats; ignore(Atomic.fetch_and_add claim_stats (length claims));
  MP bl (end_itlist CONJ (map prove_ant ants));;

let leaf_thm ctx box claims = leaf_thm_gen ctx box [] claims;;

let parse_mleaf words =
  (* "M" nr {Xa Xb Ya Yb c k1..kc}* ni k1..kni *)
  let a = Array.of_list words in
  let pos = ref 1 in
  let nxt () = let v = a.(!pos) in pos := !pos + 1; v in
  let nr = int_of_string(nxt()) in
  let rects = List.init nr (fun _ ->
    let xa = num_of_string(nxt()) in let xb = num_of_string(nxt()) in
    let ya = num_of_string(nxt()) in let yb = num_of_string(nxt()) in
    let c = int_of_string(nxt()) in
    let ks = List.init c (fun _ -> int_of_string(nxt())) in
    ((xa,xb,ya,yb),ks)) in
  let ni = int_of_string(nxt()) in
  let indiv = List.init ni (fun _ -> int_of_string(nxt())) in
  rects, indiv;;

(* ------------------------------------------------------------------------- *)
(* The tree.                                                                 *)
(* ------------------------------------------------------------------------- *)

let prove_tree ctx =
  let cd = ctx.cd in
  let pos = ref 0 in
  let n = mk_n in
  let two = Num.num_of_int 2 in
  let pts = ctx.pts_tm and wt = ctx.wt_tm and nt = ctx.n_tm
  and qt = ctx.q_tm and rt = ctx.r_tm and mt = ctx.m_tm in
  let t0 = Sys.time() in
  let rec go (x0,x1,y0,y1,u0,u1 as box) =
    let tok = cd.tree.(!pos) in
    pos := !pos + 1;
    let words = List.filter ((<>) "") (String.split_on_char ' ' tok) in
    match words with
      ["X"] ->
        let xm = quo_num (x0 +/ x1) two in
        let l = go (x0,xm,y0,y1,u0,u1) in
        let r = go (xm,x1,y0,y1,u0,u1) in
        MP (ISPECL [pts;wt;nt;mt;qt;rt;n x0;n x1;n xm;n y0;n y1;n u0;n u1] BOXCOV_SPLIT_X)
           (CONJ l r)
    | ["Y"] ->
        let ym = quo_num (y0 +/ y1) two in
        let l = go (x0,x1,y0,ym,u0,u1) in
        let r = go (x0,x1,ym,y1,u0,u1) in
        MP (ISPECL [pts;wt;nt;mt;qt;rt;n x0;n x1;n y0;n y1;n ym;n u0;n u1] BOXCOV_SPLIT_Y)
           (CONJ l r)
    | ["U"] ->
        let um = quo_num (u0 +/ u1) two in
        let l = go (x0,x1,y0,y1,u0,um) in
        let r = go (x0,x1,y0,y1,um,u1) in
        MP (ISPECL [pts;wt;nt;mt;qt;rt;n x0;n x1;n y0;n y1;n u0;n u1;n um] BOXCOV_SPLIT_U)
           (CONJ l r)
    | ["E"] ->
        let th = leaf_thm ctx box [] in
        let a = Atomic.get leaf_stats in
        if a mod 1000 = 0 then
          (Format.print_string(sprintf "leaves %d time %.1f\n" a (Sys.time() -. t0));
           Format.print_flush());
        th
    | "L"::_::ks ->
        let th = leaf_thm ctx box (map int_of_string ks) in
        let a = Atomic.get leaf_stats in
        if a mod 1000 = 0 then
          (Format.print_string(sprintf "leaves %d time %.1f\n" a (Sys.time() -. t0));
           Format.print_flush());
        th
    | _ -> failwith ("prove_tree: bad token " ^ tok) in
  let z = Num.num_of_int 0 in
  let th = go (z, cd.x1root, z, cd.x1root, z, cd.umax) in
  if !pos <> Array.length cd.tree then failwith "prove_tree: trailing tokens" else th;;

(* ------------------------------------------------------------------------- *)
(* Everything together: |- !t. t < s ==> ~packs n t.                         *)
(* ------------------------------------------------------------------------- *)

let certificate_theorem prefix fname nsq =
  let ctx, aux = cert_setup prefix fname in
  let cd = ctx.cd in
  let d4 = prove_d4 ctx aux in
  let wsum = prove_total_weight ctx nsq in
  let root = prove_tree ctx in
  let rat_le a b = EQT_ELIM(REAL_RAT_REDUCE_CONV(mk_comb(mk_comb(`(<=):real->real->bool`,a),b))) in
  let half_m = mk_comb(mk_comb(`(/):real->real->real`, ctx.m_tm), `&2`) in
  let x1q = mk_comb(mk_comb(`(/):real->real->real`, mk_comb(`&`,mk_n cd.x1root)),
                    mk_comb(`&`,ctx.q_tm)) in
  let u1r = mk_comb(mk_comb(`(/):real->real->real`, mk_comb(`&`,mk_n cd.umax)),
                    mk_comb(`&`,ctx.r_tm)) in
  let cov = MP (ISPECL [ctx.pts_tm; ctx.wt_tm; ctx.n_tm; ctx.m_tm; ctx.q_tm; ctx.r_tm;
                        ctx.px_tm; ctx.py_tm; ctx.ps_tm; mk_n cd.x1root; mk_n cd.x1root;
                        mk_n cd.umax] BOXCOV_ROOT)
               (end_itlist CONJ [d4; ctx.qpos; ctx.rpos; rat_le half_m x1q;
                                 rat_le half_m x1q;
                                 rat_le `&29 / &70` u1r; root]) in
  let s_tm = mk_comb(mk_comb(`(/):real->real->real`, mk_comb(`&`,mk_n cd.snum)),
                     mk_comb(`&`,mk_n cd.sden)) in
  let m_eq = EQT_ELIM(REAL_RAT_REDUCE_CONV(mk_eq(ctx.m_tm, s_tm))) in
  let main = prove
   (subst [s_tm,`s:real`; mk_small_numeral nsq,`n:num`] `forall t. t < s ==> ~packs n t`,
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC COVER_NO_PACK THEN
    MAP_EVERY EXISTS_TAC [ctx.n_tm; ctx.pts_tm; ctx.wt_tm; ctx.m_tm] THEN
    REWRITE_TAC[ctx.wnonneg; wsum; cov] THEN
    ASM_REWRITE_TAC[m_eq]) in
  main;;

(* ------------------------------------------------------------------------- *)
(* Parallel version: independent subtrees are proved in separate domains     *)
(* (OCaml 5).  The kernel's inference rules are pure functions, so the       *)
(* theorems produced are exactly as trustworthy as sequentially produced     *)
(* ones; only the gluing of the subtree theorems happens in the main domain. *)
(* ------------------------------------------------------------------------- *)

let tree_info cd =
  (* for each token position: end position (exclusive) and number of leaves *)
  let n = Array.length cd.tree in
  let tend = Array.make n 0 and nleaves = Array.make n 0 in
  let rec go i =
    let tok = cd.tree.(i) in
    if tok = "X" || tok = "Y" || tok = "U" then
      let j = go (i+1) in let k = go j in
      tend.(i) <- k; nleaves.(i) <- nleaves.(i+1) + nleaves.(j); k
    else (tend.(i) <- i+1; nleaves.(i) <- 1; i+1) in
  ignore(go 0); tend, nleaves;;

let prove_tree_par ctx ndom chunk =
  let cd = ctx.cd in
  let tend, nleaves = tree_info cd in
  let n = mk_n in
  let two = Num.num_of_int 2 in
  let pts = ctx.pts_tm and wt = ctx.wt_tm and nt = ctx.n_tm
  and qt = ctx.q_tm and rt = ctx.r_tm and mt = ctx.m_tm in
  let split_box tok (x0,x1,y0,y1,u0,u1) =
    match tok with
      "X" -> let xm = quo_num (x0 +/ x1) two in (x0,xm,y0,y1,u0,u1), (xm,x1,y0,y1,u0,u1), xm
    | "Y" -> let ym = quo_num (y0 +/ y1) two in (x0,x1,y0,ym,u0,u1), (x0,x1,ym,y1,u0,u1), ym
    | _ -> let um = quo_num (u0 +/ u1) two in (x0,x1,y0,y1,u0,um), (x0,x1,y0,y1,um,u1), um in
  let glue tok (x0,x1,y0,y1,u0,u1) mid l r =
    let args = match tok with
        "X" -> ([pts;wt;nt;mt;qt;rt;n x0;n x1;n mid;n y0;n y1;n u0;n u1], BOXCOV_SPLIT_X)
      | "Y" -> ([pts;wt;nt;mt;qt;rt;n x0;n x1;n y0;n y1;n mid;n u0;n u1], BOXCOV_SPLIT_Y)
      | _ -> ([pts;wt;nt;mt;qt;rt;n x0;n x1;n y0;n y1;n u0;n u1;n mid], BOXCOV_SPLIT_U) in
    MP (ISPECL (fst args) (snd args)) (CONJ l r) in
  (* sequential prover for a subtree starting at position i *)
  let rec seq i box =
    let tok = cd.tree.(i) in
    if tok = "X" || tok = "Y" || tok = "U" then
      let lb, rb, mid = split_box tok box in
      let l = seq (i+1) lb in
      let r = seq tend.(i+1) rb in
      glue tok box mid l r
    else
      let words = List.filter ((<>) "") (String.split_on_char ' ' tok) in
      match words with
        ["E"] -> leaf_thm ctx box []
      | "L"::_::ks -> leaf_thm ctx box (map int_of_string ks)
      | "M"::_ -> let rects, indiv = parse_mleaf words in leaf_thm_gen ctx box rects indiv
      | _ -> failwith ("prove_tree_par: bad token " ^ tok) in
  (* collect chunks *)
  let chunks = ref [] in
  let rec collect i box =
    let tok = cd.tree.(i) in
    if nleaves.(i) <= chunk || not(tok = "X" || tok = "Y" || tok = "U") then
      chunks := (i,box) :: !chunks
    else
      let lb, rb, _ = split_box tok box in
      (collect (i+1) lb; collect tend.(i+1) rb) in
  let z = Num.num_of_int 0 in
  let root = (z, cd.x1root, z, cd.x1root, z, cd.umax) in
  collect 0 root;
  let tasks = Array.of_list (List.rev !chunks) in
  let ntask = Array.length tasks in
  let results = Array.make ntask None in
  let index = Hashtbl.create ntask in
  Array.iteri (fun j (i,_) -> Hashtbl.add index i j) tasks;
  let next = Atomic.make 0 in
  let failed = Atomic.make "" in
  let worker () =
    let rec loop () =
      let j = Atomic.fetch_and_add next 1 in
      if j < ntask && Atomic.get failed = "" then begin
        let (i,box) = tasks.(j) in
        (try results.(j) <- Some(seq i box)
         with Failure s -> Atomic.set failed s | e -> Atomic.set failed (Printexc.to_string e));
        loop ()
      end in
    loop () in
  let t0 = Unix.gettimeofday() in
  let doms = List.init ndom (fun _ -> Domain.spawn worker) in
  (* progress reporting from the main domain *)
  let rec wait () =
    let done_ = Array.fold_left (fun a r -> if r = None then a else a + 1) 0 results in
    if done_ < ntask && Atomic.get failed = "" && Atomic.get next < ntask + ndom then begin
      Format.print_string(sprintf "chunks %d/%d leaves %d claims %d time %.0f\n"
        done_ ntask (Atomic.get leaf_stats) (Atomic.get claim_stats)
        (Unix.gettimeofday() -. t0));
      Format.print_flush(); Unix.sleepf 60.0; wait () end in
  wait ();
  List.iter Domain.join doms;
  if Atomic.get failed <> "" then failwith ("prove_tree_par: " ^ Atomic.get failed) else
  (* glue *)
  let rec glue_up i box =
    match (try Some(Hashtbl.find index i) with Not_found -> None) with
      Some j -> (match results.(j) with Some th -> th | None -> failwith "missing chunk")
    | None ->
        let tok = cd.tree.(i) in
        let lb, rb, mid = split_box tok box in
        glue tok box mid (glue_up (i+1) lb) (glue_up tend.(i+1) rb) in
  glue_up 0 root;;

let certificate_theorem_par prefix fname nsq ndom chunk =
  let ctx, aux = cert_setup prefix fname in
  let cd = ctx.cd in
  let d4 = prove_d4 ctx aux in
  let wsum = prove_total_weight ctx nsq in
  let root = prove_tree_par ctx ndom chunk in
  let rat_le a b = EQT_ELIM(REAL_RAT_REDUCE_CONV(mk_comb(mk_comb(`(<=):real->real->bool`,a),b))) in
  let half_m = mk_comb(mk_comb(`(/):real->real->real`, ctx.m_tm), `&2`) in
  let x1q = mk_comb(mk_comb(`(/):real->real->real`, mk_comb(`&`,mk_n cd.x1root)),
                    mk_comb(`&`,ctx.q_tm)) in
  let u1r = mk_comb(mk_comb(`(/):real->real->real`, mk_comb(`&`,mk_n cd.umax)),
                    mk_comb(`&`,ctx.r_tm)) in
  let cov = MP (ISPECL [ctx.pts_tm; ctx.wt_tm; ctx.n_tm; ctx.m_tm; ctx.q_tm; ctx.r_tm;
                        ctx.px_tm; ctx.py_tm; ctx.ps_tm; mk_n cd.x1root; mk_n cd.x1root;
                        mk_n cd.umax] BOXCOV_ROOT)
               (end_itlist CONJ [d4; ctx.qpos; ctx.rpos; rat_le half_m x1q;
                                 rat_le half_m x1q;
                                 rat_le `&29 / &70` u1r; root]) in
  let s_tm = mk_comb(mk_comb(`(/):real->real->real`, mk_comb(`&`,mk_n cd.snum)),
                     mk_comb(`&`,mk_n cd.sden)) in
  let m_eq = EQT_ELIM(REAL_RAT_REDUCE_CONV(mk_eq(ctx.m_tm, s_tm))) in
  prove
   (subst [s_tm,`s:real`; mk_small_numeral nsq,`n:num`] `forall t. t < s ==> ~packs n t`,
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC COVER_NO_PACK THEN
    MAP_EVERY EXISTS_TAC [ctx.n_tm; ctx.pts_tm; ctx.wt_tm; ctx.m_tm] THEN
    REWRITE_TAC[ctx.wnonneg; wsum; cov] THEN
    ASM_REWRITE_TAC[m_eq]);;
