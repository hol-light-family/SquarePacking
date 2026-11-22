(* ========================================================================= *)
(* Case 84 bridge pieces (Jatloe: Bridge/C84Ownership, C84MergedBottomDomain,*)
(* RelaxedOwnerDomain.ofSmallBudget, S12.Diameter, ForcedAuxiliary).         *)
(* ========================================================================= *)

needs "n12/geometry/bridge_ext.ml";;
needs "n12/geometry/C84MergedBottom.ml";;

(* S12.normalized_diameter_bound (squared form) *)
let C84B_DIAMETER = prove
 (`forall c s u v a x1 y1 x2 y2. c * c + s * s = &1 /\ &0 < a /\ a <= &1001 / &1000 /\
     linside c s u v a x1 y1 /\ linside c s u v a x2 y2
     ==> (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2) < &2 * (&1001 / &1000) * (&1001 / &1000)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2) =
                (c * (x1 - x2) + s * (y1 - y2)) * (c * (x1 - x2) + s * (y1 - y2)) +
                (--s * (x1 - x2) + c * (y1 - y2)) * (--s * (x1 - x2) + c * (y1 - y2))` SUBST1_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `w1 = c * (x1 - x2) + s * (y1 - y2)` THEN
  ABBREV_TAC `w2 = --s * (x1 - x2) + c * (y1 - y2)` THEN
  SUBGOAL_THEN `--a < w1 /\ w1 < a /\ --a < w2 /\ w2 < a` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["w1"; "w2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC []);;


(* l-form facts of a square from osq-form facts *)
let to_lform th = REWRITE_RULE[OSQ_LSQ] th;;

(* osq fact at point p among ths (positive) *)
let pos_at ths (x, y) =
  let ptm = mk_comb(`vector:(real)list->real^2`, mk_list([x; y], `:real`)) in
  find (fun th -> not (is_neg (concl th)) && aconv (lhand(concl th)) ptm) ths;;
let neg_at ths (x, y) =
  let ptm = mk_comb(`vector:(real)list->real^2`, mk_list([x; y], `:real`)) in
  find (fun th -> is_neg (concl th) && aconv (lhand(rand(concl th))) ptm) ths;;

(* C84MergedBottomDomain.domain: auxown 1 sq = {5} \/ {6} \/ {8}  for mask 8704 *)
let c84_bottom_domain hnp hrow r sq =
  let (m, iv, lt, own, sqth) = sq in
  if m <> 8704 then failwith "c84_bottom_domain: mask" else
  let [h1; h2; h3; _] = sqth in
  let (atm, kth, eq) = card_one hnp hrow r sq 1 in
  let sub = MATCH_MP AUXOWN_SUBSET10 kth |> SPECL (sq_params iv) in
  let d10 = MATCH_MP CARD1_ENUM (CONJ sub eq) in
  let goal = list_mk_disj (map (fun j -> mk_eq(atm, set_tm [j])) [5; 6; 8]) in
  let mf = marker_facts own in
  let lf = map to_lform (filter (fun th -> not (is_neg (concl th))) mf) in
  let bottom = find (fun th -> rand(concl th) = `&457 / &500` && rand(rator(concl th)) = `&2`) lf in
  let central = find (fun th -> rand(concl th) = `&33 / &20` && rand(rator(concl th)) = `&47 / &20`) lf in
  let missing = to_lform (neg_at mf (`&33 / &20`, `&33 / &20`)) in
  let a0 = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) h1 in
  over_disj d10 (fun e ->
    let j = hd (eq_set e) in
    if mem j [5; 6; 8] then inject_disj goal e else
    let af = aux_facts 1 e in
    let pt = to_lform (find (fun th -> not (is_neg (concl th))) af) in
    if mem j [0; 2; 3] then
      let g5 = to_lform (neg_at af (`&113 / &50`, `&1`)) in
      let fb = MATCH_MP C84MB_FORBIDDEN (end_itlist CONJ [h3; h1; h2; bottom; central; missing; g5]) in
      let negs = CONJUNCTS fb in
      let ng = find (fun th -> aconv (rand(concl th)) (concl pt)) negs in
      CONTR goal (MP (NOT_ELIM ng) pt)
    else
      let d = MATCH_MP C84B_DIAMETER (end_itlist CONJ [h3; a0; h2; bottom; pt]) in
      CONTR goal (EQ_MP (REAL_RAT_REDUCE_CONV (concl d)) d));;

(* RelaxedOwnerDomain.ofSmallBudget (budget <= 2): every subset of size <= budget *)
let SMALL_NONEMPTY = prove
 (`forall S:num->bool. S SUBSET {x | x < 10} ==> S = {} \/ exists j. j < 10 /\ j IN S`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `S:num->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let small_budget_domain hnp hrow sq k =
  let (m, iv, lt, own, sqth) = sq in
  let hb = std_budget hnp hrow sq k in
  if dest_small_numeral (rand(concl hb)) > 2 then failwith "small_budget_domain: budget > 2" else
  let kth = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let atm = list_mk_comb(`auxown`, mk_small_numeral k :: sq_params iv) in
  let sub = MATCH_MP AUXOWN_SUBSET10 kth |> SPECL (sq_params iv) in
  let fin = SPECL (mk_small_numeral k :: sq_params iv) FINITE_AUXOWN in
  let hb2 = MP (ARITH_RULE (mk_imp(concl hb, mk_binop `(<=):num->num->bool` (lhand(concl hb)) `2`))) hb in
  let all = [] :: List.concat (map (fun j -> [j] :: map (fun v -> [j; v]) ((j+1) -- 9)) (0 -- 9)) in
  let goal = list_mk_disj (map (fun s -> mk_eq(atm, set_tm s)) all) in
  let th0 = MATCH_MP SMALL_NONEMPTY sub in
  let (d1, d2) = dest_disj (concl th0) in
  let c1 = inject_disj goal (TRANS (ASSUME d1) (SYM (REWRITE_CONV[set_of_list] (set_tm [])))) in
  let jv = `j:num` in
  let bj = snd (dest_exists d2) in
  let hj = ASSUME bj in
  let ltj = CONJUNCT1 hj and inj = CONJUNCT2 hj in
  let cases = EQ_MP (REWRITE_CONV[LT10_CASES] (concl ltj)) ltj |> fun th ->
    (* j = 0 \/ ... *) th in
  let c2 = over_disj cases (fun e ->
    let n = dest_small_numeral (rhs(concl e)) in
    let inn = EQ_MP (AP_THM (AP_TERM `(IN):num->(num->bool)->bool` e) atm) inj in
    let th = MATCH_MP (small2_lemma n) (end_itlist CONJ [sub; fin; hb2; inn]) in
    over_disj th (fun e2 -> inject_disj goal e2)) in
  let c2' = CHOOSE (jv, ASSUME d2) c2 in
  let th = DISJ_CASES th0 c1 c2' in
  restrict_card th hb (nonexempt_lower hnp sq k);;

(* ForcedAuxiliary.contains: idx IN auxown 2 (square of mask) under every assignment *)
let forced_point ctx m idx =
  let (_, iv, _, _, _) = csq ctx m in
  let a2 = list_mk_comb(`auxown`, `2` :: sq_params iv) in
  let goal = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral idx), a2) in
  fst (enum_dfs ctx goal (fun chosen ->
    let e = try assoc m chosen with Failure _ -> failwith "forced_point: no domain" in
    if not (mem idx (eq_set e)) then failwith (Printf.sprintf "case %d: point %d of %d not forced" ctx.cid idx m) else
    EQ_MP (SYM (CONV_RULE (RAND_CONV (REWRITE_CONV[IN_SET_OF_LIST; MEM] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[]))
                  (AP_TERM (mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral idx)) e))) TRUTH));;

(* |- vector[x;y] IN osq (square)  from |- idx IN auxown 2 (square) *)
let point_of_member th =
  let th1 = REWRITE_RULE[auxown; IN_ELIM_THM] th in
  let th2 = CONJUNCT2 th1 in
  CONV_RULE (ONCE_DEPTH_CONV EL_CONV) (REWRITE_RULE[AUXPTS_EXPL.(2)] th2);;

(* drop the kind-2 owner sets containing an auxiliary index whose point is farther than
   the square diameter from an owned seed point (MergedTopFurther.merged_top_diameter) *)
let diam_remove hnp sq dth idxs seed =
  let (m, iv, lt, own, sqth) = sq in
  let [h1; h2; h3; _] = sqth in
  let a0 = MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) h1 in
  let seeds = seeds_at (sq_params iv) sqth (marker_facts own) (bits m) in
  let sth = to_lform (pos_at seeds seed) in
  let bad s = exists (fun j -> mem j s) idxs in
  let ds = filter (fun t -> not (bad (map dest_small_numeral (dest_list (rand(rand t)))))) (disjuncts (concl dth)) in
  let goal = if ds = [] then `false` else list_mk_disj ds in
  over_disj dth (fun e ->
    let s = eq_set e in
    if not (bad s) then inject_disj goal e else
    let j = find (fun j -> mem j s) idxs in
    let af = aux_facts 2 e in
    let pts = filter (fun th -> not (is_neg (concl th))) af in
    let pt = to_lform (el (index j s) pts) in
    let d = MATCH_MP C84B_DIAMETER (end_itlist CONJ [h3; a0; h2; sth; pt]) in
    CONTR goal (EQ_MP (REAL_RAT_REDUCE_CONV (concl d)) d));;
