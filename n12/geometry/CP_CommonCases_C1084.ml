(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C1084.lean                         *)
(* (N12Compact.CommonCases.C1084).  C1084's complete original owner         *)
(* entrance and continuous ending.  The packing is NPACK c1 c2 a b l with    *)
(* family cc1084_family; owner p m is the 5-tuple (ooc .. m, oos .. m,       *)
(* oou .. m, oov .. m, l).  Domains: ofCombined is ro_combined,              *)
(* ofTransformedCombined (halfTurnPerm, MergedLower.halfturnedAllowed) is    *)
(* ro_transformed .. RO_HALFTURN RO_HALFTURN (mlh_halfturned_allowed 5).     *)
(* The private decide cuts are proved over the computed allowed lists.      *)
(* seed / known_point / apart / auxiliary_exact / auxiliary_disjoint /      *)
(* domain: oo_seed, oo_known, oo_apart, oo_aux_point, OO_AUX_DISJOINT,      *)
(* OO_DOMAIN.  Geometry: CentralPair.impossible = CCCPAIR_IMPOSSIBLE,        *)
(* C981CompletionWallAdvance.point = C981WA_POINT; pullY / pullSwap via      *)
(* LINSIDE_PULLY / LINSIDE_PULLSW, container_pullSwap / container_pullY are  *)
(* LCONT_PULLSW / LCONT_PULLY.  ExcludesCase is excl_case, row 568.          *)
(* Tag CC1084_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_CommonCases_CentralPair.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/Helpers.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: family *)
let cc1084_family = new_definition
 `cc1084_family = {1,12,48,64,256,512,1024,2048,4096,8192,16384,32768}`;;
let CC1084_F = `cc1084_family`;;

(* ------------------------------------------------------------------------- *)
(* Literal list cuts (Lean: decide +kernel).                                 *)
(* ------------------------------------------------------------------------- *)

let cc1084_seteq_conv tm =
  let l, r = dest_eq tm in
  let ls = numset_of l and rs = numset_of r in
  if ls = rs then EQT_INTRO (setlit_eq l r) else
  let e = mk_small_numeral (hd (filter (fun x -> not (mem x rs)) ls @ filter (fun x -> not (mem x ls)) rs)) in
  let th = AP_TERM (mk_comb(`(IN):num->(num->bool)->bool`, e)) (ASSUME tm) in
  let f = CONV_RULE (BINOP_CONV (REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ])) th in
  EQF_INTRO (NOT_INTRO (DISCH tm (EQ_MP (REWRITE_CONV[] (concl f)) f)));;

let CC1084_DEC_CONV =
  REWRITE_CONV[DISJOINT_INSERT; DISJOINT_EMPTY; INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT;
               NOT_IN_EMPTY; ARITH_EQ; MEM] THENC
  DEPTH_CONV (fun t -> if is_eq t && type_of (lhs t) = `:num->bool` then cc1084_seteq_conv t
                       else failwith "") THENC
  REWRITE_CONV[];;

let CC1084_CUT_TAC =
  REWRITE_TAC[MEM] THEN
  REPEAT(GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
  CONV_TAC CC1084_DEC_CONV;;

(* ------------------------------------------------------------------------- *)
(* Domains.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Lean: southDomain, rightDomain, bottomDomain, topDomain (private) *)
let CC1084_SOUTH_DOMAIN = ro_combined CC1084_F 7;;
let CC1084_RIGHT_DOMAIN = ro_combined CC1084_F 20;;
let CC1084_BOTTOM_DOMAIN = cdom_cache (ro_combined CC1084_F 18) `[{2,12}; {6,15}]`;;
let CC1084_TOP_DOMAIN = cdom_cache (ro_combined CC1084_F 22) `[{3,14}; {7,17}]`;;
(* Lean: northDomain (private) *)
let CC1084_NORTH_DOMAIN =
  ro_transformed CC1084_F 1024 (false, true, true) 5 RO_HALFTURN RO_HALFTURN (mlh_halfturned_allowed 5);;

(* Lean: southChoices, northChoices, Pattern (private) *)
let cc1084_south_choices = new_definition
 `cc1084_south_choices = [{4,16}; {4,18}; {8,16}; {8,18}]`;;
let cc1084_north_choices = new_definition
 `cc1084_north_choices = [{5,16}; {5,19}; {9,16}; {9,19}]`;;
let cc1084_pattern = new_definition
 `cc1084_pattern (a:num->bool) (n:num->bool) (r:num->bool) <=>
    (a = {4,16} /\ MEM n [{5,19}; {9,19}] /\ r = {8,18}) \/
    (n = {5,16} /\ MEM a [{4,18}; {8,18}] /\ r = {9,19})`;;

let cc1084_mem_all v th = mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, v), rand (concl th));;

(* Lean: south_filtered (private) *)
let CC1084_SOUTH_FILTERED = prove
 (mk_forall(`a:num->bool`, mk_imp(cc1084_mem_all `a:num->bool` CC1084_SOUTH_DOMAIN,
    `DISJOINT a {6,15} ==> MEM a cc1084_south_choices`)),
  REWRITE_TAC[cc1084_south_choices] THEN CC1084_CUT_TAC);;
(* Lean: north_filtered (private) *)
let CC1084_NORTH_FILTERED = prove
 (mk_forall(`n:num->bool`, mk_imp(cc1084_mem_all `n:num->bool` CC1084_NORTH_DOMAIN,
    `DISJOINT n {7,17} ==> MEM n cc1084_north_choices`)),
  REWRITE_TAC[cc1084_north_choices] THEN CC1084_CUT_TAC);;
(* Lean: patterns_checked (private) *)
let CC1084_PATTERNS_CHECKED = prove
 (list_mk_forall([`a:num->bool`; `n:num->bool`; `r:num->bool`],
    mk_imp(`MEM a cc1084_south_choices`, mk_imp(`MEM n cc1084_north_choices`,
    mk_imp(cc1084_mem_all `r:num->bool` CC1084_RIGHT_DOMAIN,
    `DISJOINT a n ==> DISJOINT a r ==> DISJOINT n r ==> cc1084_pattern a n r`)))),
  REWRITE_TAC[cc1084_south_choices; cc1084_north_choices; cc1084_pattern] THEN
  REWRITE_TAC[MEM] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC CC1084_DEC_CONV);;

(* ------------------------------------------------------------------------- *)
(* Owner facts under the hypothesis  NPACK .. /\ IMAGE .. = cc1084_family.   *)
(* ------------------------------------------------------------------------- *)

let CC1084_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let CC1084_HYP = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = cc1084_family`;;
let CC1084_HH = ASSUME CC1084_HYP;;
let CC1084_NP = CONJUNCT1 CC1084_HH;;
let cc1084_mp th = MP (SPECL CC1084_VARS th) CC1084_HH;;
let cc1084_q m = map (fun f -> list_mk_comb(f, CC1084_VARS @ [mk_small_numeral m]))
                   [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let cc1084_aux m = list_mk_comb(`ooaux`, CC1084_VARS @ [mk_small_numeral m]);;
let cc1084_pull tms q =
  match q with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms
  | _ -> failwith "cc1084_pull";;
let cc1084_pully = cc1084_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let cc1084_pullsw = cc1084_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* Lean: inside_seed (private) *)
let cc1084_seed m p = cc1084_mp (oo_inst CC1084_F (oo_seed m p));;
(* Lean: inside_known (private) *)
let cc1084_known m eqth p =
  MP (SPECL CC1084_VARS (oo_inst CC1084_F (oo_known m (rhs (concl eqth)) p)))
     (CONJ CC1084_NP (CONJ (CONJUNCT2 CC1084_HH) eqth));;
let cc1084_apart m n = REWRITE_RULE[ldisj] (cc1084_mp (oo_apart CC1084_F m n));;
let cc1084_ldisj m n = cc1084_mp (oo_apart CC1084_F m n);;
let cc1084_foreign m n thn =
  let args = snd (strip_comb (concl thn)) in
  let d = SPECL [el 5 args; el 6 args] (cc1084_apart m n) in
  let a = lhand (rand (concl d)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d) (CONJ (ASSUME a) thn)));;
let cc1084_unit m = MP (SPECL (CC1084_VARS @ [mk_small_numeral m]) OO_UNIT) CC1084_NP;;
let cc1084_box m = MP (SPECL (CC1084_VARS @ [mk_small_numeral m]) OO_BOX) CC1084_NP;;
let CC1084_SIDE = MP (SPECL CC1084_VARS OO_SIDE) CC1084_NP;;
let CC1084_SIDE0 = MP (REAL_ARITH `&1 < l ==> &0 < l`) CC1084_SIDE;;
let cc1084_pt m j memth =
  EQ_MP (SYM (SPECL (CC1084_VARS @ [mk_small_numeral m]) (oo_aux_point j))) memth;;
let cc1084_mem_eq eqth j =
  let t = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j), lhs (concl eqth)) in
  let r = REWRITE_CONV[eqth; IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] t in
  if rand (concl r) = `true` then EQT_ELIM r else EQF_ELIM r;;
let cc1084_dom m d =
  MATCH_MP OO_DOMAIN (CONJ d (CONJ CC1084_NP (CONJ (CONJUNCT2 CC1084_HH) (in_fam m CC1084_F))));;
let cc1084_disj m n =
  MP (SPECL (CC1084_VARS @ [CC1084_F; mk_small_numeral m; mk_small_numeral n]) OO_AUX_DISJOINT)
     (end_itlist CONJ [CC1084_NP; CONJUNCT2 CC1084_HH; in_fam m CC1084_F; in_fam n CC1084_F;
                       EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n)))]);;
let cc1084_cutth th xs ths = List.fold_left MP (SPECL xs th) ths;;
let cc1084_close hyp_th = GENL CC1084_VARS (DISCH CC1084_HYP hyp_th);;
(* the whole segment between two owned points of one height:
   |- !z. x0 <= z ==> z <= x1 ==> linside .. z y *)
let cc1084_hseg_all th0 th1 =
  let args0 = snd (strip_comb (concl th0)) and args1 = snd (strip_comb (concl th1)) in
  let sq = fst (chop_list 5 args0) in
  let th = SPECL (sq @ [el 5 args0; el 5 args1; el 6 args0]) OO_HORIZONTAL_SEGMENT in
  let lt = EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_binop `(<):real->real->bool` (el 5 args0) (el 5 args1))) in
  let h0 = mk_binop `(<=):real->real->bool` (el 5 args0) `z:real`
  and h1 = mk_binop `(<=):real->real->bool` `z:real` (el 5 args1) in
  GEN `z:real` (DISCH h0 (DISCH h1 (MP (SPEC `z:real` th) (end_itlist CONJ
    [th0; th1; lt; ASSUME h0; ASSUME h1]))));;
(* the segment at a literal abscissa x *)
let cc1084_hseg th0 th1 x =
  let th = SPEC x (cc1084_hseg_all th0 th1) in
  let p1 = lhand (concl th) in
  let th = MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV p1)) in
  MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th))));;

let cc1084_is_rrel t =
  (is_eq t && type_of (lhs t) = `:real`) ||
  (try let op = fst (dest_const (rator (rator t))) in
       (op = "real_lt" || op = "real_le") with Failure _ -> false);;
let CC1084_DISCH_TAC (asl, w as g) =
  if is_forall w then (REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN ASM_MESON_TAC[]) g else
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MAP_EVERY (fun (_, th) -> if cc1084_is_rrel (concl th) then MP_TAC th else ALL_TAC) asl THEN
         REAL_ARITH_TAC] g;;
let cc1084_app th tup facts =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLY; LINSIDE_PULLSW; ldisj] THENC
                       ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (SPECL tup th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  let ant = lhand (concl th') in
  MP th' (TAC_PROOF((map (fun t -> ("", t)) facts, ant), REPEAT CONJ_TAC THEN CC1084_DISCH_TAC));;

(* Lean: bottom_top (private) *)
let CC1084_BOTTOM_TOP =
  let seed = cc1084_seed in
  let sw = cc1084_hseg (seed 1 (`&28 / &25`, `&1`)) (seed 1 (`&87 / &50`, `&1`)) `&8 / &5` in
  let nw = cc1084_hseg (seed 64 (`&28 / &25`, `&3`)) (seed 64 (`&87 / &50`, `&3`)) `&8 / &5` in
  let side m d j other seg =
    let options = REWRITE_RULE[MEM] (cc1084_dom m d) in
    let o1, o2 = dest_disj (concl options) in
    let h = cc1084_pt m j (cc1084_mem_eq (ASSUME o1) j) in
    let xy = snd (chop_list 5 (snd (strip_comb (concl h)))) in
    let bad = CONTR o2 (MP (NOT_ELIM (SPECL xy (cc1084_apart m other))) (CONJ h seg)) in
    DISJ_CASES options bad (ASSUME o2) in
  let bottom = side 8192 CC1084_BOTTOM_DOMAIN 2 1 sw in
  let top = side 32768 CC1084_TOP_DOMAIN 3 64 nw in
  cc1084_close (CONJ bottom top);;

(* Lean: central_pattern (private) *)
let CC1084_CENTRAL_PATTERN =
  let aux = cc1084_aux and dom = cc1084_dom and disj = cc1084_disj and cut = cc1084_cutth in
  let btm = `ooaux c1 c2 a b l 8192 = {6, 15}` and tp = `ooaux c1 c2 a b l 32768 = {7, 17}` in
  let south = dom 512 CC1084_SOUTH_DOMAIN and north = dom 1024 CC1084_NORTH_DOMAIN in
  let right = dom 16384 CC1084_RIGHT_DOMAIN in
  let southBottom = REWRITE_RULE[ASSUME btm] (disj 512 8192) in
  let northTop = REWRITE_RULE[ASSUME tp] (disj 1024 32768) in
  let sc = cut CC1084_SOUTH_FILTERED [aux 512] [south; southBottom] in
  let nc = cut CC1084_NORTH_FILTERED [aux 1024] [north; northTop] in
  let th = cut CC1084_PATTERNS_CHECKED [aux 512; aux 1024; aux 16384]
             [sc; nc; right; disj 512 1024; disj 512 16384; disj 1024 16384] in
  let h = list_mk_conj [`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = cc1084_family`; btm; tp] in
  let cs = CONJUNCTS (ASSUME h) in
  GENL CC1084_VARS (DISCH h (PROVE_HYP (CONJ (el 0 cs) (el 1 cs))
    (PROVE_HYP (el 2 cs) (PROVE_HYP (el 3 cs) th))));;

(* Lean: family_impossible *)
let CC1084_FAMILY_IMPOSSIBLE =
  let seed = cc1084_seed and foreign = cc1084_foreign and known = cc1084_known in
  let unit = cc1084_unit and side = CC1084_SIDE and side0 = CC1084_SIDE0 in
  let bt = MP (SPECL CC1084_VARS CC1084_BOTTOM_TOP) CC1084_HH in
  let bottomLabel = CONJUNCT1 bt and topLabel = CONJUNCT2 bt in
  let markSW = seed 256 (`&33 / &20`, `&33 / &20`) in
  let markSE = seed 512 (`&47 / &20`, `&33 / &20`) in
  let markNE = seed 1024 (`&47 / &20`, `&47 / &20`) in
  let markNW = seed 2048 (`&33 / &20`, `&47 / &20`) in
  let bottomMarker = seed 8192 (`&2`, `&457 / &500`) in
  let topMarker = seed 32768 (`&2`, `&1543 / &500`) in
  let rightMarker = seed 16384 (`&1543 / &500`, `&2`) in
  let bottomElbow = known 8192 bottomLabel (`&113 / &50`, `&1`) in
  let bottomOuter = known 8192 bottomLabel (`&12 / &5`, `&1`) in
  let topElbow = known 32768 topLabel (`&113 / &50`, `&3`) in
  let topOuter = known 32768 topLabel (`&12 / &5`, `&3`) in
  let swTip = seed 1 (`&87 / &50`, `&1`) in
  let swSeed = seed 1 (`&187 / &100`, `&19 / &25`) in
  let nwTip = seed 64 (`&87 / &50`, `&3`) in
  let nwSeed = seed 64 (`&187 / &100`, `&81 / &25`) in
  let bottomAdvance = cc1084_app C981WA_POINT (cc1084_pullsw (cc1084_q 8192))
    [unit 8192; side; side0; MATCH_MP LCONT_PULLSW (cc1084_box 8192); bottomMarker; bottomOuter;
     foreign 8192 1 swTip; foreign 8192 1 swSeed; foreign 8192 512 markSE] in
  let topAdvance = cc1084_app C981WA_POINT (cc1084_pullsw (cc1084_pully (cc1084_q 32768)))
    [unit 32768; side; side0; MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (cc1084_box 32768));
     topMarker; topOuter; foreign 32768 64 nwTip; foreign 32768 64 nwSeed;
     foreign 32768 1024 markNE] in
  let segall = cc1084_hseg_all in
  let avoid all m n =
    let th = SPEC `z:real` all in
    let h0 = lhand (concl th) in let h1 = lhand (rand (concl th)) in
    let seg = MP (MP th (ASSUME h0)) (ASSUME h1) in
    GEN `z:real` (DISCH h0 (DISCH h1 (foreign m n seg))) in
  let lowerAll = segall bottomElbow bottomAdvance and upperAll = segall topElbow topAdvance in
  let seCorner = seed 12 (`&3`, `&1`) and seCornerMarker = seed 12 (`&1543 / &500`, `&1`) in
  let neCorner = seed 48 (`&3`, `&3`) and neCornerMarker = seed 48 (`&1543 / &500`, `&3`) in
  let pat = REWRITE_RULE[cc1084_pattern; MEM]
    (MP (SPECL CC1084_VARS CC1084_CENTRAL_PATTERN) (end_itlist CONJ [CC1084_NP; CONJUNCT2 CC1084_HH;
                                                                   bottomLabel; topLabel])) in
  let lowerT, upperT = dest_disj (concl pat) in
  let pair2 m eq1 eq2 (p1, p2) (q1, q2) =
    let a1 = known m (ASSUME eq1) p1 and a2 = known m (ASSUME eq1) p2 in
    let b1 = known m (ASSUME eq2) q1 and b2 = known m (ASSUME eq2) q2 in
    let l = CONJ a1 a2 and r = CONJ b1 b2 in
    let t = mk_disj(concl l, concl r) in
    DISJ_CASES (ASSUME (mk_disj(eq1, eq2))) (DISJ1 l (concl r)) (DISJ2 (concl l) r), t in
  let lower =
    let h = ASSUME lowerT in
    let aLabel = CONJUNCT1 h and nOpt = CONJUNCT1 (CONJUNCT2 h) in
    let inwardA = known 512 aLabel (`&2`, `&87 / &50`) in
    let elbowA = known 512 aLabel (`&113 / &50`, `&2`) in
    let e1, e2 = dest_disj (concl nOpt) in
    let pairN, _ = pair2 1024 e1 e2 ((`&2`, `&113 / &50`), (`&3`, `&12 / &5`))
                                     ((`&3`, `&113 / &50`), (`&3`, `&12 / &5`)) in
    let pairN = PROVE_HYP nOpt pairN in
    cc1084_app CCCPAIR_IMPOSSIBLE (cc1084_q 512 @ cc1084_q 1024)
      [unit 512; unit 1024; side; markSE; inwardA; elbowA; foreign 512 256 markSW;
       foreign 512 8192 bottomOuter; markNE; pairN; foreign 1024 16384 rightMarker;
       foreign 1024 48 neCorner; foreign 1024 48 neCornerMarker; avoid upperAll 1024 32768;
       cc1084_apart 512 1024] in
  let upper =
    let h = ASSUME upperT in
    let nLabel = CONJUNCT1 h and aOpt = CONJUNCT1 (CONJUNCT2 h) in
    let inwardN = known 1024 nLabel (`&2`, `&113 / &50`) in
    let elbowN = known 1024 nLabel (`&113 / &50`, `&2`) in
    let e1, e2 = dest_disj (concl aOpt) in
    let pairA, _ = pair2 512 e1 e2 ((`&2`, `&87 / &50`), (`&3`, `&8 / &5`))
                                    ((`&3`, `&87 / &50`), (`&3`, `&8 / &5`)) in
    let pairA = PROVE_HYP aOpt pairA in
    cc1084_app CCCPAIR_IMPOSSIBLE (cc1084_pully (cc1084_q 1024) @ cc1084_pully (cc1084_q 512))
      [unit 512; unit 1024; side; markNE; inwardN; elbowN; foreign 1024 2048 markNW;
       foreign 1024 32768 topOuter; markSE; pairA; foreign 512 16384 rightMarker;
       foreign 512 12 seCorner; foreign 512 12 seCornerMarker; avoid lowerAll 512 8192;
       cc1084_apart 1024 512] in
  let th = DISJ_CASES pat lower upper in
  if concl th <> `false` then failwith "CC1084_FAMILY_IMPOSSIBLE" else cc1084_close th;;

(* Lean: row_checked (private) / excludes *)
let CC1084_EXCLUDES = prove
 (`excl_case 1084`,
  REWRITE_TAC[ri_excludes_case_iff 568 `cc1084_family`; excl_fam] THEN
  MESON_TAC[CC1084_FAMILY_IMPOSSIBLE]);;

(* for the assembly: |- EXCLUDED_ROW 568 *)
let CC1084_EXCLUDED_ROW = ri_excluded_row 568 CC1084_EXCLUDES;;
