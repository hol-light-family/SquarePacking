(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C1072.lean                         *)
(* (N12Compact.CommonCases.C1072).  Original C1072, retaining its missing    *)
(* southwest corner; the four central/left-wall alternatives have one       *)
(* common top-wall advance.  The packing is NPACK c1 c2 a b l with family    *)
(* cc1072_family; owner p m is the 5-tuple (ooc .. m, oos .. m, oou .. m,    *)
(* oov .. m, l).  Domains: ofCombined is ro_combined; the private decide     *)
(* cuts are proved over the computed allowed lists.  seed / known_point /    *)
(* apart / auxiliary_exact / auxiliary_disjoint / missing_marker / domain:   *)
(* oo_seed, oo_known, oo_apart, oo_aux_point, OO_AUX_DISJOINT, oo_missing,   *)
(* OO_DOMAIN.  Geometry: CentralPair.impossible = CCCPAIR_IMPOSSIBLE,        *)
(* StrongBarPoint.point_original = CCSBP_POINT_ORIGINAL,                     *)
(* InwardPoint.point_original = CCIP_POINT_ORIGINAL,                         *)
(* C1092MixedSpan.impossible = C1092MS_IMPOSSIBLE,                           *)
(* C981CompletionWallAdvance.point = C981WA_POINT; pullX / pullY /           *)
(* Transform.pull <true,true,true> (= pullSwap (pullY (pullX q))) via        *)
(* LINSIDE_PULLX / _PULLY / _PULLSW; container_transform via LCONT_PULL*.    *)
(* ExcludesCase is excl_case, row 556.  Tag CC1072_.                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_CommonCases_CentralPair.ml";;
needs "n12/geometry/CP_CommonCases_StrongBarPoint.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/RowIdentity.ml";;

needs "n12/geometry/Helpers.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: family *)
let cc1072_family = new_definition
 `cc1072_family = {1,12,16,192,256,512,1024,2048,4096,8192,16384,32768}`;;
let CC1072_F = `cc1072_family`;;

(* ------------------------------------------------------------------------- *)
(* Literal list cuts (Lean: decide +kernel).                                 *)
(* ------------------------------------------------------------------------- *)

let cc1072_seteq_conv tm =
  let l, r = dest_eq tm in
  let ls = numset_of l and rs = numset_of r in
  if ls = rs then EQT_INTRO (setlit_eq l r) else
  let e = mk_small_numeral (hd (filter (fun x -> not (mem x rs)) ls @ filter (fun x -> not (mem x ls)) rs)) in
  let th = AP_TERM (mk_comb(`(IN):num->(num->bool)->bool`, e)) (ASSUME tm) in
  let f = CONV_RULE (BINOP_CONV (REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ])) th in
  EQF_INTRO (NOT_INTRO (DISCH tm (EQ_MP (REWRITE_CONV[] (concl f)) f)));;

let CC1072_DEC_CONV =
  REWRITE_CONV[DISJOINT_INSERT; DISJOINT_EMPTY; INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT;
               NOT_IN_EMPTY; ARITH_EQ; MEM] THENC
  DEPTH_CONV (fun t -> if is_eq t && type_of (lhs t) = `:num->bool` then cc1072_seteq_conv t
                       else failwith "") THENC
  REWRITE_CONV[];;

let CC1072_CUT_TAC =
  REWRITE_TAC[MEM] THEN
  REPEAT(GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
  CONV_TAC CC1072_DEC_CONV;;

(* ------------------------------------------------------------------------- *)
(* Domains and the private cuts.                                             *)
(* ------------------------------------------------------------------------- *)

(* Lean: southDomain, northDomain, leftDomain, topDomain, southwestDomain (private) *)
let CC1072_SOUTH_DOMAIN = ro_combined CC1072_F 5;;
let CC1072_NORTH_DOMAIN = ro_combined CC1072_F 12;;
let CC1072_LEFT_DOMAIN = ro_combined CC1072_F 16;;
let CC1072_TOP_DOMAIN = cdom_cache (ro_combined CC1072_F 22) `[{3,14}; {7,17}]`;;
let CC1072_SOUTHWEST_DOMAIN = cdom_cache (ro_combined CC1072_F 0) `[{2,12}]`;;

(* Lean: Pattern (private) *)
let cc1072_pattern = new_definition
 `cc1072_pattern (a:num->bool) (n:num->bool) <=>
    (a = {4,13} /\ MEM n [{1,11}; {5,11}]) \/
    (n = {5,13} /\ MEM a [{0,10}; {4,10}])`;;

let cc1072_mem_all v th = mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, v), rand (concl th));;

(* Lean: patterns_checked (private) *)
let CC1072_PATTERNS_CHECKED = prove
 (list_mk_forall([`a:num->bool`; `n:num->bool`; `l:num->bool`],
    mk_imp(cc1072_mem_all `a:num->bool` CC1072_SOUTH_DOMAIN,
    mk_imp(cc1072_mem_all `n:num->bool` CC1072_NORTH_DOMAIN,
    mk_imp(cc1072_mem_all `l:num->bool` CC1072_LEFT_DOMAIN,
    `DISJOINT a {2,12} ==> DISJOINT n {3,14} ==> DISJOINT a n ==> DISJOINT a l ==>
     DISJOINT n l ==> cc1072_pattern a n`)))),
  REWRITE_TAC[cc1072_pattern] THEN REWRITE_TAC[MEM] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC CC1072_DEC_CONV);;

(* ------------------------------------------------------------------------- *)
(* Owner facts under the hypothesis  NPACK .. /\ IMAGE .. = cc1072_family.   *)
(* ------------------------------------------------------------------------- *)

let CC1072_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let CC1072_HYP = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = cc1072_family`;;
let CC1072_HH = ASSUME CC1072_HYP;;
let CC1072_NP = CONJUNCT1 CC1072_HH;;
let cc1072_mp th = MP (SPECL CC1072_VARS th) CC1072_HH;;
let cc1072_q m = map (fun f -> list_mk_comb(f, CC1072_VARS @ [mk_small_numeral m]))
                   [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let cc1072_aux m = list_mk_comb(`ooaux`, CC1072_VARS @ [mk_small_numeral m]);;
let cc1072_pull tms q =
  match q with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms
  | _ -> failwith "cc1072_pull";;
let cc1072_pullx = cc1072_pull [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;
let cc1072_pully = cc1072_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let cc1072_pullsw = cc1072_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* Lean: seed_point (private) *)
let cc1072_seed m p = cc1072_mp (oo_inst CC1072_F (oo_seed m p));;
(* Lean: known (private) *)
let cc1072_known m eqth p =
  MP (SPECL CC1072_VARS (oo_inst CC1072_F (oo_known m (rhs (concl eqth)) p)))
     (CONJ CC1072_NP (CONJ (CONJUNCT2 CC1072_HH) eqth));;
let cc1072_apart m n = REWRITE_RULE[ldisj] (cc1072_mp (oo_apart CC1072_F m n));;
let cc1072_ldisj m n = cc1072_mp (oo_apart CC1072_F m n);;
let cc1072_foreign m n thn =
  let args = snd (strip_comb (concl thn)) in
  let d = SPECL [el 5 args; el 6 args] (cc1072_apart m n) in
  let a = lhand (rand (concl d)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d) (CONJ (ASSUME a) thn)));;
let cc1072_unit m = MP (SPECL (CC1072_VARS @ [mk_small_numeral m]) OO_UNIT) CC1072_NP;;
let cc1072_box m = MP (SPECL (CC1072_VARS @ [mk_small_numeral m]) OO_BOX) CC1072_NP;;
let CC1072_SIDE = MP (SPECL CC1072_VARS OO_SIDE) CC1072_NP;;
let CC1072_SIDE0 = MP (REAL_ARITH `&1 < l ==> &0 < l`) CC1072_SIDE;;
let cc1072_pt m j memth =
  EQ_MP (SYM (SPECL (CC1072_VARS @ [mk_small_numeral m]) (oo_aux_point j))) memth;;
let cc1072_mem_eq eqth j =
  let t = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j), lhs (concl eqth)) in
  let r = REWRITE_CONV[eqth; IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] t in
  if rand (concl r) = `true` then EQT_ELIM r else EQF_ELIM r;;
let cc1072_dom m d =
  MATCH_MP OO_DOMAIN (CONJ d (CONJ CC1072_NP (CONJ (CONJUNCT2 CC1072_HH) (in_fam m CC1072_F))));;
let cc1072_disj m n =
  MP (SPECL (CC1072_VARS @ [CC1072_F; mk_small_numeral m; mk_small_numeral n]) OO_AUX_DISJOINT)
     (end_itlist CONJ [CC1072_NP; CONJUNCT2 CC1072_HH; in_fam m CC1072_F; in_fam n CC1072_F;
                       EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n)))]);;
let cc1072_cutth th xs ths = List.fold_left MP (SPECL xs th) ths;;
let cc1072_close hyp_th = GENL CC1072_VARS (DISCH CC1072_HYP hyp_th);;
(* the whole segment between two owned points of one height:
   |- !z. x0 <= z ==> z <= x1 ==> linside .. z y *)
let cc1072_hseg_all th0 th1 =
  let args0 = snd (strip_comb (concl th0)) and args1 = snd (strip_comb (concl th1)) in
  let sq = fst (chop_list 5 args0) in
  let th = SPECL (sq @ [el 5 args0; el 5 args1; el 6 args0]) OO_HORIZONTAL_SEGMENT in
  let lt = EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_binop `(<):real->real->bool` (el 5 args0) (el 5 args1))) in
  let h0 = mk_binop `(<=):real->real->bool` (el 5 args0) `z:real`
  and h1 = mk_binop `(<=):real->real->bool` `z:real` (el 5 args1) in
  GEN `z:real` (DISCH h0 (DISCH h1 (MP (SPEC `z:real` th) (end_itlist CONJ
    [th0; th1; lt; ASSUME h0; ASSUME h1]))));;
(* the segment at a literal abscissa x *)
let cc1072_hseg th0 th1 x =
  let th = SPEC x (cc1072_hseg_all th0 th1) in
  let p1 = lhand (concl th) in
  let th = MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV p1)) in
  MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th))));;

let cc1072_is_rrel t =
  (is_eq t && type_of (lhs t) = `:real`) ||
  (try let op = fst (dest_const (rator (rator t))) in
       (op = "real_lt" || op = "real_le") with Failure _ -> false);;
let CC1072_DISCH_TAC (asl, w as g) =
  if is_forall w then (REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN ASM_MESON_TAC[]) g else
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MAP_EVERY (fun (_, th) -> if cc1072_is_rrel (concl th) then MP_TAC th else ALL_TAC) asl THEN
         REAL_ARITH_TAC] g;;
let cc1072_app th tup facts =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW; ldisj] THENC
                       ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (SPECL tup th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  let ant = lhand (concl th') in
  MP th' (TAC_PROOF((map (fun t -> ("", t)) facts, ant), REPEAT CONJ_TAC THEN CC1072_DISCH_TAC));;


(* a proved avoidance statement  !z. .. ==> ~linside (owner m) X Y  from a whole segment of
   owner n (|- !z. x0 <= z ==> z <= x1 ==> linside .. z y) and the apartness of m, n *)
let cc1072_avoid tm segall m n =
  let ap = cc1072_apart m n in
  TAC_PROOF(([], tm), REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun own -> if fst(strip_comb(concl own)) = `linside` then
      let args = snd (strip_comb (concl own)) in
      let x = el 5 args and y = el 6 args in
      MP_TAC(SPEC x segall) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      MP_TAC(SPECL [x; y] ap) THEN ASM_REWRITE_TAC[] else NO_TAC));;

(* the disjunctive pair facts of two labelled alternatives eq1 \/ eq2 *)
let cc1072_pair2 m opt (p1, p2) (q1, q2) swap =
  let eq1, eq2 = dest_disj (concl opt) in
  let a1 = cc1072_known m (ASSUME eq1) p1 and a2 = cc1072_known m (ASSUME eq1) p2 in
  let b1 = cc1072_known m (ASSUME eq2) q1 and b2 = cc1072_known m (ASSUME eq2) q2 in
  let l = CONJ a1 a2 and r = CONJ b1 b2 in
  if swap then DISJ_CASES opt (DISJ2 (concl r) l) (DISJ1 r (concl l))
  else DISJ_CASES opt (DISJ1 l (concl r)) (DISJ2 (concl l) r);;

(* Lean: entrance (private) *)
let CC1072_ENTRANCE =
  let seed = cc1072_seed and aux = cc1072_aux and dom = cc1072_dom and disj = cc1072_disj in
  let singleton = cc1072_hseg (seed 16 (`&113 / &50`, `&3`)) (seed 16 (`&72 / &25`, `&3`)) `&12 / &5` in
  let options = REWRITE_RULE[MEM] (dom 32768 CC1072_TOP_DOMAIN) in
  let o1, o2 = dest_disj (concl options) in
  let h = cc1072_pt 32768 7 (cc1072_mem_eq (ASSUME o2) 7) in
  let xy = snd (chop_list 5 (snd (strip_comb (concl h)))) in
  let bad = CONTR o1 (MP (NOT_ELIM (SPECL xy (cc1072_apart 32768 16))) (CONJ h singleton)) in
  let top = DISJ_CASES options (ASSUME o1) bad in
  let southwest = REWRITE_RULE[MEM] (dom 1 CC1072_SOUTHWEST_DOMAIN) in
  let aBottom = REWRITE_RULE[southwest] (disj 256 1) in
  let nTop = REWRITE_RULE[top] (disj 2048 32768) in
  let pat = cc1072_cutth CC1072_PATTERNS_CHECKED [aux 256; aux 2048; aux 4096]
    [dom 256 CC1072_SOUTH_DOMAIN; dom 2048 CC1072_NORTH_DOMAIN; dom 4096 CC1072_LEFT_DOMAIN;
     aBottom; nTop; disj 256 2048; disj 256 4096; disj 2048 4096] in
  cc1072_close (CONJ top pat);;

(* Lean: family_impossible *)
let CC1072_FAMILY_IMPOSSIBLE =
  let seed = cc1072_seed and foreign = cc1072_foreign and known = cc1072_known in
  let unit = cc1072_unit and side = CC1072_SIDE and side0 = CC1072_SIDE0 in
  let ent = MP (SPECL CC1072_VARS CC1072_ENTRANCE) CC1072_HH in
  let topLabel = CONJUNCT1 ent and pat = REWRITE_RULE[cc1072_pattern; MEM] (CONJUNCT2 ent) in
  let markA = seed 256 (`&33 / &20`, `&33 / &20`) in
  let markN = seed 2048 (`&33 / &20`, `&47 / &20`) in
  let markSE = seed 512 (`&47 / &20`, `&33 / &20`) in
  let markNE = seed 1024 (`&47 / &20`, `&47 / &20`) in
  let markL = seed 4096 (`&457 / &500`, `&2`) in
  let topMarker = seed 32768 (`&2`, `&1543 / &500`) in
  let topElbow = known 32768 topLabel (`&87 / &50`, `&3`) in
  let topOuter = known 32768 topLabel (`&8 / &5`, `&3`) in
  let trTip = seed 16 (`&113 / &50`, `&3`) in
  let trSeed = seed 16 (`&213 / &100`, `&81 / &25`) in
  let bottomLo = seed 1 (`&28 / &25`, `&1`) and bottomHi = seed 1 (`&87 / &50`, `&1`) in
  let bottomAll = cc1072_hseg_all bottomLo bottomHi in
  let bottom85 = cc1072_hseg bottomLo bottomHi `&8 / &5` in
  let corner = seed 192 (`&1`, `&3`) and cornerMarker = seed 192 (`&457 / &500`, `&3`) in
  let ptt q = cc1072_pullsw (cc1072_pully (cc1072_pullx q)) in
  let topAdvance = cc1072_app C981WA_POINT (ptt (cc1072_q 32768))
    [unit 32768; side; side0;
     MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (MATCH_MP LCONT_PULLX (cc1072_box 32768)));
     topMarker; topOuter; foreign 32768 16 trTip; foreign 32768 16 trSeed;
     foreign 32768 2048 markN] in
  let topAll = cc1072_hseg_all topAdvance topElbow in
  let lowerT, upperT = dest_disj (concl pat) in
  let lower =
    let h = ASSUME lowerT in
    let aLabel = CONJUNCT1 h and nOpt = CONJUNCT2 h in
    let inwardA = known 256 aLabel (`&2`, `&87 / &50`) in
    let elbowA = known 256 aLabel (`&87 / &50`, `&2`) in
    let pairN = cc1072_pair2 2048 nOpt ((`&1`, `&113 / &50`), (`&1`, `&12 / &5`))
                                       ((`&2`, `&113 / &50`), (`&1`, `&12 / &5`)) true in
    let avoidTop = cc1072_avoid
      `forall z. &113 / &50 <= z ==> z <= &14 / &5 ==>
           ~linside (ooc c1 c2 a b l 2048) (oos c1 c2 a b l 2048) (oou c1 c2 a b l 2048)
                    (oov c1 c2 a b l 2048) l (&4 - z) (&3)` topAll 2048 32768 in
    cc1072_app CCCPAIR_IMPOSSIBLE (cc1072_pullx (cc1072_q 256) @ cc1072_pullx (cc1072_q 2048))
      [unit 256; unit 2048; side; markA; inwardA; elbowA; foreign 256 512 markSE;
       foreign 256 1 bottom85; markN; pairN; foreign 2048 4096 markL; foreign 2048 192 corner;
       foreign 2048 192 cornerMarker; avoidTop; cc1072_apart 256 2048] in
  let upper =
    let h = ASSUME upperT in
    let nLabel = CONJUNCT1 h and aOpt = CONJUNCT2 h in
    let inwardN = known 2048 nLabel (`&2`, `&113 / &50`) in
    let elbowN = known 2048 nLabel (`&87 / &50`, `&2`) in
    let pyx q = cc1072_pully (cc1072_pullx q) in
    let inwardPoint = cc1072_app CCIP_POINT_ORIGINAL (pyx (cc1072_q 2048))
      [unit 2048; side; markN; inwardN; elbowN; foreign 2048 1024 markNE; foreign 2048 256 markA;
       foreign 2048 32768 topOuter] in
    let e1, e2 = dest_disj (concl aOpt) in
    let outward =
      let lab = ASSUME e1 in
      let outwardA = known 256 lab (`&1`, `&87 / &50`) and upperA = known 256 lab (`&1`, `&8 / &5`) in
      let missingH = cc1072_mp (oo_inst CC1072_F (oo_missing 256 1)) in
      let avoidBottom = cc1072_avoid
        `forall z. &113 / &50 <= z /\ z <= &143 / &50 ==>
             ~linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                      (oov c1 c2 a b l 256) l (&4 - z) (&1)` bottomAll 256 1 in
      let outwardPoint = cc1072_app CCSBP_POINT_ORIGINAL (pyx (cc1072_q 256))
        [unit 256; side; side0; markA; outwardA; upperA; foreign 256 2048 elbowN;
         foreign 256 4096 markL; missingH; avoidBottom] in
      let args = snd (strip_comb (concl outwardPoint)) in
      MP (NOT_ELIM (SPECL [el 5 args; el 6 args] (cc1072_apart 256 2048))) (CONJ outwardPoint inwardPoint) in
    let mixed =
      let lab = ASSUME e2 in
      let notF0 = REWRITE_RULE[GSYM (SPECL (CC1072_VARS @ [`256`]) (oo_aux_point 0))]
                    (cc1072_mem_eq lab 0) in
      cc1072_app C1092MS_IMPOSSIBLE (cc1072_pullx (cc1072_q 256))
        [unit 256; side; side0; known 256 lab (`&2`, `&87 / &50`); known 256 lab (`&1`, `&8 / &5`);
         foreign 256 2048 elbowN; notF0; foreign 256 1 bottomHi; foreign 256 1 bottom85] in
    DISJ_CASES aOpt outward mixed in
  let th = DISJ_CASES pat lower upper in
  if concl th <> `false` then failwith "CC1072_FAMILY_IMPOSSIBLE" else cc1072_close th;;

(* Lean: row_checked (private) / excludes *)
let CC1072_EXCLUDES = prove
 (`excl_case 1072`,
  REWRITE_TAC[ri_excludes_case_iff 556 `cc1072_family`; excl_fam] THEN
  MESON_TAC[CC1072_FAMILY_IMPOSSIBLE]);;

(* for the assembly: |- EXCLUDED_ROW 556 *)
let CC1072_EXCLUDED_ROW = ri_excluded_row 556 CC1072_EXCLUDES;;
