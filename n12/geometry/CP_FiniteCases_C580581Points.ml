(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C580581Points.lean                 *)
(* (N12Compact.FiniteCases.C580581Points).  Compulsory F points for both     *)
(* original merged-left families (v = 0: c580e_family0, bottomMask 8192;     *)
(* v = 1: c580e_family1, bottomMask 8196).  Statements indexed by v : Fin 2  *)
(* are OCaml arrays of the two theorems.  Private domains: ofCombined =      *)
(* ro_combined, ofTransformedCombined = ro_transformed (reflectedAllowed =   *)
(* mlh_reflected_allowed), OwnerBudget.product = pk_product,                 *)
(* ofSmallBudgetWithSeed = ro_small_budget_seed, HalfDomain.ofSeedHull =     *)
(* pk_hdom_seedhull.  The private checked cuts are stated over the computed  *)
(* allowed lists and decided literally.  secondHalf = rosecond.              *)
(* Tag FC580P_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C580581Entrance.ml";;
needs "n12/geometry/Helpers.ml";;

let FC580P_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* ------------------------------------------------------------------------- *)
(* Domains.                                                                  *)
(* ------------------------------------------------------------------------- *)

let fc580p_rat s = nlin_rat s;;

(* Lean: southwest, west, south, east, north, upper, lower (private) *)
let FC580P_SOUTHWEST = Array.init 2 (fun v -> ro_combined C580E_FAM.(v) 1);;
let FC580P_WEST = Array.init 2 (fun v -> ro_combined C580E_FAM.(v) 17);;
let FC580P_SOUTH = Array.init 2 (fun v -> ro_combined C580E_FAM.(v) 8);;
let FC580P_EAST = Array.init 2 (fun v -> ro_combined C580E_FAM.(v) 21);;
let FC580P_NORTH = Array.init 2 (fun v ->
  ro_transformed C580E_FAM.(v) 1024 (false, true, false) 13 RO_REFLECTXF RO_REFLECTXG
    (mlh_reflected_allowed 13));;
let FC580P_UPPER = Array.init 2 (fun v -> ro_combined C580E_FAM.(v) 23);;
let FC580P_LOWER = Array.init 2 (fun v ->
  if v = 0 then ro_combined C580E_FAM.(0) 19 else
  pk_product
    (ro_small_budget_seed C580E_FAM.(1) 8196 0 6
       ([(fc580p_rat "9/4", num 1); (fc580p_rat "11/4", num 1); (fc580p_rat "9/4", num 1)],
        (fc580p_rat "12/5", num 1), fc580p_rat "3/10", num 0))
    (pk_hdom_seedhull C580E_FAM.(1) 8196 1 5
       ([(fc580p_rat "9/4", num 1); (fc580p_rat "11/4", num 1); (fc580p_rat "9/4", num 1)],
        (fc580p_rat "113/50", num 1), fc580p_rat "1/50", num 0)));;

(* ------------------------------------------------------------------------- *)
(* Literal cuts over the computed allowed lists (Lean: decide +kernel).      *)
(* ------------------------------------------------------------------------- *)

let fc580p_seteq_conv tm =
  let l, r = dest_eq tm in
  let ls = numset_of l and rs = numset_of r in
  if ls = rs then EQT_INTRO (setlit_eq l r) else
  let e = mk_small_numeral (hd (filter (fun x -> not (mem x rs)) ls @ filter (fun x -> not (mem x ls)) rs)) in
  let th = AP_TERM (mk_comb(`(IN):num->(num->bool)->bool`, e)) (ASSUME tm) in
  let f = CONV_RULE (BINOP_CONV (REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ])) th in
  EQF_INTRO (NOT_INTRO (DISCH tm (EQ_MP (REWRITE_CONV[] (concl f)) f)));;

(* rosecond S = S' for a literal S *)
let fc580p_rosecond_conv tm =
  if not (is_comb tm && rator tm = `rosecond`) then failwith "fc580p_rosecond_conv" else
  let r = mk_numset (filter (fun x -> x >= 10) (numset_of (rand tm))) in
  prove(mk_eq(tm, r),
    REWRITE_TAC[rosecond; EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let FC580P_DEC_CONV =
  DEPTH_CONV fc580p_rosecond_conv THENC
  REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; MEM] THENC
  DEPTH_CONV (fun t -> if is_eq t && type_of (lhs t) = `:num->bool` then fc580p_seteq_conv t
                       else failwith "") THENC
  REWRITE_CONV[];;

let FC580P_CUT_TAC =
  REWRITE_TAC[MEM] THEN
  TRY(GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC FC580P_DEC_CONV);;

let fc580p_cut th body =
  let s = `s:num->bool` in
  prove(mk_forall(s, mk_imp(mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, s), rand (concl th)),
                            body)), FC580P_CUT_TAC);;

(* Lean: checked (local cuts of compulsory), for each v *)
let FC580P_SW_CHECKED = Array.map (fun th -> fc580p_cut th `2 IN s`) FC580P_SOUTHWEST;;
let FC580P_LOWER_CHECKED = Array.map (fun th -> fc580p_cut th `rosecond s = {15} ==> 6 IN s`) FC580P_LOWER;;
let FC580P_WEST_CHECKED = Array.map (fun th -> fc580p_cut th `rosecond s = {11} ==> 1 IN s`) FC580P_WEST;;
let FC580P_EAST_CHECKED = Array.map (fun th -> fc580p_cut th `rosecond s = {19} ==> 9 IN s`) FC580P_EAST;;
let FC580P_UPPER_CHECKED = Array.map (fun th -> fc580p_cut th `rosecond s = {14} ==> 3 IN s`) FC580P_UPPER;;
let FC580P_SOUTH_CHECKED = Array.map (fun th ->
  fc580p_cut th `rosecond s = {16} ==> ~(6 IN s) ==> ~(8 IN s) ==> 4 IN s`) FC580P_SOUTH;;
let FC580P_NORTH_CHECKED = Array.map (fun th ->
  fc580p_cut th `rosecond s = {17} ==> ~(9 IN s) ==> 5 IN s \/ 7 IN s`) FC580P_NORTH;;

(* ------------------------------------------------------------------------- *)
(* g_part, foreign_aux, compulsory.                                          *)
(* ------------------------------------------------------------------------- *)

let fc580p_aux m = list_mk_comb(`ooaux`, FC580P_VARS @ [mk_small_numeral m]);;

(* Lean: g_part  (conjunction over the ten claims i) *)
let FC580P_G_PART = Array.init 2 (fun v ->
  let goal = list_mk_conj (map (fun (m, j) ->
      mk_eq(mk_comb(`rosecond`, fc580p_aux m), mk_numset [j + 10])) (c580e_claims v)) in
  prove(c580e_all v goal,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (SPEC_ALL C580E_FORCED.(v)) THEN ASM_REWRITE_TAC[c580e_G] THEN STRIP_TAC THEN
    REWRITE_TAC[ooaux; AUXOWN2_COMBOWN] THEN
    SIMP_TAC[RO_SECOND_COMBINED; AUXOWN_SUBSET10; ARITH_RULE `0 < 2`] THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV));;

(* Lean: foreign_aux (private; stated for any family) *)
let FC580P_FOREIGN_AUX = prove
 (`forall c1 c2 a b l fam m n index.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     m IN fam /\ n IN fam /\ ~(m = n) /\ index IN ooaux c1 c2 a b l n
     ==> ~(index IN ooaux c1 c2 a b l m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `m:num`; `n:num`] OO_AUX_DISJOINT) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Lean: compulsory *)
let FC580P_COMPULSORY = Array.init 2 (fun v ->
  let fam = C580E_FAM.(v) and bm = C580E_BOTTOM.(v) in
  let hyp = c580e_hyp v in
  let hh = ASSUME hyp in
  let np = CONJUNCT1 hh in
  let dom m d = MATCH_MP OO_DOMAIN (CONJ d (CONJ np (CONJ (CONJUNCT2 hh) (in_fam m fam)))) in
  let cut th m ths = List.fold_left MP (SPEC (fc580p_aux m) th) ths in
  let gp = CONJUNCTS (MP (SPECL FC580P_VARS FC580P_G_PART.(v)) hh) in
  let g m = find (fun th -> lhand (concl th) = mk_comb(`rosecond`, fc580p_aux m)) gp in
  let seed m p = MP (SPECL FC580P_VARS (oo_inst fam (oo_seed m p))) hh in
  let pt m j th = EQ_MP (SPECL (FC580P_VARS @ [mk_small_numeral m]) (oo_aux_point j)) th in
  let foreign m n j th =
    MP (SPECL (FC580P_VARS @ [fam; mk_small_numeral m; mk_small_numeral n; mk_small_numeral j])
          FC580P_FOREIGN_AUX)
       (end_itlist CONJ [np; CONJUNCT2 hh; in_fam m fam; in_fam n fam;
                         EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n))); th]) in
  let sw = cut FC580P_SW_CHECKED.(v) 1 [dom 1 FC580P_SOUTHWEST.(v)] in
  let low = pt 2 0 (seed 2 (`&1`, `&87 / &50`)) in
  let se = pt 8 8 (seed 8 (`&3`, `&87 / &50`)) in
  let bottom = cut FC580P_LOWER_CHECKED.(v) bm [dom bm FC580P_LOWER.(v); g bm] in
  let left = cut FC580P_WEST_CHECKED.(v) 4096 [dom 4096 FC580P_WEST.(v); g 4096] in
  let right = cut FC580P_EAST_CHECKED.(v) 16384 [dom 16384 FC580P_EAST.(v); g 16384] in
  let top = cut FC580P_UPPER_CHECKED.(v) 32768 [dom 32768 FC580P_UPPER.(v); g 32768] in
  let south = cut FC580P_SOUTH_CHECKED.(v) 512
    [dom 512 FC580P_SOUTH.(v); g 512; foreign 512 bm 6 bottom; foreign 512 8 8 se] in
  let north = cut FC580P_NORTH_CHECKED.(v) 1024
    [dom 1024 FC580P_NORTH.(v); g 1024; foreign 1024 16384 9 right] in
  let th = end_itlist CONJ [sw; low; se; bottom; left; south; right; top; north] in
  GENL FC580P_VARS (DISCH hyp th));;
