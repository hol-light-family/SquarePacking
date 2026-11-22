(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedPending/UpperCenters.lean    *)
(* (namespace N12Compact.MergedPending).  Actual center and southwest-face  *)
(* cuts for the three pending merged families.  Conventions of             *)
(* Families.ml / UpperSectors.ml: Lean Case k is the entry of MPF_FAMILIES, *)
(* a theorem for all k is an OCaml list (same order); owner p m is the      *)
(* OriginalOwners tuple (mpwr_tuple m).  The arbitrary OpenSquares H, A are *)
(* cH sH uH vH aH, cA sA uA vA aA with their invariants (unit normal,        *)
(* 0 < side) as explicit hypotheses; (owner p m).side is l.  The statements  *)
(* for all k keep the hypothesis 3072 IN family k (vacuous for c700).       *)
(* upper_center is MPUCC_UPPER_CENTER, UpperData.reframe MPUSC_REFRAME,      *)
(* UpperData.nonnegative_residue MPUCC_NONNEGATIVE_RESIDUE; pullSwap         *)
(* (c,s,u,v,a) is (s,c,u,--v - a,a) (LINSIDE_PULLSW).  Tag MPUC_.            *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_UpperSectors.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_UpperCenterCore.ml";;

let MPUC_H = [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`];;
let MPUC_A = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`];;
let mpuc_lin sq x y = list_mk_comb(`linside`, sq @ [x; y]);;
let mpuc_equiv sq m swap =
  list_mk_forall([`x:real`; `y:real`],
    mk_iff(mpuc_lin sq `x:real` `y:real`,
           if swap then mpwr_inside m `y:real` `x:real` else mpwr_inside m `x:real` `y:real`));;
let mpuc_sqhyps sq = match sq with
    [c; s; u; v; a] -> [mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                                (mk_binop `( * ):real->real->real` s s), `&1`);
                        mk_binop `(<):real->real->bool` `&0` a]
  | _ -> failwith "mpuc_sqhyps";;
let mpuc_h_hyps = [`&0 < cH`; `&0 <= sH`; `sH <= cH`];;
let mpuc_stmt fam member hyps body =
  list_mk_forall(MPWR_VARS @ MPUC_H, mk_imp(list_mk_conj ([`NPACK c1 c2 a b l`;
     mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)] @
     (if member then [mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `3072`), fam)] else []) @ hyps),
     body));;

(* move the hypothesis NPACK .. /\ IMAGE .. = fam of a fact to the two goal assumptions *)
let mpuc_fix fam th =
  PROVE_HYP (CONJ (ASSUME `NPACK c1 c2 a b l`) (ASSUME (mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)))) th;;

(* close a goal from a list of facts, after rewriting through the inside equivalences *)
let MPUC_FACTS_TAC facts =
  REPEAT CONJ_TAC THEN
  FIRST (map (fun th -> ACCEPT_TAC (mpcp_norm th)) facts @
         [ASM_REWRITE_TAC[] THEN NO_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: upper_nonnegative_center *)
let MPUC_UPPER_NONNEGATIVE_CENTER = map (fun fam ->
  let hyps = mpuc_sqhyps MPUC_H @ mpuc_h_hyps @ [`aH:real = l`; mpuc_equiv MPUC_H 3072 false] in
  let tm = mpuc_stmt fam true hyps (mpuc_lin MPUC_H `&2` `&2`) in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  let i = index fam MPF_FAMILIES in
  let np = mpwr_np fam in
  let marks = CONJUNCTS (mpus_inst_member fam 3072 (el i MPF_UPPER_MERGED_MARKERS)) in
  let lab = mpwr_labels fam and w = mpcp_walls fam in
  let left = mpwr_auxpt 4096 11 (el 3 lab) and far = mpwr_auxpt 32768 3 (el 6 lab) in
  let near = mpwr_auxpt 32768 14 (el 7 lab) in
  let mark = mpwr_seed fam 32768 (`&2`, `&1543 / &500`) in
  let excl n th = mpcp_excl fam 3072 n th in
  let facts = [MP (SPECL MPWR_VARS OO_SIDE) np; MP (REAL_ARITH `&1 < l ==> &0 < l`) (MP (SPECL MPWR_VARS OO_SIDE) np); MP (SPECL (MPWR_VARS @ [`32768`]) OO_UNIT) np;
               MP (SPECL (MPWR_VARS @ [`32768`]) OO_BOX) np; el 0 marks; el 1 marks;
               excl 16 (mpwr_bar (el 2 w) `&113 / &50`); excl 32768 near; excl 4096 left;
               mark; far] in
  let ap = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam 3072 32768)) in
  let th = TAC_PROOF(([], tm),
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MPUCC_UPPER_CENTER THEN
    MAP_EVERY EXISTS_TAC (mpwr_tuple 32768) THEN
    REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST (map (fun th -> ACCEPT_TAC (mpuc_fix fam (mpcp_norm th))) facts @
           [ASM_REAL_ARITH_TAC; MATCH_ACCEPT_TAC (mpuc_fix fam ap)])) in
  prove(tm, MESON_TAC[th])) MPF_FAMILIES;;

(* Lean: upper_nonnegative_residue *)
let MPUC_UPPER_NONNEGATIVE_RESIDUE = map2 (fun fam center ->
  let hyps = mpuc_sqhyps MPUC_A @ mpuc_sqhyps MPUC_H @
             [`&0 < cA`; `abs sA <= cA`] @ mpuc_h_hyps @
             [`aA:real = l`; `aH:real = l`; mpuc_equiv MPUC_A 256 false; mpuc_equiv MPUC_H 3072 false] in
  let body = list_mk_conj [`sA < &0`; mpwr_inside 1 `&1` `&1`; mpuc_lin MPUC_H `&2` `&2`;
                           `vA + aA <= &2 * (cA - sA)`] in
  let tm = list_mk_forall(MPWR_VARS @ MPUC_A @ MPUC_H, mk_imp(list_mk_conj ([`NPACK c1 c2 a b l`;
     mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam);
     mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `3072`), fam)] @ hyps), body)) in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  let i = index fam MPF_FAMILIES in
  let data = el i MPUS_UPPER_DATA in
  let cross = CONJUNCT1 (mpwr_inst fam (el i MPCP_SOUTHWEST_CROSSPOINTS)) in
  prove(tm,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `aA:real = l` || concl th = `aH:real = l`))) THEN
    SUBGOAL_THEN (subst [`l:real`, `aH:real`] (mpuc_lin MPUC_H `&2` `&2`)) ASSUME_TAC THENL
     [MP_TAC(SPECL (MPWR_VARS @ map (subst [`l:real`, `aH:real`]) MPUC_H) center) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL (map (subst [`l:real`, `aA:real`; `l:real`, `aH:real`]) (MPUC_A @ MPUC_H) @ mpwr_tuple 1 @ mpwr_tuple 2) MPUCC_NONNEGATIVE_RESIDUE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[lsquare; OO_LSQUARE; c977cc_normal; GSYM REAL_POW_2] THEN
      REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC MPUSC_REFRAME THEN MAP_EVERY EXISTS_TAC (mpwr_tuple 256 @ mpwr_tuple 3072) THEN
             ASM_REWRITE_TAC[] THEN MATCH_MP_TAC data THEN ASM_REWRITE_TAC[];
             ASM_REWRITE_TAC[REAL_POW_2] THEN NO_TAC;
             ACCEPT_TAC (mpuc_fix fam cross);
             ASM_MESON_TAC[]];
      SIMP_TAC[]])) MPF_FAMILIES MPUC_UPPER_NONNEGATIVE_CENTER;;

(* Lean: c700_transposed_nonnegative_center *)
let MPUC_C700_TRANSPOSED_NONNEGATIVE_CENTER =
  let fam = `mpf_family_c700` in
  let hyps = mpuc_sqhyps MPUC_H @ mpuc_h_hyps @ [`aH:real = l`; mpuc_equiv MPUC_H 1536 true] in
  let tm = mpuc_stmt fam false hyps (mpuc_lin MPUC_H `&2` `&2`) in
  let np = mpwr_np fam in
  let marks = CONJUNCTS (mpwr_inst fam MPF_C700_MERGED_MARKERS) in
  let lab = mpwr_labels fam in
  let rl = CONJUNCTS (mpwr_inst fam MPD_C700_RIGHT_LABELS) in
  let bottom = mpwr_auxpt 8192 6 (el 4 lab) in
  let far = mpwr_auxpt 16384 18 (el 1 rl) and near = mpwr_auxpt 16384 8 (el 0 rl) in
  let mark = mpwr_seed fam 16384 (`&1543 / &500`, `&2`) in
  let excl n th = mpcp_excl fam 1536 n th in
  let single = mpwr_singleton fam MPSB_SINGLETON_RIGHT 32 `&113 / &50` in
  let facts = [MP (SPECL MPWR_VARS OO_SIDE) np; MP (REAL_ARITH `&1 < l ==> &0 < l`) (MP (SPECL MPWR_VARS OO_SIDE) np);
               ONCE_REWRITE_RULE[REAL_ADD_SYM] (MP (SPECL (MPWR_VARS @ [`16384`]) OO_UNIT) np);
               MATCH_MP LCONT_PULLSW (MP (SPECL (MPWR_VARS @ [`16384`]) OO_BOX) np);
               el 0 marks; el 1 marks; excl 32 single; excl 16384 near; excl 8192 bottom;
               mark; far] in
  let ap = REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam 1536 16384)) in
  let th = TAC_PROOF(([], tm),
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MPUCC_UPPER_CENTER THEN
    MAP_EVERY EXISTS_TAC (mpus_swap (mpwr_tuple 16384)) THEN
    REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT CONJ_TAC THEN
    FIRST (map (fun th -> ACCEPT_TAC (mpuc_fix fam (mpcp_norm th))) facts @
           [ASM_REAL_ARITH_TAC; REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (mpuc_fix fam ap)])) in
  prove(tm, MESON_TAC[th]);;

(* Lean: c700_transposed_nonnegative_residue *)
let MPUC_C700_TRANSPOSED_NONNEGATIVE_RESIDUE =
  let fam = `mpf_family_c700` in
  let hyps = mpuc_sqhyps MPUC_A @ mpuc_sqhyps MPUC_H @
             [`&0 < cA`; `abs sA <= cA`] @ mpuc_h_hyps @
             [`aA:real = l`; `aH:real = l`; mpuc_equiv MPUC_A 256 true; mpuc_equiv MPUC_H 1536 true] in
  let body = list_mk_conj [`sA < &0`; mpwr_inside 2 `&1` `&1`; mpuc_lin MPUC_H `&2` `&2`;
                           `vA + aA <= &2 * (cA - sA)`] in
  let tm = list_mk_forall(MPWR_VARS @ MPUC_A @ MPUC_H, mk_imp(list_mk_conj ([`NPACK c1 c2 a b l`;
     mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)] @ hyps), body)) in
  let cross = CONJUNCT2 (mpwr_inst fam (el 1 MPCP_SOUTHWEST_CROSSPOINTS)) in
  prove(tm,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `aA:real = l` || concl th = `aH:real = l`))) THEN
    SUBGOAL_THEN (subst [`l:real`, `aH:real`] (mpuc_lin MPUC_H `&2` `&2`)) ASSUME_TAC THENL
     [MP_TAC(SPECL (MPWR_VARS @ map (subst [`l:real`, `aH:real`]) MPUC_H)
        MPUC_C700_TRANSPOSED_NONNEGATIVE_CENTER) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL (map (subst [`l:real`, `aA:real`; `l:real`, `aH:real`]) (MPUC_A @ MPUC_H) @ mpus_swap (mpwr_tuple 2) @ mpus_swap (mpwr_tuple 1))
      MPUCC_NONNEGATIVE_RESIDUE) THEN
    REWRITE_TAC[LINSIDE_PULLSW] THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[lsquare; OO_LSQUARE; LSQUARE_PULLS; c977cc_normal; GSYM REAL_POW_2] THEN
      REPEAT CONJ_TAC THEN
      FIRST [MATCH_MP_TAC MPUSC_REFRAME THEN
             MAP_EVERY EXISTS_TAC (mpus_swap (mpwr_tuple 256) @ mpus_swap (mpwr_tuple 1536)) THEN
             ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN MATCH_MP_TAC MPUS_C700_TRANSPOSED_DATA THEN
             ASM_REWRITE_TAC[];
             ASM_REWRITE_TAC[REAL_POW_2] THEN NO_TAC;
             ACCEPT_TAC (mpuc_fix fam cross);
             ASM_MESON_TAC[]];
      SIMP_TAC[]]);;
