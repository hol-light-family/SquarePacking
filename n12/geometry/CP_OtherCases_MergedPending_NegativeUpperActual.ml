(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/NegativeUpperActual  *)
(* .lean (namespace N12Compact.MergedPending; Lean header: "No whole-family  *)
(* exclusion is asserted").  Actual-owner entrances to the negative-upper    *)
(* face profile.  Conventions of Families.ml / UpperCenters.ml: Lean Case k  *)
(* is the entry of MPF_FAMILIES, a theorem for all k is an OCaml list (same  *)
(* order); owner p m is the tuple (mpwr_tuple m), side l.  The arbitrary     *)
(* OpenSquare H is cH sH uH vH aH with its invariants as hypotheses.         *)
(* H.translated x y is (c, s, u - (c * x + s * y), v - (--s * x + c * y), a) *)
(* (S12 OpenSquare.translated).  NegativeUpperFaces.Input is ocmpnuf_input. *)
(* upper_negative_input / upper_outward_projection keep the hypothesis      *)
(* 3072 IN family k (vacuous for c700).  Tag MPNUA_.                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_UpperNegative.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_NegativeUpperFaces.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_SoutheastBranches.ml";;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let MPNUA_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let MPNUA_TRANSLATED_INPUT =
  `ocmpnuf_input cH sH (uH - (cH * &2 + sH * &2)) (vH - (--sH * &2 + cH * &2)) aH`;;
let mpnua_hyps m swap =
  mpuc_sqhyps MPUN_H @ [`c977cc_normal cH (--sH)`; `aH:real = l`; mpuc_equiv MPUN_H m swap];;
let mpnua_stmt fam member hyps body =
  list_mk_forall(MPWR_VARS @ MPUN_H, mk_imp(list_mk_conj ([`NPACK c1 c2 a b l`;
     mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)] @
     (if member then [mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `3072`), fam)] else []) @ hyps),
     body));;

let MPNUA_INPUT_TAC fam facts =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aH:real = l`)) THEN
  REWRITE_TAC[ocmpnuf_input; MPNUA_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC(map (mpuc_fix fam) facts);;

(* Lean: upper_negative_input *)
let MPNUA_UPPER_NEGATIVE_INPUT = map (fun fam ->
  let tm = mpnua_stmt fam true (mpnua_hyps 3072 false) MPNUA_TRANSLATED_INPUT in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  let i = index fam MPF_FAMILIES in
  let np = mpwr_np fam in
  let marks = CONJUNCTS (mpus_inst_member fam 3072 (el i MPF_UPPER_MERGED_MARKERS)) in
  let points = CONJUNCTS (mpwr_inst fam (el i MPCP_SOUTHWEST_POINTS)) in
  let lab = mpwr_labels fam in
  let facts = [MP (SPECL MPWR_VARS OO_SIDE) np; el 0 marks; el 1 marks;
               mpcp_excl fam 3072 256 (el 1 points);
               mpcp_label fam 3072 32768 14 (el 7 lab);
               mpcp_norm (mpwr_missing fam 3072 15)] in
  prove(tm, MPNUA_INPUT_TAC fam facts)) MPF_FAMILIES;;

(* Lean: c700_transposed_negative_input *)
let MPNUA_C700_TRANSPOSED_NEGATIVE_INPUT =
  let fam = `mpf_family_c700` in
  let tm = mpnua_stmt fam false (mpnua_hyps 1536 true) MPNUA_TRANSLATED_INPUT in
  let np = mpwr_np fam in
  let marks = CONJUNCTS (mpwr_inst fam MPF_C700_MERGED_MARKERS) in
  let points = CONJUNCTS (mpwr_inst fam (el 1 MPCP_SOUTHWEST_POINTS)) in
  let right = CONJUNCT1 (mpwr_inst fam MPD_C700_RIGHT_LABELS) in
  let facts = [MP (SPECL MPWR_VARS OO_SIDE) np; el 0 marks; el 1 marks;
               mpcp_excl fam 1536 256 (el 0 points);
               mpcp_label fam 1536 16384 8 right;
               mpcp_norm (mpwr_missing fam 1536 14)] in
  prove(tm, MPNUA_INPUT_TAC fam facts);;

(* Lean: upper_outward_projection *)
let MPNUA_UPPER_OUTWARD_PROJECTION = map2 (fun fam input ->
  let hyps = mpnua_hyps 3072 false @
             [mk_neg (mpwr_inside 512 `&113 / &50` `&2`);
              `&543 / &500 * sH <= uH - &2 * (cH + sH)`] in
  let tm = mpnua_stmt fam true hyps `&1000 < &525 * cH - &961 * sH` in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  let i = index fam MPF_FAMILIES in
  let np = mpwr_np fam in
  let pos = mpuc_fix fam (MP (REAL_ARITH `&1 < l ==> &0 < l`) (MP (SPECL MPWR_VARS OO_SIDE) np)) in
  let ap = REWRITE_RULE[ldisj] (mpuc_fix fam (mpwr_inst fam (oo_apart fam 3072 512))) in
  let tu = `uH - (cH * &2 + sH * &2)` and tv = `vH - (--sH * &2 + cH * &2)` in
  let q = [`cH:real`; `sH:real`; tu; tv; `l:real`] in
  prove(tm,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aH:real = l`)) THEN
    MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) input) THEN ASM_REWRITE_TAC[in_fam 3072 fam] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < l /\ &543 / &500 * sH <= uH - (cH * &2 + sH * &2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ACCEPT_TAC pos; RASM_ARITH_TAC]; ALL_TAC] THEN
    MP_TAC(SPECL q OCMPNUF_TOP_LOWER_TILT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cH:real`; `--sH:real`] C977CC_NORMAL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&9 * cH <= --(&35) * sH` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL q OCMPNUF_SHARP_POINT) THEN ASM_REWRITE_TAC[MPNUA_INSIDE_TRANSLATED] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN DISCH_TAC THEN
    MP_TAC(SPECL MPWR_VARS (el i MPSE_SOUTHEAST_OUTWARD_POINTS)) THEN
    ASM_REWRITE_TAC[in_fam 512 fam] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`&101 / &40`; `&17 / &8`] ap) THEN ASM_REWRITE_TAC[])) MPF_FAMILIES
  MPNUA_UPPER_NEGATIVE_INPUT;;
