(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/UpperNegative.lean  *)
(* (namespace N12Compact.MergedPending; Lean header: "Source only,           *)
(* uncompiled").  The nonnegative-upper ending transfers to the three        *)
(* pending merged families: a strict signed canonical frame for the merged   *)
(* square.  Conventions of Families.ml / UpperSectors.ml / UpperCenters.ml:  *)
(* Lean Case k is the entry of MPF_FAMILIES, a theorem for all k is an OCaml *)
(* list (same order); owner p m is the tuple (mpwr_tuple m), its side is l.  *)
(* "?H : OpenSquare" is an existential over a 5-tuple with its OpenSquare    *)
(* invariants (as in ClosedFrames.ml).  UpperData is mpusc_upper_data;      *)
(* C868.UpperNonnegative.impossible is C868UN_IMPOSSIBLE.  upper_negative_   *)
(* frame keeps the hypothesis 3072 IN family k (vacuous for c700).           *)
(* pullSwap (c,s,u,v,a) is (s,c,u,--v - a,a) (LINSIDE_PULLSW).  Tag MPUN_.   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_UpperCenters.ml";;
needs "n12/geometry/UpperNonnegative.ml";;

(* Lean: UpperData.nonnegative_upper_impossible *)
let MPUN_NONNEGATIVE_UPPER_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cH sH uH vH aH /\
     lsquare cO sO uO vO aO /\ lsquare cL sL uL vL aL /\
     mpusc_upper_data cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL /\
     &0 < cA /\ abs sA <= cA /\ c977cc_normal cH sH /\
     linside cH sH uH vH aH (&2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     ~linside cH sH uH vH aH (&113 / &50) (&3) ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mpusc_upper_data] o
    check (fun th -> fst (strip_comb (concl th)) = `mpusc_upper_data`)) THEN
  SUBGOAL_THEN `cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lsquare]; ALL_TAC] THEN
  SUBGOAL_THEN `linside cO sO uO vO aO (&8 / &5) (&1) /\ linside cL sL uL vL aL (&1) (&8 / &5)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MPUSC_BAR_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&8 / &5) (&1) /\ ~linside cA sA uA vA aA (&1) (&8 / &5)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `ldisj cO sO uO vO aO cA sA uA vA aA` THEN REWRITE_TAC[ldisj] THEN
      DISCH_THEN(MP_TAC o SPECL [`&8 / &5`; `&1`]) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ldisj cA sA uA vA aA cL sL uL vL aL` THEN REWRITE_TAC[ldisj] THEN
      DISCH_THEN(MP_TAC o SPECL [`&1`; `&8 / &5`]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sA` THENL
   [MATCH_MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                        `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`;
                        `cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                        `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
       MPUSC_POSITIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC;
    MATCH_MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                        `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`]
       C868UN_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    RASM_ARITH_TAC]);;

let MPUN_A = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`];;
let MPUN_H = [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`];;
let MPUN_AL = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `l:real`];;
let MPUN_HL = [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `l:real`];;

(* the frame body ?H. OpenSquare H /\ sign conditions /\ H.side = l /\ equivalence *)
let mpun_frame signs equiv =
  list_mk_exists(MPUN_H, list_mk_conj (mpuc_sqhyps MPUN_H @ signs @ [`aH:real = l`; equiv]));;

(* obtain a canonical frame of the tuple sq (lsquare fact lsq) as the variables vs *)
let MPUN_FRAME_TAC lsq sq vs =
  MP_TAC(SPECL sq CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ACCEPT_TAC (REWRITE_RULE[lsquare] lsq); ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC vs THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = last vs && rhs (concl th) = `l:real`));;

(* the common end: H.s < 0, since the nonnegative sector is impossible.        *)
(* center: the universal center theorem (MP_TAC'd, antecedent by ASM_REWRITE   *)
(* with extra), datat: the tuples (A H) of the data theorem data, reframe:     *)
(* the specialised MPUN_NONNEGATIVE_UPPER_IMPOSSIBLE, facts: point facts.      *)
let MPUN_CLOSE_TAC side center extra datat data reframe facts =
  MAP_EVERY EXISTS_TAC MPUN_HL THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 <= sH` THENL [ALL_TAC; RASM_ARITH_TAC] THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  SUBGOAL_THEN `sH <= cH /\ &0 < l` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [RASM_ARITH_TAC; ACCEPT_TAC side]; ALL_TAC] THEN
  SUBGOAL_THEN (list_mk_comb(`linside`, MPUN_HL @ [`&2`; `&2`])) ASSUME_TAC THENL
   [MP_TAC(SPECL (MPWR_VARS @ MPUN_HL) center) THEN ASM_REWRITE_TAC extra; ALL_TAC] THEN
  MATCH_MP_TAC reframe THEN
  REWRITE_TAC[lsquare; c977cc_normal; REAL_POW_2] THEN
  REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC MPUSC_REFRAME THEN MAP_EVERY EXISTS_TAC datat THEN
           ASM_REWRITE_TAC[data; LINSIDE_PULLSW] THEN NO_TAC;
         ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN REWRITE_TAC facts THEN NO_TAC;
         ASM_REWRITE_TAC facts THEN NO_TAC];;

(* Lean: upper_negative_frame *)
let MPUN_UPPER_NEGATIVE_FRAME = map (fun fam ->
  let body = mpun_frame [`&0 < cH`; `sH < &0`; `--sH <= cH`] (mpuc_equiv MPUN_H 3072 false) in
  let tm = mpus_member_stmt fam 3072 body in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  let i = index fam MPF_FAMILIES in
  let np = mpwr_np fam in
  let lsq m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_LSQUARE) np in
  let w = mpcp_walls fam in
  let data = mpus_inst_member fam 3072 (el i MPUS_UPPER_DATA) in
  let cross = CONJUNCT1 (mpwr_inst fam (el i MPCP_SOUTHWEST_CROSSPOINTS)) in
  let top = mpcp_excl fam 3072 16 (mpwr_bar (el 2 w) `&113 / &50`) in
  let reframe = SPECL (MPUN_AL @ MPUN_HL @ mpwr_tuple 1 @ mpwr_tuple 2) MPUN_NONNEGATIVE_UPPER_IMPOSSIBLE in
  let side = MP (REAL_ARITH `&1 < l ==> &0 < l`) (MP (SPECL MPWR_VARS OO_SIDE) np) in
  let facts = [side; cross; top; REWRITE_RULE[lsquare] (lsq 1); REWRITE_RULE[lsquare] (lsq 2)] in
  let th = prove(mpwr_stmt fam body,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MPUN_FRAME_TAC (lsq 256) (mpwr_tuple 256) MPUN_A THEN
    MPUN_FRAME_TAC (lsq 3072) (mpwr_tuple 3072) MPUN_H THEN
    MPUN_CLOSE_TAC side (el i MPUC_UPPER_NONNEGATIVE_CENTER) [in_fam 3072 fam]
      (mpwr_tuple 256 @ mpwr_tuple 3072) data reframe facts) in
  prove(tm, REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[])) MPF_FAMILIES;;

(* Lean: c700_transposed_negative_frame *)
let MPUN_C700_TRANSPOSED_NEGATIVE_FRAME =
  let fam = `mpf_family_c700` in
  let body = mpun_frame [`&0 < cH`; `sH < &0`; `--sH <= cH`] (mpuc_equiv MPUN_H 1536 true) in
  let np = mpwr_np fam in
  let lsq m = CONJUNCT2 (CONJUNCT2 (MATCH_MP LSQUARE_PULLS
                (MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_LSQUARE) np))) in
  let data = mpwr_inst fam MPUS_C700_TRANSPOSED_DATA in
  let cross = CONJUNCT2 (mpwr_inst fam (el 1 MPCP_SOUTHWEST_CROSSPOINTS)) in
  let single = mpwr_singleton fam MPSB_SINGLETON_RIGHT 32 `&113 / &50` in
  let top = mpcp_excl fam 1536 32 single in
  let reframe = SPECL (MPUN_AL @ MPUN_HL @ mpus_swap (mpwr_tuple 2) @ mpus_swap (mpwr_tuple 1))
                  MPUN_NONNEGATIVE_UPPER_IMPOSSIBLE in
  let side = MP (REAL_ARITH `&1 < l ==> &0 < l`) (MP (SPECL MPWR_VARS OO_SIDE) np) in
  let facts = [side; cross; top; REWRITE_RULE[lsquare] (lsq 1); REWRITE_RULE[lsquare] (lsq 2)] in
  prove(mpwr_stmt fam body,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MPUN_FRAME_TAC (lsq 256) (mpus_swap (mpwr_tuple 256)) MPUN_A THEN
    MPUN_FRAME_TAC (lsq 1536) (mpus_swap (mpwr_tuple 1536)) MPUN_H THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LINSIDE_PULLSW]) THEN
    MPUN_CLOSE_TAC side MPUC_C700_TRANSPOSED_NONNEGATIVE_CENTER []
      (mpus_swap (mpwr_tuple 256) @ mpus_swap (mpwr_tuple 1536)) data reframe facts);;

(* Lean: c700_positive_merged_frame *)
let MPUN_C700_POSITIVE_MERGED_FRAME = prove
 (mpwr_stmt `mpf_family_c700`
    (mpun_frame [`&0 < cH`; `&0 < sH`; `sH <= cH`] (mpuc_equiv MPUN_H 1536 false)),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MPUN_C700_TRANSPOSED_NEGATIVE_FRAME) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `e:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `e:real = l`)) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `--s:real`; `v:real`; `u:real`; `l:real`] THEN
  REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN NO_TAC;
         RASM_ARITH_TAC;
         REPEAT GEN_TAC THEN FIRST_X_ASSUM(fun th ->
           if is_forall (concl th) then REWRITE_TAC[GSYM th] else failwith "") THEN
         REWRITE_TAC[linside] THEN REAL_ARITH_TAC]);;
