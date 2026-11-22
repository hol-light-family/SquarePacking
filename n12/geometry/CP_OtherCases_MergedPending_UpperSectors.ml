(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/UpperSectors.lean   *)
(* (namespace N12Compact.MergedPending).  Original-owner entrances to the   *)
(* upper-merged local reduction.  Conventions of Families.ml / WallReach.ml *)
(* (Case k = MPF_FAMILIES entry, per-case theorems as OCaml lists; owner p m *)
(* is the OriginalOwners tuple).  UpperData / UpperResidue are               *)
(* mpusc_upper_data / mpusc_upper_residue (UpperSectorCore.ml);  pullSwap    *)
(* (c,s,u,v,a) is (s,c,u,--v - a,a).  upper_data / upper_remaining keep the  *)
(* hypothesis 3072 IN family k (vacuous for c700).  Tag MPUS_.               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_CentralPoints.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_UpperSectorCore.ml";;

let mpus_swap tl = match tl with
    [c; s; u; v; a] -> [s; c; u; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, v)) a; a]
  | _ -> failwith "mpus_swap";;
let mpus_data tuples = list_mk_comb(`mpusc_upper_data`, List.concat tuples);;
let mpus_residue tuples = list_mk_comb(`mpusc_upper_residue`, List.concat tuples);;
let mpus_member_stmt fam n body =
  list_mk_forall(MPWR_VARS, mk_imp(list_mk_conj [`NPACK c1 c2 a b l`;
    mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam);
    mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral n), fam)], body));;
let mpus_inst_member fam n th =
  MP (SPECL MPWR_VARS th) (CONJ (mpwr_np fam) (CONJ (CONJUNCT2 (ASSUME (mpwr_hyp fam))) (in_fam n fam)));;
let mpus_box m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_BOX) (mpwr_np `mpf_family_c700`);;
let mpus_lsq m = SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_LSQUARE;;

(* Lean: upper_data *)
let MPUS_UPPER_DATA = map (fun fam ->
  let body = mpus_data (map mpwr_tuple [256; 3072; 1; 2]) in
  let tm = mpus_member_stmt fam 3072 body in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  let i = index fam MPF_FAMILIES in
  let np = mpwr_np fam in
  let points = CONJUNCTS (mpwr_inst fam (el i MPCP_SOUTHWEST_POINTS)) in
  let half = CONJUNCTS (mpwr_inst fam (el i MPCP_SOUTHWEST_CROSSPOINTS)) in
  let marks = CONJUNCTS (mpus_inst_member fam 3072 (el i MPF_UPPER_MERGED_MARKERS)) in
  let w = mpcp_walls fam in
  let lab = mpwr_labels fam in
  let facts =
    [MP (SPECL MPWR_VARS OO_SIDE) np; MP (SPECL (MPWR_VARS @ [`1`]) OO_BOX) np;
     mpwr_seed fam 256 (`&33 / &20`, `&33 / &20`); el 0 points; el 1 points; el 1 half;
     el 0 marks; el 1 marks;
     mpwr_seed fam 1 (`&1`, `&457 / &500`); mpwr_seed fam 1 (`&187 / &100`, `&19 / &25`);
     el 0 w; el 1 w; mpcp_norm (mpwr_missing fam 1 13);
     mpwr_inst fam (oo_apart fam 256 3072); mpwr_inst fam (oo_apart fam 1 256);
     mpwr_inst fam (oo_apart fam 256 2);
     mpcp_label fam 3072 32768 14 (el 7 lab)] in
  let th = prove(mpwr_stmt fam body,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mpusc_upper_data] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT CONJ_TAC THEN FIRST (map (fun th -> ACCEPT_TAC (mpcp_norm th)) facts)) in
  prove(tm, MESON_TAC[th])) MPF_FAMILIES;;

(* Lean: upper_remaining *)
let MPUS_UPPER_REMAINING = map2 (fun fam data ->
  let body = mpus_residue (map mpwr_tuple [256; 3072; 1]) in
  prove(mpus_member_stmt fam 3072 body,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MPUSC_REMAINING THEN
    MAP_EVERY EXISTS_TAC (mpwr_tuple 2) THEN
    ASM_SIMP_TAC[OO_LSQUARE] THEN MATCH_MP_TAC data THEN ASM_REWRITE_TAC[])) MPF_FAMILIES MPUS_UPPER_DATA;;

(* Lean: c700_transposed_data *)
let MPUS_C700_TRANSPOSED_DATA =
  let fam = `mpf_family_c700` in
  let np = mpwr_np fam in
  let body = mpus_data (map (fun m -> mpus_swap (mpwr_tuple m)) [256; 1536; 2; 1]) in
  let points = CONJUNCTS (mpwr_inst fam (el 1 MPCP_SOUTHWEST_POINTS)) in
  let half = CONJUNCTS (mpwr_inst fam (el 1 MPCP_SOUTHWEST_CROSSPOINTS)) in
  let marks = CONJUNCTS (mpwr_inst fam MPF_C700_MERGED_MARKERS) in
  let w = mpcp_walls fam in
  let right = mpwr_auxpt 16384 8 (CONJUNCT1 (mpwr_inst fam MPD_C700_RIGHT_LABELS)) in
  let facts =
    [MP (SPECL MPWR_VARS OO_SIDE) np; MATCH_MP LCONT_PULLSW (mpus_box 2);
     mpwr_seed fam 256 (`&33 / &20`, `&33 / &20`); el 1 points; el 0 points; el 0 half;
     el 0 marks; el 1 marks;
     mpwr_seed fam 2 (`&457 / &500`, `&1`); mpwr_seed fam 2 (`&19 / &25`, `&187 / &100`);
     el 1 w; el 0 w; mpcp_norm (mpwr_missing fam 2 12);
     mpcp_excl fam 1536 16384 right] in
  let aparts = map (fun (m, n) -> REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam m n)))
                 [(256, 1536); (2, 256); (256, 1)] in
  prove(mpwr_stmt fam body,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mpusc_upper_data; LINSIDE_PULLSW; ldisj] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT CONJ_TAC THEN
    FIRST (map (fun th -> ACCEPT_TAC (mpcp_norm th)) facts @
           map (fun th -> REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC th) aparts));;

(* Lean: c700_remaining *)
let MPUS_C700_REMAINING =
  let fam = `mpf_family_c700` in
  let body = mpus_residue (map (fun m -> mpus_swap (mpwr_tuple m)) [256; 1536; 2]) in
  prove(mpwr_stmt fam body,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MPUSC_REMAINING THEN
    MAP_EVERY EXISTS_TAC (mpus_swap (mpwr_tuple 1)) THEN
    ASM_SIMP_TAC[OO_LSQUARE; LSQUARE_PULLS] THEN MATCH_MP_TAC MPUS_C700_TRANSPOSED_DATA THEN
    ASM_REWRITE_TAC[]);;
