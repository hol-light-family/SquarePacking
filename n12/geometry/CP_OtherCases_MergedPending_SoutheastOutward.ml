(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/SoutheastOutward     *)
(* .lean (namespace N12Compact.MergedPending).  The inward southeast         *)
(* alternative is impossible in C683 and C867; the outward points / frame    *)
(* of SE512 then hold unconditionally (given 3072 IN family k).              *)
(* Conventions of SoutheastBranches.ml: per-case theorems are OCaml lists    *)
(* over MPF_FAMILIES (c683, c700, c867); every statement keeps the           *)
(* hypothesis 3072 IN family k (vacuous for c700).                           *)
(* C868.merged_inward_low_points applied to (owner 3072).translated 2 2 is   *)
(* C868IC_MERGED_ORIGINAL (the same lemma at the untranslated coordinates).  *)
(* upper_merged_markers = seeds of 3072, singleton_top = top singleton bar   *)
(* of MPF_WALLS, common_labels.top.2 = label 14 of 32768.  Tag MPSO_.        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_SoutheastBranches.ml";;
needs "n12/geometry/UpperNegativeInwardCenter.ml";;

let mpso_stmt fam extra body =
  list_mk_forall(MPWR_VARS, mk_imp(list_mk_conj ([`NPACK c1 c2 a b l`;
    mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam);
    mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `3072`), fam)] @ extra), body));;

(* per case: vacuous for c700 (3072 not in the family); otherwise th proves the body
   under the assumptions NPACK /\ IMAGE = fam (and the extra ones) *)
let mpso_case extra body mk = map (fun fam ->
  let tm = mpso_stmt fam extra body in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  let th = mk fam in
  prove (tm, REPEAT GEN_TAC THEN STRIP_TAC THEN
             MP_TAC (DISCH (mpwr_hyp fam) th) THEN ASM_REWRITE_TAC[])) MPF_FAMILIES;;

let mpso_apart fam m n x y =
  SPECL [x; y] (REWRITE_RULE[ldisj] (mpwr_inst fam (oo_apart fam m n)));;
let mpso_excl fam m n th =
  let x, y = match snd (strip_comb (concl th)) with
    [_; _; _; _; _; x; y] -> x, y | _ -> failwith "mpso_excl" in
  let ap = mpso_apart fam m n x y in
  let p = lhand (rand (concl ap)) in
  MP (MP (TAUT (mk_imp(mk_neg(mk_conj(p, concl th)), mk_imp(concl th, mk_neg p)))) ap) th;;

let MPSO_INWARD = mpwr_inside 512 `&113 / &50` `&2`;;

(* F from the inward point, under NPACK /\ IMAGE = fam and MPSO_INWARD *)
let mpso_contra fam =
  let i = index fam MPF_FAMILIES in
  let inward = ASSUME MPSO_INWARD in
  let lab = mpwr_labels fam and w = mpcp_walls fam in
  let sw = CONJUNCTS (mpwr_inst fam (el i MPCP_SOUTHWEST_POINTS)) in
  let topLeft = mpcp_norm (mpwr_auxpt 32768 14 (el 7 lab)) in
  let topRight = mpwr_bar (el 2 w) `&113 / &50` in
  let topMarker = mpwr_seed fam 32768 (`&2`, `&1543 / &500`) in
  let facts = map mpcp_norm
    [mpse_unit fam 3072; mpse_pos fam; mpse_side fam;
     mpwr_seed fam 3072 (`&33 / &20`, `&47 / &20`);
     mpwr_seed fam 3072 (`&47 / &20`, `&47 / &20`);
     mpso_excl fam 3072 256 (el 1 sw);
     mpso_excl fam 3072 512 inward;
     mpso_excl fam 3072 32768 topLeft;
     mpso_excl fam 3072 16 topRight;
     mpso_excl fam 3072 32768 topMarker] in
  let lem = SPECL (mpwr_tuple 3072) C868IC_MERGED_ORIGINAL in
  let point = MP lem (TAC_PROOF(([], lhand (concl lem)),
    REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC facts))) in
  let duplicate = CONJUNCT1 point in
  MP (NOT_ELIM (mpso_excl fam 3072 256 (el 2 sw))) duplicate;;

(* Lean: southeast_missing_inward *)
let MPSO_SOUTHEAST_MISSING_INWARD = mpso_case [] (mk_neg MPSO_INWARD) (fun fam ->
  NOT_INTRO (DISCH MPSO_INWARD (mpso_contra fam)));;

let mpso_miss fam =
  MP (SPEC_ALL (el (index fam MPF_FAMILIES) MPSO_SOUTHEAST_MISSING_INWARD))
     (end_itlist CONJ [mpwr_np fam; CONJUNCT2 (ASSUME (mpwr_hyp fam)); in_fam 3072 fam]);;

(* Lean: southeast_outward_points_unconditional *)
let MPSO_SOUTHEAST_OUTWARD_POINTS_UNCONDITIONAL = mpso_case [] MPSE_OUTWARD_BODY (fun fam ->
  let i = index fam MPF_FAMILIES in
  let miss = mpso_miss fam in
  let pts = el i MPSE_SOUTHEAST_OUTWARD_POINTS in
  MP (SPEC_ALL pts) (end_itlist CONJ [mpwr_np fam; CONJUNCT2 (ASSUME (mpwr_hyp fam));
                                      in_fam 512 fam; miss]));;

(* Lean: southeast_outward_frame_unconditional *)
let MPSO_SOUTHEAST_OUTWARD_FRAME_UNCONDITIONAL = mpso_case [] MPSE_FRAME_BODY (fun fam ->
  let i = index fam MPF_FAMILIES in
  let miss = mpso_miss fam in
  let fr = el i MPSE_SOUTHEAST_OUTWARD_FRAME in
  MP (SPEC_ALL fr) (end_itlist CONJ [mpwr_np fam; CONJUNCT2 (ASSUME (mpwr_hyp fam));
                                     in_fam 512 fam; miss]));;
