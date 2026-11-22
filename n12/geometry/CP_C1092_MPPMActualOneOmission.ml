(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualOneOmission.lean               *)
(* (N12Compact.C1092MPPMActualOneOmission).  The sole ordinary-right         *)
(* alternative in the actual MPPM one-omission branch.  Conventions and      *)
(* forward toolkit of CP_C1092_MPPMOmissionCenter.ml (c1092moc_ functions;   *)
(* owners p i at mask EL i c1092wc_code, side l; WallContext p mppm is       *)
(* C1092MPPE_CTX, omitted is C1092MPPE_OMIT); missing is                     *)
(* C1092MPAOO_MISSING.  The private side_gt / side_same / mark are           *)
(* C1092MOC_SIDE_GT / SIDE_SAME / MARKER_POINT (markers through oo_seed).    *)
(* WallUpperMissingReach.point WUMR_POINT; MMMPStrongNortheastFaces.profile  *)
(* C1092MSNF_PROFILE; MMMPEnding.Profile / impossible c1092mend_profile /    *)
(* C1092MEND_IMPOSSIBLE; MPPMUpperSign.PositiveActual / exists_positive      *)
(* c1092mpus_pos / C1092MPUS_EXISTS_POSITIVE; MPPMUpperOrigin.top_origin     *)
(* C1092MPUO_TOP_ORIGIN; MPPMRightInner.other_ordinary                       *)
(* C1092MPRI_OTHER_ORDINARY; MPPMTopOrigin.right_origin C1092MTO_RIGHT_ORIGIN;*)
(* MPPMPointCore.rectangle / bottom_crosspoint / diagonal C1092MPC_*;        *)
(* MPPMOmissionCenter.bottom_center C1092MOC_BOTTOM_CENTER;                  *)
(* OriginalOwners.horizontal_segment OO_HORIZONTAL_SEGMENT.                  *)
(* (Lean header: "Source only, uncompiled".)  Tag C1092MPAOO_.               *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMUpperOrigin.ml";;
needs "n12/geometry/CP_C1092_MMMP_StrongNortheastFaces.ml";;
needs "n12/geometry/CP_C1092_MMMP_Ending.ml";;
needs "n12/geometry/WallUpperMissingReach.ml";;

let C1092MPAOO_MISSING = "~" ^ c1092mppe_in 11 "&87 / &50" "&3";;
let C1092MPAOO_HYPS = Printf.sprintf "%s /\\ %s" C1092MPRI_HYPS C1092MPAOO_MISSING;;

let c1092mpaoo_missing () =
  CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term C1092MPAOO_MISSING));;

(* the far point (64/25, 3) of owner 11 *)
let c1092mpaoo_far () =
  let layers = [C1092MOC_Y; C1092MOC_SW] in
  let t, eqs = c1092moc_layers 11 layers in
  let other = CONJUNCT2 (c1092moc_use C1092MPRI_OTHER_ORDINARY) in
  c1092moc_apply (c1092moc_conv eqs) (SPECL t WUMR_POINT)
    [c1092moc_punit 11 t; c1092moc_pos (); c1092moc_side (); c1092moc_plcont 11 layers;
     c1092moc_seed 11 (`&2`, `&1543 / &500`); other; c1092mpaoo_missing ();
     c1092moc_excl 11 6 (c1092moc_seed 6 (`&47 / &20`, `&47 / &20`))];;

(* Lean: top_reach *)
let C1092MPAOO_TOP_REACH = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s /\\ !x. &2 <= x ==> x <= &64 / &25 ==> %s"
    C1092AE_P C1092MPAOO_HYPS (c1092mppe_in 11 "&64 / &25" "&3") (c1092mppe_in 11 "x" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MOC_CODE_CONV THEN
  let far = c1092mpaoo_far () in
  let origin = c1092moc_use C1092MPUO_TOP_ORIGIN in
  CONJ_TAC THENL
   [ACCEPT_TAC far;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`&2`; `&64 / &25`] THEN
    ASM_REWRITE_TAC[far; origin] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* the facts of PositiveActual p N (EL-free) *)
let c1092mpaoo_n () =
  let nv = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] in
  let npos = ASSUME (list_mk_comb(`c1092mpus_pos`, C1092MPPE_V @ nv)) in
  nv, npos, CONJUNCTS (CONV_RULE C1092MOC_CODE_CONV (REWRITE_RULE[c1092mpus_pos; GSYM CONJ_ASSOC] npos));;

(* Lean: northeast_profile *)
let c1092mpaoo_northeast_profile () =
  let nv, npos, [nunit; npos0; nside; ninside; nnormal; npositive] = c1092mpaoo_n () in
  let conv = GEN_REWRITE_CONV ONCE_DEPTH_CONV [ninside] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let ordinary = CONJUNCT1 (c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS) in
  let reach = UNDISCH (SPECL C1092MPPE_V C1092MPAOO_TOP_REACH) in
  let reach = CONV_RULE C1092MOC_CODE_CONV (PROVE_HYP
    (end_itlist CONJ [ASSUME C1092MOC_NP; ASSUME C1092MOC_IMG; ASSUME C1092MOC_CTX;
                      ASSUME C1092MOC_OMIT; ASSUME (parse_term C1092MPAOO_MISSING)]) reach) in
  let bar =
    let y = `y:real` in
    let h1 = ASSUME `&13 / &50 <= y` and h2 = ASSUME `y <= &14 / &25` in
    let a1 = c1092moc_arith [h1] `&2 <= &2 + y` and a2 = c1092moc_arith [h2] `&2 + y <= &64 / &25` in
    let pt = MP (MP (SPEC `&2 + y` (CONJUNCT2 reach)) a1) a2 in
    GEN y (DISCH (concl h1) (DISCH (concl h2) (c1092moc_excl 6 11 pt))) in
  c1092moc_apply2 conv (SPECL nv C1092MSNF_PROFILE)
    [nunit; npos0; nnormal;
     c1092moc_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 ordinary;
     c1092moc_excl 6 5 (c1092mpus_core `&113 / &50` `&2`);
     c1092moc_excl 6 5 (c1092mpus_core `&12 / &5` `&2`);
     c1092moc_excl 6 10 (c1092moc_use C1092MTO_RIGHT_ORIGIN);
     c1092moc_excl 6 2 (c1092moc_seed 2 (`&3`, `&3`)); bar]
    [nside; c1092moc_side ()];;

let C1092MPAOO_NORTHEAST_PROFILE = prove
 (parse_term (Printf.sprintf "!%s cN sN uN vN aN. %s /\\ c1092mpus_pos %s cN sN uN vN aN
      ==> c1092mend_profile cN sN uN vN aN /\\ &252 / &373 <= sN" C1092AE_P C1092MPAOO_HYPS C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN ACCEPT_TAC (c1092mpaoo_northeast_profile ()));;

(* Lean: impossible_of_top_g4_omission *)
let C1092MPAOO_IMPOSSIBLE_OF_TOP_G4_OMISSION = prove
 (parse_term (Printf.sprintf "!%s. %s ==> F" C1092AE_P C1092MPAOO_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPUS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cN:real` (X_CHOOSE_THEN `sN:real` (X_CHOOSE_THEN `uN:real`
    (X_CHOOSE_THEN `vN:real` (X_CHOOSE_THEN `aN:real` ASSUME_TAC))))) THEN
  let nv, npos, [nunit; npos0; nside; ninside; nnormal; npositive] = c1092mpaoo_n () in
  let profile = c1092mpaoo_northeast_profile () in
  let tW, eqW = c1092moc_layers 5 [C1092MOC_SW; c1092moc_tr `&2` `&2`] in
  let convN = GEN_REWRITE_CONV ONCE_DEPTH_CONV [ninside] in
  let conv = TRY_CONV (c1092moc_unfold eqW) THENC TRY_CONV convN THENC
             ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let ordinary = CONJUNCT1 (c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS) in
  let bbar = c1092moc_use C1092MPPE_OMITTED_BOTTOM_BAR in
  let rr tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm) in
  let bot x = let th = SPEC x bbar in MP (MP th (rr (lhand (concl th)))) (rr (lhand (rand (concl th)))) in
  let disj =
    let tm = list_mk_comb(`ldisj`, tW @ nv) in
    let eq = (REWRITE_CONV[ldisj] THENC TRY_CONV (c1092moc_unfold eqW) THENC TRY_CONV convN) tm in
    let r = rhs (concl eq) in
    let ap = c1092moc_apart 5 6 in
    EQ_MP (SYM eq) (MP (prove(mk_imp(concl ap, r),
      DISCH_TAC THEN REPEAT GEN_TAC THEN
      REWRITE_TAC[REAL_ARITH `forall y. y + &2 = &2 + y`] THEN ASM_REWRITE_TAC[])) ap) in
  ACCEPT_TAC(c1092moc_apply2 conv (SPECL (tW @ nv) C1092MEND_IMPOSSIBLE)
    [c1092moc_punit 5 tW; c1092moc_pos (); c1092moc_side (); nunit; npos0; nnormal;
     CONJUNCT2 profile; CONJUNCT1 profile;
     c1092moc_use C1092MOC_BOTTOM_CENTER; c1092moc_use C1092MPC_BOTTOM_CROSSPOINT;
     CONJUNCT1 (c1092moc_use C1092MPC_DIAGONAL);
     c1092moc_seed 5 (`&47 / &20`, `&33 / &20`);
     c1092moc_excl 5 4 (c1092moc_seed 4 (`&33 / &20`, `&33 / &20`));
     c1092moc_excl 5 9 (bot `&239 / &100`);
     c1092moc_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 ordinary; CONJUNCT2 ordinary;
     disj]
    [nside; c1092moc_side ()]));;

(* Lean: top_g4 *)
let C1092MPAOO_TOP_G4 = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MPRI_HYPS (c1092mppe_in 11 "&87 / &50" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL C1092MPPE_V C1092MPAOO_IMPOSSIBLE_OF_TOP_G4_OMISSION) THEN
  ASM_REWRITE_TAC[]);;
