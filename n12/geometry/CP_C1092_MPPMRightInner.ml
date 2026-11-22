(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMRightInner.lean                      *)
(* (N12Compact.C1092MPPMRightInner).  The genuine top owner excludes the     *)
(* right inward auxiliary in the transposed MPPM one-omission chart.         *)
(* Conventions and forward toolkit of CP_C1092_MPPMOmissionCenter.ml         *)
(* (c1092moc_ functions; owners p i at mask EL i c1092wc_code, side l;       *)
(* WallContext p mppm is C1092MPPE_CTX, omitted is C1092MPPE_OMIT).  The     *)
(* private side_gt / side_same are C1092MOC_SIDE_GT / C1092MOC_SIDE_SAME.    *)
(* MPPMOmissions.Missing / at_most_one: c1092mom_missing /                   *)
(* C1092MOM_AT_MOST_ONE; C1092AuxiliaryCover.northwest_f/g_cover:            *)
(* C1092AC_NORTHWEST_F/G_COVER; wall_auxiliaries C1092MPPE_WALL_AUXILIARIES; *)
(* omitted_bottom_neighbors C1092MPPE_OMITTED_BOTTOM_NEIGHBORS;              *)
(* C1092MixedSpan.impossible C1092MS_IMPOSSIBLE; MPPMUpperSign.              *)
(* exists_positive C1092MPUS_EXISTS_POSITIVE (PositiveActual =               *)
(* c1092mpus_pos); C1092MMMPRightInnerPositive.impossible                    *)
(* C1092MRIPOS_IMPOSSIBLE.  Tag C1092MPRI_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMUpperSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_RightInnerPositive.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;

let c1092mpri_in i x y = list_mk_comb(`linside`, c1092moc_own i @ [x; y]);;

(* an EL-form packing theorem with hypothesis NPACK /\ IMAGE only *)
let c1092mpri_useh th =
  CONV_RULE C1092MOC_CODE_CONV (MP (SPECL C1092MPPE_V th) (c1092moc_hh ()));;

(* Lean: other_ordinary *)
let C1092MPRI_OTHER_ORDINARY = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP
    C1092MPPE_CTX C1092MPPE_OMIT (c1092mppe_in 8 "&1" "&12 / &5") (c1092mppe_in 11 "&12 / &5" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPECL (C1092MPPE_V @ [`0`; `1`]) C1092MOM_AT_MOST_ONE) THEN
    ASM_REWRITE_TAC[c1092mom_missing; ARITH] THEN
    REWRITE_TAC(Array.to_list C1092WC_WALL_ELS @ Array.to_list C1092MOM_OPOINT_ELS) THEN
    REWRITE_TAC[FST; SND] THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL C1092MPPE_V C1092MPUS_TOPF) THEN ASM_REWRITE_TAC[]]);;

let C1092MPRI_HYPS = Printf.sprintf "%s /\\ %s /\\ %s" C1092AE_HYP C1092MPPE_CTX C1092MPPE_OMIT;;

(* Lean: northwest_pair (private) *)
let C1092MPRI_NORTHWEST_PAIR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092MPRI_HYPS
    (c1092mppe_in 11 "&2" "&113 / &50") (c1092mppe_in 7 "&8 / &5" "&3") (c1092mppe_in 7 "&87 / &50" "&3")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MOC_CODE_CONV THEN
  let inward = CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term (c1092mppe_in 11 "&2" "&113 / &50"))) in
  let leftF = CONJUNCT1 (c1092moc_use C1092MPPE_WALL_AUXILIARIES) in
  let leftG = CONJUNCT1 (c1092moc_use C1092MPRI_OTHER_ORDINARY) in
  let fcov = c1092mpri_useh C1092AC_NORTHWEST_F_COVER in
  let gcov = c1092mpri_useh C1092AC_NORTHWEST_G_COVER in
  let e78 = c1092moc_excl 7 8 leftF and e711 = c1092moc_excl 7 11 inward
  and e78g = c1092moc_excl 7 8 leftG in
  let ftm = c1092mpri_in 7 `&8 / &5` `&3` in
  SUBGOAL_THEN ftm ASSUME_TAC THENL [MESON_TAC[fcov; e78; e711]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  let habs = mk_neg (c1092mpri_in 7 `&87 / &50` `&3`) in
  let itm = c1092mpri_in 7 `&87 / &50` `&2` in
  SUBGOAL_THEN itm ASSUME_TAC THENL
   [MP_TAC gcov THEN MP_TAC e78g THEN UNDISCH_TAC habs THEN MESON_TAC[]; ALL_TAC] THEN
  let t, eqs = c1092moc_layers 7 [C1092MOC_SW] in
  ACCEPT_TAC(c1092moc_apply (c1092moc_conv eqs) (SPECL t C1092MS_IMPOSSIBLE)
    [c1092moc_punit 7 t; c1092moc_pos (); c1092moc_side ();
     ASSUME itm; ASSUME ftm; e711; ASSUME habs; e78; e78g]));;

(* Lean: missing *)
let C1092MPRI_MISSING = prove
 (parse_term (Printf.sprintf "!%s. %s ==> ~%s" C1092AE_P C1092MPRI_HYPS
    (c1092mppe_in 11 "&2" "&113 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPPE_V C1092MPUS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[c1092mpus_pos] THEN
  CONV_TAC C1092MOC_CODE_CONV THEN STRIP_TAC THEN DISCH_TAC THEN
  let inner = ASSUME (c1092mpri_in 11 `&2` `&113 / &50`) in
  let el_inner = EQ_MP (SYM (C1092MOC_CODE_CONV (parse_term (c1092mppe_in 11 "&2" "&113 / &50")))) inner in
  let pair = CONV_RULE C1092MOC_CODE_CONV (MP (SPECL C1092MPPE_V C1092MPRI_NORTHWEST_PAIR)
    (CONJ (ASSUME C1092MOC_NP) (CONJ (ASSUME C1092MOC_IMG) (CONJ (ASSUME C1092MOC_CTX)
      (CONJ (ASSUME C1092MOC_OMIT) el_inner))))) in
  let ne = CONJUNCT1 (c1092moc_use C1092MPPE_OMITTED_BOTTOM_NEIGHBORS) in
  let other = CONJUNCT2 (c1092moc_use C1092MPRI_OTHER_ORDINARY) in
  let tR, eqR = c1092moc_layers 11 [C1092MOC_SW; c1092moc_tr `&2` `&2`] in
  let facts = [c1092moc_punit 11 tR; c1092moc_pos (); c1092moc_side ();
               c1092moc_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 ne; CONJUNCT2 ne;
               inner; c1092moc_seed 11 (`&2`, `&1543 / &500`); other;
               c1092moc_excl 11 7 (CONJUNCT2 pair); c1092moc_apart 6 11] in
  MATCH_MP_TAC (SPECL ([`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] @ tR)
    C1092MRIPOS_IMPOSSIBLE) THEN
  REWRITE_TAC[ldisj] THEN CONV_TAC (c1092moc_conv eqR) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC;
         REWRITE_TAC[REAL_ARITH `forall x. x + &2 = &2 + x`] THEN
         REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;
