(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/RightInnerActual.lean               *)
(* (N12Compact.C1092MMMPRightInnerActual).  Original MMMP right-inner        *)
(* exclusion.  Conventions of CP_C1092_MMMP_BottomPair.ml /                  *)
(* CP_C1092_MMMP_NortheastActualSign.ml (forward toolkit c1092mo_*, charts   *)
(* via c1092mo_layers; PositiveActual is c1092mnas_pos).  Covers:            *)
(* C1092AuxiliaryCover.southeast_g_cover C1092AC_SOUTHEAST_G_COVER,          *)
(* C1092MMMMEntrance.southeast_f_cover C1092MMEN_SOUTHEAST_F_COVER;          *)
(* C1092CornerTwoGaps.impossible C1092CTG_IMPOSSIBLE, C1092MixedSpan.        *)
(* impossible C1092MS_IMPOSSIBLE, C1092MMMPRightNearAdvance.point            *)
(* C1092MRNA_POINT, C1092MMMPRightInnerPositive.impossible                   *)
(* C1092MRIPOS_IMPOSSIBLE.  Tag C1092MRIA_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_NortheastActualSign.ml";;
needs "n12/geometry/CP_C1092_MMMP_RightInnerPositive.ml";;
needs "n12/geometry/CP_C1092_MMMP_RightNearAdvance.ml";;
needs "n12/geometry/CP_C1092_MMMMEntrance.ml";;
needs "n12/geometry/CP_C1092_CornerTwoGaps.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;

let c1092mria_useh th =
  CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V th) (c1092mo_hh ()));;

(* the bottom wall tip: local_wall_segment at wall 1 *)
let C1092MRIA_BOTTOM_TIP = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092AE_P C1092MMPE_CTX (c1092mmpe_in 9 "&239 / &100" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`c1092mmpe_mmmp`; `1`; `&161 / &100`]) C1092WC_LOCAL_WALL_SEGMENT) THEN
  ASM_REWRITE_TAC[c1092wc_pmx; c1092wc_pmy; c1092wc_by; c1092mmpe_mmmp; ARITH] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]);;

let C1092MRIA_INNER = c1092mo_in 10 `&113 / &50` `&2`;;

(* Lean: southeast_pair_of_inner *)
let C1092MRIA_SOUTHEAST_PAIR_OF_INNER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s /\\ %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 10 "&113 / &50" "&2") (c1092mmpe_in 5 "&3" "&87 / &50") (c1092mmpe_in 5 "&3" "&8 / &5")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let inner = ASSUME C1092MRIA_INNER in
  let wa = c1092mo_use C1092MMPE_WALL_AUXILIARIES in
  let bottom = CONJUNCT1 (CONJUNCT2 wa) in
  let gcov = c1092mria_useh C1092AC_SOUTHEAST_G_COVER in
  let fcov = c1092mria_useh C1092MMEN_SOUTHEAST_F_COVER in
  let btip = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MRIA_BOTTOM_TIP)) in
  let e59 = c1092mo_excl 5 9 bottom and e510 = c1092mo_excl 5 10 inner in
  let gtm = c1092mo_in 5 `&3` `&8 / &5` in
  SUBGOAL_THEN gtm ASSUME_TAC THENL [MESON_TAC[gcov; e59; e510]; ALL_TAC] THEN
  let g = ASSUME gtm in
  let habs = mk_neg (c1092mo_in 5 `&3` `&87 / &50`) and hout = c1092mo_in 5 `&12 / &5` `&1` in
  let t, eqs = c1092mo_layers 5 [C1092MO_Y] in
  let ctg = DISCH habs (DISCH hout (c1092mo_apply (c1092mo_conv eqs)
    (SPECL (t @ [`&39 / &100`; `&13 / &50`]) C1092CTG_IMPOSSIBLE)
    [c1092mo_punit 5 t; c1092mo_pos (); c1092mo_side ();
     c1092mo_seed 5 (`&47 / &20`, `&33 / &20`); ASSUME hout; g;
     c1092mo_excl 5 9 btip; ASSUME habs; c1092mo_excl 5 1 (c1092mo_seed 1 (`&3`, `&1`))])) in
  let hpt = c1092mo_in 5 `&2` `&87 / &50` in
  let ms = DISCH habs (DISCH (mk_neg hout) (DISCH hpt (c1092mo_apply ALL_CONV (SPECL (c1092mo_own 5) C1092MS_IMPOSSIBLE)
    [c1092mo_unit 5; c1092mo_pos (); c1092mo_side (); ASSUME hpt; g; e510; ASSUME habs; e59;
     ASSUME (mk_neg hout)]))) in
  CONJ_TAC THENL [MESON_TAC[fcov; ctg; ms]; ACCEPT_TAC g]);;

(* Lean: right_missing_inner *)
let C1092MRIA_RIGHT_MISSING_INNER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> ~%s"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX (c1092mmpe_in 10 "&113 / &50" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MMPE_V C1092MNAS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[c1092mnas_pos] THEN
  CONV_TAC C1092MO_CODE_CONV THEN STRIP_TAC THEN DISCH_TAC THEN
  let inner = ASSUME C1092MRIA_INNER in
  let el_inner = EQ_MP (SYM (C1092MO_CODE_CONV (parse_term (c1092mmpe_in 10 "&113 / &50" "&2")))) inner in
  let se = CONJUNCT1 (CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V C1092MRIA_SOUTHEAST_PAIR_OF_INNER)
    (CONJ (ASSUME C1092MO_NP) (CONJ (ASSUME C1092MO_IMG) (CONJ (ASSUME C1092MO_CTX) el_inner))))) in
  let ne = c1092mo_use C1092MMPE_NORTHEAST_PAIR in
  let tip = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MNAS_RIGHT_TIP)) in
  let tR, eqR = c1092mo_layers 10 [c1092mo_tr `&2` `&2`] in
  let mR = c1092mo_seed 10 (`&1543 / &500`, `&2`) in
  let rmiss = c1092mo_excl 10 5 se and rmark = c1092mo_excl 10 6 (c1092mo_seed 6 (`&47 / &20`, `&47 / &20`)) in
  let upper = c1092mo_apply (c1092mo_conv eqR) (SPECL tR C1092MRNA_POINT)
    [c1092mo_punit 10 tR; c1092mo_pos (); c1092mo_side (); inner; mR; tip; rmiss; rmark] in
  let facts = [c1092mo_punit 10 tR; c1092mo_pos (); c1092mo_side ();
               c1092mo_seed 6 (`&47 / &20`, `&47 / &20`); CONJUNCT1 ne; CONJUNCT2 ne;
               inner; mR; upper; rmiss; c1092mo_apart 6 10] in
  MATCH_MP_TAC (SPECL ([`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] @ tR) C1092MRIPOS_IMPOSSIBLE) THEN
  REWRITE_TAC[ldisj] THEN CONV_TAC (c1092mo_conv eqR) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;
