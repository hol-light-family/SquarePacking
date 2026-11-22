(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/InwardTwoBars.lean                 *)
(* (N12Compact.Completion.OtherCases.InwardTwoBars).  The full all-angle     *)
(* inward two-bar ending: E is put in canonical frame (CLF_CANONICAL_FRAME); *)
(* the positive sector is InwardSign.positive_impossible                     *)
(* (OCISG_POSITIVE_IMPOSSIBLE), the negative one NegativeElbowTwoBars.       *)
(* impossible (CCNETB_IMPOSSIBLE).  W = (cW,sW,uW,vW,aW), E = (cE,..,aE).   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_InwardSign.ml";;
needs "n12/geometry/CP_OtherCases_NegativeElbowTwoBars.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: impossible *)
let OCITB_IMPOSSIBLE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      &1 < aE /\ aW = aE /\
      linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
      linside cW sW uW vW aW (&0) (&0) /\
      linside cW sW uW vW aW (&0) (&13 / &50) /\
      linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
      linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
      linside cE sE uE vE aE (&13 / &50) (&0) /\
      (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside cE sE uE vE aE x (--(&1))) /\
      (forall y. --(&13 / &50) <= y ==> y <= &0 ==> ~linside cE sE uE vE aE (&1) y) /\
      ldisj cW sW uW vW aW cE sE uE vE aE
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `forall x y. linside c' s' u' v' a' x y <=> linside cE sE uE vE aE x y`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[ldisj; GSYM th]) else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = aE`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aE`)) THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [MATCH_MP_TAC OCISG_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aE:real`;
                          `c:real`; `s:real`; `u:real`; `v:real`; `aE:real`] THEN
    ASM_REWRITE_TAC[ldisj] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `--(&13 / &50)` o check (fun th ->
        can (term_match [] `forall y. P y ==> Q y ==> ~linside c s u v aE (&1) y`) (concl th))) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    MATCH_MP_TAC CCNETB_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `s:real`; `u:real`; `v:real`; `aE:real`; `--s`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;
