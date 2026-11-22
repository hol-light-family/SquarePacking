(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/InwardSign.lean                     *)
(* (namespace N12Compact.Completion.OtherCases.InwardSign).  The inward     *)
(* southeast owner with an omitted F8 has negative canonical sine.          *)
(* Squares W = cW sW uW vW aW, E = cE sE uE vE aE.  InwardSignSupports.*:    *)
(* ocisup_data / OCISUP_*; BottomBarSupport.positive: CCBBS_POSITIVE;       *)
(* increasing_projection: CCOS_INCREASING_PROJECTION; the SAT reduction:    *)
(* ABT_FOUR_AXES; upper_neg / lower_neg: OCWPVG_UPPER_NEG / _LOWER_NEG;     *)
(* strict_bounds: ABT_SB_TAC; canonical_frame: CLF_CANONICAL_FRAME.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_InwardSignSupports.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCISG_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || (can (find_term ((=) `linside`)) t && not (mem t keep))
    then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* the separator cone (Lean: cone, local to positive_impossible) *)
let OCISG_CONE = prove
 (`forall cW sW uW vW cE sE uE vE a nx ny.
      cW * cW + sW * sW = &1 /\ cE * cE + sE * sE = &1 /\ &0 < a /\
      linside cW sW uW vW a (--(&7 / &20)) (--(&7 / &20)) /\
      linside cW sW uW vW a (&0) (&13 / &50) /\
      linside cE sE uE vE a (&7 / &20) (--(&7 / &20)) /\
      linside cE sE uE vE a (&0) (--(&13 / &50)) /\
      nx pow 2 + ny pow 2 = &1 /\
      ABT_upper cW sW uW vW a nx ny <= ABT_lower cE sE uE vE a nx ny
      ==> &0 < nx /\ ny < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_SB_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`]
    `--(&7 / &20)` `--(&7 / &20)` `nx:real` `ny:real` THEN
  ABT_SB_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`]
    `&0` `&13 / &50` `nx:real` `ny:real` THEN
  ABT_SB_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`]
    `&7 / &20` `--(&7 / &20)` `nx:real` `ny:real` THEN
  ABT_SB_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`]
    `&0` `--(&13 / &50)` `nx:real` `ny:real` THEN
  ABT_ARITH_TAC);;

(* Lean: reverse (local) *)
let OCISG_REVERSE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE nx ny.
      ABT_upper cE sE uE vE aE nx ny <= ABT_lower cW sW uW vW aW nx ny
      ==> ABT_upper cW sW uW vW aW (--nx) (--ny) <= ABT_lower cE sE uE vE aE (--nx) (--ny)`,
  REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN REAL_ARITH_TAC);;

(* Lean: positive_impossible *)
let OCISG_POSITIVE_IMPOSSIBLE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      &1 < aE /\ aW = aE /\ &0 < cE /\ &0 <= sE /\ sE <= cE /\
      linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
      linside cW sW uW vW aW (&0) (&0) /\
      linside cW sW uW vW aW (&0) (&13 / &50) /\
      linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
      linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
      linside cE sE uE vE aE (&13 / &50) (&0) /\
      ~linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
      (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside cE sE uE vE aE x (--(&1))) /\
      ldisj cW sW uW vW aW cE sE uE vE aE
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aE`)) THEN
  let mkE = `linside cE sE uE vE aE (&7 / &20) (--(&7 / &20))`
  and inE = `linside cE sE uE vE aE (&0) (--(&13 / &50))`
  and elE = `linside cE sE uE vE aE (&13 / &50) (&0)` in
  MP_TAC(SPECL [`cE:real`; `sE:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  SUBGOAL_THEN `vE + aE <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `ldisj cW sW uW vW aE cE sE uE vE aE` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `&0`]) THEN
    ASM_REWRITE_TAC[] THEN OCISG_KEEP_TAC [mkE; inE; elE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sE` ASSUME_TAC THENL [OCISG_KEEP_TAC [elE]; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `&13 / &50`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN `uE + aE <= cE - &13 / &50 * sE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCISG_KEEP_TAC [`~linside cE sE uE vE aE (&1) (--(&13 / &50))`; inE; elE]; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] CCBBS_POSITIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           REPEAT STRIP_TAC THEN
           FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (is_forall o concl)) THEN
           ASM_REWRITE_TAC[];
           OCISG_KEEP_TAC [inE]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `ocisup_data cE sE uE vE aE` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ocisup_data]; ALL_TAC] THEN
  (* canonical frame of W *)
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aE:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aE`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th) &&
       length(fst(strip_forall(concl th))) = 2 && is_eq(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  SUBGOAL_THEN `forall nx ny. nx pow 2 + ny pow 2 = &1 /\
      ABT_upper c1 s1 u1 v1 aE nx ny <= ABT_lower cE sE uE vE aE nx ny
      ==> &0 < nx /\ ny < &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `cE:real`; `sE:real`;
                  `uE:real`; `vE:real`; `aE:real`; `nx:real`; `ny:real`] OCISG_CONE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aE:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ldisj]; ALL_TAC] THEN
  let cone nx ny =
    FIRST_X_ASSUM(MP_TAC o SPECL [nx; ny] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ABT_upper`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
                    ASM_REAL_ARITH_TAC] in
  let rev =
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OCISG_REVERSE o check (fun th ->
      can (term_match [] `ABT_upper cE sE uE vE aE nx ny <= ABT_lower c1 s1 u1 v1 aE nx ny`)
        (concl th))) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_CASES_TAC `&0 <= s1` THENL
     [cone `c1:real` `s1:real`;
      MATCH_MP_TAC OCISUP_NEGATIVE_W_AXIS THEN
      MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aE:real`;
                            `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--s1`] THEN
      ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC];
    rev THEN cone `--c1` `--s1`;
    cone `--s1` `c1:real`;
    rev THEN ASM_CASES_TAC `&0 <= s1` THENL
     [MATCH_MP_TAC OCISUP_POSITIVE_W_AXIS THEN
      MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aE:real`;
                            `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      cone `s1:real` `--c1`];
    cone `cE:real` `sE:real`;
    rev THEN cone `--cE` `--sE`;
    cone `--sE` `cE:real`;
    rev THEN MATCH_MP_TAC OCISUP_OWN_AXIS THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `aE:real`;
                          `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: canonical_negative *)
let OCISG_CANONICAL_NEGATIVE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
      cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
      &1 < aE /\ aW = aE /\ &0 < cE /\ abs sE <= cE /\
      linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
      linside cW sW uW vW aW (&0) (&0) /\
      linside cW sW uW vW aW (&0) (&13 / &50) /\
      linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
      linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
      linside cE sE uE vE aE (&13 / &50) (&0) /\
      ~linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
      (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside cE sE uE vE aE x (--(&1))) /\
      ldisj cW sW uW vW aW cE sE uE vE aE
      ==> sE < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC OCISG_POSITIVE_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                        `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
