(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMEnding.lean                          *)
(* (N12Compact.C1092MMMMEnding).  The continuous whole MMMM three-central   *)
(* ending, with literal rigid charts.  Charts (RigidCharts):                 *)
(*   opposite Q = (c, s, --u - a, --v - a, a), swap Q = (c, --s, v, u, a).   *)
(* MMMMFirstPair.result: C1092MFP_RESULT; MMMMSecondPair.result:             *)
(* C1092MSP_RESULT; MMMMCancellation.impossible: C1092MMC_IMPOSSIBLE;        *)
(* ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME.                        *)
(* N, E, W are written cN sN uN vN aN, cE ..., cW ....                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMMSecondPair.ml";;
needs "n12/geometry/CP_C1092_MMMMCancellation.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: Data (structure) *)
let c1092mme_data = new_definition
 `c1092mme_data cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW <=>
    &1 < aN /\ aN = aE /\ aN = aW /\
    linside cN sN uN vN aN (&0) (&0) /\
    linside cN sN uN vN aN (&1 / &2) (&0) /\
    linside cN sN uN vN aN (&0) (&1 / &2) /\
    linside cN sN uN vN aN (&7 / &20) (&7 / &20) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
    linside cE sE uE vE aE (&1) (--(&2 / &5)) /\
    linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
    linside cW sW uW vW aW (--(&13 / &50)) (&1) /\
    linside cW sW uW vW aW (--(&2 / &5)) (&1) /\
    ~linside cE sE uE vE aE (&1) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (&0) /\
    ~linside cE sE uE vE aE (&39 / &100) (--(&1)) /\
    ~linside cE sE uE vE aE (&39 / &100) (&0) /\
    ~linside cW sW uW vW aW (--(&1)) (&1) /\
    ~linside cW sW uW vW aW (&0) (&1) /\
    ~linside cW sW uW vW aW (--(&1)) (&39 / &100) /\
    ~linside cW sW uW vW aW (&0) (&39 / &100) /\
    ldisj cN sN uN vN aN cE sE uE vE aE /\
    ldisj cN sN uN vN aN cW sW uW vW aW`;;

(* Lean: Data.swapped *)
let C1092MME_DATA_SWAPPED = prove
 (`forall cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW.
     c1092mme_data cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW
     ==> c1092mme_data cN (--sN) vN uN aN cW (--sW) vW uW aW cE (--sE) vE uE aE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mme_data; ldisj; C1092RC_INSIDE_SWAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[REAL_NEG_NEG] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_MESON_TAC[]);;

(* Lean: reframe (private) *)
let C1092MME_REFRAME = prove
 (`forall cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW cQ sQ uQ vQ aQ.
     c1092mme_data cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW /\ aQ = aN /\
     (forall x y. linside cQ sQ uQ vQ aQ x y <=> linside cN sN uN vN aN x y)
     ==> c1092mme_data cQ sQ uQ vQ aQ cE sE uE vE aE cW sW uW vW aW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aQ:real = aN`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mme_data; ldisj] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "c1092mme_data"
                     with Failure _ -> false)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `aN:real = aE` || concl th = `aN:real = aW`))) THEN
  ASM_REWRITE_TAC[c1092mme_data; ldisj]);;

(* Lean: negative (private) *)
let C1092MME_NEGATIVE = prove
 (`forall cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092mme_data cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW /\
     c977cc_normal cN (--sN)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mme_data] o
    check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) = "c1092mme_data"
                     with Failure _ -> false)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    concl th = `aN:real = aE` || concl th = `aN:real = aW`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  (* B: canonical frame of opposite E *)
  MP_TAC(SPECL [`cE:real`; `sE:real`; `--uE - aN`; `--vE - aN`; `aN:real`]
    CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:real` (X_CHOOSE_THEN `t1:real` (X_CHOOSE_THEN `p1:real`
    (X_CHOOSE_THEN `q1:real` (X_CHOOSE_THEN `a1:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aN`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092RC_INSIDE_OPPOSITE]) THEN
  (* A: canonical frame of opposite (swap W) *)
  MP_TAC(SPECL [`cW:real`; `--sW`; `--vW - aN`; `--uW - aN`; `aN:real`]
    CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b2:real` (X_CHOOSE_THEN `t2:real` (X_CHOOSE_THEN `p2:real`
    (X_CHOOSE_THEN `q2:real` (X_CHOOSE_THEN `a2:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a2:real = aN`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092RC_INSIDE_OPPOSITE; C1092RC_INSIDE_SWAP]) THEN
  (* the first pair *)
  MP_TAC(SPECL [`cN:real`; `sN:real`; `--uN - aN`; `--vN - aN`; `aN:real`;
                `b1:real`; `t1:real`; `p1:real`; `q1:real`; `aN:real`] C1092MFP_RESULT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[C1092RC_INSIDE_OPPOSITE; REAL_NEG_NEG; REAL_NEG_0; ldisj] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[];
    REWRITE_TAC[C1092MFP_result; c1092sct_positive_faces] THEN STRIP_TAC] THEN
  (* the second pair *)
  MP_TAC(SPECL [`cN:real`; `--sN`; `--vN - aN`; `--uN - aN`; `aN:real`;
                `b2:real`; `t2:real`; `p2:real`; `q2:real`; `aN:real`] C1092MSP_RESULT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[C1092RC_INSIDE_OPPOSITE; C1092RC_INSIDE_SWAP; REAL_NEG_NEG;
                    REAL_NEG_0; ldisj] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(UNDISCH_TAC `cN * cN + sN * sN = &1` THEN REAL_ARITH_TAC) THEN ASM_MESON_TAC[];
    REWRITE_TAC[C1092MSP_result] THEN STRIP_TAC] THEN
  (* cancellation *)
  MP_TAC(SPECL [`aN:real`; `cN:real`; `--sN`; `b1:real`; `t1:real`; `b2:real`; `t2:real`;
                `uN:real`; `vN:real`] C1092MMC_IMPOSSIBLE) THEN
  SUBGOAL_THEN `c977cc_normal b1 t1 /\ c977cc_normal b2 t2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `uN < &0 /\ vN < &0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cN sN uN vN aN (&0) (&0)` THEN REWRITE_TAC[linside] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
    REWRITE_TAC[]]);;

(* Lean: impossible *)
let C1092MME_IMPOSSIBLE = prove
 (`forall cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c1092mme_data cN sN uN vN aN cE sE uE vE aE cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `u:real`
    (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092MME_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `s <= &0` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C1092MME_NEGATIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC; REWRITE_TAC[]];
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
      C1092MME_DATA_SWAPPED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `--s`; `v:real`; `u:real`; `a:real`;
                  `cW:real`; `--sW`; `vW:real`; `uW:real`; `aW:real`;
                  `cE:real`; `--sE`; `vE:real`; `uE:real`; `aE:real`] C1092MME_NEGATIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_NEG] THEN RASM_ARITH_TAC;
      REWRITE_TAC[]]]);;
