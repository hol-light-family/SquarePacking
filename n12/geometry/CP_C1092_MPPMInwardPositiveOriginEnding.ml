(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveOriginEnding.lean      *)
(* (N12Compact.C1092MPPMInwardPositive).  Complete local POSITIVE-MISSING-   *)
(* INWARD-ORIGIN-ENDING.  Squares C = cC sC uC vC aC, E = cE sE uE vE aE     *)
(* (unit normals and positive sides explicit).  Input / profile:             *)
(* c1092ipp_input / C1092IPP_PROFILE; PairInput: c1092ipsf_pair;             *)
(* successor_negative: C1092IPSU_SUCCESSOR_NEGATIVE; impossible_of_target /  *)
(* target_support_of_cap: C1092IPNSU_ theorems; NegativeScalars.small_target *)
(* / marker_target: C1092IPNS_SMALL_TARGET / C1092IPNS_MARKER_TARGET.        *)
(* Tag C1092IPOE_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveNegativeSupport.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveSuccessor.ml";;

(* Lean: origin_cap *)
let C1092IPOE_ORIGIN_CAP = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     c1092ipp_input c s u v a /\ ~linside c s u v a (--(&1)) (&0)
     ==> v + a <= s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092IPP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092ipp_profile] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input] o
    check (fun th -> can (term_match [] `c1092ipp_input a b c d e`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (--(&7 / &20)) (--(&7 / &20))`;
    `linside c s u v a (--(&1 / &2)) (&0)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside c s u v a (--(&1)) (&0)` THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: origin_impossible *)
let C1092IPOE_ORIGIN_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ abs sE <= cE /\
     ~linside cC sC uC vC aC (--(&1)) (&0)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092IPSU_SUCCESSOR_NEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c977cc_normal cE (--sE)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN
    UNDISCH_TAC `abs sE <= cE` THEN UNDISCH_TAC `sE < &0` THEN
    UNDISCH_TAC `cE * cE + sE * sE = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipsf_pair] o
    check (fun th -> can (term_match [] `c1092ipsf_pair a b c d e f g h i j`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092IPP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092ipp_profile] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input] o
    check (fun th -> can (term_match [] `c1092ipp_input a b c d e`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MATCH_MP_TAC C1092IPNSU_IMPOSSIBLE_OF_TARGET THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `C1092WPS_half cC sC <= &1 / &5` THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`]
      C1092IPNSU_TARGET_SUPPORT_OF_CAP) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092IPOE_ORIGIN_CAP) THEN
       ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPNS_SMALL_TARGET) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `(&7 / &20) * (cC + sC)`]
      C1092IPNSU_TARGET_SUPPORT_OF_CAP) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPNS_MARKER_TARGET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;
