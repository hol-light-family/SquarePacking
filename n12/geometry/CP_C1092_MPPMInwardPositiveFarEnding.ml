(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveFarEnding.lean         *)
(* (N12Compact.C1092MPPMInwardPositive).  POSITIVE-MISSING-INWARD-FAR-       *)
(* ENDING (Lean header: "Source only, uncompiled").  Squares C = cC sC uC vC *)
(* aC, E = cE sE uE vE aE, L = cL sL uL vL aL (unit normals and positive     *)
(* sides explicit).  PairInput: c1092ipsf_pair; upper: ABT_upper;            *)
(* FarScalars.alpha/gamma/L0: c1092ipfs_alpha/gamma/L0; NegativeScalars.k/   *)
(* ell: c1092ipns_k/ell.  Tag C1092IPFE_.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveFarFaces.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveFarScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveSuccessor.ml";;

let C1092IPFE_FACTS =
  filter (fun th -> let t = concl th in is_binary "real_lt" t || is_binary "real_le" t);;

(* Lean: far_target_support *)
let C1092IPFE_FAR_TARGET_SUPPORT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cL sL uL vL aL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE (--sE) /\
     C1092WPS_half cC sC <= &1 / &5 /\
     ~linside cE sE uE vE aE (&1) (--(&14 / &25)) /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&13 / &50) /\
     ldisj cC sC uC vC aC cL sL uL vL aL
     ==> uE < ABT_upper cC sC uC vC aC cE sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092IPFF_NEGATIVE_FAR_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipsf_pair] o
    check (fun th -> can (term_match [] `c1092ipsf_pair a b c d e f g h i j`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] C1092IPFF_LEFT_SEGMENT_ALTERNATIVES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN DISJ_CASES_TAC THENL
   [(* transverse *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `(&543 / &500) * sC`]
      C1092IPNSU_TARGET_SUPPORT_OF_CAP) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPFS_TRANSVERSE_TARGET) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input] o
      check (fun th -> can (term_match [] `c1092ipp_input a b c d e`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    (* oblique *)
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092IPNSU_NEGATIVE_FACES) THEN
  ASM_REWRITE_TAC[c1092mane_successorFaces] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092IPP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092ipp_profile] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input] o
    check (fun th -> can (term_match [] `c1092ipp_input a b c d e`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPNS_RELATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPFS_OBLIQUE_TARGET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
                `c1092ipns_k cC sC cE (--sE)`; `--c1092ipns_ell cC sC cE (--sE)`] C1092TFSU_UPPER_POS_NEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[c1092ipns_k; c1092ipns_ell] THEN REAL_ARITH_TAC) THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  (* atoms *)
  SUBGOAL_THEN
   `c1092ipfs_L0 cC sC = c1092ipfs_alpha cC sC + c1092ipfs_gamma cC sC - &7059 / &25000 /\
    &0 < c1092ipfs_alpha cC sC /\ &0 < c1092ipfs_gamma cC sC /\
    --(&7059 / &25000) <= c1092ipfs_alpha cC sC * uC - c1092ipfs_gamma cC sC * (vC + aC) /\
    c1092ipns_k cC sC cE (--sE) * c1092ipfs_gamma cC sC -
    c1092ipns_ell cC sC cE (--sE) * c1092ipfs_alpha cC sC = (&43 / &500) * cE + (&13 / &50) * sE`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092ipfs_L0; c1092ipfs_alpha; c1092ipfs_gamma] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[c1092ipns_k; c1092ipns_ell] THEN
      UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  ABBREV_TAC `kk = c1092ipns_k cC sC cE (--sE)` THEN
  ABBREV_TAC `ll = c1092ipns_ell cC sC cE (--sE)` THEN
  ABBREV_TAC `al = c1092ipfs_alpha cC sC` THEN
  ABBREV_TAC `ga = c1092ipfs_gamma cC sC` THEN
  ABBREV_TAC `l0 = c1092ipfs_L0 cC sC` THEN
  SUBGOAL_THEN `kk * ga - ll * al < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (ll * al - kk * ga) * (--uC - aC) /\
                &0 <= ll * (al * uC - ga * (vC + aC) + &7059 / &25000) /\
                &0 <= ga * (cE - sE - aC - uE) /\
                &0 < (aC - &1) * (ga + ll * (al + ga))`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LT_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ga * (kk * (uC + aC) + --ll * vC - uE)` MP_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `l0 = al + ga - &7059 / &25000` then
       RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o C1092IPFE_FACTS) THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN REAL_ARITH_TAC]);;

(* Lean: far_impossible *)
let C1092IPFE_FAR_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cL sL uL vL aL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ abs sE <= cE /\
     ~linside cE sE uE vE aE (&1) (--(&14 / &25)) /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&13 / &50) /\
     ldisj cC sC uC vC aC cL sL uL vL aL
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
  MATCH_MP_TAC C1092IPNSU_IMPOSSIBLE_OF_TARGET THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `C1092WPS_half cC sC <= &1 / &5` THENL
   [MATCH_MP_TAC C1092IPFE_FAR_TARGET_SUPPORT THEN
    MAP_EVERY EXISTS_TAC [`vE:real`; `aE:real`; `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipsf_pair] o
    check (fun th -> can (term_match [] `c1092ipsf_pair a b c d e f g h i j`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092IPP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092ipp_profile] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input] o
    check (fun th -> can (term_match [] `c1092ipp_input a b c d e`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `(&7 / &20) * (cC + sC)`]
    C1092IPNSU_TARGET_SUPPORT_OF_CAP) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092IPNS_MARKER_TARGET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;
