(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveFarFaces.lean          *)
(* (N12Compact.C1092MPPMInwardPositive).  The two extra entrances of the     *)
(* positive inward far ending.  Squares C = cC sC uC vC aC, E = cE sE uE vE  *)
(* aE, L = cL sL uL vL aL (unit normals and positive sides explicit).        *)
(* PairInput: c1092ipsf_pair; Input: c1092ipp_input; negative_faces:         *)
(* C1092IPNSU_NEGATIVE_FACES; IncreasingSegmentAvoidance.dichotomy:          *)
(* ISA_DICHOTOMY; UnitCircleChord.increasing: CCUCC_INCREASING.              *)
(* Tag C1092IPFF_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveNegativeSupport.ml";;
needs "n12/geometry/IncreasingSegmentAvoidance.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

let C1092IPFF_LIN = NLIN_TAC ~deg2:false [];;

(* Lean: negative_far_faces *)
let C1092IPFF_NEGATIVE_FAR_FACES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE (--sE) /\
     ~linside cE sE uE vE aE (&1) (--(&14 / &25))
     ==> vE + aE <= --sE - (&14 / &25) * cE /\ &60 / &109 < --sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092IPNSU_NEGATIVE_FACES) THEN
  ASM_REWRITE_TAC[c1092mane_successorFaces] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipsf_pair; c1092minf_data] o
    check (fun th -> can (term_match [] `c1092ipsf_pair a b c d e f g h i j`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cE sE uE vE aE (&7 / &20) (--(&7 / &20))`;
    `linside cE sE uE vE aE (&13 / &50) (--(&1))`] THEN
  SUBGOAL_THEN `&0 < --sE` ASSUME_TAC THENL [C1092IPFF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `cE - (&14 / &25) * sE < uE + aE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cE:real`; `--sE`; `&3 / &50`] C1092IPP_HALF_OF_WIDTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IPFF_LIN; DISCH_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `--sE`] C1092IPP_SINE_LE_TWICE_HALF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092IPFF_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `vE + aE <= --sE - (&14 / &25) * cE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cE sE uE vE aE (&1) (--(&14 / &25))` THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092IPFF_LIN;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 < --sE + (&263 / &500) * cE` ASSUME_TAC THENL [C1092IPFF_LIN; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&91 / &109`; `&60 / &109`; `cE:real`; `--sE`; `&263 / &500`; `&1`] CCUCC_INCREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]);;

(* Lean: left_segment_alternatives *)
let C1092IPFF_LEFT_SEGMENT_ALTERNATIVES = prove
 (`forall cC sC uC vC aC cL sL uL vL aL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     c1092ipp_input cC sC uC vC aC /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&13 / &50) /\
     ldisj cC sC uC vC aC cL sL uL vL aL
     ==> vC + aC <= (&543 / &500) * sC \/
         --(&7059 / &25000) <= ((&13 / &50) * cC - (&43 / &500) * sC) * uC -
                               ((&13 / &50) * sC + (&43 / &500) * cC) * (vC + aC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092IPP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092ipp_profile] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ipp_input] o
    check (fun th -> can (term_match [] `c1092ipp_input a b c d e`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC sC`)) THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cC sC uC vC aC (--(&1 / &2)) (&0)`;
    `linside cC sC uC vC aC (&0) (--(&1 / &2))`] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `--(&543 / &500)`; `&0`; `--(&1)`; `&13 / &50`] ISA_DICHOTOMY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092IPFF_LIN; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a ==> c) /\ (b ==> d) ==> a \/ b ==> c \/ d`) THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    UNDISCH_TAC `cC * cC + sC * sC = &1` THEN REAL_ARITH_TAC]);;
