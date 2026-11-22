(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveSuccessorFaces.lean    *)
(* (N12Compact.C1092MPPMInwardPositive).  Same-owner recipient faces for    *)
(* the positive missing-center inward branch.  Squares C = cC sC uC vC aC,  *)
(* E = cE sE uE vE aE (unit normals and positive sides explicit).           *)
(* PairInput is c1092ipsf_pair, NonnegativeFaces is c1092ipsf_faces;         *)
(* Input / profile: c1092ipp_input / C1092IPP_PROFILE; NonnegativeRecipient *)
(* Data / faces: c1092minf_data / C1092MINF_FACES; half_of_width /           *)
(* sine_le_twice_half: C1092IPP_ lemmas; UnitCircleChord.increasing:         *)
(* CCUCC_INCREASING.  Tag C1092IPSF_.                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveSuccessorScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardNonnegativeFaces.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveProfile.ml";;

(* Lean: PairInput (structure) *)
let c1092ipsf_pair = new_definition
 `c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE <=>
    c1092ipp_input cC sC uC vC aC /\ aC = aE /\ c1092minf_data cE sE uE vE aE /\
    linside cE sE uE vE aE (&1 / &2) (--(&1)) /\
    ldisj cC sC uC vC aC cE sE uE vE aE`;;

(* Lean: NonnegativeFaces (structure) *)
let c1092ipsf_faces = new_definition
 `c1092ipsf_faces (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    u + a <= c - (&2 / &5) * s /\ --c - s <= v /\ v + a <= --c / &2 /\
    --(&543 / &500) * s <= u /\ &3 / &5 < s /\ c < &4 / &5`;;

let C1092IPSF_LIN = NLIN_TAC ~deg2:false [];;

(* Lean: nonnegative_faces *)
let C1092IPSF_NONNEGATIVE_FACES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE sE
     ==> c1092ipsf_faces cE sE uE vE aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092ipsf_pair]
    (ASSUME `c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092MINF_FACES) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092IPP_PROFILE) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[c1092ipp_profile] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092minf_data]
    (ASSUME `c1092minf_data cE sE uE vE aE`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal cE sE`)) THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cE sE uE vE aE (&7 / &20) (--(&7 / &20))`;
    `linside cE sE uE vE aE (&13 / &50) (--(&1))`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  SUBGOAL_THEN `uE < --sE / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(MP (SPECL [`cE:real`; `sE:real`] C1092IPP_SINE_LE_TWICE_HALF)
      (ASSUME `c977cc_normal cE sE`)) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `&1 / &10`] C1092IPP_HALF_OF_WIDTH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IPSF_LIN; DISCH_TAC] THEN C1092IPSF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `vE + aC <= --cE / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aC` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&0`; `--(&1 / &2)`]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092IPSF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `--(&543 / &500) * sE <= uE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cE sE uE vE aC (&0) (--(&543 / &500))` THEN
    REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN C1092IPSF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < sE + cE / &2` ASSUME_TAC THENL [C1092IPSF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &5 < sE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `cE:real`; `sE:real`; `&1 / &2`; `&1`] CCUCC_INCREASING) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `cE < &4 / &5` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (cE - &4 / &5) * (cE + &4 / &5) /\ &0 < (sE - &3 / &5) * (sE + &3 / &5)`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    C1092IPSF_LIN; ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092ipsf_faces]);;
