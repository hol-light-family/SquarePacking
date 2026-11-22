(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardPositiveSuccessor.lean         *)
(* (N12Compact.C1092MPPMInwardPositive).  Complete same-square successor     *)
(* sign comparison for positive missing-center inward C.  Squares            *)
(* C = cC sC uC vC aC, E = cE sE uE vE aE (unit normals / positive sides     *)
(* explicit).  PairInput / NonnegativeFaces: c1092ipsf_pair / c1092ipsf_faces*)
(* (C1092IPSF_NONNEGATIVE_FACES); profile: C1092IPP_PROFILE; k / delta and   *)
(* the margins: c1092ipss_k / c1092ipss_delta / C1092IPSS_ lemmas;           *)
(* SteepPositiveThreeSquare.signed_axes: C1092SPTS_SIGNED_AXES; formulas /   *)
(* lower_pn: C1092WS_FORMULAS / C1092WS_LOWER_PN; TwoFifths.Support          *)
(* upper_neg / lower_neg / upper_pos_neg / upper_neg_neg: C1092TFSU_ lemmas; *)
(* ownU / ownV / strict_bounds: ABT_OWNU / ABT_OWNV / ABT_STRICT_BOUNDS.     *)
(* Tag C1092IPSU_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardPositiveSuccessorFaces.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareData.ml";;

let C1092IPSU_LIN = NLIN_TAC ~deg2:false [];;

let C1092IPSU_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092IPSU_LIN; ALL_TAC];;

let C1092IPSU_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092IPSU_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`];;

(* unpack the pair input (with aE replaced by aC), the profile of C and faces of E *)
let C1092IPSU_SETUP_TAC =
  MP_TAC(SPECL (C1092IPSU_C @ [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`])
    C1092IPSF_NONNEGATIVE_FACES) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092ipsf_pair]
    (ASSUME `c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE`)) THEN
  MP_TAC(SPECL C1092IPSU_C C1092IPP_PROFILE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092ipsf_faces]
    (ASSUME `c1092ipsf_faces cE sE uE vE aC`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092ipp_profile]
    (ASSUME `c1092ipp_profile cC sC uC vC aC`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092ipp_input]
    (ASSUME `c1092ipp_input cC sC uC vC aC`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092minf_data]
    (ASSUME `c1092minf_data cE sE uE vE aC`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal cC sC`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal cE sE`));;

(* Lean: cone (local of axes) *)
let C1092IPSU_CONE = prove
 (`forall cC sC uC vC aC cE sE uE vE nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
     linside cE sE uE vE aC (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aC (&1 / &2) (--(&1)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cE sE uE vE aC nx ny
     ==> &0 < nx /\ &0 < nx / &2 - (&37 / &50) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092IPSU_C @ [`--(&7 / &20)`; `--(&7 / &20)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092IPSU_C @ [`&0`; `--(&13 / &50)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092IPSU_E @ [`&7 / &20`; `--(&7 / &20)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092IPSU_E @ [`&1 / &2`; `--(&1)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: axes (private) *)
let C1092IPSU_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE sE
     ==> (uC + aC <= ABT_lower cE sE uE vE aE cC sC /\ &0 < c1092ipss_delta cC sC cE sE) \/
         ABT_upper cC sC uC vC aC sC (--cC) <= ABT_lower cE sE uE vE aE sC (--cC) \/
         ABT_upper cC sC uC vC aC sE (--cE) <= --(vE + aE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092IPSU_SETUP_TAC THEN
  let cone nx ny =
    MP_TAC(SPECL (C1092IPSU_C @ [`cE:real`; `sE:real`; `uE:real`; `vE:real`; nx; ny]) C1092IPSU_CONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_2] THEN TRY RASM_ARITH_TAC; STRIP_TAC] in
  MP_TAC(SPECL (C1092IPSU_C @ C1092IPSU_E) C1092SPTS_SIGNED_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [cone `cC:real` `sC:real` THEN DISJ1_TAC THEN
    MP_TAC(SPECL C1092IPSU_C ABT_OWNU) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    C1092IPSU_PROD `&0 < cC * (sE - (&3 / &4) * cE)` THEN
    C1092IPSU_PROD `&0 <= cE * ((&3 / &4) * cC - sC)` THEN
    REWRITE_TAC[c1092ipss_delta] THEN C1092IPSU_LIN;
    cone `--cC` `--sC` THEN ASM_REAL_ARITH_TAC;
    cone `--sC` `cC:real` THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[];
    cone `cE:real` `sE:real` THEN ASM_REAL_ARITH_TAC;
    cone `--cE` `--sE` THEN ASM_REAL_ARITH_TAC;
    cone `--sE` `cE:real` THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL C1092IPSU_E C1092TFSU_LOWER_OPPOSITE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN ASM_REWRITE_TAC[]]);;

let C1092IPSU_K = `c1092ipss_k cC sC cE sE`;;
let C1092IPSU_Z = `c1092ipss_delta cC sC cE sE`;;

(* Lean: nonnegative_successor_impossible *)
let C1092IPSU_NONNEGATIVE_SUCCESSOR_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE sE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092IPSU_C @ [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]) C1092IPSU_AXES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092IPSU_SETUP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092IPSS_RELATIVE) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092IPSS_SOURCE_MARGIN) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092IPSS_DOWNWARD_MARGIN) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092IPSS_TARGET_AFTER) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`] C1092IPSS_TARGET_BEFORE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cE sE uE vE aC (&7 / &20) (--(&7 / &20))`] THEN
  SUBGOAL_THEN `uE <= cE - (&2 / &5) * sE - aC /\ vC <= (&7 / &20) * (cC + sC) - aC /\
                aC - cC - (&2 / &5) * sC <= uC + aC /\ --(&7 / &20) * (cE + sE) < vE + aC`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN C1092IPSU_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cC sC uC vC aC sC (--cC) = --vC` ASSUME_TAC THENL
   [MP_TAC(SPECL (C1092IPSU_C @ [`--sC`; `cC:real`]) C1092TFSU_UPPER_NEG) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL C1092IPSU_C ABT_OWNV) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC o
    check (fun th -> is_disj (concl th) && can (find_term ((=) `ABT_upper`)) (concl th))) THENL
   [(* current *)
    MP_TAC(SPECL (C1092IPSU_E @ [`cC:real`; `sC:real`; C1092IPSU_K; mk_comb(`(--):real->real`, C1092IPSU_Z)])
      C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c1092ipss_k; c1092ipss_delta] THEN REPEAT CONJ_TAC THEN
      TRY REAL_ARITH_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[c1092ipss_k; c1092ipss_delta]) THEN C1092IPSU_LIN;
      DISCH_TAC] THEN
    C1092IPSU_PROD (subst [C1092IPSU_K, `K:real`] `&0 <= K * ((cE - (&2 / &5) * sE - aC) - uE)`) THEN
    C1092IPSU_PROD (subst [C1092IPSU_Z, `z:real`] `&0 < z * ((vE + aC) - --(&7 / &20) * (cE + sE))`) THEN
    C1092IPSU_PROD (subst [C1092IPSU_K, `K:real`] `&0 < (aC - &1) * (&1 + K)`) THEN
    C1092IPSU_LIN;
    (* downward *)
    MP_TAC(CONJUNCT1(MP (SPECL (C1092IPSU_E @ [`sC:real`; `--cC`]) C1092WS_FORMULAS)
      (CONJ (ASSUME `cE * cE + sE * sE = &1`) (ASSUME `&0 < aC`)))) THEN
    SUBGOAL_THEN (subst [C1092IPSU_K, `K:real`; C1092IPSU_Z, `z:real`]
      `sC * cE + --cC * sE = --z /\ --sC * sE + --cC * cE = --K`) (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[c1092ipss_k; c1092ipss_delta] THEN CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    C1092IPSU_PROD (subst [C1092IPSU_K, `K:real`] `&0 < K * ((vE + aC) - --(&7 / &20) * (cE + sE))`) THEN
    ASM_CASES_TAC (subst [C1092IPSU_Z, `z:real`] `&0 <= z`) THENL
     [SUBGOAL_THEN (subst [C1092IPSU_K, `K:real`; C1092IPSU_Z, `z:real`]
        `min (--z) (&0) = --z /\ min (--K) (&0) = --K`) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [CONJ_TAC THEN REWRITE_TAC[REAL_ARITH `min x (&0) = x <=> x <= &0`] THEN C1092IPSU_LIN; ALL_TAC] THEN
      C1092IPSU_PROD (subst [C1092IPSU_Z, `z:real`] `&0 <= z * (uE + aC)`) THEN
      C1092IPSU_LIN;
      SUBGOAL_THEN (subst [C1092IPSU_K, `K:real`; C1092IPSU_Z, `z:real`]
        `min (--z) (&0) = &0 /\ min (--K) (&0) = --K`) (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [CONJ_TAC THEN REWRITE_TAC[REAL_ARITH `min x (&0) = &0 <=> &0 <= x`;
                                  REAL_ARITH `min x (&0) = x <=> x <= &0`] THEN C1092IPSU_LIN; ALL_TAC] THEN
      C1092IPSU_PROD (subst [C1092IPSU_Z, `z:real`] `&0 <= --z * --uE`) THEN
      C1092IPSU_LIN];
    (* target *)
    C1092IPSU_PROD (subst [C1092IPSU_K, `K:real`] `&0 <= K * (((&7 / &20) * (cC + sC) - aC) - vC)`) THEN
    ASM_CASES_TAC (subst [C1092IPSU_Z, `z:real`] `&0 <= z`) THENL
     [MP_TAC(SPECL (C1092IPSU_C @ [`sE:real`; `--cE`; C1092IPSU_Z; mk_comb(`(--):real->real`, C1092IPSU_K)])
        C1092TFSU_UPPER_POS_NEG) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[c1092ipss_k; c1092ipss_delta] THEN REPEAT CONJ_TAC THEN
        TRY REAL_ARITH_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[c1092ipss_k; c1092ipss_delta]) THEN C1092IPSU_LIN;
        DISCH_TAC] THEN
      C1092IPSU_PROD (subst [C1092IPSU_Z, `z:real`] `&0 <= z * ((uC + aC) - (aC - cC - (&2 / &5) * sC))`) THEN
      C1092IPSU_PROD (subst [C1092IPSU_K, `K:real`; C1092IPSU_Z, `z:real`] `&0 < (aC - &1) * (&1 + z + K)`) THEN
      C1092IPSU_LIN;
      MP_TAC(SPECL (C1092IPSU_C @ [`sE:real`; `--cE`; C1092IPSU_Z; mk_comb(`(--):real->real`, C1092IPSU_K)])
        C1092TFSU_UPPER_NEG_NEG) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[c1092ipss_k; c1092ipss_delta] THEN REPEAT CONJ_TAC THEN
        TRY REAL_ARITH_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[c1092ipss_k; c1092ipss_delta]) THEN C1092IPSU_LIN;
        DISCH_TAC] THEN
      SUBGOAL_THEN (subst [C1092IPSU_Z, `z:real`] `z <= &0`) ASSUME_TAC THENL
       [C1092IPSU_LIN; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
        can (find_term ((=) `c1092ipss_delta`)) (lhand (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      C1092IPSU_PROD (subst [C1092IPSU_Z, `z:real`] `&0 <= --z * (--aC - uC)`) THEN
      C1092IPSU_PROD (subst [C1092IPSU_K, `K:real`; C1092IPSU_Z, `z:real`] `&0 < (aC - &1) * (&1 - z + K)`) THEN
      C1092IPSU_LIN]]);;

(* Lean: successor_negative *)
let C1092IPSU_SUCCESSOR_NEGATIVE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092ipsf_pair cC sC uC vC aC cE sE uE vE aE /\ abs sE <= cE
     ==> sE < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC C1092IPSU_NONNEGATIVE_SUCCESSOR_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC (C1092IPSU_C @ [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]) THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC);;
