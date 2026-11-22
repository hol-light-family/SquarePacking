(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardSmallThreeEnding.lean          *)
(* (N12Compact.C1092MPPMInwardSmallThree; Lean header: "Source only").       *)
(* SMALL-INWARD-THREE-SQUARE-ENDING sections 4--6.  Squares C = cC sC uC vC  *)
(* aC, B = cB sB uB vB aB, E = cE sE uE vE aE (unit normals, 0 < sides       *)
(* explicit).  Input: c1092istd_input; BottomProfile: c1092istbo_profile;    *)
(* BoundaryRange: c1092isbs_range; nu / eta / X0 / Y0 / Delta0 / Z0:         *)
(* c1092isbs_*; d = cE, t = --sE, h = cB, k = sB; lam = cC * cB + sC * sB,   *)
(* gam = cC * sB - sC * cB.  The local `have`s of canonical_impossible       *)
(* (first_source, longitudinal, transverse, bottom_transverse, cone) are     *)
(* separate theorems C1092ISTE_* with the same hypotheses.                   *)
(* BottomAngle.central_faces / positive_wall / negative_wall_height:         *)
(* C1092IFBD_*; signed_axes: C1092SPTS_SIGNED_AXES; exists_positive_frame:   *)
(* WCB_EXISTS_POSITIVE_FRAME; turnFrame^3 of (c,s,u,v,a) is                  *)
(* (s, --c, --v - a, u, a); lower_nn / lower_np: C1092WS_*; upper_pos_neg /  *)
(* upper_pos_pos: C1092TFSU_*; ownU / ownV / strict_bounds: ABT_*.           *)
(* Tag C1092ISTE_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardSmallThreeBoundaryScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardSmallThreeData.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareData.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

let C1092ISTE_LIN = NLIN_TAC ~deg2:false [];;
let c1092iste_stmt c = parse_term (Printf.sprintf "!%s. %s /\\ abs sB <= cB ==> %s"
                                     C1092ISTD_VARS C1092ISTD_HYP c);;
let C1092ISTE_SQ = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`;
                    `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`];;
let C1092ISTE_CB = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;
let C1092ISTE_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;
let C1092ISTE_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`];;
let C1092ISTE_DTHK = [`cE:real`; `--sE`; `cB:real`; `sB:real`];;
let C1092ISTE_N = `c1092isbs_nu cE (--sE) cB sB`;;
let C1092ISTE_ETA = `c1092isbs_eta cE (--sE) cB sB`;;

(* instantiate a lemma, prove its antecedent conjuncts from the assumptions *)
let C1092ISTE_USE th args =
  MP_TAC(SPECL args th) THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC; C1092ISTE_LIN];
    DISCH_THEN STRIP_ASSUME_TAC];;

let C1092ISTE_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ISTE_LIN; ALL_TAC];;

let C1092ISTE_PT_TAC tm =
  MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* the common facts of canonical_impossible (profile, eb, bounds, q, coeff, width,
   margins, center, same, marker, Apositive, Dcap) *)
let C1092ISTE_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092ISTD_SQ C1092ISTD_SUCCESSOR_BOUNDS) THEN
  MP_TAC(SPECL C1092ISTD_SQ C1092ISTD_SUCCESSOR_LOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  REPEAT GEN_TAC THEN REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092istd_input] o
    check (can (term_match [] `c1092istd_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifbd_input] o
    check (can (term_match [] `c1092ifbd_input a b c d e f g h i j`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (can (term_match [] `c1092ifsu_negsucc a b c d e`) o concl)) THEN
  C1092PRS_NORMAL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092ISTE_USE C1092ISTBO_BOTTOM_PROFILE C1092ISTE_CB THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092istbo_profile] o
    check (can (term_match [] `c1092istbo_profile a b c d e f g h i j`) o concl)) THEN
  SUBGOAL_THEN `c1092isbs_range cE (--sE) cB sB` ASSUME_TAC THENL
   [REWRITE_TAC[c1092isbs_range] THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; C1092ISTE_LIN;
           UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  C1092ISTE_USE C1092ISBS_BOUNDARY_COEFFICIENTS C1092ISTE_DTHK THEN
  SUBGOAL_THEN `&1 < --sE + (&343 / &500) * cE` ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC] THEN
  C1092ISTE_USE C1092ISBS_BOUNDARY_MARGINS C1092ISTE_DTHK THEN
  C1092ISTE_USE C1092IFBD_CENTRAL_FACES C1092ISTE_CB THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifbd_faces] o
    check (can (term_match [] `c1092ifbd_faces a b c d e`) o concl)) THEN
  C1092ISTE_PT_TAC `linside cB sB uB vB aC (&0) (--(&543 / &500))` THEN
  SUBGOAL_THEN `--(&543 / &500) * sB < uB + aC` ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < uC + aC` ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC] THEN
  C1092ISTE_PROD `&0 < (cC * sB - sC * cB) * (uC + aC)` THEN
  C1092ISTE_PROD `&0 <= (cC * cB + sC * sB) * (--aC - vC)` THEN
  SUBGOAL_THEN `vB + aC < --(cC * cB + sC * sB) * aC` ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC];;

(* Lean: first_source (local have of canonical_impossible) *)
let C1092ISTE_FIRST_SOURCE = prove
 (c1092iste_stmt "~(uB + aB <= ABT_lower cE sE uE vE aE cB sB)",
  C1092ISTE_OPEN_TAC THEN
  MP_TAC(SPECL (C1092ISTE_E @ [`cB:real`; `sB:real`; C1092ISTE_N; C1092ISTE_ETA]) C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[c1092isbs_nu; c1092isbs_eta] THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092isbs_nu; c1092isbs_eta]) THEN C1092ISTE_LIN;
    DISCH_TAC] THEN
  C1092ISTE_PROD (mk_binop `(<=):real->real->bool` `&0` C1092ISTE_N) THEN
  C1092ISTE_PROD (mk_binop `(<=):real->real->bool` `&0` C1092ISTE_ETA) THEN
  SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`; C1092ISTE_ETA, `e:real`]
    `n * (uE + aC) <= n * (cE - sE) /\ e * (vE + aC) <= e * (--sE - &2 / &5 * cE) /\
     &0 < (aC - &1) * (n + e) /\
     n * (cE + --sE - &1) + e * (--sE - (&2 / &5) * cE - &1) =
     cB * c1092isbs_X0 cE (--sE) + sB * c1092isbs_Y0 cE (--sE)`) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C1092ISTE_LIN;
      REWRITE_TAC[c1092isbs_nu; c1092isbs_eta; c1092isbs_X0; c1092isbs_Y0] THEN
      UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  C1092ISTE_USE C1092ISBS_FIRST_SOURCE_MARGIN C1092ISTE_DTHK THEN
  C1092ISTE_LIN);;

(* Lean: longitudinal (local have of canonical_impossible) *)
let C1092ISTE_LONGITUDINAL = prove
 (c1092iste_stmt "~(ABT_upper cB sB uB vB aB cE sE <= uE)",
  C1092ISTE_OPEN_TAC THEN
  MP_TAC(SPECL (C1092ISTE_B @ [`cE:real`; `sE:real`; C1092ISTE_N; mk_comb(`(--):real->real`, C1092ISTE_ETA)])
    C1092TFSU_UPPER_POS_NEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092isbs_nu; c1092isbs_eta] THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092isbs_nu; c1092isbs_eta]) THEN C1092ISTE_LIN;
    DISCH_TAC] THEN
  SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`; C1092ISTE_ETA, `e:real`]
    `n * (--(&543 / &500) * sB) < n * (uB + aC) /\
     (--e) * (--aC * (&1 + (cC * cB + sC * sB))) < (--e) * vB /\
     &0 < (aC - &1) * (e * (&1 + (cC * cB + sC * sB))) /\
     &0 <= n * (&21 / &1000 - sB) /\
     &0 < (e - &7 / &25) * (&1 + (cC * cB + sC * sB))`) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[REAL_ARITH `--e * x < --e * y <=> e * y < e * x`] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THEN C1092ISTE_LIN;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [C1092ISTE_LIN; MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C1092ISTE_LIN];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C1092ISTE_LIN;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C1092ISTE_LIN];
    ALL_TAC] THEN
  SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`] `n * sB <= &21 / &1000`) ASSUME_TAC THENL
   [C1092ISTE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 < ABT_upper cB sB uB vB aC cE sE` ASSUME_TAC THENL
   [C1092ISTE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `uE < &1 / &2` ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC] THEN
  C1092ISTE_LIN);;

(* Lean: transverse (local have of canonical_impossible) *)
let C1092ISTE_TRANSVERSE = prove
 (c1092iste_stmt "~(ABT_upper cB sB uB vB aB (--sE) cE <= vE)",
  C1092ISTE_OPEN_TAC THEN
  MP_TAC(SPECL (C1092ISTE_B @ [`--sE`; `cE:real`; C1092ISTE_ETA; C1092ISTE_N]) C1092TFSU_UPPER_POS_POS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[c1092isbs_nu; c1092isbs_eta] THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092isbs_nu; c1092isbs_eta]) THEN C1092ISTE_LIN;
    DISCH_TAC] THEN
  SUBGOAL_THEN (subst [C1092ISTE_ETA, `e:real`] `e * (--(&543 / &500) * sB) < e * (uB + aC)`)
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THEN C1092ISTE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `vE < --sE - (&2 / &5) * cE - &1` ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sB` THENL
   [SUBGOAL_THEN `c977cc_normal cB sB` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `abs sB <= cB` THEN ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`];
        UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    C1092ISTE_USE C1092IFBD_POSITIVE_WALL C1092ISTE_CB THEN
    C1092ISTE_PROD `&0 <= (&1 - cB) * (&3 - cB)` THEN
    C1092ISTE_PROD `&0 <= cB * (cB + sB)` THEN
    C1092ISTE_PROD `&0 < (aC - &1) * (&1 + cB * (cB + sB))` THEN
    C1092ISTE_PROD `&0 <= sB * (cB / &2 - &49 / &100)` THEN
    SUBGOAL_THEN `--(&1) + (&49 / &100) * sB < vB + aC` ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC] THEN
    SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`] `n * (--(&1) + (&49 / &100) * sB) < n * (vB + aC)`)
      ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    C1092ISTE_USE C1092ISBS_POSITIVE_TRANSVERSE_COEFFICIENT C1092ISTE_DTHK THEN
    C1092ISTE_PROD `&0 <= sB * c1092isbs_Z0 cE (--sE) cB sB` THEN
    C1092ISTE_PROD `&0 <= cE * (&1 - cB)` THEN
    SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`; C1092ISTE_ETA, `e:real`]
      `--(&543 / &500) * e * sB + n * (--(&1) + (&49 / &100) * sB) - (--sE - (&2 / &5) * cE - &1) =
       c1092isbs_Delta0 cE (--sE) + cE * (&1 - cB) + sB * c1092isbs_Z0 cE (--sE) cB sB`)
      ASSUME_TAC THENL
     [REWRITE_TAC[c1092isbs_nu; c1092isbs_eta; c1092isbs_Delta0; c1092isbs_Z0] THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092ISTE_LIN;
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE] o check (fun th -> concl th = `~(&0 <= sB)`)) THEN
    SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THENL
       [C1092ISTE_LIN;
        UNDISCH_TAC `abs sB <= cB` THEN ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> abs x = --x`];
        UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    C1092ISTE_USE C1092IFBD_NEGATIVE_WALL_HEIGHT C1092ISTE_CB THEN
    SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`] `n * --(&1) < n * (vB + aC)`)
      ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    C1092ISTE_USE C1092ISBS_NEGATIVE_TRANSVERSE_MARGIN C1092ISTE_DTHK THEN
    SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`; C1092ISTE_ETA, `e:real`]
      `--(&543 / &500) * e * sB - n - (--sE - (&2 / &5) * cE - &1) =
       c1092isbs_Delta0 cE (--sE) + cE * (&1 - cB) - (&543 / &500) * cE * sB pow 2 +
       (--sB) * (--sE) * ((&543 / &500) * cB - &1)`)
      ASSUME_TAC THENL
     [REWRITE_TAC[c1092isbs_nu; c1092isbs_eta; c1092isbs_Delta0] THEN
      CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092ISTE_LIN]);;

(* Lean: bottom_transverse (local have of canonical_impossible) *)
let C1092ISTE_BOTTOM_TRANSVERSE = prove
 (c1092iste_stmt "sB < &0 ==> ~(vB + aB <= ABT_lower cE sE uE vE aE (--sB) cB)",
  C1092ISTE_OPEN_TAC THEN
  MP_TAC(SPECL (C1092ISTE_E @ [`--sB`; `cB:real`; mk_comb(`(--):real->real`, C1092ISTE_ETA); C1092ISTE_N]) C1092WS_LOWER_NP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[c1092isbs_nu; c1092isbs_eta] THEN
    REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092isbs_nu; c1092isbs_eta]) THEN C1092ISTE_LIN;
    DISCH_TAC] THEN
  SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`; C1092ISTE_ETA, `e:real`]
    `--e * uE <= --e * (--(&13 / &50) * sE) /\
     n * (vE + aC) <= n * (--sE - &2 / &5 * cE) /\
     &0 < (aC - &1) * (n + e) /\ &0 <= e * --sE`) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `--e * x <= --e * y <=> e * y <= e * x`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN C1092ISTE_LIN;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN C1092ISTE_LIN;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C1092ISTE_LIN;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C1092ISTE_LIN];
    ALL_TAC] THEN
  C1092ISTE_USE C1092ISBS_NEGATIVE_RELATIVE_COSINE C1092ISTE_DTHK THEN
  SUBGOAL_THEN `&15 / &17 < &1 - --sE + (&2 / &5) * cE` ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC] THEN
  C1092ISTE_PROD (subst [C1092ISTE_N, `n:real`]
    `&0 < (n - &15 / &17) * (&1 - --sE + (&2 / &5) * cE)`) THEN
  SUBGOAL_THEN (subst [C1092ISTE_N, `n:real`; C1092ISTE_ETA, `e:real`]
    `&1 < e + n * (&1 - --sE + (&2 / &5) * cE)`) ASSUME_TAC THENL [C1092ISTE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THENL
     [C1092ISTE_LIN;
      UNDISCH_TAC `abs sB <= cB` THEN ASM_SIMP_TAC[REAL_ARITH `x < &0 ==> abs x = --x`];
      UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  C1092ISTE_USE C1092IFBD_NEGATIVE_WALL_HEIGHT C1092ISTE_CB THEN
  C1092ISTE_LIN);;

(* Lean: cone (local have of canonical_impossible) *)
let C1092ISTE_CONE = prove
 (c1092iste_stmt "!nx ny. nx pow 2 + ny pow 2 = &1 /\\
     ABT_upper cB sB uB vB aB nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx /\\ &0 < (&7 / &20) * nx + (&92 / &125) * ny",
  C1092ISTE_OPEN_TAC THEN
  MP_TAC(SPECL (C1092ISTE_B @ [`--(&13 / &50)`; `--(&1)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092ISTE_E @ [`&13 / &50`; `--(&1)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092ISTE_B @ [`&0`; `--(&543 / &500)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092ISTE_E @ [`&7 / &20`; `--(&7 / &20)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  UNDISCH_TAC `ABT_upper cB sB uB vB aC nx ny <= ABT_lower cE sE uE vE aC nx ny` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: canonical_impossible *)
let C1092ISTE_CANONICAL_IMPOSSIBLE = prove
 (c1092iste_stmt "F",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL C1092ISTD_SQ th))
   [C1092ISTE_FIRST_SOURCE; C1092ISTE_LONGITUDINAL; C1092ISTE_TRANSVERSE;
    C1092ISTE_BOTTOM_TRANSVERSE; C1092ISTE_CONE; C1092ISTD_SUCCESSOR_BOUNDS;
    C1092ISTD_SUCCESSOR_LOW] THEN
  ASM_REWRITE_TAC[] THEN REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092istd_input] o
    check (can (term_match [] `c1092istd_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifbd_input] o
    check (can (term_match [] `c1092ifbd_input a b c d e f g h i j`) o concl)) THEN
  C1092ISTE_USE C1092ISTBO_BOTTOM_PROFILE
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092istbo_profile] o
    check (can (term_match [] `c1092istbo_profile a b c d e f g h i j`) o concl)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092SPTS_SIGNED_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  let cone_tac (asl, w as g) =
    let sep = concl(snd(find (fun (_, th) ->
      try let l, _ = dest_binary "real_le" (concl th) in
          fst(dest_const(fst(strip_comb l))) = "ABT_upper" with _ -> false) asl)) in
    let args = snd(strip_comb(lhand sep)) in
    let nx = el 5 args and ny = el 6 args in
    let cone = snd(find (fun (_, th) -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "ABT_upper" with _ -> false)) (concl th)) asl) in
    (MP_TAC(SPECL [nx; ny] cone) THEN ANTS_TAC THENL
      [CONJ_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
       STRIP_TAC]) g in
  REPEAT STRIP_TAC THENL
   [(* bu *) RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_upper cB sB uB vB aB cB sB = uB + aB`]) THEN
    ASM_MESON_TAC[];
    (* bu' *) cone_tac THEN RASM_ARITH_TAC;
    (* bv *) cone_tac THEN
    SUBGOAL_THEN `sB < &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_upper cB sB uB vB aB (--sB) cB = vB + aB`]) THEN
    ASM_MESON_TAC[];
    (* bv' *) cone_tac THEN RASM_ARITH_TAC;
    (* eu *) RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_lower cE sE uE vE aE cE sE = uE`]) THEN
    ASM_MESON_TAC[];
    (* eu' *) cone_tac THEN RASM_ARITH_TAC;
    (* ev *) RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_lower cE sE uE vE aE (--sE) cE = vE`]) THEN
    ASM_MESON_TAC[];
    (* ev' *) cone_tac THEN RASM_ARITH_TAC]);;

(* reindexing a square: the input is unchanged when B is replaced by a square Q
   with the same points, side and centre abscissa *)
let C1092ISTE_REFRAME = prove
 (`forall cC sC uC vC aC cB sB uB vB aB cQ sQ uQ vQ aQ cE sE uE vE aE.
     (forall x y. linside cQ sQ uQ vQ aQ x y <=> linside cB sB uB vB aB x y) /\ aQ = aB /\
     lcx cQ sQ uQ vQ aQ = lcx cB sB uB vB aB /\
     c1092istd_input cC sC uC vC aC cB sB uB vB aB cE sE uE vE aE
     ==> c1092istd_input cC sC uC vC aC cQ sQ uQ vQ aQ cE sE uE vE aE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c1092istd_input; c1092ifbd_input; ldisj] THEN
  UNDISCH_TAC `c1092istd_input cC sC uC vC aC cB sB uB vB aB cE sE uE vE aE` THEN
  REWRITE_TAC[c1092istd_input; c1092ifbd_input; ldisj]);;

(* Lean: impossible *)
let C1092ISTE_IMPOSSIBLE = prove
 (c1092istd_stmt "F",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = aB`)) THEN
  ASM_CASES_TAC `sD <= cD` THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aB:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092ISTE_CANONICAL_IMPOSSIBLE) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    MATCH_MP_TAC C1092ISTE_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `sD:real`; `--cD`; `--vD - aB`; `uD:real`; `aB:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092ISTE_CANONICAL_IMPOSSIBLE) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `cD * cD + sD * sD = &1` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC C1092ISTE_REFRAME THEN
      MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN FIRST_X_ASSUM(fun th ->
          if is_forall (concl th) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
        REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_comb (lhs (concl th)) &&
            fst(strip_comb(lhs(concl th))) = `lcx` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
        REWRITE_TAC[lcx] THEN REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs(--x) = x`] THEN
      UNDISCH_TAC `~(sD <= cD)` THEN REAL_ARITH_TAC]]);;
