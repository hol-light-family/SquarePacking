(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositiveShallow.lean           *)
(* (N12Compact.C1092MPPMAllNonpositive), ALL-NEGATIVE-MIXED-FORWARD-ENDING  *)
(* section 5.3.  Squares C = cC sC uC vC aC, W = cW sW uW vW aW and the bar *)
(* owner B = cB sB uB vB aB with their OpenSquare invariants as hypotheses. *)
(* Core / faces / above_bar: c1092anc_core / C1092ANC_FACES /                *)
(* C1092ANC_ABOVE_BAR; MissingPredecessor c1092manp_missingPredecessor;      *)
(* predecessor_cap C1092MANPR_PREDECESSOR_CAP; preliminary_angle /           *)
(* heightGap(_positive) C1092ANAS_*; normal_bounds C977CC_NORMAL_BOUNDS;     *)
(* WallProfile.vertex OCWPVG_VERTEX.  With c = cC, s = --sC.  Tag C1092ANSH_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositivePredecessor.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let C1092ANSH_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;
let C1092ANSH_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092ANSH_LP_TAC; ALL_TAC];;
let C1092ANSH_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092ANSH_LP_TAC; ALL_TAC];;

(* Lean: Shallow (structure) *)
let c1092ansh_shallow = new_definition
 `c1092ansh_shallow (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    &4 * --s < c /\ &97 / &100 < c /\ --s < &1 / &4 /\ v + a < &43 / &500`;;

(* Lean: predecessor_shallow *)
let C1092ANSH_PREDECESSOR_SHALLOW = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092anc_core cC sC uC vC aC /\ c1092manp_missingPredecessor cW sW uW vW aW /\ aC = aW /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     ldisj cC sC uC vC aC cW sW uW vW aW /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> c1092ansh_shallow cC sC uC vC aC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] C1092MANPR_PREDECESSOR_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (--(&13 / &50)) (&0)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  MAP_EVERY (fun tm -> MP_TAC(REWRITE_RULE[linside] (ASSUME tm)) THEN STRIP_TAC)
    [`linside cC sC uC vC aC (--(&1)) (--(&13 / &50))`;
     `linside cC sC uC vC aC (--(&13 / &50)) (&0)`] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `vC + aC`] C1092ANAS_PRELIMINARY_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092ANSH_LP_TAC; STRIP_TAC] THEN
  C1092ANSH_FACT `&0 < cC /\ &0 < --sC` THEN
  SUBGOAL_THEN `&4 * --sC < cC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092ANSH_FACT `vC + aC < &0` THEN
    (* upperU *)
    SUBGOAL_THEN `uC + aC <= --sC` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `linside cB sB uB vB aB (&0) (--(&1))` ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `linside cC sC uC vC aC (&0) (--(&1))` ASSUME_TAC THENL
       [REWRITE_TAC[linside] THEN C1092ANSH_LP_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `--(&1)`] o REWRITE_RULE[ldisj] o
        check (fun th -> concl th = `ldisj cC sC uC vC aC cB sB uB vB aB`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    (* the lowest closure vertex X, Y *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `uC + aC`; `vC:real`]
      OCWPVG_VERTEX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092ANSH_LP_TAC; ALL_TAC] THEN
    ABBREV_TAC `X = cC * (uC + aC) - sC * vC` THEN
    ABBREV_TAC `Y = sC * (uC + aC) + cC * vC` THEN DISCH_TAC THEN
    C1092ANSH_PROD `&0 <= cC * (uC - --cC)` THEN
    C1092ANSH_PROD `&0 <= --sC * (vC - (sC - cC))` THEN
    C1092ANSH_PROD `&0 < cC * (aC - &1)` THEN
    C1092ANSH_PROD `&0 <= --sC * (&1 - cC)` THEN
    SUBGOAL_THEN `--(&14 / &25) < X` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    SUBGOAL_THEN `--(&1) < Y` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `cC * X - --sC * Y = uC + aC` ASSUME_TAC THENL
       [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
        UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      C1092ANSH_PROD `&0 <= --sC * (--(&1) - Y)` THEN
      C1092ANSH_FACT `cC * X <= &0` THEN
      SUBGOAL_THEN `X <= &0` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        C1092ANSH_PROD `&0 < cC * X` THEN C1092ANSH_LP_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                    `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `X:real`; `Y:real`]
        C1092ANC_ABOVE_BAR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092ANSH_LP_TAC; DISCH_TAC THEN C1092ANSH_LP_TAC];
      ALL_TAC] THEN
    C1092ANSH_PROD `&0 <= --sC * ((uC + aC) - (aC - cC))` THEN
    C1092ANSH_PROD `&0 < (aC - &1) * (cC + --sC)` THEN
    C1092ANSH_PROD `&0 < cC * (((&43 / &500) * cC + (&12 / &25) * sC) - (vC + aC))` THEN
    MP_TAC(SPECL [`cC:real`; `--sC`] C1092ANAS_HEIGHTGAP_POSITIVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[c1092anas_heightGap; REAL_POW_2] THEN DISCH_TAC THEN
    UNDISCH_TAC `--(&1) < Y` THEN EXPAND_TAC "Y" THEN DISCH_TAC THEN
    C1092ANSH_LP_TAC;
    ALL_TAC] THEN
  C1092ANSH_PROD `&0 < (cC - &4 * --sC) * (cC + &4 * --sC)` THEN
  SUBGOAL_THEN `&97 / &100 < cC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092ANSH_PROD `&0 <= (&97 / &100 - cC) * (&97 / &100 + cC)` THEN
    C1092ANSH_LP_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092ansh_shallow] THEN ASM_REWRITE_TAC[] THEN C1092ANSH_LP_TAC);;
