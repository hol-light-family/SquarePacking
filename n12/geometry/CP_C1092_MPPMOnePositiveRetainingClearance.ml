(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOnePositiveRetainingClearance.lean   *)
(* (N12Compact.C1092MPPMOnePositive).  ONE-POSITIVE-CONTINUOUS-ENDING Lemma *)
(* 3.2.  Squares C = c s u v a (retaining), D = cD sD uD vD aD and the bar   *)
(* owner B = cB sB uB vB aB, OpenSquare invariants explicit.  Core / faces / *)
(* above_bar: c1092anc_core / C1092ANC_FACES / C1092ANC_ABOVE_BAR;           *)
(* RetainingPairInput c1092opra_input, retaining_successor_bounds            *)
(* C1092OPRA_RETAINING_SUCCESSOR_BOUNDS; MMMPEndingAxes.clockwise D is       *)
(* (cD, sD, --vD - aD, uD, aD); ClearedSuccessor c1092manp_clearedSuccessor; *)
(* WallProfile.vertex OCWPVG_VERTEX.  Tag C1092OPRC_.                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMOnePositiveRetainingAngle.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveProfiles.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let C1092OPRC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;
let C1092OPRC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092OPRC_LP_TAC; ALL_TAC];;
let C1092OPRC_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092OPRC_LP_TAC; ALL_TAC];;

(* Lean: narrow_crosspoint_clearance *)
let C1092OPRC_NARROW_CROSSPOINT_CLEARANCE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092anc_core cC sC uC vC aC /\ &89 / &100 < cC /\ --sC < &9 / &20 /\
     ~linside cC sC uC vC aC (&0) (--(&1 / &2)) /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> uC + aC <= --sC / &2 /\ --(&1) < sC * (uC + aC) + cC * vC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  MAP_EVERY (fun tm -> MP_TAC(REWRITE_RULE[linside] (ASSUME tm)) THEN STRIP_TAC)
    [`linside cC sC uC vC aC (--(&1)) (--(&13 / &50))`;
     `linside cC sC uC vC aC (--(&13 / &50)) (&0)`] THEN
  C1092OPRC_FACT `&0 < cC /\ &0 < --sC` THEN
  SUBGOAL_THEN `uC + aC <= --sC / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside cC sC uC vC aC (&0) (--(&1 / &2))` THEN
    REWRITE_TAC[linside] THEN C1092OPRC_LP_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `--cC + (&14 / &25) * sC <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `linside cB sB uB vB aB (--(&14 / &25)) (--(&1))` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (is_forall o concl)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `linside cC sC uC vC aC (--(&14 / &25)) (--(&1))` ASSUME_TAC THENL
     [REWRITE_TAC[linside] THEN C1092OPRC_LP_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`--(&14 / &25)`; `--(&1)`] o REWRITE_RULE[ldisj] o
      check (fun th -> concl th = `ldisj cC sC uC vC aC cB sB uB vB aB`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `uC + aC`; `vC:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092OPRC_LP_TAC; ALL_TAC] THEN
  ABBREV_TAC `X = cC * (uC + aC) - sC * vC` THEN
  ABBREV_TAC `Y = sC * (uC + aC) + cC * vC` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  C1092OPRC_PROD `&0 <= cC * (uC - --cC)` THEN
  C1092OPRC_PROD `&0 <= --sC * (vC - (--cC + (&14 / &25) * sC))` THEN
  C1092OPRC_PROD `&0 < cC * (aC - &1)` THEN
  C1092OPRC_PROD `&0 <= --sC * (&1 - cC)` THEN
  C1092OPRC_PROD `&0 < (cC - &89 / &100) * (&9 / &20 - --sC)` THEN
  SUBGOAL_THEN `--(&14 / &25) < X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN NLIN_TAC [SQ_NONNEG `sC:real`]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cC * X + sC * Y = uC + aC` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
    UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092OPRC_PROD `&0 <= --sC * (--(&1) - Y)` THEN
  C1092OPRC_FACT `cC * X <= &0` THEN
  SUBGOAL_THEN `X <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092OPRC_PROD `&0 < cC * X` THEN C1092OPRC_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `X:real`; `Y:real`]
    C1092ANC_ABOVE_BAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092OPRC_LP_TAC; DISCH_TAC THEN C1092OPRC_LP_TAC]);;

(* Lean: retaining_successor_cleared *)
let C1092OPRC_RETAINING_SUCCESSOR_CLEARED = prove
 (`forall c s u v a cD sD uD vD aD cB sB uB vB aB.
     c * c + s * s = &1 /\ &0 < a /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092opra_input c s u v a cD sD (--vD - aD) uD aD /\
     c1092anc_core cD sD uD vD aD /\ ~linside cD sD uD vD aD (&0) (--(&1 / &2)) /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cD sD uD vD aD cB sB uB vB aB
     ==> c1092manp_clearedSuccessor cD sD (--vD - aD) uD aD`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cD:real`; `sD:real`; `--vD - aD`; `uD:real`; `aD:real`]
    C1092OPRA_RETAINING_SUCCESSOR_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C1092OPRC_NARROW_CROSSPOINT_CLEARANCE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cD (--sD)`)) THEN
  SUBGOAL_THEN `cD < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092OPRC_PROD `&0 < --sD * --sD` THEN
    C1092OPRC_PROD `&0 <= (cD - &1) * (cD + &1)` THEN C1092OPRC_LP_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092manp_clearedSuccessor] THEN ASM_REWRITE_TAC[] THEN C1092OPRC_LP_TAC);;
