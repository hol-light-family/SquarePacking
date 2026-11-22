(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointGeometry.lean*)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointGeometry; Lean header:      *)
(* "Source only, uncompiled").  Same-center elimination for the missing-     *)
(* negative successor.  Squares C, E, B (and the frame Q) are (cC, ..),      *)
(* (cE, ..), (cB, ..), (cQ, ..) with unit normals and positive sides as      *)
(* explicit hypotheses.  Input c1092mncd_input (C1092MNCD_OPEN_TAC); the     *)
(* sources, dots and caps C1092MNCD_*; recipient_faces C1092MNCF_*; Quarter, *)
(* kC, deltaC, kE, deltaE, ell, width, C0, FC: c1092mncs_*; E0, FE, G00..G11,*)
(* G00star..G11star: c1092mmncs_*; floor_upper C1092SPTG_FLOOR_UPPER;        *)
(* exists_positive_frame WCB_EXISTS_POSITIVE_FRAME.  H00..H11, NegativeMode, *)
(* ModesNonnegative: c1092mncge_*.  Same structure as the port of            *)
(* MPPMNegativeCrosspointGeometry (CP_C1092_MPPMNegativeCrosspointGeometry). *)
(* Tag C1092MNCGE_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointData.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

let C1092MNCGE_LIN = C1092NCGD_LIN;;
let C1092MNCGE_PROD = C1092NCGD_PROD;;

let C1092MNCGE_V =
  [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
   `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
   `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* the same at the opened input (sides aC) *)
let C1092MNCGE_VC = C1092MNCD_V15;;

let c1092mncge_stmt = c1092mncd_stmt;;

(* open the input (sides identified with aC), the quarter and the dots *)
let C1092MNCGE_DATA_TAC =
  C1092MNCD_OPEN_TAC THEN C1092MNCD_QUARTER_TAC THEN
  MP_TAC(SPECL C1092MNCGE_VC C1092MNCD_CENTRAL_DOT) THEN
  MP_TAC(SPECL C1092MNCGE_VC C1092MNCD_RECIPIENT_DOT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC;;

(* Lean: boundary_supports (private) *)
let C1092MNCGE_BOUNDARY_SUPPORTS = prove
 (c1092mncge_stmt "" " /\\ c1092mncs_quarter cB sB"
   "(--sC) * lcx cB sB uB vB aB - &2 * cC +
         (aC / &2) * (cC * (cB + sB) + c1092mncs_kC cC sC cB sB +
                      abs(c1092mncs_deltaC cC sC cB sB))
         <= ABT_upper cB sB uB vB aB (--sC) cC /\\
         (--sE) * lcx cB sB uB vB aB - &2 * cE +
         (aC / &2) * (cE * (cB + sB) + c1092mncs_kE cE (--sE) cB sB +
                      abs(c1092mncs_deltaE cE (--sE) cB sB))
         <= ABT_upper cB sB uB vB aB (--sE) cE /\\
         (--sB) * lcx cB sB uB vB aB - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)
         <= ABT_upper cB sB uB vB aB (--sB) cB /\\
         cB * lcx cB sB uB vB aB - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)
         <= ABT_upper cB sB uB vB aB cB sB",
  C1092MNCGE_DATA_TAC THEN
  let fl nx ny =
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; nx; ny]
      C1092SPTG_FLOOR_UPPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[c1092mcs_quarter] THEN C1092MNCGE_LIN; DISCH_TAC] in
  fl `--sC` `cC:real` THEN fl `--sE` `cE:real` THEN fl `--sB` `cB:real` THEN
  fl `cB:real` `sB:real` THEN
  SUBGOAL_THEN
   `abs(--sC * cB + cC * sB) = abs(c1092mncs_deltaC cC sC cB sB) /\
    abs(-- --sC * sB + cC * cB) = c1092mncs_kC cC sC cB sB /\
    abs(--sE * cB + cE * sB) = c1092mncs_kE cE (--sE) cB sB /\
    abs(-- --sE * sB + cE * cB) = abs(c1092mncs_deltaE cE (--sE) cB sB) /\
    abs(--sB * cB + cB * sB) = &0 /\ abs(-- --sB * sB + cB * cB) = &1 /\
    abs(cB * cB + sB * sB) = &1 /\ abs(--cB * sB + sB * cB) = &0`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[c1092mncs_deltaC; c1092mncs_kC; c1092mncs_deltaE; c1092mncs_kE] THEN
    REPEAT CONJ_TAC THEN
    FIRST [AP_TERM_TAC THEN REAL_ARITH_TAC;
           MATCH_MP_TAC(REAL_ARITH `x = --y ==> abs x = abs y`) THEN REAL_ARITH_TAC;
           MATCH_MP_TAC(REAL_ARITH `x = y /\ &0 <= y ==> abs x = y`) THEN CONJ_TAC THENL
            [REAL_ARITH_TAC;
             RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_kC; c1092mncs_kE]) THEN
             FIRST_ASSUM ACCEPT_TAC];
           REWRITE_TAC[REAL_ARITH `--x * y + y * x = &0`; REAL_ABS_0] THEN NO_TAC;
           MATCH_MP_TAC(REAL_ARITH `x = &1 ==> abs x = &1`) THEN
           UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th ->
    if can (find_term ((=) `ABT_upper`)) (concl th) then MP_TAC th else ALL_TAC)) THEN
  REAL_ARITH_TAC);;

(* Lean: H00, H01, H10, H11 (definitions) *)
let c1092mncge_H00 = new_definition
 `c1092mncge_H00 (c:real) s d t h r = c1092mncs_width c s d t h r / &2 + t + s`;;
let c1092mncge_H01 = new_definition
 `c1092mncge_H01 (c:real) s d t h r =
    (c1092mncs_kC c s h r * (h + r) + h * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r)) +
     s) / &2 + h + s * (c1092mncs_kE d t h r + abs(c1092mncs_deltaE d t h r))`;;
let c1092mncge_H10 = new_definition
 `c1092mncge_H10 (c:real) s d t h r =
    (c1092mncs_kE d t h r * (h + r) + t + r * (c1092mncs_kE d t h r + abs(c1092mncs_deltaE d t h r))) /
    &2 + t * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r)) + r`;;
let c1092mncge_H11 = new_definition
 `c1092mncge_H11 (c:real) s d t h r =
    h + r + h * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r)) +
    r * (c1092mncs_kE d t h r + abs(c1092mncs_deltaE d t h r))`;;

(* generalize the absolute values and the case-split scalars FC, FE *)
let C1092MNCGE_ABS_TAC =
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN
  MP_TAC(SPEC `c1092mncs_deltaC cC sC cB sB` REAL_ABS_POS) THEN
  MP_TAC(SPEC `c1092mncs_deltaE cE (--sE) cB sB` REAL_ABS_POS) THEN
  SPEC_TAC(`abs(c1092mncs_deltaC cC sC cB sB)`, `AC:real`) THEN
  SPEC_TAC(`abs(c1092mncs_deltaE cE (--sE) cB sB)`, `AE:real`) THEN
  SPEC_TAC(`c1092mncs_FC cC sC cB sB`, `FC:real`) THEN
  SPEC_TAC(`c1092mmncs_FE cE (--sE) cB sB`, `FE:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC;;

(* Lean: side_coefficients (private) *)
let C1092MNCGE_SIDE_COEFFICIENTS = prove
 (c1092mncge_stmt "" " /\\ c1092mncs_quarter cB sB"
   "&0 < c1092mncge_H00 cC sC cE (--sE) cB sB /\\ &0 < c1092mncge_H01 cC sC cE (--sE) cB sB /\\
    &0 < c1092mncge_H10 cC sC cE (--sE) cB sB /\\ &0 < c1092mncge_H11 cC sC cE (--sE) cB sB",
  C1092MNCGE_DATA_TAC THEN
  SUBGOAL_THEN `&0 < cB + sB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `cB = &0 /\ sB = &0` STRIP_ASSUME_TAC THENL [C1092MNCGE_LIN; ALL_TAC] THEN
    UNDISCH_TAC `cB * cB + sB * sB = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092mncge_H00; c1092mncge_H01; c1092mncge_H10; c1092mncge_H11; c1092mncs_width;
              c1092mncs_ell] THEN
  C1092MNCGE_ABS_TAC THEN
  C1092MNCGE_PROD `&0 < cC * --sE` THEN C1092MNCGE_PROD `&0 < sC * cE` THEN
  C1092MNCGE_PROD `&0 <= (cC * --sE + sC * cE) * (cB + sB)` THEN
  C1092MNCGE_PROD `&0 <= --sE * (c1092mncs_kC cC sC cB sB + AC)` THEN
  C1092MNCGE_PROD `&0 <= sC * (c1092mncs_kE cE (--sE) cB sB + AE)` THEN
  C1092MNCGE_PROD `&0 <= c1092mncs_kC cC sC cB sB * (cB + sB)` THEN
  C1092MNCGE_PROD `&0 <= cB * (c1092mncs_kC cC sC cB sB + AC)` THEN
  C1092MNCGE_PROD `&0 <= c1092mncs_kE cE (--sE) cB sB * (cB + sB)` THEN
  C1092MNCGE_PROD `&0 <= sB * (c1092mncs_kE cE (--sE) cB sB + AE)` THEN
  C1092MNCGE_LIN);;

(* Lean: caps (private) *)
let C1092MNCGE_CAPS = prove
 (c1092mncge_stmt "" ""
   "vC <= c1092mncs_C0 sC + (&43 / &500) * sC - (aC - &1) /\\
    vE <= c1092mmncs_E0 cE (--sE) - (aC - &1)",
  C1092MNCD_OPEN_TAC THEN
  REWRITE_TAC[c1092mncs_C0; c1092mmncs_E0] THEN C1092MNCGE_LIN);;

(* common opening of the four modes: data, supports, caps, side coefficients *)
let C1092MNCGE_MODE_TAC =
  C1092MNCD_OPEN_TAC THEN
  MP_TAC(SPECL C1092MNCGE_VC C1092MNCGE_BOUNDARY_SUPPORTS) THEN
  MP_TAC(SPECL C1092MNCGE_VC C1092MNCGE_SIDE_COEFFICIENTS) THEN
  MP_TAC(SPECL C1092MNCGE_VC C1092MNCGE_CAPS) THEN
  MP_TAC(SPECL C1092MNCGE_VC C1092MNCD_CENTRAL_CAP) THEN
  MP_TAC(SPECL C1092MNCGE_VC C1092MNCD_RECIPIENT_CAP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092MNCD_QUARTER_TAC;;

let c1092mncge_mode_stmt hyps concl =
  c1092mncge_stmt "" (" /\\ c1092mncs_quarter cB sB /\\ " ^ hyps) concl;;

(* Lean: mode00 *)
let C1092MNCGE_MODE00 = prove
 (c1092mncge_mode_stmt
   "ABT_upper cB sB uB vB aB (--sC) cC <= vC /\\ ABT_upper cB sB uB vB aB (--sE) cE <= vE"
   "c1092mmncs_G00star (&43 / &500) cC sC cE (--sE) cB sB < &0",
  C1092MNCGE_MODE_TAC THEN
  REWRITE_TAC[c1092mmncs_G00star; c1092mmncs_G00; c1092mncs_width; c1092mncs_ell] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncge_H00; c1092mncs_width; c1092mncs_ell]) THEN
  C1092MNCGE_ABS_TAC THEN
  C1092MNCGE_PROD `&0 <= --sE * ((c1092mncs_C0 sC + (&43 / &500) * sC - (aC - &1)) -
     ((--sC) * lcx cB sB uB vB aC - &2 * cC +
      (aC / &2) * (cC * (cB + sB) + c1092mncs_kC cC sC cB sB + AC)))` THEN
  C1092MNCGE_PROD `&0 <= sC * ((c1092mmncs_E0 cE (--sE) - (aC - &1)) -
     ((--sE) * lcx cB sB uB vB aC - &2 * cE +
      (aC / &2) * (cE * (cB + sB) + c1092mncs_kE cE (--sE) cB sB + AE)))` THEN
  C1092MNCGE_PROD `&0 < (aC - &1) *
     (((cC * --sE + sC * cE) * (cB + sB) + --sE * (c1092mncs_kC cC sC cB sB + AC) +
       sC * (c1092mncs_kE cE (--sE) cB sB + AE)) / &2 + --sE + sC)` THEN
  C1092MNCGE_LIN);;

(* Lean: mode01 *)
let C1092MNCGE_MODE01 = prove
 (c1092mncge_mode_stmt
   "ABT_upper cB sB uB vB aB (--sC) cC <= vC /\\
    ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB"
   "c1092mmncs_G01star (&43 / &500) cC sC cE (--sE) cB sB < &0",
  C1092MNCGE_MODE_TAC THEN
  REWRITE_TAC[c1092mmncs_G01star; c1092mmncs_G01] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncge_H01]) THEN
  C1092MNCGE_ABS_TAC THEN
  C1092MNCGE_PROD `&0 <= cB * ((c1092mncs_C0 sC + (&43 / &500) * sC - (aC - &1)) -
     ((--sC) * lcx cB sB uB vB aC - &2 * cC +
      (aC / &2) * (cC * (cB + sB) + c1092mncs_kC cC sC cB sB + AC)))` THEN
  C1092MNCGE_PROD `&0 <= sC * ((FE - (aC - &1) * (c1092mncs_kE cE (--sE) cB sB + AE)) -
     (cB * lcx cB sB uB vB aC - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)))` THEN
  C1092MNCGE_PROD `&0 < (aC - &1) *
     ((c1092mncs_kC cC sC cB sB * (cB + sB) + cB * (c1092mncs_kC cC sC cB sB + AC) + sC) / &2 +
      cB + sC * (c1092mncs_kE cE (--sE) cB sB + AE))` THEN
  UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN REWRITE_TAC[c1092mncs_kC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_kC]) THEN DISCH_TAC THEN
  C1092MNCGE_LIN);;

(* Lean: mode10 *)
let C1092MNCGE_MODE10 = prove
 (c1092mncge_mode_stmt
   "ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB /\\
    ABT_upper cB sB uB vB aB (--sE) cE <= vE"
   "c1092mmncs_G10star (&43 / &500) cC sC cE (--sE) cB sB < &0",
  C1092MNCGE_MODE_TAC THEN
  REWRITE_TAC[c1092mmncs_G10star; c1092mmncs_G10] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncge_H10]) THEN
  C1092MNCGE_ABS_TAC THEN
  C1092MNCGE_PROD `&0 <= --sE * ((FC + (&43 / &500) * sC * c1092mncs_kC cC sC cB sB -
       (aC - &1) * (c1092mncs_kC cC sC cB sB + AC)) -
     ((--sB) * lcx cB sB uB vB aC - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)))` THEN
  C1092MNCGE_PROD `&0 <= sB * ((c1092mmncs_E0 cE (--sE) - (aC - &1)) -
     ((--sE) * lcx cB sB uB vB aC - &2 * cE +
      (aC / &2) * (cE * (cB + sB) + c1092mncs_kE cE (--sE) cB sB + AE)))` THEN
  C1092MNCGE_PROD `&0 < (aC - &1) *
     ((c1092mncs_kE cE (--sE) cB sB * (cB + sB) + --sE + sB * (c1092mncs_kE cE (--sE) cB sB + AE)) / &2 +
      --sE * (c1092mncs_kC cC sC cB sB + AC) + sB)` THEN
  UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN REWRITE_TAC[c1092mncs_kE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_kE]) THEN DISCH_TAC THEN
  C1092MNCGE_LIN);;

(* Lean: mode11 *)
let C1092MNCGE_MODE11 = prove
 (c1092mncge_mode_stmt
   "ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB /\\
    ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB"
   "c1092mmncs_G11star (&43 / &500) cC sC cE (--sE) cB sB < &0",
  C1092MNCGE_MODE_TAC THEN
  REWRITE_TAC[c1092mmncs_G11star; c1092mmncs_G11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncge_H11]) THEN
  C1092MNCGE_ABS_TAC THEN
  C1092MNCGE_PROD `&0 <= cB * ((FC + (&43 / &500) * sC * c1092mncs_kC cC sC cB sB -
       (aC - &1) * (c1092mncs_kC cC sC cB sB + AC)) -
     ((--sB) * lcx cB sB uB vB aC - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)))` THEN
  C1092MNCGE_PROD `&0 <= sB * ((FE - (aC - &1) * (c1092mncs_kE cE (--sE) cB sB + AE)) -
     (cB * lcx cB sB uB vB aC - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)))` THEN
  C1092MNCGE_PROD `&0 < (aC - &1) *
     (cB + sB + cB * (c1092mncs_kC cC sC cB sB + AC) +
      sB * (c1092mncs_kE cE (--sE) cB sB + AE))` THEN
  SUBGOAL_THEN `(&2 - aC * (cB + sB) / &2) * (cB pow 2 + sB pow 2) = (&2 - aC * (cB + sB) / &2) * &1`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092MNCGE_LIN);;

(* Lean: NegativeMode (definition) *)
let c1092mncge_negativeMode = new_definition
 `c1092mncge_negativeMode (c:real) s d t h r <=>
    c1092mmncs_G00star (&43 / &500) c s d t h r < &0 \/
    c1092mmncs_G01star (&43 / &500) c s d t h r < &0 \/
    c1092mmncs_G10star (&43 / &500) c s d t h r < &0 \/
    c1092mmncs_G11star (&43 / &500) c s d t h r < &0`;;

(* Lean: one_mode_negative_quarter *)
let C1092MNCGE_ONE_MODE_NEGATIVE_QUARTER = prove
 (c1092mncge_stmt "" " /\\ c1092mncs_quarter cB sB"
   "c1092mncge_negativeMode cC sC cE (--sE) cB sB",
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092mncge_negativeMode] THEN
  MP_TAC(SPECL C1092MNCGE_V C1092MNCD_CENTRAL_SOURCES) THEN
  MP_TAC(SPECL C1092MNCGE_V C1092MNCD_RECIPIENT_SOURCES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC)) THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL C1092MNCGE_V th))
    [C1092MNCGE_MODE00; C1092MNCGE_MODE01; C1092MNCGE_MODE10; C1092MNCGE_MODE11] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: one_mode_negative *)
let C1092MNCGE_ONE_MODE_NEGATIVE = prove
 (c1092mncge_stmt "" ""
   "?cQ sQ uQ vQ aQ.
       cQ * cQ + sQ * sQ = &1 /\\ &0 < aQ /\\ aQ = aB /\\
       (!x y. linside cQ sQ uQ vQ aQ x y <=> linside cB sB uB vB aB x y) /\\
       c1092mncs_quarter cQ sQ /\\
       c1092mncge_negativeMode cC sC cE (--sE) cQ sQ",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aQ:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aQ:real = aB`)) THEN
  MAP_EVERY EXISTS_TAC [`cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `c1092mncs_quarter cQ sQ` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092mncs_quarter; c1092mcs_quarter; REAL_POW_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1092MNCGE_ONE_MODE_NEGATIVE_QUARTER THEN
  MAP_EVERY EXISTS_TAC [`uC:real`; `vC:real`; `aC:real`; `uE:real`; `vE:real`; `aE:real`;
                        `uQ:real`; `vQ:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092mncd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB` THEN
  ASM_REWRITE_TAC[c1092mncd_input; c1092mncf_recipientInput; ldisj]);;

(* Lean: ModesNonnegative (definition) *)
let c1092mncge_modesNonnegative = new_definition
 `c1092mncge_modesNonnegative (c:real) s d t <=>
    forall h r. c1092mncs_quarter h r
          ==> &0 <= c1092mmncs_G00star (&43 / &500) c s d t h r /\
              &0 <= c1092mmncs_G01star (&43 / &500) c s d t h r /\
              &0 <= c1092mmncs_G10star (&43 / &500) c s d t h r /\
              &0 <= c1092mmncs_G11star (&43 / &500) c s d t h r`;;

(* Lean: impossible_of_modes *)
let C1092MNCGE_IMPOSSIBLE_OF_MODES = prove
 (c1092mncge_stmt "" " /\\ c1092mncge_modesNonnegative cC sC cE (--sE)" "F",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MNCGE_ONE_MODE_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `c1092mncge_modesNonnegative cC sC cE (--sE)` THEN
  REWRITE_TAC[c1092mncge_modesNonnegative] THEN
  DISCH_THEN(MP_TAC o SPECL [`cQ:real`; `sQ:real`]) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092mncge_negativeMode cC sC cE (--sE) cQ sQ` THEN
  REWRITE_TAC[c1092mncge_negativeMode] THEN REAL_ARITH_TAC);;
