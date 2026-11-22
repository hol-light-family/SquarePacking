(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointGeometry.lean       *)
(* (namespace N12Compact.C1092MPPMNegativeCrosspointGeometry).  Same-center  *)
(* elimination in STEEP-POSITIVE-NEGATIVE-CROSSPOINT-TRANSFER section 4.     *)
(* Squares C, E, B (and the frame Q) are (cC, ..), (cE, ..), (cB, ..),       *)
(* (cQ, ..) with unit normals and positive sides as explicit hypotheses.     *)
(* Input: c1092ncgd_input (C1092NCGD_OPEN_TAC); Quarter, kC, deltaC, kE,     *)
(* deltaE, ell, width, C0, E0, FC, FE, G00..G11: c1092mncs_*; central /      *)
(* recipient sources, dots and caps, boundary_recipient_high: C1092NCGD_*;   *)
(* floor_upper: C1092SPTG_FLOOR_UPPER; SteepPositiveNegativeProfile.profile: *)
(* C1092SPNP_PROFILE (c1092spnp_faces); exists_positive_frame:               *)
(* WCB_EXISTS_POSITIVE_FRAME.  H00..H11, NegativeMode, ModesNonnegative:     *)
(* c1092ncg_*.  Tag C1092NCG_.                                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointGeometryData.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

let C1092NCG_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;
let C1092NCG_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092NCG_LIN; ALL_TAC];;

let C1092NCG_V =
  [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
   `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
   `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* the Data facts used below, at the opened input (sides aC) *)
let C1092NCG_VC =
  [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
   `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
   `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;

(* open the input (sides identified with aC) and add the dots and the faces of E *)
let C1092NCG_DATA_TAC =
  C1092NCGD_OPEN_TAC THEN
  MP_TAC(SPECL C1092NCG_VC C1092NCGD_CENTRAL_DOT) THEN
  MP_TAC(SPECL C1092NCG_VC C1092NCGD_RECIPIENT_DOT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092SPNP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092spnp_faces] THEN STRIP_TAC;;

(* Lean: boundary_supports (private) *)
let C1092NCG_BOUNDARY_SUPPORTS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> (--sC) * lcx cB sB uB vB aB - &2 * cC +
         (aC / &2) * (cC * (cB + sB) + c1092mncs_kC cC sC cB sB +
                      abs(c1092mncs_deltaC cC sC cB sB))
         <= ABT_upper cB sB uB vB aB (--sC) cC /\
         (--sE) * lcx cB sB uB vB aB - &2 * cE +
         (aC / &2) * (cE * (cB + sB) + c1092mncs_kE cE (--sE) cB sB +
                      abs(c1092mncs_deltaE cE (--sE) cB sB))
         <= ABT_upper cB sB uB vB aB (--sE) cE /\
         (--sB) * lcx cB sB uB vB aB - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)
         <= ABT_upper cB sB uB vB aB (--sB) cB /\
         cB * lcx cB sB uB vB aB - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)
         <= ABT_upper cB sB uB vB aB cB sB`,
  C1092NCG_DATA_TAC THEN
  let fl nx ny =
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; nx; ny]
      C1092SPTG_FLOOR_UPPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[c1092mcs_quarter] THEN C1092NCG_LIN; DISCH_TAC] in
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
let c1092ncg_H00 = new_definition
 `c1092ncg_H00 (c:real) s d t h r = c1092mncs_width c s d t h r / &2 + t`;;
let c1092ncg_H01 = new_definition
 `c1092ncg_H01 (c:real) s d t h r =
    (c1092mncs_kC c s h r * (h + r) + h * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r)) +
     s) / &2 + h + s * max (c1092mncs_deltaE d t h r) (&0)`;;
let c1092ncg_H10 = new_definition
 `c1092ncg_H10 (c:real) s d t h r =
    (c1092mncs_kE d t h r * (h + r) + t + r * (c1092mncs_kE d t h r + abs(c1092mncs_deltaE d t h r))) /
    &2 + t * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r))`;;
let c1092ncg_H11 = new_definition
 `c1092ncg_H11 (c:real) s d t h r =
    h + r + h * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r)) +
    r * max (c1092mncs_deltaE d t h r) (&0)`;;

(* Lean: side_coefficients (private) *)
let C1092NCG_SIDE_COEFFICIENTS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> &0 < c1092ncg_H00 cC sC cE (--sE) cB sB /\ &0 < c1092ncg_H01 cC sC cE (--sE) cB sB /\
         &0 < c1092ncg_H10 cC sC cE (--sE) cB sB /\ &0 < c1092ncg_H11 cC sC cE (--sE) cB sB`,
  C1092NCG_DATA_TAC THEN
  SUBGOAL_THEN `&0 < cB + sB` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `cB = &0 /\ sB = &0` STRIP_ASSUME_TAC THENL [C1092NCG_LIN; ALL_TAC] THEN
    UNDISCH_TAC `cB * cB + sB * sB = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c1092ncg_H00; c1092ncg_H01; c1092ncg_H10; c1092ncg_H11; c1092mncs_width;
              c1092mncs_ell] THEN
  MP_TAC(SPEC `c1092mncs_deltaC cC sC cB sB` REAL_ABS_POS) THEN
  MP_TAC(SPEC `c1092mncs_deltaE cE (--sE) cB sB` REAL_ABS_POS) THEN
  MP_TAC(REAL_ARITH `&0 <= max (c1092mncs_deltaE cE (--sE) cB sB) (&0)`) THEN
  SPEC_TAC(`abs(c1092mncs_deltaC cC sC cB sB)`, `AC:real`) THEN
  SPEC_TAC(`abs(c1092mncs_deltaE cE (--sE) cB sB)`, `AE:real`) THEN
  SPEC_TAC(`max (c1092mncs_deltaE cE (--sE) cB sB) (&0)`, `ME:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  C1092NCG_PROD `&0 < cC * --sE` THEN C1092NCG_PROD `&0 < sC * cE` THEN
  C1092NCG_PROD `&0 <= (cC * --sE + sC * cE) * (cB + sB)` THEN
  C1092NCG_PROD `&0 <= --sE * (c1092mncs_kC cC sC cB sB + AC)` THEN
  C1092NCG_PROD `&0 <= sC * (c1092mncs_kE cE (--sE) cB sB + AE)` THEN
  C1092NCG_PROD `&0 <= c1092mncs_kC cC sC cB sB * (cB + sB)` THEN
  C1092NCG_PROD `&0 <= cB * (c1092mncs_kC cC sC cB sB + AC)` THEN
  C1092NCG_PROD `&0 <= sC * ME` THEN
  C1092NCG_PROD `&0 <= c1092mncs_kE cE (--sE) cB sB * (cB + sB)` THEN
  C1092NCG_PROD `&0 <= sB * (c1092mncs_kE cE (--sE) cB sB + AE)` THEN
  C1092NCG_PROD `&0 <= sB * ME` THEN
  C1092NCG_LIN);;

(* Lean: caps (private) *)
let C1092NCG_CAPS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB
     ==> vC <= c1092mncs_C0 sC - (aC - &1) /\ vE <= c1092mncs_E0 cE (--sE)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ncgd_input] o
    check (fun th -> can (term_match [] `c1092ncgd_input a b c d e f g h i j k l m n o'`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092SPNP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092spnp_faces] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spnp_input] o
    check (fun th -> can (term_match [] `c1092spnp_input a b c d e f g h i j`) (concl th))) THEN
  REWRITE_TAC[c1092mncs_C0; c1092mncs_E0] THEN C1092NCG_LIN);;

(* common opening of the four modes: data, supports, caps, side coefficients *)
let C1092NCG_MODE_TAC =
  C1092NCGD_OPEN_TAC THEN
  MP_TAC(SPECL C1092NCG_VC C1092NCG_BOUNDARY_SUPPORTS) THEN
  MP_TAC(SPECL C1092NCG_VC C1092NCG_SIDE_COEFFICIENTS) THEN
  MP_TAC(SPECL C1092NCG_VC C1092NCG_CAPS) THEN
  MP_TAC(SPECL C1092NCG_VC C1092NCGD_CENTRAL_CAP) THEN
  MP_TAC(SPECL C1092NCG_VC C1092NCGD_RECIPIENT_CAP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC;;

let C1092NCG_ABS_TAC =
  POP_ASSUM_LIST(MAP_EVERY MP_TAC) THEN
  MP_TAC(SPEC `c1092mncs_deltaC cC sC cB sB` REAL_ABS_POS) THEN
  MP_TAC(SPEC `c1092mncs_deltaE cE (--sE) cB sB` REAL_ABS_POS) THEN
  MP_TAC(REAL_ARITH `&0 <= max (c1092mncs_deltaE cE (--sE) cB sB) (&0)`) THEN
  SPEC_TAC(`abs(c1092mncs_deltaC cC sC cB sB)`, `AC:real`) THEN
  SPEC_TAC(`abs(c1092mncs_deltaE cE (--sE) cB sB)`, `AE:real`) THEN
  SPEC_TAC(`max (c1092mncs_deltaE cE (--sE) cB sB) (&0)`, `ME:real`) THEN
  SPEC_TAC(`c1092mncs_FC cC sC cB sB`, `FC:real`) THEN
  SPEC_TAC(`c1092mncs_FE cE (--sE) cB sB`, `FE:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC;;

(* Lean: mode00 *)
let C1092NCG_MODE00 = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB /\
     ABT_upper cB sB uB vB aB (--sC) cC <= vC /\ ABT_upper cB sB uB vB aB (--sE) cE <= vE
     ==> c1092mncs_G00 cC sC cE (--sE) cB sB < &0`,
  C1092NCG_MODE_TAC THEN
  REWRITE_TAC[c1092mncs_G00; c1092mncs_width; c1092mncs_ell] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092ncg_H00; c1092mncs_width; c1092mncs_ell]) THEN
  C1092NCG_ABS_TAC THEN
  C1092NCG_PROD `&0 <= --sE * ((c1092mncs_C0 sC - (aC - &1)) -
     ((--sC) * lcx cB sB uB vB aC - &2 * cC +
      (aC / &2) * (cC * (cB + sB) + c1092mncs_kC cC sC cB sB + AC)))` THEN
  C1092NCG_PROD `&0 <= sC * (c1092mncs_E0 cE (--sE) -
     ((--sE) * lcx cB sB uB vB aC - &2 * cE +
      (aC / &2) * (cE * (cB + sB) + c1092mncs_kE cE (--sE) cB sB + AE)))` THEN
  C1092NCG_PROD `&0 < (aC - &1) *
     (((cC * --sE + sC * cE) * (cB + sB) + --sE * (c1092mncs_kC cC sC cB sB + AC) +
       sC * (c1092mncs_kE cE (--sE) cB sB + AE)) / &2 + --sE)` THEN
  C1092NCG_LIN);;

(* Lean: mode01 *)
let C1092NCG_MODE01 = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB /\
     ABT_upper cB sB uB vB aB (--sC) cC <= vC /\
     ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB
     ==> c1092mncs_G01 cC sC cE (--sE) cB sB < &0`,
  C1092NCG_MODE_TAC THEN
  REWRITE_TAC[c1092mncs_G01] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092ncg_H01]) THEN
  C1092NCG_ABS_TAC THEN
  C1092NCG_PROD `&0 <= cB * ((c1092mncs_C0 sC - (aC - &1)) -
     ((--sC) * lcx cB sB uB vB aC - &2 * cC +
      (aC / &2) * (cC * (cB + sB) + c1092mncs_kC cC sC cB sB + AC)))` THEN
  C1092NCG_PROD `&0 <= sC * ((FE - (aC - &1) * ME) -
     (cB * lcx cB sB uB vB aC - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)))` THEN
  C1092NCG_PROD `&0 < (aC - &1) *
     ((c1092mncs_kC cC sC cB sB * (cB + sB) + cB * (c1092mncs_kC cC sC cB sB + AC) + sC) / &2 +
      cB + sC * ME)` THEN
  UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN REWRITE_TAC[c1092mncs_kC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_kC]) THEN DISCH_TAC THEN
  C1092NCG_LIN);;

(* Lean: mode10 *)
let C1092NCG_MODE10 = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB /\
     ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB /\
     ABT_upper cB sB uB vB aB (--sE) cE <= vE
     ==> c1092mncs_G10 cC sC cE (--sE) cB sB < &0`,
  C1092NCG_MODE_TAC THEN
  REWRITE_TAC[c1092mncs_G10] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092ncg_H10]) THEN
  C1092NCG_ABS_TAC THEN
  C1092NCG_PROD `&0 <= --sE * ((FC - (aC - &1) * (c1092mncs_kC cC sC cB sB + AC)) -
     ((--sB) * lcx cB sB uB vB aC - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)))` THEN
  C1092NCG_PROD `&0 <= sB * (c1092mncs_E0 cE (--sE) -
     ((--sE) * lcx cB sB uB vB aC - &2 * cE +
      (aC / &2) * (cE * (cB + sB) + c1092mncs_kE cE (--sE) cB sB + AE)))` THEN
  C1092NCG_PROD `&0 < (aC - &1) *
     ((c1092mncs_kE cE (--sE) cB sB * (cB + sB) + --sE + sB * (c1092mncs_kE cE (--sE) cB sB + AE)) / &2 +
      --sE * (c1092mncs_kC cC sC cB sB + AC))` THEN
  UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN REWRITE_TAC[c1092mncs_kE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_kE]) THEN DISCH_TAC THEN
  C1092NCG_LIN);;

(* Lean: mode11 *)
let C1092NCG_MODE11 = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB /\
     ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB /\
     ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB
     ==> c1092mncs_G11 cC sC cE (--sE) cB sB < &0`,
  C1092NCG_MODE_TAC THEN
  REWRITE_TAC[c1092mncs_G11] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092ncg_H11]) THEN
  C1092NCG_ABS_TAC THEN
  C1092NCG_PROD `&0 <= cB * ((FC - (aC - &1) * (c1092mncs_kC cC sC cB sB + AC)) -
     ((--sB) * lcx cB sB uB vB aC - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)))` THEN
  C1092NCG_PROD `&0 <= sB * ((FE - (aC - &1) * ME) -
     (cB * lcx cB sB uB vB aC - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)))` THEN
  C1092NCG_PROD `&0 < (aC - &1) *
     (cB + sB + cB * (c1092mncs_kC cC sC cB sB + AC) + sB * ME)` THEN
  SUBGOAL_THEN `(&2 - aC * (cB + sB) / &2) * (cB pow 2 + sB pow 2) = (&2 - aC * (cB + sB) / &2) * &1`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092NCG_LIN);;

(* Lean: NegativeMode (definition) *)
let c1092ncg_negativeMode = new_definition
 `c1092ncg_negativeMode (c:real) s d t h r <=>
    c1092mncs_G00 c s d t h r < &0 \/ (h <= r /\ c1092mncs_G01 c s d t h r < &0) \/
    c1092mncs_G10 c s d t h r < &0 \/ (h <= r /\ c1092mncs_G11 c s d t h r < &0)`;;

(* Lean: one_mode_negative_quarter *)
let C1092NCG_ONE_MODE_NEGATIVE_QUARTER = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> c1092ncg_negativeMode cC sC cE (--sE) cB sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1092ncg_negativeMode] THEN
  MP_TAC(SPECL C1092NCG_V C1092NCGD_CENTRAL_SOURCES) THEN
  MP_TAC(SPECL C1092NCG_V C1092NCGD_RECIPIENT_SOURCES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC)) THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL C1092NCG_V th))
    [C1092NCG_MODE00; C1092NCG_MODE01; C1092NCG_MODE10; C1092NCG_MODE11;
     C1092NCGD_BOUNDARY_RECIPIENT_HIGH] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* Lean: one_mode_negative *)
let C1092NCG_ONE_MODE_NEGATIVE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB
     ==> exists cQ sQ uQ vQ aQ.
           cQ * cQ + sQ * sQ = &1 /\ &0 < aQ /\ aQ = aB /\
           (forall x y. linside cQ sQ uQ vQ aQ x y <=> linside cB sB uB vB aB x y) /\
           c1092mncs_quarter cQ sQ /\
           c1092ncg_negativeMode cC sC cE (--sE) cQ sQ`,
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
  MATCH_MP_TAC C1092NCG_ONE_MODE_NEGATIVE_QUARTER THEN
  MAP_EVERY EXISTS_TAC [`uC:real`; `vC:real`; `aC:real`; `uE:real`; `vE:real`; `aE:real`;
                        `uQ:real`; `vQ:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB` THEN
  ASM_REWRITE_TAC[c1092ncgd_input; ldisj]);;

(* Lean: ModesNonnegative (definition) *)
let c1092ncg_modesNonnegative = new_definition
 `c1092ncg_modesNonnegative (c:real) s d t <=>
    forall h r. c1092mncs_quarter h r
          ==> &0 <= c1092mncs_G00 c s d t h r /\ (h <= r ==> &0 <= c1092mncs_G01 c s d t h r) /\
              &0 <= c1092mncs_G10 c s d t h r /\ (h <= r ==> &0 <= c1092mncs_G11 c s d t h r)`;;

(* Lean: impossible_of_modes *)
let C1092NCG_IMPOSSIBLE_OF_MODES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092ncg_modesNonnegative cC sC cE (--sE)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092NCG_ONE_MODE_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `c1092ncg_modesNonnegative cC sC cE (--sE)` THEN
  REWRITE_TAC[c1092ncg_modesNonnegative] THEN
  DISCH_THEN(MP_TAC o SPECL [`cQ:real`; `sQ:real`]) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092ncg_negativeMode cC sC cE (--sE) cQ sQ` THEN
  REWRITE_TAC[c1092ncg_negativeMode] THEN REAL_ARITH_TAC);;
