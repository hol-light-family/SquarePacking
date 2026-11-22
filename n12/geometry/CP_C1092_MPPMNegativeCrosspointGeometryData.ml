(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointGeometryData.lean   *)
(* (namespace N12Compact.C1092MPPMNegativeCrosspointGeometry).  Actual       *)
(* signed sources and simultaneous support caps for                          *)
(* STEEP-POSITIVE-NEGATIVE-CROSSPOINT-TRANSFER sections 1--3.                *)
(* Squares C, E, B are (cC, ..), (cE, ..), (cB, ..) with unit normals and    *)
(* positive sides as explicit hypotheses.  Input: c1092ncgd_input (its       *)
(* field `central` is c1092spnp_input C E); Quarter, kC, deltaC, kE, deltaE, *)
(* E0, FC, FE, P, Q, P2, Q2: c1092mncs_*; lower / upper: ABT_lower /         *)
(* ABT_upper; lower_nn / lower_np: C1092WS_LOWER_NN / _NP; strict_bounds /   *)
(* ownV: ABT_STRICT_BOUNDS / ABT_OWNV; ThreeSquare signed_axes / anchor_cone *)
(* / northeast_of_faces: C1092SPTS_*; SteepPositiveNegativeProfile.profile / *)
(* Faces: C1092SPNP_PROFILE / c1092spnp_faces.  Tag C1092NCGD_.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveNegativeProfile.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointSupportScalars.ml";;

(* Lean: Input (structure) *)
let c1092ncgd_input = new_definition
 `c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB <=>
    c1092spnp_input cC sC uC vC aC cE sE uE vE aE /\
    aC = aB /\
    linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
    linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
    linside cB sB uB vB aB (&0) (--(&1)) /\
    (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
    ldisj cB sB uB vB aB cC sC uC vC aC /\
    ldisj cB sB uB vB aB cE sE uE vE aE`;;

let C1092NCGD_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;

let C1092NCGD_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092NCGD_LIN; ALL_TAC];;

(* unpack the input (keeping the linside facts), the quarter and the normals;
   the sides of E and B are identified with aC *)
let C1092NCGD_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092ncgd_input]
    (ASSUME `c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092spnp_input]
    (ASSUME `c1092spnp_input cC sC uC vC aC cE sE uE vE aE`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]
    (ASSUME `c1092mncs_quarter cB sB`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME t)) THEN
                      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME t)))
    [`c977cc_normal cC sC`; `c977cc_normal cE (--sE)`];;

let C1092NCGD_CONE_TAC nx ny =
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; nx; ny]
    C1092SPTS_ANCHOR_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC;;

(* Lean: central_sources *)
let C1092NCGD_CENTRAL_SOURCES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> ABT_upper cB sB uB vB aB (--sC) cC <= vC \/
         ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB`,
  C1092NCGD_OPEN_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092SPTS_SIGNED_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `cB:real`; `sB:real`]
      C1092SPTS_NORTHEAST_OF_FACES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    C1092NCGD_CONE_TAC `--cB` `--sB`;
    ASM_REWRITE_TAC[];
    C1092NCGD_CONE_TAC `sB:real` `--cB`;
    C1092NCGD_CONE_TAC `cC:real` `sC:real`;
    C1092NCGD_CONE_TAC `--cC` `--sC`;
    DISJ1_TAC THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    C1092NCGD_CONE_TAC `sC:real` `--cC`]);;

let C1092NCGD_ECONE_TAC nx ny =
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC])
   [[`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`], (`&2 / &5`,`--(&1)`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`], (`&0`,`--(&13 / &50)`);
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`], (`&0`,`--(&1)`)] THEN
  RASM_ARITH_TAC;;

(* Lean: recipient_sources *)
let C1092NCGD_RECIPIENT_SOURCES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> ABT_upper cB sB uB vB aB (--sE) cE <= vE \/
         ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB`,
  C1092NCGD_OPEN_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092SPTS_SIGNED_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[];
    C1092NCGD_ECONE_TAC `--cB` `--sB`;
    C1092NCGD_ECONE_TAC `--sB` `cB:real`;
    C1092NCGD_ECONE_TAC `sB:real` `--cB`;
    C1092NCGD_ECONE_TAC `cE:real` `sE:real`;
    C1092NCGD_ECONE_TAC `--cE` `--sE`;
    DISJ1_TAC THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    C1092NCGD_ECONE_TAC `sE:real` `--cE`]);;

(* Lean: central_dot *)
let C1092NCGD_CENTRAL_DOT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> &0 <= c1092mncs_kC cC sC cB sB`,
  C1092NCGD_OPEN_TAC THEN REWRITE_TAC[c1092mncs_kC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  RASM_ARITH_TAC);;

(* Lean: recipient_dot *)
let C1092NCGD_RECIPIENT_DOT = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> &0 <= c1092mncs_kE cE (--sE) cB sB`,
  C1092NCGD_OPEN_TAC THEN REWRITE_TAC[c1092mncs_kE] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  RASM_ARITH_TAC);;

let C1092NCGD_DOT_TAC =
  SUBGOAL_THEN `&0 <= c1092mncs_kC cC sC cB sB /\ &0 <= c1092mncs_kE cE (--sE) cB sB`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_kC; c1092mncs_kE] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    RASM_ARITH_TAC; ALL_TAC];;

(* Lean: central_cap *)
let C1092NCGD_CENTRAL_CAP = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> ABT_lower cC sC uC vC aC (--sB) cB <=
         c1092mncs_FC cC sC cB sB -
         (aC - &1) * (c1092mncs_kC cC sC cB sB + abs(c1092mncs_deltaC cC sC cB sB))`,
  C1092NCGD_OPEN_TAC THEN C1092NCGD_DOT_TAC THEN
  SUBGOAL_THEN `--sB * cC + cB * sC = --c1092mncs_deltaC cC sC cB sB /\
                -- --sB * sC + cB * cC = c1092mncs_kC cC sC cB sB` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_deltaC; c1092mncs_kC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092NCGD_PROD `&0 <= c1092mncs_kC cC sC cB sB * (sC - (vC + aC))` THEN
  REWRITE_TAC[c1092mncs_FC; real_abs] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--c1092mncs_deltaC cC sC cB sB`; `c1092mncs_kC cC sC cB sB`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NCGD_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092NCGD_PROD `&0 <= c1092mncs_deltaC cC sC cB sB * (uC - (--cC - sC))` THEN
    C1092NCGD_LIN;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--c1092mncs_deltaC cC sC cB sB`; `c1092mncs_kC cC sC cB sB`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NCGD_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092NCGD_PROD `&0 <= --c1092mncs_deltaC cC sC cB sB * (--cC / &2 - (uC + aC))` THEN
    C1092NCGD_LIN]);;

let C1092NCGD_FACES_TAC =
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092SPNP_PROFILE) THEN
  ASM_REWRITE_TAC[c1092spnp_faces] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cB * cE + sB * sE = --c1092mncs_deltaE cE (--sE) cB sB /\
                --cB * sE + sB * cE = c1092mncs_kE cE (--sE) cB sB` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_deltaE; c1092mncs_kE] THEN REAL_ARITH_TAC; ALL_TAC];;

(* Lean: recipient_cap *)
let C1092NCGD_RECIPIENT_CAP = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB
     ==> ABT_lower cE sE uE vE aE cB sB <=
         c1092mncs_FE cE (--sE) cB sB -
         (aC - &1) * max (c1092mncs_deltaE cE (--sE) cB sB) (&0)`,
  C1092NCGD_OPEN_TAC THEN C1092NCGD_DOT_TAC THEN C1092NCGD_FACES_TAC THEN
  C1092NCGD_PROD `&0 <= c1092mncs_kE cE (--sE) cB sB * ((--(&13 / &50) * sE - cE) - vE)` THEN
  REWRITE_TAC[c1092mncs_FE; real_max] THEN
  ASM_CASES_TAC `&0 <= c1092mncs_deltaE cE (--sE) cB sB` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (x <= &0 <=> x = &0)`] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cB:real`; `sB:real`;
                  `--c1092mncs_deltaE cE (--sE) cB sB`; `c1092mncs_kE cE (--sE) cB sB`]
      C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NCGD_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092NCGD_PROD `&0 <= c1092mncs_deltaE cE (--sE) cB sB * (uE - --(&7 / &20) * (cE + sE))` THEN
    SUBGOAL_THEN
     `c1092mncs_P2 cE (--sE) * cB + c1092mncs_Q2 cE (--sE) * sB =
      --c1092mncs_deltaE cE (--sE) cB sB * (&1 - (&7 / &20) * (cE + sE)) +
      c1092mncs_kE cE (--sE) cB sB * c1092mncs_E0 cE (--sE)` SUBST1_TAC THENL
     [REWRITE_TAC[c1092mncs_P2; c1092mncs_Q2; c1092mncs_deltaE; c1092mncs_kE; c1092mncs_E0] THEN
      UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[c1092mncs_E0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    SUBGOAL_THEN `c1092mncs_deltaE cE (--sE) cB sB <= &0` ASSUME_TAC THENL
     [RASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cB:real`; `sB:real`;
                  `--c1092mncs_deltaE cE (--sE) cB sB`; `c1092mncs_kE cE (--sE) cB sB`]
      C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NCGD_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092NCGD_PROD `&0 <= --c1092mncs_deltaE cE (--sE) cB sB * (--(&13 / &50) * sE - uE)` THEN
    SUBGOAL_THEN
     `--c1092mncs_P cE (--sE) * cB - c1092mncs_Q cE (--sE) * sB =
      --c1092mncs_deltaE cE (--sE) cB sB * (--(&13 / &50) * sE) +
      c1092mncs_kE cE (--sE) cB sB * c1092mncs_E0 cE (--sE)` SUBST1_TAC THENL
     [REWRITE_TAC[c1092mncs_P; c1092mncs_Q; c1092mncs_deltaE; c1092mncs_kE; c1092mncs_E0] THEN
      UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[c1092mncs_E0] THEN RASM_ARITH_TAC]);;

(* Lean: boundary_recipient_high *)
let C1092NCGD_BOUNDARY_RECIPIENT_HIGH = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092ncgd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mncs_quarter cB sB /\
     ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB
     ==> cB < sB`,
  C1092NCGD_OPEN_TAC THEN C1092NCGD_DOT_TAC THEN C1092NCGD_FACES_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092NCGD_PROD `&0 <= --sE * (cB - sB)` THEN
  C1092NCGD_PROD `&0 <= cB * (cE + sE)` THEN
  SUBGOAL_THEN `c1092mncs_deltaE cE (--sE) cB sB <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_deltaE] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cB:real`; `sB:real`;
                `--c1092mncs_deltaE cE (--sE) cB sB`; `c1092mncs_kE cE (--sE) cB sB`]
    C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NCGD_LIN; DISCH_TAC] THEN
  C1092NCGD_PROD `&0 <= --c1092mncs_deltaE cE (--sE) cB sB * (--(&13 / &50) * sE - uE)` THEN
  C1092NCGD_PROD `&0 <= c1092mncs_kE cE (--sE) cB sB * ((--(&13 / &50) * sE - cE) - vE)` THEN
  SUBGOAL_THEN
   `--c1092mncs_P cE (--sE) * cB - c1092mncs_Q cE (--sE) * sB =
    --c1092mncs_deltaE cE (--sE) cB sB * (--(&13 / &50) * sE) +
    c1092mncs_kE cE (--sE) cB sB * c1092mncs_E0 cE (--sE)` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_P; c1092mncs_Q; c1092mncs_deltaE; c1092mncs_kE; c1092mncs_E0] THEN
    UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cE` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--sE < (&3 / &8) * cE` ASSUME_TAC THENL
   [UNDISCH_TAC `(--sE) / cE < &3 / &8` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092mncs_P cE (--sE) /\
                &0 <= c1092mncs_P cE (--sE) + c1092mncs_Q cE (--sE) - &1`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_P; c1092mncs_Q] THEN
    C1092NCGD_PROD `&0 <= --sE * ((&37 / &50) * cE + (&13 / &50) * sE)` THEN
    C1092NCGD_PROD `&0 <= --sE * ((&12 / &25) * cE + sE)` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092NCGD_PROD `&0 <= c1092mncs_P cE (--sE) * (cB - sB)` THEN
  C1092NCGD_PROD `&0 <= (c1092mncs_P cE (--sE) + c1092mncs_Q cE (--sE) - &1) * sB` THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `&0`; `--(&1)`;
                `cB:real`; `sB:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_E0]) THEN
  RASM_ARITH_TAC);;
