(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointData.lean   *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointGeometry; Lean header:      *)
(* "Source only, uncompiled").  Actual normal cones for the missing-negative *)
(* successor three-square theorem.  Squares C, E, B are (cC, ..), (cE, ..),  *)
(* (cB, ..) with unit normals and positive sides as explicit hypotheses.     *)
(* Input c1092mncd_input; RecipientInput / recipient_faces:                  *)
(* c1092mncf_recipientInput / C1092MNCF_RECIPIENT_FACES; Quarter, kC,        *)
(* deltaC, kE, deltaE, FC: c1092mncs_*; FE, E0: c1092mmncs_FE / _E0; lower / *)
(* upper ABT_lower / ABT_upper; lower_nn / lower_np C1092WS_*; strict_bounds *)
(* / ownV ABT_STRICT_BOUNDS / ABT_OWNV; ThreeSquare signed_axes / anchor_cone*)
(* / northeast_of_faces C1092SPTS_*; cosine_order C977CSB_COSINE_ORDER.      *)
(* Tag C1092MNCD_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointFaces.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointGeometryData.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointScalars.ml";;

(* Lean: Input (structure) *)
let c1092mncd_input = new_definition
 `c1092mncd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB <=>
    &1 < aC /\ aC = aE /\ aC = aB /\ c977cc_normal cC sC /\ &3 / &5 <= sC /\
    --cC - sC <= uC /\ uC + aC <= --cC / &2 /\ vC + aC <= (&543 / &500) * sC /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
    c1092mncf_recipientInput cE sE uE vE aE cB sB uB vB aB /\
    linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
    linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
    (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
    ldisj cB sB uB vB aB cC sC uC vC aC`;;

let C1092MNCD_SQ = "cC * cC + sC * sC = &1 /\\ &0 < aC /\\ cE * cE + sE * sE = &1 /\\ &0 < aE /\\
     cB * cB + sB * sB = &1 /\\ &0 < aB /\\
     c1092mncd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB";;
let c1092mncd_stmt vars hyps concl =
  parse_term (Printf.sprintf "!cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB%s. %s%s ==> %s"
    vars C1092MNCD_SQ hyps concl);;

(* unpack the input, the recipient input and the recipient faces; sides = aC *)
let C1092MNCD_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092MNCF_RECIPIENT_FACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o el 10 o CONJUNCTS o REWRITE_RULE[c1092mncd_input] o
      check (c1092mpapo_head `c1092mncd_input`));
    REWRITE_TAC[c1092mncf_recipientFaces] THEN STRIP_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mncd_input]
    (ASSUME `c1092mncd_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mncf_recipientInput]
    (ASSUME `c1092mncf_recipientInput cE sE uE vE aE cB sB uB vB aB`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME t)) THEN
                      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS (ASSUME t)))
    [`c977cc_normal cC sC`; `c977cc_normal cE (--sE)`];;

let C1092MNCD_QUARTER_TAC =
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter] (ASSUME `c1092mncs_quarter cB sB`));;

(* Lean: central_sources *)
let C1092MNCD_CENTRAL_SOURCES = prove
 (c1092mncd_stmt "" " /\\ c1092mncs_quarter cB sB"
   "ABT_upper cB sB uB vB aB (--sC) cC <= vC \\/
    ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB",
  C1092MNCD_OPEN_TAC THEN C1092MNCD_QUARTER_TAC THEN
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

(* Lean: recipient_cone *)
let C1092MNCD_RECIPIENT_CONE = prove
 (c1092mncd_stmt " nx ny" " /\\ nx pow 2 + ny pow 2 = &1 /\\
     ABT_upper cB sB uB vB aB nx ny <= ABT_lower cE sE uE vE aE nx ny"
   "&0 < nx /\\ &0 < (&7 / &20) * nx + (&13 / &20) * ny",
  C1092MNCD_OPEN_TAC THEN
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [[`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`], (`&2 / &5`,`--(&1)`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`], (`&7 / &20`,`--(&7 / &20)`);
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`], (`&0`,`--(&1)`)] THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

let C1092MNCD_LIN = C1092NCGD_LIN;;
let C1092MNCD_PROD = C1092NCGD_PROD;;
let C1092MNCD_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092MNCD_LIN; ALL_TAC];;

(* Lean: downward_impossible *)
let C1092MNCD_DOWNWARD_IMPOSSIBLE = prove
 (c1092mncd_stmt " xi eta" " /\\ &0 < xi /\\ &0 <= eta /\\ xi pow 2 + (--eta) pow 2 = &1"
   "~(ABT_upper cB sB uB vB aB xi (--eta) <= ABT_lower cE sE uE vE aE xi (--eta))",
  C1092MNCD_OPEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`; `uE:real`;
    `vE:real`; `aC:real`; `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `xi:real`; `--eta`]
    C1092MNCD_RECIPIENT_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `--sE`; `&275 / &373`; `&252 / &373`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092MNCD_PROD `&0 < cE * xi` THEN C1092MNCD_PROD `&0 <= --sE * eta` THEN
  C1092MNCD_FACT `&0 < cE * xi - sE * eta` THEN
  C1092MNCD_PROD `&0 <= (--sE - &252 / &373) * xi` THEN
  C1092MNCD_PROD `&0 <= (&1 - cE) * eta` THEN
  C1092MNCD_FACT `&0 < --sE * xi - cE * eta` THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `xi:real`; `--eta`;
    `cE * xi - sE * eta`; `--sE * xi - cE * eta`] C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MNCD_LIN; DISCH_TAC] THEN
  C1092MNCD_PROD `&0 <= (cE * xi - sE * eta) * ((cE - sE) - (uE + aC))` THEN
  C1092MNCD_PROD `&0 <= (--sE * xi - cE * eta) * ((--sE - (&14 / &25) * cE) - (vE + aC))` THEN
  C1092MNCD_PROD `&0 < (aC - &1) * ((cE * xi - sE * eta) + (--sE * xi - cE * eta))` THEN
  C1092MNCD_PROD `&0 <= (cE + sE) * (cE + sE)` THEN
  C1092MNCD_FACT `cE * --sE <= &1 / &2` THEN
  C1092MNCD_PROD `&0 <= (cE + sE) * (cE - sE)` THEN
  C1092MNCD_FACT `sE * sE <= &1 / &2` THEN
  C1092MNCD_FACT `&1 - cE + sE - (&11 / &25) * cE * sE < &0` THEN
  C1092MNCD_FACT `&0 < &1 + (--sE - cE - &14 / &25 - (&11 / &25) * sE * sE)` THEN
  C1092MNCD_PROD `&0 < xi * --(&1 - cE + sE - (&11 / &25) * cE * sE)` THEN
  C1092MNCD_PROD `&0 <= (&1 + (--sE - cE - &14 / &25 - (&11 / &25) * sE * sE)) * eta` THEN
  SUBGOAL_THEN `(cE * xi - sE * eta) * (cE - sE - &1) + (--sE * xi - cE * eta) * (--sE - (&14 / &25) * cE - &1) - eta =
                (&1 - cE + sE - (&11 / &25) * cE * sE) * xi -
                (&1 + (--sE - cE - &14 / &25 - (&11 / &25) * sE * sE)) * eta` ASSUME_TAC THENL
   [UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `&0`; `--(&1)`; `xi:real`; `--eta`]
    ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C1092MNCD_LIN);;

let C1092MNCD_V15 = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`; `uE:real`;
  `vE:real`; `aC:real`; `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;
let C1092MNCD_ECONE_TAC nx ny =
  MP_TAC(SPECL (C1092MNCD_V15 @ [nx; ny]) C1092MNCD_RECIPIENT_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC;;

(* Lean: recipient_sources *)
let C1092MNCD_RECIPIENT_SOURCES = prove
 (c1092mncd_stmt "" " /\\ c1092mncs_quarter cB sB"
   "ABT_upper cB sB uB vB aB (--sE) cE <= vE \\/
    ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB",
  C1092MNCD_OPEN_TAC THEN C1092MNCD_QUARTER_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092SPTS_SIGNED_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[];
    C1092MNCD_ECONE_TAC `--cB` `--sB`;
    C1092MNCD_ECONE_TAC `--sB` `cB:real`;
    MP_TAC(SPECL (C1092MNCD_V15 @ [`sB:real`; `cB:real`]) C1092MNCD_DOWNWARD_IMPOSSIBLE) THEN
    MP_TAC(SPECL (C1092MNCD_V15 @ [`sB:real`; `--cB`]) C1092MNCD_RECIPIENT_CONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN RASM_ARITH_TAC;
    C1092MNCD_ECONE_TAC `cE:real` `sE:real`;
    C1092MNCD_ECONE_TAC `--cE` `--sE`;
    DISJ1_TAC THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNV) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    C1092MNCD_ECONE_TAC `sE:real` `--cE`]);;

(* Lean: central_dot *)
let C1092MNCD_CENTRAL_DOT = prove
 (c1092mncd_stmt "" " /\\ c1092mncs_quarter cB sB" "&0 <= c1092mncs_kC cC sC cB sB",
  C1092MNCD_OPEN_TAC THEN C1092MNCD_QUARTER_TAC THEN REWRITE_TAC[c1092mncs_kC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  RASM_ARITH_TAC);;

(* Lean: recipient_dot *)
let C1092MNCD_RECIPIENT_DOT = prove
 (c1092mncd_stmt "" " /\\ c1092mncs_quarter cB sB" "&0 <= c1092mncs_kE cE (--sE) cB sB",
  C1092MNCD_OPEN_TAC THEN C1092MNCD_QUARTER_TAC THEN REWRITE_TAC[c1092mncs_kE] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  RASM_ARITH_TAC);;

let C1092MNCD_DOT_TAC =
  SUBGOAL_THEN `&0 <= c1092mncs_kC cC sC cB sB /\ &0 <= c1092mncs_kE cE (--sE) cB sB`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_kC; c1092mncs_kE] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    RASM_ARITH_TAC; ALL_TAC];;

(* Lean: central_cap *)
let C1092MNCD_CENTRAL_CAP = prove
 (c1092mncd_stmt "" " /\\ c1092mncs_quarter cB sB"
   "ABT_lower cC sC uC vC aC (--sB) cB <=
    c1092mncs_FC cC sC cB sB + (&43 / &500) * sC * c1092mncs_kC cC sC cB sB -
    (aC - &1) * (c1092mncs_kC cC sC cB sB + abs(c1092mncs_deltaC cC sC cB sB))",
  C1092MNCD_OPEN_TAC THEN C1092MNCD_QUARTER_TAC THEN C1092MNCD_DOT_TAC THEN
  SUBGOAL_THEN `--sB * cC + cB * sC = --c1092mncs_deltaC cC sC cB sB /\
                -- --sB * sC + cB * cC = c1092mncs_kC cC sC cB sB` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_deltaC; c1092mncs_kC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MNCD_PROD `&0 <= c1092mncs_kC cC sC cB sB * ((&543 / &500) * sC - (vC + aC))` THEN
  REWRITE_TAC[c1092mncs_FC; real_abs] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--c1092mncs_deltaC cC sC cB sB`; `c1092mncs_kC cC sC cB sB`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MNCD_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092MNCD_PROD `&0 <= c1092mncs_deltaC cC sC cB sB * (uC - (--cC - sC))` THEN
    C1092MNCD_LIN;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--c1092mncs_deltaC cC sC cB sB`; `c1092mncs_kC cC sC cB sB`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MNCD_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092MNCD_PROD `&0 <= --c1092mncs_deltaC cC sC cB sB * (--cC / &2 - (uC + aC))` THEN
    C1092MNCD_LIN]);;

(* Lean: recipient_cap *)
let C1092MNCD_RECIPIENT_CAP = prove
 (c1092mncd_stmt "" " /\\ c1092mncs_quarter cB sB"
   "ABT_lower cE sE uE vE aE cB sB <=
    c1092mmncs_FE cE (--sE) cB sB -
    (aC - &1) * (c1092mncs_kE cE (--sE) cB sB + abs(c1092mncs_deltaE cE (--sE) cB sB))",
  C1092MNCD_OPEN_TAC THEN C1092MNCD_QUARTER_TAC THEN C1092MNCD_DOT_TAC THEN
  SUBGOAL_THEN `cB * cE + sB * sE = --c1092mncs_deltaE cE (--sE) cB sB /\
                --cB * sE + sB * cE = c1092mncs_kE cE (--sE) cB sB` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mncs_deltaE; c1092mncs_kE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MNCD_PROD `&0 <= c1092mncs_kE cE (--sE) cB sB * ((--sE - (&14 / &25) * cE) - (vE + aC))` THEN
  REWRITE_TAC[c1092mmncs_FE; c1092mmncs_E0; real_abs] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cB:real`; `sB:real`;
                  `--c1092mncs_deltaE cE (--sE) cB sB`; `c1092mncs_kE cE (--sE) cB sB`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MNCD_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092MNCD_PROD `&0 <= c1092mncs_deltaE cE (--sE) cB sB * (uE - --(&13 / &50) * sE)` THEN
    C1092MNCD_LIN;
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cB:real`; `sB:real`;
                  `--c1092mncs_deltaE cE (--sE) cB sB`; `c1092mncs_kE cE (--sE) cB sB`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MNCD_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092MNCD_PROD `&0 <= --c1092mncs_deltaE cE (--sE) cB sB * ((cE - sE) - (uE + aC))` THEN
    C1092MNCD_LIN]);;
