(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCenters.lean          *)
(* (N12Compact.C1092MPPMMissingNegativeCenters).  MISSING-NEGATIVE-         *)
(* BOUNDARIES Theorems 2-3 for the actual neighboring squares.  Squares     *)
(* C = cC sC uC vC aC, B = cB sB uB vB aB, L = cL sL uL vL aL (unit normals  *)
(* and positive sides explicit).  Data C: c1092mncsp_data; Data.large /      *)
(* negative_widths / northwest / northeast: C1092MNCSP_ lemmas; bounds /     *)
(* central_margins / Fb / Fl: C1092MNCS_BOUNDS / C1092MNCS_CENTRAL_MARGINS / *)
(* c1092mncs_Fb / c1092mncs_Fl; strict_bounds, ownU: ABT_STRICT_BOUNDS,      *)
(* ABT_OWNU; negative_support: C1092MCSUP_NEGATIVE_SUPPORT; bottom_center,   *)
(* left_center, bottom_face, left_face, FaceNormal: C1092SBS_ lemmas and     *)
(* c1092sbs_FaceNormal; directed_faces: C1092MPBEB_DIRECTED_FACES.           *)
(* Tag C1092MNCT_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCentersSupport.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;

let C1092MNCT_LIN = NLIN_TAC ~deg2:false [];;

let C1092MNCT_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MNCT_LIN; ALL_TAC];;

let C1092MNCT_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MNCT_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;
let C1092MNCT_L = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`];;

(* data of C: faces, marker coordinates, large, bounds *)
let C1092MNCT_DATA_TAC =
  MP_TAC(SPECL C1092MNCT_C C1092MNCSP_DATA_LARGE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mncsp_data; c1092mnpg_strong_faces; c1092mnpg_faces]
    (ASSUME `c1092mncsp_data cC sC uC vC aC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal c s`) o concl)) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092MNCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* ---- bottom_order ---- *)

(* Lean: cone (local of bottom_order) *)
let C1092MNCT_BOTTOM_CONE = prove
 (`forall cC sC uC vC aC cB sB uB vB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\
     c1092mncsp_data cC sC uC vC aC /\
     linside cB sB uB vB aC (&0) (--(&543 / &500)) /\ linside cB sB uB vB aC (--(&2 / &5)) (--(&1)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cB sB uB vB aC nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < ny /\ nx < (&413 / &500) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mncsp_data] (ASSUME `c1092mncsp_data cC sC uC vC aC`)) THEN
  MP_TAC(SPECL (C1092MNCT_B @ [`&0`; `--(&543 / &500)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`--(&1)`; `--(&13 / &50)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092MNCT_B @ [`--(&2 / &5)`; `--(&1)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`--(&7 / &20)`; `--(&7 / &20)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: central (local of bottom_order) *)
let C1092MNCT_BOTTOM_CENTRAL = prove
 (`forall cC sC uC vC aC cB sB uB vB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &1 < aC /\
     c1092mncsp_data cC sC uC vC aC /\
     (forall x y. linside cB sB uB vB aC x y ==> --(&2) <= y) /\
     lcx cB sB uB vB aC <= --(&1 / &5)
     ==> ~(ABT_upper cB sB uB vB aC (--cC) (--sC) <= ABT_lower cC sC uC vC aC (--cC) (--sC))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN C1092MNCT_DATA_TAC THEN
  MP_TAC(SPECL C1092MNCT_B C1092SBS_BOTTOM_CENTER) THEN
  MP_TAC(SPECL (C1092MNCT_B @ [`cC:real`; `--sC`]) C1092MNCSP_NEGATIVE_WIDTHS) THEN
  MP_TAC(SPECL C1092MNCT_C ABT_OWNU) THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`cC:real`; `sC:real`]) C1092MCSUP_NEGATIVE_SUPPORT) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092MNCS_CENTRAL_MARGINS) THEN
  ASM_REWRITE_TAC[REAL_ARITH `-- &2 = --(&2)`] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ABT_upper cB sB uB vB aC (--cC) (--sC) <= ABT_lower cC sC uC vC aC (--cC) (--sC)` THEN
  ASM_REWRITE_TAC[ABT_upper] THEN DISCH_TAC THEN
  C1092MNCT_PROD `&0 <= --sC * (lcy cB sB uB vB aC - (--(&2) + aC * c1092sbs_width0 cB sB / &2))` THEN
  C1092MNCT_PROD `&0 <= cC * (--(&1 / &5) - lcx cB sB uB vB aC)` THEN
  C1092MNCT_PROD `&0 <= --sC * (cC + --sC)` THEN
  C1092MNCT_PROD `&0 < (aC - &1) * (&3 / &2 + --sC * (cC + --sC) / &2)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_Fb; REAL_NEG_NEG]) THEN
  C1092MNCT_LIN);;

(* Lean: boundary (local of bottom_order) *)
let C1092MNCT_BOTTOM_BOUNDARY = prove
 (`forall cC sC uC vC aC cB sB uB vB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &1 < aC /\
     c1092mncsp_data cC sC uC vC aC /\
     linside cB sB uB vB aC (&0) (--(&543 / &500)) /\ linside cB sB uB vB aC (--(&2 / &5)) (--(&1)) /\
     (forall x y. linside cB sB uB vB aC x y ==> --(&2) <= y) /\
     lcx cB sB uB vB aC <= --(&1 / &5) /\
     nx pow 2 + ny pow 2 = &1 /\ c1092sbs_FaceNormal cB sB nx ny
     ==> ~(ABT_upper cB sB uB vB aC nx ny <= ABT_lower cC sC uC vC aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `nx:real`; `ny:real`])
    C1092MNCT_BOTTOM_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MNCT_B @ [`--(&2 / &5)`; `--(&1)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= nx` THENL
   [MP_TAC(SPECL (C1092MNCT_C @ [`nx:real`; `ny:real`]) C1092MNCSP_NORTHEAST) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MNCT_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--nx`; `ny:real`]
    C1092SBS_BOTTOM_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG; REAL_ARITH `-- &2 = --(&2)`] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])] THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`--nx`; `ny:real`]) C1092MNCSP_NORTHWEST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG; c1092mcs_quarter; REAL_POW_NEG; ARITH] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[REAL_NEG_NEG])] THEN
  C1092MNCT_PROD `&0 <= --nx * (--(&1 / &5) - lcx cB sB uB vB aC)` THEN
  C1092MNCT_LIN);;

(* Lean: bottom_order *)
let C1092MNCT_BOTTOM_ORDER = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC = aB /\ c1092mncsp_data cC sC uC vC aC /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\ linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
     (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> --(&1 / &5) < lcx cB sB uB vB aB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C1092MNCT_DATA_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MNCT_B @ C1092MNCT_C) C1092MPBEB_DIRECTED_FACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ldisj cC sC uC vC aC cB sB uB vB aC` THEN
    REWRITE_TAC[ldisj] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nx:real` (X_CHOOSE_THEN `ny:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC)))) THENL
   [MP_TAC(SPECL (C1092MNCT_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`;
                                 `nx:real`; `ny:real`]) C1092MNCT_BOTTOM_BOUNDARY) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`;
                               `nx:real`; `ny:real`]) C1092MNCT_BOTTOM_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `c1092sbs_FaceNormal a b c d`) o concl)) THEN
  REWRITE_TAC[c1092sbs_FaceNormal] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  TRY ASM_REAL_ARITH_TAC THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`]) C1092MNCT_BOTTOM_CENTRAL) THEN
  ASM_REWRITE_TAC[]);;

(* ---- left_order ---- *)

(* Lean: cone (local of left_order) *)
let C1092MNCT_LEFT_CONE = prove
 (`forall cC sC uC vC aC cL sL uL vL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\
     c1092mncsp_data cC sC uC vC aC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\ linside cL sL uL vL aC (--(&1)) (&0) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny
     ==> &0 < ny /\ nx < (&175 / &368) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mncsp_data] (ASSUME `c1092mncsp_data cC sC uC vC aC`)) THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`--(&1)`; `--(&13 / &50)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092MNCT_L @ [`--(&1)`; `&0`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`--(&7 / &20)`; `--(&7 / &20)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092MNCT_L @ [`--(&543 / &500)`; `&0`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: central (local of left_order) *)
let C1092MNCT_LEFT_CENTRAL = prove
 (`forall cC sC uC vC aC cL sL uL vL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     c1092mncsp_data cC sC uC vC aC /\
     (forall x y. linside cL sL uL vL aC x y ==> --(&2) <= x) /\
     lcy cL sL uL vL aC <= &1 / &5
     ==> ~(ABT_upper cC sC uC vC aC (--cC) (--sC) <= ABT_lower cL sL uL vL aC (--cC) (--sC))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN C1092MNCT_DATA_TAC THEN
  MP_TAC(SPECL C1092MNCT_L C1092SBS_LEFT_CENTER) THEN
  MP_TAC(SPECL (C1092MNCT_L @ [`cC:real`; `--sC`]) C1092MNCSP_NEGATIVE_WIDTHS) THEN
  MP_TAC(SPECL C1092MNCT_C ABT_OWNU) THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`cC:real`; `sC:real`]) C1092MCSUP_NEGATIVE_SUPPORT) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092MNCS_CENTRAL_MARGINS) THEN
  ASM_REWRITE_TAC[REAL_ARITH `-- &2 = --(&2)`] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ABT_upper cC sC uC vC aC (--cC) (--sC) <= ABT_lower cL sL uL vL aC (--cC) (--sC)` THEN
  ASM_REWRITE_TAC[ABT_lower] THEN DISCH_TAC THEN
  C1092MNCT_PROD `&0 <= cC * (lcx cL sL uL vL aC - (--(&2) + aC * c1092sbs_width0 cL sL / &2))` THEN
  C1092MNCT_PROD `&0 <= --sC * (&1 / &5 - lcy cL sL uL vL aC)` THEN
  C1092MNCT_PROD `&0 <= cC * (cC + --sC)` THEN
  C1092MNCT_PROD `&0 < (aC - &1) * (&3 / &2 + cC * (cC + --sC) / &2)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_Fl; REAL_NEG_NEG]) THEN
  C1092MNCT_LIN);;

(* Lean: boundary (local of left_order) *)
let C1092MNCT_LEFT_BOUNDARY = prove
 (`forall cC sC uC vC aC cL sL uL vL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     c1092mncsp_data cC sC uC vC aC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\ linside cL sL uL vL aC (--(&1)) (&0) /\
     (forall x y. linside cL sL uL vL aC x y ==> --(&2) <= x) /\
     lcy cL sL uL vL aC <= &1 / &5 /\
     nx pow 2 + ny pow 2 = &1 /\ c1092sbs_FaceNormal cL sL nx ny
     ==> ~(ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `nx:real`; `ny:real`])
    C1092MNCT_LEFT_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MNCT_L @ [`--(&1)`; `&0`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= nx` THENL
   [MP_TAC(SPECL (C1092MNCT_C @ [`nx:real`; `ny:real`]) C1092MNCSP_NORTHEAST) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN C1092MNCT_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`; `--nx`; `ny:real`]
    C1092SBS_LEFT_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG; REAL_ARITH `-- &2 = --(&2)`] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])] THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`--nx`; `ny:real`]) C1092MNCSP_NORTHWEST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG; c1092mcs_quarter; REAL_POW_NEG; ARITH] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[REAL_NEG_NEG])] THEN
  C1092MNCT_PROD `&0 <= ny * (&1 / &5 - lcy cL sL uL vL aC)` THEN
  C1092MNCT_LIN);;

(* Lean: left_order *)
let C1092MNCT_LEFT_ORDER = prove
 (`forall cC sC uC vC aC cL sL uL vL aL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aC /\ aC = aL /\ c1092mncsp_data cC sC uC vC aC /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\ linside cL sL uL vL aL (--(&1)) (&0) /\
     (forall x y. linside cL sL uL vL aL x y ==> --(&2) <= x) /\
     ldisj cC sC uC vC aC cL sL uL vL aL
     ==> &1 / &5 < lcy cL sL uL vL aL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aL`)) THEN
  C1092MNCT_DATA_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MNCT_C @ C1092MNCT_L) C1092MPBEB_DIRECTED_FACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nx:real` (X_CHOOSE_THEN `ny:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC)))) THENL
   [ALL_TAC;
    MP_TAC(SPECL (C1092MNCT_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`;
                                 `nx:real`; `ny:real`]) C1092MNCT_LEFT_BOUNDARY) THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`;
                               `nx:real`; `ny:real`]) C1092MNCT_LEFT_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `c1092sbs_FaceNormal a b c d`) o concl)) THEN
  REWRITE_TAC[c1092sbs_FaceNormal] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  TRY ASM_REAL_ARITH_TAC THEN
  MP_TAC(SPECL (C1092MNCT_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`]) C1092MNCT_LEFT_CENTRAL) THEN
  ASM_REWRITE_TAC[]);;
