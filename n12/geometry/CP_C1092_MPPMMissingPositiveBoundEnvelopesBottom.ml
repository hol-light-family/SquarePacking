(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingPositiveBoundEnvelopesBottom  *)
(* .lean (namespace N12Compact.C1092MPPMMissingPositiveBoundaries).  The     *)
(* actual bottom-square envelope.  Squares C, B are cC sC uC vC aC and       *)
(* cB sB uB vB aB (A, B in directed_faces: cA .., cB ..).  Data C:           *)
(* c1092mpbp_data; profile: C1092MPBP_PROFILE / C1092MPBES_FACTS;            *)
(* Envelopes.margins / bottomGap: C1092MPBES_MARGINS / c1092mpbes_bottomGap; *)
(* b: c1092scs_b; arc: C1092SCS_ARC; FaceNormal / bottom_center /            *)
(* width_bounds / bottom_face: c1092sbs_FaceNormal / C1092SBS_*;             *)
(* negative_support: C1092MCSUP_NEGATIVE_SUPPORT; faceSeparation_of_disjoint *)
(* with separated / parallel_radius / transverse_radius: ABT_FOUR_AXES;      *)
(* upper / lower: ABT_upper / ABT_lower.  The local cone and central of      *)
(* bottom_order are literally the C1092ShallowBottomOrder ones               *)
(* (C1092SBO_CONE, C1092SBO_CENTRAL).  Unit normals / positive sides of the  *)
(* OpenSquares are explicit hypotheses.  Tag C1092MPBEB_.                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundEnvelopesScalars.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_ShallowBottomOrder.ml";;

let C1092MPBEB_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;
let C1092MPBEB_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MPBEB_LIN; ALL_TAC];;

(* Lean: Envelopes.face_neg *)
let C1092MPBEB_FACE_NEG = prove
 (`forall cq sq x y. c1092sbs_FaceNormal cq sq x y ==> c1092sbs_FaceNormal cq sq (--x) (--y)`,
  REWRITE_TAC[c1092sbs_FaceNormal] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* Lean: Envelopes.directed_faces *)
let C1092MPBEB_DIRECTED_FACES = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     aA = aB /\ ldisj cA sA uA vA aA cB sB uB vB aB
     ==> exists nx ny. nx pow 2 + ny pow 2 = &1 /\
                 (c1092sbs_FaceNormal cA sA nx ny \/ c1092sbs_FaceNormal cB sB nx ny) /\
                 ABT_upper cA sA uA vA aA nx ny <= ABT_lower cB sB uB vB aB nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  POP_ASSUM(fun th ->
    let args = snd(strip_comb(lhand(concl th))) in
    let nx = el 5 args and ny = el 6 args in
    if el 0 args = `cA:real` then
      MAP_EVERY EXISTS_TAC [nx; ny] THEN REWRITE_TAC[th]
    else
      MAP_EVERY EXISTS_TAC [mk_comb(`(--):real->real`, nx); mk_comb(`(--):real->real`, ny)] THEN
      REWRITE_TAC[MATCH_MP C1092TFSU_REVERSE th]) THEN
  REWRITE_TAC[c1092sbs_FaceNormal; REAL_NEG_NEG; REAL_POW_2; REAL_NEG_MUL2] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: Envelopes.northeast_coefficients *)
let C1092MPBEB_NORTHEAST_COEFFICIENTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ c1092mpbp_data c s u v a
     ==> --c + s + &7 / &50 - (&37 / &50) * s pow 2 < &0 /\
         &1 - c - s + (&37 / &50) * c * s < &0 /\
         &0 < c - s + (&11 / &25) * s pow 2 /\
         &0 < c + s - &1 - (&11 / &25) * c * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPBES_SETUP_TAC THEN
  C1092MPBEB_PROD `&0 < c * s` THEN
  SUBGOAL_THEN `c + s <= &3 / &2` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  C1092MPBEB_PROD `&0 <= (c - s) * (&1 - (&37 / &100) * (c + s))` THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092SCS_ARC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MPBEB_PROD `&0 < s * s` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092MPBEB_LIN);;

let C1092MPBEB_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MPBEB_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;

(* Lean: northeast (local of bottom_order) *)
let C1092MPBEB_NORTHEAST = prove
 (`forall cC sC uC vC aC cB sB uB vB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &1 < aC /\
     c1092mpbp_data cC sC uC vC aC /\
     linside cB sB uB vB aC (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aC (--(&2 / &5)) (--(&1)) /\
     nx pow 2 + ny pow 2 = &1 /\ &0 <= nx
     ==> ~(ABT_upper cB sB uB vB aC nx ny <= ABT_lower cC sC uC vC aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mpbp_data] (ASSUME `c1092mpbp_data cC sC uC vC aC`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C1092MPBEB_NORTHEAST_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPBES_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPBEB_C @ C1092MPBEB_B @ [`nx:real`; `ny:real`]) C1092SBO_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MPBEB_PROD `&0 <= cC * nx` THEN C1092MPBEB_PROD `&0 < sC * ny` THEN
  C1092MPBEB_PROD `&0 <= (cC - sC) * ny` THEN C1092MPBEB_PROD `&0 < sC * (ny - nx)` THEN
  SUBGOAL_THEN `&0 < nx * cC + ny * sC /\ &0 < --nx * sC + ny * cC` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MPBEB_LIN; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPBEB_C @ [`nx:real`; `ny:real`; `nx * cC + ny * sC`;
                                `--nx * sC + ny * cC`]) C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MPBEB_LIN; DISCH_TAC] THEN
  C1092MPBEB_PROD `&0 <= (nx * cC + ny * sC) * ((--(&13 / &50) * cC - aC) - uC)` THEN
  C1092MPBEB_PROD `&0 <= (--nx * sC + ny * cC) * ((sC - aC) - vC)` THEN
  C1092MPBEB_PROD `&0 < (aC - &1) * ((nx * cC + ny * sC) + (--nx * sC + ny * cC))` THEN
  C1092MPBEB_PROD `&0 <= nx * --(--cC + sC + &7 / &50 - (&37 / &50) * sC pow 2)` THEN
  C1092MPBEB_PROD `&0 < ny * --(&1 - cC - sC + (&37 / &50) * cC * sC)` THEN
  SUBGOAL_THEN
   `(nx * cC + ny * sC) * (--(&13 / &50) * cC - &1) + (--nx * sC + ny * cC) * (sC - &1) -
    (--(&2 / &5) * nx - ny) =
    nx * (--cC + sC + &7 / &50 - (&37 / &50) * sC pow 2) +
    ny * (&1 - cC - sC + (&37 / &50) * cC * sC)` ASSUME_TAC THENL
   [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPBEB_B @ [`--(&2 / &5)`; `--(&1)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MPBEB_LIN);;

(* Lean: boundary (local of bottom_order) *)
let C1092MPBEB_BOUNDARY = prove
 (`forall cC sC uC vC aC cB sB uB vB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &1 < aC /\
     aC <= &1001 / &1000 /\ c1092mpbp_data cC sC uC vC aC /\
     linside cB sB uB vB aC (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aC (--(&2 / &5)) (--(&1)) /\
     (forall x y. linside cB sB uB vB aC x y ==> --(&2) <= y) /\
     lcx cB sB uB vB aC < c1092scs_b aC cC sC (vC + aC) /\
     nx pow 2 + ny pow 2 = &1 /\ c1092sbs_FaceNormal cB sB nx ny
     ==> ~(ABT_upper cB sB uB vB aC nx ny <= ABT_lower cC sC uC vC aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= nx` THENL
   [MATCH_MP_TAC C1092MPBEB_NORTHEAST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mpbp_data] (ASSUME `c1092mpbp_data cC sC uC vC aC`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPBES_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPBEB_C @ C1092MPBEB_B @ [`nx:real`; `ny:real`]) C1092SBO_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--nx`; `ny:real`]
    C1092SBS_BOTTOM_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN C1092MPBEB_LIN;
    DISCH_THEN(LABEL_TAC "bf" o REWRITE_RULE[REAL_NEG_NEG])] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--nx`; `ny:real`]
    C1092MPBES_MARGINS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
    REPEAT C1092MPBEB_LIN;
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN `&0 < sC * --nx + cC * ny` ASSUME_TAC THENL
   [C1092MPBEB_PROD `&0 <= sC * --nx` THEN C1092MPBEB_PROD `&0 < cC * ny` THEN C1092MPBEB_LIN;
    ALL_TAC] THEN
  C1092MPBEB_PROD `&0 < --nx * (c1092scs_b aC cC sC (vC + aC) - lcx cB sB uB vB aC)` THEN
  UNDISCH_TAC `&0 <= c1092mpbes_bottomGap aC cC sC (uC + aC) (vC + aC) (--nx) ny` THEN
  REWRITE_TAC[c1092mpbes_bottomGap] THEN
  ASM_CASES_TAC `&0 <= sC * ny - cC * --nx` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`] THEN
    MP_TAC(SPECL (C1092MPBEB_C @ [`nx:real`; `ny:real`; `sC * ny - cC * --nx`;
                                  `sC * --nx + cC * ny`]) C1092WS_LOWER_NN);
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= d) ==> max d (&0) = &0`] THEN
    MP_TAC(SPECL (C1092MPBEB_C @ [`nx:real`; `ny:real`; `sC * ny - cC * --nx`;
                                  `sC * --nx + cC * ny`]) C1092WS_LOWER_NP)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT C1092MPBEB_LIN; ALL_TAC]) THEN
  UNDISCH_TAC `ABT_upper cB sB uB vB aC nx ny <= ABT_lower cC sC uC vC aC nx ny` THEN
  REMOVE_THEN "bf" MP_TAC THEN
  UNDISCH_TAC `&0 < --nx * (c1092scs_b aC cC sC (vC + aC) - lcx cB sB uB vB aC)` THEN
  REAL_ARITH_TAC);;

(* Lean: bottom_order *)
let C1092MPBEB_BOTTOM_ORDER = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ aC <= &1001 / &1000 /\ aC = aB /\ c1092mpbp_data cC sC uC vC aC /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
     (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> c1092scs_b aC cC sC (vC + aC) <= lcx cB sB uB vB aB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mpbp_data] (ASSUME `c1092mpbp_data cC sC uC vC aC`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPBES_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPBEB_B @ C1092MPBEB_C) C1092MPBEB_DIRECTED_FACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ldisj cC sC uC vC aC cB sB uB vB aC` THEN
    REWRITE_TAC[ldisj] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nx:real` (X_CHOOSE_THEN `ny:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC)))) THENL
   [MP_TAC(SPECL (C1092MPBEB_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`;
                                  `nx:real`; `ny:real`]) C1092MPBEB_BOUNDARY) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `c1092sbs_FaceNormal a b c d`) o concl)) THEN
  REWRITE_TAC[c1092sbs_FaceNormal] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [MP_TAC(SPECL (C1092MPBEB_C @ C1092MPBEB_B @ [`cC:real`; `sC:real`]) C1092SBO_CONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MPBEB_LIN;
    MP_TAC(SPECL (C1092MPBEB_C @ C1092MPBEB_B @ [`--cC`; `--sC`]) C1092SBO_CONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MPBEB_LIN;
    MP_TAC(SPECL (C1092MPBEB_C @ [`cB:real`; `sB:real`; `uB:real`; `vB:real`]) C1092SBO_CENTRAL) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL (C1092MPBEB_C @ C1092MPBEB_B @ [`sC:real`; `--cC`]) C1092SBO_CONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MPBEB_LIN]);;
