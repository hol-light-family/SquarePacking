(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingPositiveBoundEnvelopes.lean   *)
(* (namespace N12Compact.C1092MPPMMissingPositiveBoundaries).  The second    *)
(* actual boundary envelope and the strict same-face center sum ("Written    *)
(* source only").  Squares C, B, L are cC sC uC vC aC, cB .., cL ..; unit    *)
(* normals / positive sides explicit.  Data C: c1092mpbp_data; profile:      *)
(* C1092MPBES_FACTS; Envelopes.margins / leftGap: C1092MPBES_MARGINS /       *)
(* c1092mpbes_leftGap; directed_faces / northeast_coefficients / bottom_order*)
(* : C1092MPBEB_*; ell / same_face_sum: c1092scs_ell / C1092SCS_SAME_FACE_SUM*)
(* ; left_center / width_bounds / left_face / FaceNormal / width0:           *)
(* C1092SBS_* / c1092sbs_*; upper_nn: C1092MCSUP_UPPER_NN; upper_np:         *)
(* C1092WS_UPPER_NP.  Tag C1092MPBE_.                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundEnvelopesBottom.ml";;

let C1092MPBE_LIN = C1092MPBEB_LIN;;
let C1092MPBE_PROD = C1092MPBEB_PROD;;
let C1092MPBE_C = C1092MPBEB_C;;
let C1092MPBE_L = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`];;
let C1092MPBE_DATA_TAC =
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092mpbp_data] (ASSUME `c1092mpbp_data cC sC uC vC aC`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPBES_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* Lean: cone (local of left_order) *)
let C1092MPBE_CONE = prove
 (`forall cC sC uC vC aC cL sL uL vL aL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&0) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aL nx ny
     ==> &0 < ny /\ nx < (&175 / &368) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&7 / &20)`,`--(&7 / &20)`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&1)`,`--(&13 / &50)`);
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`], (`--(&543 / &500)`,`&0`);
    [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`], (`--(&1)`,`&0`)] THEN
  C1092MPBE_LIN);;

(* Lean: central (local of left_order) *)
let C1092MPBE_CENTRAL = prove
 (`forall cC sC uC vC aC cL sL uL vL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\
     c977cc_normal cC sC /\ &0 < cC /\ &0 < sC /\
     (forall x y. linside cL sL uL vL aC x y ==> --(&2) <= x) /\
     lcy cL sL uL vL aC < c1092scs_ell aC cC sC (vC + aC)
     ==> ~(ABT_upper cC sC uC vC aC (--sC) cC <= ABT_lower cL sL uL vL aC (--sC) cC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MPBE_C ABT_OWNV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`] C1092SBS_LEFT_CENTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`; `cC:real`; `sC:real`]
    C1092SBS_WIDTH_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cC * c1092scs_ell aC cC sC (vC + aC) =
                (vC + aC) - &2 * sC + (aC / &2) * (&1 + sC * (cC + sC))` ASSUME_TAC THENL
   [REWRITE_TAC[c1092scs_ell] THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C1092MPBE_LIN;
    ALL_TAC] THEN
  C1092MPBE_PROD `&0 <= sC * (lcx cL sL uL vL aC - (--(&2) + aC * c1092sbs_width0 cL sL / &2))` THEN
  C1092MPBE_PROD `&0 < cC * (c1092scs_ell aC cC sC (vC + aC) - lcy cL sL uL vL aC)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ABT_lower]) THEN C1092MPBE_LIN);;

(* Lean: northeast (local of left_order) *)
let C1092MPBE_NORTHEAST = prove
 (`forall cC sC uC vC aC cL sL uL vL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     c1092mpbp_data cC sC uC vC aC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aC (--(&1)) (&0) /\
     nx pow 2 + ny pow 2 = &1 /\ &0 <= nx
     ==> ~(ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN C1092MPBE_DATA_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C1092MPBEB_NORTHEAST_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPBE_C @ C1092MPBE_L @ [`nx:real`; `ny:real`]) C1092MPBE_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MPBE_PROD `&0 <= cC * nx` THEN C1092MPBE_PROD `&0 < sC * ny` THEN
  C1092MPBE_PROD `&0 <= (cC - sC) * ny` THEN C1092MPBE_PROD `&0 < sC * (ny - nx)` THEN
  SUBGOAL_THEN `&0 < nx * cC + ny * sC /\ &0 < --nx * sC + ny * cC` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092MPBE_LIN; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPBE_C @ [`nx:real`; `ny:real`; `nx * cC + ny * sC`;
                               `--nx * sC + ny * cC`]) C1092MCSUP_UPPER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MPBE_LIN; DISCH_TAC] THEN
  C1092MPBE_PROD `&0 <= (nx * cC + ny * sC) * ((uC + aC) - (aC - cC - sC))` THEN
  C1092MPBE_PROD `&0 <= (--nx * sC + ny * cC) * ((vC + aC) - (aC + (&14 / &25) * sC - cC))` THEN
  C1092MPBE_PROD `&0 < (aC - &1) * ((nx * cC + ny * sC) + (--nx * sC + ny * cC))` THEN
  C1092MPBE_PROD `&0 <= nx * (cC - sC + (&11 / &25) * sC pow 2)` THEN
  C1092MPBE_PROD `&0 < ny * (cC + sC - &1 - (&11 / &25) * cC * sC)` THEN
  SUBGOAL_THEN
   `(nx * cC + ny * sC) * (&1 - cC - sC) + (--nx * sC + ny * cC) * (&1 + (&14 / &25) * sC - cC) + nx =
    nx * (cC - sC + (&11 / &25) * sC pow 2) + ny * (cC + sC - &1 - (&11 / &25) * cC * sC)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPBE_L @ [`--(&1)`; `&0`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MPBE_LIN);;

(* Lean: boundary (local of left_order) *)
let C1092MPBE_BOUNDARY = prove
 (`forall cC sC uC vC aC cL sL uL vL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     aC <= &1001 / &1000 /\ c1092mpbp_data cC sC uC vC aC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aC (--(&1)) (&0) /\
     (forall x y. linside cL sL uL vL aC x y ==> --(&2) <= x) /\
     lcy cL sL uL vL aC < c1092scs_ell aC cC sC (vC + aC) /\
     nx pow 2 + ny pow 2 = &1 /\ c1092sbs_FaceNormal cL sL nx ny
     ==> ~(ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= nx` THENL
   [MATCH_MP_TAC C1092MPBE_NORTHEAST THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN C1092MPBE_DATA_TAC THEN
  MP_TAC(SPECL (C1092MPBE_C @ C1092MPBE_L @ [`nx:real`; `ny:real`]) C1092MPBE_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`; `--nx`; `ny:real`]
    C1092SBS_LEFT_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN C1092MPBE_LIN;
    DISCH_THEN(LABEL_TAC "lf" o REWRITE_RULE[REAL_NEG_NEG])] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--nx`; `ny:real`]
    C1092MPBES_MARGINS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
    REPEAT C1092MPBE_LIN;
    DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  SUBGOAL_THEN `&0 < sC * --nx + cC * ny` ASSUME_TAC THENL
   [C1092MPBE_PROD `&0 <= sC * --nx` THEN C1092MPBE_PROD `&0 < cC * ny` THEN C1092MPBE_LIN;
    ALL_TAC] THEN
  C1092MPBE_PROD `&0 < ny * (c1092scs_ell aC cC sC (vC + aC) - lcy cL sL uL vL aC)` THEN
  UNDISCH_TAC `&0 <= c1092mpbes_leftGap aC cC sC (uC + aC) (vC + aC) (--nx) ny` THEN
  REWRITE_TAC[c1092mpbes_leftGap] THEN
  ASM_CASES_TAC `&0 <= sC * ny - cC * --nx` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max (--d) (&0) = &0`;
                 REAL_ARITH `&0 <= s * t - c * h ==> max (c * h - s * t) (&0) = &0`] THEN
    MP_TAC(SPECL (C1092MPBE_C @ [`nx:real`; `ny:real`; `sC * ny - cC * --nx`;
                                 `sC * --nx + cC * ny`]) C1092MCSUP_UPPER_NN);
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= s * t - c * h) ==> max (c * h - s * t) (&0) = c * h - s * t`] THEN
    MP_TAC(SPECL (C1092MPBE_C @ [`nx:real`; `ny:real`; `sC * ny - cC * --nx`;
                                 `sC * --nx + cC * ny`]) C1092WS_UPPER_NP)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT C1092MPBE_LIN; ALL_TAC]) THEN
  UNDISCH_TAC `ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny` THEN
  REMOVE_THEN "lf" MP_TAC THEN
  UNDISCH_TAC `&0 < ny * (c1092scs_ell aC cC sC (vC + aC) - lcy cL sL uL vL aC)` THEN
  REAL_ARITH_TAC);;

(* Lean: left_order *)
let C1092MPBE_LEFT_ORDER = prove
 (`forall cC sC uC vC aC cL sL uL vL aL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aC /\ aC <= &1001 / &1000 /\ aC = aL /\ c1092mpbp_data cC sC uC vC aC /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&0) /\
     (forall x y. linside cL sL uL vL aL x y ==> --(&2) <= x) /\
     ldisj cC sC uC vC aC cL sL uL vL aL
     ==> c1092scs_ell aC cC sC (vC + aC) <= lcy cL sL uL vL aL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aL`)) THEN
  C1092MPBE_DATA_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPBE_C @ C1092MPBE_L) C1092MPBEB_DIRECTED_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nx:real` (X_CHOOSE_THEN `ny:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC)))) THENL
   [ALL_TAC;
    MP_TAC(SPECL (C1092MPBE_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`;
                                 `nx:real`; `ny:real`]) C1092MPBE_BOUNDARY) THEN
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `c1092sbs_FaceNormal a b c d`) o concl)) THEN
  REWRITE_TAC[c1092sbs_FaceNormal] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [MP_TAC(SPECL (C1092MPBE_C @ C1092MPBE_L @ [`cC:real`; `sC:real`]) C1092MPBE_CONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MPBE_LIN;
    MP_TAC(SPECL (C1092MPBE_C @ C1092MPBE_L @ [`--cC`; `--sC`]) C1092MPBE_CONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MPBE_LIN;
    MP_TAC(SPECL (C1092MPBE_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`]) C1092MPBE_CENTRAL) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL (C1092MPBE_C @ C1092MPBE_L @ [`sC:real`; `--cC`]) C1092MPBE_CONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MPBE_LIN]);;

(* Lean: order *)
let C1092MPBE_ORDER = prove
 (`forall cC sC uC vC aC cB sB uB vB aB cL sL uL vL aL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aC /\ aC <= &1001 / &1000 /\ aC = aB /\ aC = aL /\ c1092mpbp_data cC sC uC vC aC /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
     (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
     linside cL sL uL vL aL (--(&1)) (&0) /\
     (forall x y. linside cL sL uL vL aL x y ==> --(&2) <= x) /\
     ldisj cC sC uC vC aC cB sB uB vB aB /\
     ldisj cC sC uC vC aC cL sL uL vL aL
     ==> &0 < lcx cB sB uB vB aB + lcy cL sL uL vL aL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092MPBEB_BOTTOM_ORDER) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] C1092MPBE_LEFT_ORDER) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPBES_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`aC:real`; `cC:real`; `sC:real`; `vC + aC`] C1092SCS_SAME_FACE_SUM) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
