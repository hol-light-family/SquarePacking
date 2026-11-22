(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveNegativeRetaining.lean       *)
(* (namespace N12Compact.C1092MPPMPositiveNegativeRetaining).                *)
(* POSITIVE-NEGATIVE-RETAINING-SHALLOW Theorem 1.  Squares C E R are the     *)
(* tuples cC sC uC vC aC, cE .., cR ..; Input / Profile are the predicates  *)
(* c1092pnrsup_input / c1092pnrsup_profile (Support file).                  *)
(* WallProfile.vertex / strict_closed_segment: OCWPVG_VERTEX /               *)
(* OCWPVG_STRICT_CLOSED_SEGMENT; ClosedPointExclusion.outside_of_closed:     *)
(* OUTSIDE_OF_CLOSED; Scalars.preliminary / sharpen: C1092PNRS_PRELIMINARY / *)
(* C1092PNRS_SHARPEN.  The local abbreviations X, Y, z of the Lean proof are *)
(* the arguments of the helper lemmas C1092PNR_CLEARANCE_*.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveNegativeRetainingSupport.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;

(* the common opening: Input unfolded, negative / height_envelope / next_face,
   normal bounds and Scalars.preliminary *)
let C1092PNR_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092PNRSUP_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092PNRSUP_HEIGHT_ENVELOPE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092PNRSUP_NEXT_FACE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pnrsup_input] o
    check (can (term_match [] `c1092pnrsup_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_successorFaces] o
    check (can (term_match [] `c1092anc_successorFaces a b c d e`) o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`cE:real`; `--sE`; `--uE`] C1092PNRS_PRELIMINARY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `linside cE sE uE vE aE (&0) (--(&13 / &50))` THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; STRIP_TAC];;

(* the tail of right_clearance for X > 1, with z = (X - 1) / X *)
let C1092PNR_CLEARANCE_SEGMENT = prove
 (`forall cE sE uE vE aE cR sR uR vR aR X Y z.
     lclosed cE sE uE vE aE X Y /\ linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     &0 < z /\ z < &1 /\ z * X = X - &1 /\ --(&23 / &50) < Y /\ Y < &0 /\
     ldisj cE sE uE vE aE cR sR uR vR aR /\
     (forall y. --(&14 / &25) <= y ==> y <= &0 ==> linside cR sR uR vR aR (&1) y)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `X:real`; `Y:real`;
                `&0`; `--(&13 / &50)`; `z:real`] OCWPVG_STRICT_CLOSED_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 - z) * X + z * &0 = &1` SUBST1_TAC THENL
   [UNDISCH_TAC `z * X = X - &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - z) * Y + z * --(&13 / &50)` o check (is_forall o concl)) THEN
  SUBGOAL_THEN `&0 <= (&1 - z) * (Y + &14 / &25) /\ &0 <= (&1 - z) * --Y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ANTS_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `ldisj cE sE uE vE aE cR sR uR vR aR` THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&1`; `(&1 - z) * Y + z * --(&13 / &50)`]) THEN
  ASM_REWRITE_TAC[]);;

(* right_clearance in terms of the closed vertex (X, Y) *)
let C1092PNR_CLEARANCE_CORE = prove
 (`forall cE sE uE vE aE cR sR uR vR aR X Y.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ &0 < cE /\ &0 < --sE /\
     lclosed cE sE uE vE aE X Y /\ --(&23 / &50) < Y /\
     cE * Y = (vE + aE) + sE * X /\ vE + aE <= --sE / &2 /\
     linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     ldisj cE sE uE vE aE cR sR uR vR aR /\
     (forall y. --(&14 / &25) <= y ==> y <= &0 ==> linside cR sR uR vR aR (&1) y)
     ==> X < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`--sE`; `&1`; `X:real`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `cE * Y < &0` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `Y < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cE:real`; `Y:real`] REAL_LE_MUL) THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `X = &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `&1`; `Y:real`]
      OUTSIDE_OF_CLOSED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ldisj cE sE uE vE aE cR sR uR vR aR` THEN
      REWRITE_TAC[ldisj] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Y:real` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < X` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC C1092PNR_CLEARANCE_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                        `X:real`; `Y:real`; `(X - &1) / X`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < X /\ &0 < X - &1` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  RASM_ARITH_TAC);;

(* Lean: right_clearance *)
let C1092PNR_RIGHT_CLEARANCE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092pnrsup_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR
     ==> cE * (uE + aE) - sE * (vE + aE) < &1`,
  C1092PNR_SETUP_TAC THEN
  MATCH_MP_TAC C1092PNR_CLEARANCE_CORE THEN
  MAP_EVERY EXISTS_TAC [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                        `sE * (uE + aE) + cE * (vE + aE)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [RASM_ARITH_TAC;
    MATCH_MP_TAC OCWPVG_VERTEX THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    C1092PRS_PROD `&0 <= cE * ((vE + aE) - (aE - cE))` THEN
    C1092PRS_PROD `&0 <= --sE * ((cE - sE) - (uE + aE))` THEN
    C1092PRS_PROD `&0 < (aE - &1) * cE` THEN
    C1092PRS_PROD `&0 <= (&1 - cE) * --sE` THEN
    NLIN_TAC ~deg2:false [];
    UNDISCH_TAC `cE * cE + sE * sE = &1` THEN CONV_TAC REAL_RING]);;

(* Lean: height_lower *)
let C1092PNR_HEIGHT_LOWER = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092pnrsup_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR
     ==> cE - sE - &1 + cE * sE < cE * --uE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(UNDISCH(SPEC_ALL C1092PNR_RIGHT_CLEARANCE)) THEN
  UNDISCH_TAC (lhand(snd(strip_forall(concl C1092PNR_RIGHT_CLEARANCE)))) THEN
  C1092PNR_SETUP_TAC THEN DISCH_TAC THEN
  C1092PRS_PROD `&0 <= --sE * (vE - --cE)` THEN
  C1092PRS_PROD `&0 < (aE - &1) * (cE - sE)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: profile *)
let C1092PNR_PROFILE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092pnrsup_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR
     ==> c1092pnrsup_profile cE sE uE vE aE`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(UNDISCH(SPEC_ALL C1092PNR_HEIGHT_LOWER)) THEN
  UNDISCH_TAC (lhand(snd(strip_forall(concl C1092PNR_HEIGHT_LOWER)))) THEN
  C1092PNR_SETUP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cE:real`; `--sE`; `--uE`] C1092PNRS_SHARPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092PNRS_LP_TAC; STRIP_TAC] THEN
  REWRITE_TAC[c1092pnrsup_profile] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < cE` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN RASM_ARITH_TAC);;
