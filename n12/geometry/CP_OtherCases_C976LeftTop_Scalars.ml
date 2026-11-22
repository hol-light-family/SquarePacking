(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/Scalars.lean             *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.Scalars).  C976-LEFT-TOP-   *)
(* ANGLE sections 6-7: half-angle domains and the reduction of the two       *)
(* support residuals to the bivariate quartics.  half is C1092WPS_half;      *)
(* quarter_data is C1092WPS_QUARTER_DATA.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Polynomials.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let C976LTS_LIN = NLIN_TAC ~deg2:false [];;

let C976LTS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C976LTS_LIN; ALL_TAC];;

let C976LTS_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

(* Lean: alpha, beta, a0, b0, k0 (definitions) *)
let c976lts_alpha = new_definition
 `c976lts_alpha (l:real) (h:real) (C:real) (S:real) = l * C + h * S`;;
let c976lts_beta = new_definition
 `c976lts_beta (l:real) (h:real) (C:real) (S:real) = l * S - h * C`;;
let c976lts_a0 = new_definition
 `c976lts_a0 (l:real) (h:real) = (&13 / &100) * l + (&6 / &25) * h`;;
let c976lts_b0 = new_definition
 `c976lts_b0 (l:real) (h:real) = (&6 / &25) * l - (&13 / &100) * h`;;
let c976lts_k0 = new_definition
 `c976lts_k0 (C:real) (S:real) = (&13 / &100) * S - (&6 / &25) * C`;;

(* Lean: Elo (definition) *)
let c976lts_Elo = new_definition
 `c976lts_Elo l h C S =
    S * ((c976lts_alpha l h C S + c976lts_beta l h C S) * c976lts_a0 l h -
         (&39 / &625) * c976lts_alpha l h C S +
         c976lts_k0 C S * (--(&27 / &100) * h - (&1 / &25) * l)) +
    c976lts_a0 l h * (C pow 2 - (&63 / &50) * C * S + C + S - &2)`;;

(* Lean: Ehi (definition) *)
let c976lts_Ehi = new_definition
 `c976lts_Ehi l h C S =
    S * ((c976lts_alpha l h C S + c976lts_beta l h C S) * c976lts_a0 l h -
         (&39 / &625) * c976lts_alpha l h C S + c976lts_k0 C S * (l - &1)) +
    c976lts_a0 l h * (C pow 2 - (&63 / &50) * C * S + C + S - &2)`;;

(* half-angle data of (c, s), with the half angle generalized to z *)
let C976LTS_HALF_TAC c s z =
  MP_TAC(SPECL [c; s] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
  SPEC_TAC(list_mk_comb(`C1092WPS_half`,[c; s]), z) THEN GEN_TAC THEN
  REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC;;

(* Lean: left_domain *)
let C976LTS_LEFT_DOMAIN = prove
 (`forall l h. &0 < l /\ &0 <= h /\ l pow 2 + h pow 2 = &1 /\ (&1 / &3) * l <= h /\
         &1 < (&26 / &25) * l + (&27 / &100) * h
         ==> &4 / &25 <= C1092WPS_half l h /\ C1092WPS_half l h <= &53 / &163`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C976LTS_HALF_TAC `l:real` `h:real` `r:real` THEN
  C976LTS_PROD `&0 <= r * r` THEN
  C976LTS_PROD `&0 <= (&1 + r * r) * (&3 * h - l)` THEN
  C976LTS_PROD `&0 < (&1 + r * r) * ((&26 / &25) * l + (&27 / &100) * h - &1)` THEN
  CONJ_TAC THEN C976LTS_CONTRA THENL
   [C976LTS_PROD `&0 <= (&4 / &25 - r) * (&4 / &25 + r)` THEN C976LTS_LIN;
    C976LTS_PROD `&0 <= (r - &53 / &163) * (&102 * (r + &53 / &163) - &27)` THEN C976LTS_LIN]);;

(* Lean: right_domain (private) *)
let C976LTS_RIGHT_DOMAIN = prove
 (`forall C S. &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\ C <= (&2 / &3) * S
         ==> &0 <= C1092WPS_half S C /\ C1092WPS_half S C <= &10 / &33`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `S pow 2 + C pow 2 = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C976LTS_HALF_TAC `S:real` `C:real` `w:real` THEN
  ASM_REWRITE_TAC[] THEN
  C976LTS_PROD `&0 <= w * w` THEN
  C976LTS_PROD `&0 <= (&1 + w * w) * (&2 * S - &3 * C)` THEN
  C976LTS_CONTRA THEN
  C976LTS_PROD `&0 < (w - &10 / &33) * (w + &10 / &33 + &3)` THEN C976LTS_LIN);;

(* Lean: low_domain *)
let C976LTS_LOW_DOMAIN = prove
 (`forall C S. &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\ &0 <= c976lts_k0 C S
         ==> C1092WPS_half S C <= &13 / &50`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c976lts_k0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `S pow 2 + C pow 2 = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C976LTS_HALF_TAC `S:real` `C:real` `w:real` THEN
  C976LTS_PROD `&0 <= w * w` THEN
  C976LTS_PROD `&0 <= (&1 + w * w) * ((&13 / &100) * S - (&6 / &25) * C)` THEN
  C976LTS_CONTRA THEN
  C976LTS_PROD `&0 <= (w - &13 / &50) * (w + &13 / &50)` THEN C976LTS_LIN);;

(* Lean: high_domain *)
let C976LTS_HIGH_DOMAIN = prove
 (`forall C S. &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\ c976lts_k0 C S <= &0
         ==> &1 / &4 <= C1092WPS_half S C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c976lts_k0] THEN STRIP_TAC THEN
  SUBGOAL_THEN `S pow 2 + C pow 2 = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C976LTS_HALF_TAC `S:real` `C:real` `w:real` THEN
  C976LTS_PROD `&0 <= w * w` THEN
  C976LTS_PROD `&0 <= (&1 + w * w) * --((&13 / &100) * S - (&6 / &25) * C)` THEN
  C976LTS_CONTRA THEN
  C976LTS_PROD `&0 <= (&1 / &4 - w) * (&1 / &4 + w)` THEN C976LTS_LIN);;

(* Lean: fraction_forms (private) *)
let C976LTS_FRACTION_FORMS = prove
 (`forall c s t. (&1 + t pow 2) * c = &1 - t pow 2 /\ (&1 + t pow 2) * s = &2 * t
           ==> c = (&1 - t pow 2) / (&1 + t pow 2) /\ s = (&2 * t) / (&1 + t pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + t pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let C976LTS_IDENTITY_TAC defs =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `h:real`; `r:real`] C976LTS_FRACTION_FORMS) THEN
  MP_TAC(SPECL [`S:real`; `C:real`; `w:real`] C976LTS_FRACTION_FORMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC defs THEN
  SUBGOAL_THEN `&0 < &1 + r pow 2 /\ &0 < &1 + w pow 2` MP_TAC THENL
   [MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD;;

(* Lean: lo_identity *)
let C976LTS_LO_IDENTITY = prove
 (`forall l h C S r w.
     (&1 + r pow 2) * l = &1 - r pow 2 /\ (&1 + r pow 2) * h = &2 * r /\
     (&1 + w pow 2) * C = &2 * w /\ (&1 + w pow 2) * S = &1 - w pow 2
     ==> (&10000 * (&1 + r pow 2) pow 2 * (&1 + w pow 2) pow 2) * c976lts_Elo l h C S =
         c976ltp_Plo r w`,
  C976LTS_IDENTITY_TAC [c976lts_Elo; c976lts_alpha; c976lts_beta; c976lts_a0; c976lts_k0;
                        c976ltp_Plo]);;

(* Lean: hi_identity *)
let C976LTS_HI_IDENTITY = prove
 (`forall l h C S r w.
     (&1 + r pow 2) * l = &1 - r pow 2 /\ (&1 + r pow 2) * h = &2 * r /\
     (&1 + w pow 2) * C = &2 * w /\ (&1 + w pow 2) * S = &1 - w pow 2
     ==> (&10000 * (&1 + r pow 2) pow 2 * (&1 + w pow 2) pow 2) * c976lts_Ehi l h C S =
         c976ltp_Phi r w`,
  C976LTS_IDENTITY_TAC [c976lts_Ehi; c976lts_alpha; c976lts_beta; c976lts_a0; c976lts_k0;
                        c976ltp_Phi]);;

let C976LTS_POS_OF_MUL = prove
 (`forall x k. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let C976LTS_POSITIVE_TAC domain poly identity =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `h:real`] C976LTS_LEFT_DOMAIN) THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C976LTS_RIGHT_DOMAIN) THEN
  MP_TAC(SPECL [`C:real`; `S:real`] domain) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`C1092WPS_half l h`; `C1092WPS_half S C`] poly) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`l:real`; `h:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`S:real`; `C:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`l:real`; `h:real`; `C:real`; `S:real`;
                `C1092WPS_half l h`; `C1092WPS_half S C`] identity) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC C976LTS_POS_OF_MUL THEN
  EXISTS_TAC `&10000 * (&1 + C1092WPS_half l h pow 2) pow 2 *
              (&1 + C1092WPS_half S C pow 2) pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC REAL_POW_LT) THEN
  MP_TAC(SPEC `C1092WPS_half l h` REAL_LE_POW_2) THEN
  MP_TAC(SPEC `C1092WPS_half S C` REAL_LE_POW_2) THEN REAL_ARITH_TAC;;

(* Lean: lo_positive *)
let C976LTS_LO_POSITIVE = prove
 (`forall l h C S. &0 < l /\ &0 <= h /\ l pow 2 + h pow 2 = &1 /\ (&1 / &3) * l <= h /\
             h < (&8 / &11) * l /\ &1 < (&26 / &25) * l + (&27 / &100) * h /\
             &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\ C <= (&2 / &3) * S /\
             &0 <= c976lts_k0 C S
             ==> &0 < c976lts_Elo l h C S`,
  C976LTS_POSITIVE_TAC C976LTS_LOW_DOMAIN C976LTP_LO_POSITIVE C976LTS_LO_IDENTITY);;

(* Lean: hi_positive *)
let C976LTS_HI_POSITIVE = prove
 (`forall l h C S. &0 < l /\ &0 <= h /\ l pow 2 + h pow 2 = &1 /\ (&1 / &3) * l <= h /\
             h < (&8 / &11) * l /\ &1 < (&26 / &25) * l + (&27 / &100) * h /\
             &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\ C <= (&2 / &3) * S /\
             c976lts_k0 C S <= &0
             ==> &0 < c976lts_Ehi l h C S`,
  C976LTS_POSITIVE_TAC C976LTS_HIGH_DOMAIN C976LTP_HI_POSITIVE C976LTS_HI_IDENTITY);;
