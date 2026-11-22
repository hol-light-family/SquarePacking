(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardOuterFar.lean                  *)
(* (namespace N12Compact.C1092MPPMInwardOuterFar).  Complete local endings   *)
(* of OUTER-OWNED-INWARD-FAR-ENDING and CENTERED-OUTER-OWNED-FAR-ENDING.     *)
(* Squares C, E, R are cC sC uC vC aC, cE sE uE vE aE, cR sR uR vR aR.       *)
(* Normal: c977cc_normal; half: C1092WPS_half; NegativeSuccessor:            *)
(* c1092ifsu_negsucc; far_cap: C1092IOFB_FAR_CAP; successor_bottom /         *)
(* width_half / longitudinal_axes: C1092IFSU_*; relative_order:              *)
(* C1092MIFS_RELATIVE_ORDER; central_positive / alpha / recipientGap:        *)
(* C1092MIOF_CENTRAL_POSITIVE / c1092miof_*; lower_nn / formulas:            *)
(* C1092WS_*; lower / upper: ABT_lower / ABT_upper; the two recipient bounds *)
(* C1092MIOFE_*_RECIPIENT_POSITIVE.  Structure Input: c1092miofo_input       *)
(* (the OpenSquare unit normals / positive sides are explicit hypotheses).   *)
(* Tag C1092MIOFO_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOuterFarEndpoints.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOmittedFarBar.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessor.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOuterFarScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

(* Lean: Input (structure) *)
let c1092miofo_input = new_definition
 `c1092miofo_input (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                   (cE:real) (sE:real) (uE:real) (vE:real) (aE:real)
                   (cR:real) (sR:real) (uR:real) (vR:real) (aR:real) <=>
    &1 < aC /\
    c977cc_normal cC (--sC) /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
    --cC - (&13 / &50) * sC <= uC /\
    c1092ifsu_negsucc cE sE uE vE aE /\
    aC = aE /\
    ldisj cC sC uC vC aC cE sE uE vE aE /\
    ~linside cE sE uE vE aE (&0) (--(&1)) /\
    (forall y. --(&14 / &25) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
    ldisj cE sE uE vE aE cR sR uR vR aR`;;

let C1092MIOFO_LIN = NLIN_TAC ~deg2:false [];;

let C1092MIOFO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC THEN
   C1092MIOFO_LIN; ALL_TAC];;

(* Lean: far_profile *)
let C1092MIOFO_FAR_PROFILE = prove
 (`forall c s u v a cR sR uR vR aR.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092ifsu_negsucc c s u v a /\
     ~linside c s u v a (&0) (--(&1)) /\
     (forall y. --(&14 / &25) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
     ldisj c s u v a cR sR uR vR aR
     ==> --c <= v /\ v + a <= --s - (&14 / &25) * c /\
         &7 / &18 < C1092WPS_half c (--s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092IOFB_FAR_CAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal c (--s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[c1092ifsu_negsucc]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  SUBGOAL_THEN `v + a <= --s - &36 / &85 * c` ASSUME_TAC THENL
   [C1092MIOFO_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092IFSU_SUCCESSOR_BOTTOM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&11 / &25`; `c:real`; `--s`] C1092IFSU_WIDTH_HALF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092MIOFO_LIN;
    CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN REWRITE_TAC[]]);;

(* Lean: ending (private) *)
let C1092MIOFO_ENDING = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR eta.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092miofo_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR /\
     C1092WPS_half cC (--sC) <= &279 / &1000 /\ vC + aC <= eta /\
     &0 < c1092miof_recipientGap eta cC (--sC) cE (--sE)
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092miofo_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092MIOFO_FAR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (fun th -> concl th = `c1092ifsu_negsucc cE sE uE vE aC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE (--sE)`)) THEN
  (* kp, zp, margin *)
  SUBGOAL_THEN `&0 < cC * cE + sC * sE` ASSUME_TAC THENL
   [C1092MIOFO_PROD `&0 < cC * cE` THEN
    C1092MIOFO_PROD `&0 <= (--sC) * (--sE)` THEN C1092MIOFO_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sC * cE - cC * sE` ASSUME_TAC THENL
   [MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092MIFS_RELATIVE_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MIOFO_LIN; REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092MIOF_CENTRAL_POSITIVE) THEN
  ASM_REWRITE_TAC[c1092miof_centralGap; c1092miof_alpha] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092miof_recipientGap; c1092miof_alpha]) THEN
  C1092MIOFO_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) + (sC * cE - cC * sE))` THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092IFSU_LONGITUDINAL_AXES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                  `cC * cE + sC * sE`; `sC * cE - cC * sE`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN C1092MIOFO_LIN;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    C1092MIOFO_PROD `&0 <= (cC * cE + sC * sE) * ((cE - sE - aC) - uE)` THEN
    C1092MIOFO_PROD `&0 <= (sC * cE - cC * sE) * ((--sE - &14 / &25 * cE - aC) - vE)` THEN
    C1092MIOFO_LIN;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`]
      C1092WS_FORMULAS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `max (cE * cC + sE * sC) (&0) = cC * cE + sC * sE /\
                  max (--cE * sC + sE * cC) (&0) = &0` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `(&0 <= x /\ y = x) \/ (x <= &0 /\ y = &0)
                                            ==> max x (&0) = y`) THEN
      TRY(DISJ1_TAC THEN CONJ_TAC THENL [C1092MIOFO_LIN; REAL_ARITH_TAC]) THEN
      DISJ2_TAC THEN REWRITE_TAC[] THEN C1092MIOFO_LIN;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
    C1092MIOFO_PROD `&0 <= (cC * cE + sC * sE) * ((uC + aC) - (aC - cC + &13 / &50 * --sC))` THEN
    C1092MIOFO_PROD `&0 <= (sC * cE - cC * sE) * (eta - (vC + aC))` THEN
    C1092MIOFO_LIN]);;

(* Lean: missing_center_impossible *)
let C1092MIOFO_MISSING_CENTER_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092miofo_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR /\
     C1092WPS_half cC (--sC) <= &279 / &1000 /\ vC + aC <= &0
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SPEC `&0` (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
    `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
    `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092MIOFO_ENDING)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092miofo_input] o
    check (fun th -> is_comb(concl th) && fst(strip_comb(concl th)) = `c1092miofo_input`)) THEN
  SUBGOAL_THEN `&1 < aE` ASSUME_TAC THENL [C1092MIOFO_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092MIOFO_FAR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092MIOFE_MISSING_RECIPIENT_POSITIVE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[c1092ifsu_negsucc]);;

(* Lean: centered_impossible *)
let C1092MIOFO_CENTERED_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c1092miofo_input cC sC uC vC aC cE sE uE vE aE cR sR uR vR aR /\
     C1092WPS_half cC (--sC) <= &21 / &100 /\ vC + aC <= &17 / &125
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SPEC `&17 / &125` (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
    `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
    `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092MIOFO_ENDING)) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092miofo_input] o
    check (fun th -> is_comb(concl th) && fst(strip_comb(concl th)) = `c1092miofo_input`)) THEN
  SUBGOAL_THEN `&1 < aE` ASSUME_TAC THENL [C1092MIOFO_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C1092MIOFO_FAR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092MIOFE_CENTERED_RECIPIENT_POSITIVE THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[c1092ifsu_negsucc]);;
