(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalSuccessorScalars.lean     *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  The common successor        *)
(* comparisons of the two inward-final chapters.  Normal: c977cc_normal;     *)
(* CanonicalProjection.after: CCCP_AFTER.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;

(* Lean: alpha (definition) *)
let c1092mifss_alpha = new_definition
 `c1092mifss_alpha (beta:real) (c:real) (s:real) = &1 - c + beta * s`;;

(* Lean: P (definition) *)
let c1092mifss_P = new_definition
 `c1092mifss_P (d:real) (t:real) = &2 - d - t + (&49 / &85) * d * t`;;

(* Lean: Q (definition) *)
let c1092mifss_Q = new_definition
 `c1092mifss_Q (beta:real) (d:real) (t:real) =
    d - t + &36 / &85 - beta + (&49 / &85) * t pow 2`;;

(* Lean: FC (definition) *)
let c1092mifss_FC = new_definition
 `c1092mifss_FC (beta:real) (c:real) (s:real) (d:real) (t:real) =
    c1092mifss_alpha beta c s + (c * d + s * t) * (&1 - d - t) +
    (c * t - s * d) * (&1 - t + (&36 / &85) * d)`;;

(* Lean: FE (definition) *)
let c1092mifss_FE = new_definition
 `c1092mifss_FE (beta:real) (h:real) (c:real) (s:real) (d:real) (t:real) =
    &1 - d - t + (c * d + s * t) * c1092mifss_alpha beta c s + (c * t - s * d) * (&1 - h)`;;

(* Lean: FC_formula *)
let C1092MIFSS_FC_FORMULA = prove
 (`forall beta c s d t. d pow 2 + t pow 2 = &1
     ==> c1092mifss_FC beta c s d t =
         &1 - c * c1092mifss_P d t - s * c1092mifss_Q beta d t`,
  REWRITE_TAC[c1092mifss_FC; c1092mifss_alpha; c1092mifss_P; c1092mifss_Q] THEN
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

(* Lean: FE_formula *)
let C1092MIFSS_FE_FORMULA = prove
 (`forall beta h c s d t.
     c1092mifss_FE beta h c s d t =
     &1 - (&1 + (&1 - h) * s - c * c1092mifss_alpha beta c s) * d -
     (&1 - (&1 - h) * c - s * c1092mifss_alpha beta c s) * t`,
  REWRITE_TAC[c1092mifss_FE] THEN REAL_ARITH_TAC);;

(* Lean: coordinates_after *)
let C1092MIFSS_COORDINATES_AFTER = prove
 (`forall d t d0 t0. c977cc_normal d t /\ c977cc_normal d0 t0 /\ t0 * d <= d0 * t
     ==> d <= d0 /\ t0 <= t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `d0:real`; `t0:real`; `&1`; `&0`] CCCP_AFTER) THEN
  C1092MIFS_NORMAL_TAC THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `d <= d0` ASSUME_TAC THENL [RASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  NLIN_FACTS_TAC [] [`&0 <= (d0 - d) * (d0 + d)`; `&0 < (t0 - t) * (t0 + t)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: coefficients_after *)
let C1092MIFSS_COEFFICIENTS_AFTER = prove
 (`forall beta d t d0 t0. c977cc_normal d t /\ c977cc_normal d0 t0 /\ t0 * d <= d0 * t
     ==> c1092mifss_P d t <= c1092mifss_P d0 t0 /\
         c1092mifss_Q beta d t <= c1092mifss_Q beta d0 t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `d0:real`; `t0:real`] C1092MIFSS_COORDINATES_AFTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  REWRITE_TAC[c1092mifss_P; c1092mifss_Q] THEN
  SUBGOAL_THEN `(d0 - d) * (d + d0) = (t - t0) * (t + t0)` ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(d + d0) * ((&2 - d - t + (&49 / &85) * d * t) -
                  (&2 - d0 - t0 + (&49 / &85) * d0 * t0)) =
      --(t - t0) * ((d + d0) - (t + t0)) * (&1 - (&49 / &170) * ((d + d0) + (t + t0)))`
     ASSUME_TAC THENL
     [UNDISCH_TAC `(d0 - d) * (d + d0) = (t - t0) * (t + t0)` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (t - t0) * ((d + d0) - (t + t0))`;
      `&0 <= ((t - t0) * ((d + d0) - (t + t0))) *
             (&1 - (&49 / &170) * ((d + d0) + (t + t0)))`] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < (d + d0) * ((&2 - d - t + (&49 / &85) * d * t) -
                        (&2 - d0 - t0 + (&49 / &85) * d0 * t0))`] THEN
    NLIN_TAC ~deg2:false [];
    NLIN_FACTS_TAC [] [`(t - t0) * (-- &1 + (&49 / &85) * (t + t0)) <= &0`] THEN
    REWRITE_TAC[REAL_POW_2] THEN NLIN_TAC ~deg2:false []]);;

(* Lean: FC_after *)
let C1092MIFSS_FC_AFTER = prove
 (`forall beta c s d t d0 t0.
     c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal d0 t0 /\ t0 * d <= d0 * t
     ==> c1092mifss_FC beta c s d0 t0 <= c1092mifss_FC beta c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`beta:real`; `d:real`; `t:real`; `d0:real`; `t0:real`]
    C1092MIFSS_COEFFICIENTS_AFTER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MIFS_NORMAL_TAC THEN
  ASM_SIMP_TAC[C1092MIFSS_FC_FORMULA] THEN
  NLIN_FACTS_TAC []
   [`c * c1092mifss_P d t <= c * c1092mifss_P d0 t0`;
    `s * c1092mifss_Q beta d t <= s * c1092mifss_Q beta d0 t0`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: FE_after *)
let C1092MIFSS_FE_AFTER = prove
 (`forall beta h c s d t d0 t0.
     c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal d0 t0 /\
     &49 / &50 <= c /\ s <= &1 / &5 /\ &0 <= beta /\ beta <= &1 / &2 /\
     &0 <= h /\ h <= &1 / &10 /\ &4 / &5 <= d0 /\ &19 / &50 <= t0 /\
     t0 * d <= d0 * t
     ==> c1092mifss_FE beta h c s d0 t0 <= c1092mifss_FE beta h c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C1092MIFSS_FE_FORMULA] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `d0:real`; `t0:real`;
                `&1 + (&1 - h) * s - c * c1092mifss_alpha beta c s`;
                `&1 - (&1 - h) * c - s * c1092mifss_alpha beta c s`] CCCP_AFTER) THEN
  C1092MIFS_NORMAL_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c1092mifss_alpha] THEN DISCH_TAC THEN
  ABBREV_TAC `al = &1 - c + beta * s` THEN
  ABBREV_TAC `A = &1 + (&1 - h) * s - c * al` THEN
  ABBREV_TAC `B = &1 - (&1 - h) * c - s * al` THEN
  NLIN_FACTS_TAC []
   [`&0 <= beta * s`; `beta * s <= &1 / &2 * s`; `&0 <= al`; `al <= &3 / &25`;
    `c * al <= &1 * al`; `s * al <= s * (&3 / &25)`;
    `&0 <= (&1 - h) * s`; `h * c <= &1 / &10 * c`;
    `&22 / &25 <= A`; `&0 <= s * al`; `B <= &3 / &25`; `&0 <= h * c`;
    `-- (&3 / &125) <= B`;
    `B * d0 <= &3 / &25 * d0`; `&22 / &25 * t0 <= A * t0`;
    `B * d0 <= A * t0`;
    `&22 / &25 * d0 <= A * d0`; `-- (&3 / &125) * t0 <= B * t0`;
    `&0 <= A * d0 + B * t0`] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
