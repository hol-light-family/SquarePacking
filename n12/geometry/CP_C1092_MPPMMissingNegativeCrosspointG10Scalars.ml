(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointG10Scalars.lean *)
(* (namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport.G10Scalars). *)
(* Quarter, kE, deltaE, FC: c1092mncs_*; G10, E0: c1092mmncs_G10 /         *)
(* c1092mmncs_E0; Normal: c977cc_normal; G01Quartic.bernstein /             *)
(* parameter_bound: C1092G01Q_BERNSTEIN / C1092G01Q_PARAMETER_BOUND;        *)
(* C1092MPPMCrosspointSupport.steep_bounds: C1092G10_STEEP_BOUNDS;          *)
(* UnitCircleChord: CCUCC_*.  Tag C1092MNG10S_.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointEnvelope.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointG01Quartic.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryG10Clamp.ml";;

let C1092MNG10S_LIN = REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092MNG10S_QUARTER_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC));;

(* Lean: quarter_bounds *)
let C1092MNG10S_QUARTER_BOUNDS = prove
 (`forall h r. c1092mncs_quarter h r ==> h <= &1 /\ r <= &1 /\ &1 <= h + r /\ h + r <= &10 / &7`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MNG10S_QUARTER_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `h <= &1 /\ r <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `h - &1`; SQ_NONNEG `r - &1`]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MP_TAC(SPECL [`h:real`; `&1 - h`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`r:real`; `&1 - r`] REAL_LE_MUL) THEN
    REPEAT(ANTS_TAC THENL [C1092MNG10S_LIN; DISCH_TAC]) THEN C1092MNG10S_LIN;
    NLIN_TAC [SQ_NONNEG `h - r`; SQ_NONNEG `h + r - &10 / &7`]]);;

(* Lean: recipient_bounds *)
let C1092MNG10S_RECIPIENT_BOUNDS = prove
 (`forall d t. c977cc_normal d t /\ &252 / &373 <= t
         ==> d <= &3 / &4 /\ &27 / &40 <= t /\ t <= &3 / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `&275 / &373`; `&252 / &373`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092G10_STEEP_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MNG10S_LIN; STRIP_TAC] THEN
  C1092MNG10S_LIN);;

(* Lean: before_formula *)
let C1092MNG10S_BEFORE_FORMULA = prove
 (`forall c s d t h r. c1092mncs_quarter h r /\ c1092mncs_deltaE d t h r <= &0
     ==> c1092mmncs_G10 c s d t h r =
         t * (h * (h + r) - &2 * h - r - c1092mncs_FC c s h r) +
         d * r * (h + r - &36 / &25) + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNG10S_QUARTER_TAC THEN
  ASM_SIMP_TAC[c1092mmncs_G10; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REWRITE_TAC[c1092mncs_kE; c1092mncs_deltaE; c1092mmncs_E0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: after_formula *)
let C1092MNG10S_AFTER_FORMULA = prove
 (`forall c s d t h r. c1092mncs_quarter h r /\ &0 <= c1092mncs_deltaE d t h r
     ==> c1092mmncs_G10 c s d t h r =
         t * (&1 + h * r - &2 * h - r - c1092mncs_FC c s h r) +
         d * r * (r - &36 / &25) + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNG10S_QUARTER_TAC THEN
  ASM_SIMP_TAC[c1092mmncs_G10; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  REWRITE_TAC[c1092mncs_kE; c1092mncs_deltaE; c1092mmncs_E0] THEN
  UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING);;

(* Lean: low_bounds *)
let C1092MNG10S_LOW_BOUNDS = prove
 (`forall h r. c1092mncs_quarter h r /\ r <= &3 / &5
         ==> &4 / &5 <= h /\ r <= h /\ h + r <= &7 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNG10S_QUARTER_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `&4 / &5`; `&3 / &5`] CCUCC_COSINE_ORDER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `h:real`; `r:real`; `&1`; `&1`] CCUCC_INCREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C1092MNG10S_LIN);;

(* Lean: low_radial *)
let C1092MNG10S_LOW_RADIAL = prove
 (`forall h r. c1092mncs_quarter h r /\ r <= &3 / &5
         ==> &9 / &125 <= &3 / &4 - (&63 / &100) * h - (&149 / &100) * r + (&3 / &2) * h * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNG10S_LOW_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MNG10S_QUARTER_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  NLIN_TAC [SQ_NONNEG `h - &1`; SQ_NONNEG `r - &1 / &2`]);;

(* Lean: high_radial *)
let C1092MNG10S_HIGH_RADIAL = prove
 (`forall h r. c1092mncs_quarter h r /\ h <= r
         ==> &3 / &50 <= &3 / &4 + (&3 / &4) * h * r - (&9 / &8) * h + (&3 / &4) * r pow 2 -
                         (&359 / &400) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092G01Q_PARAMETER_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MNG10S_QUARTER_TAC THEN
  MP_TAC(SPECL [`r:real`; `h:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `C1092WPS_half r h <= &5 / &12` THEN
  SPEC_TAC(`C1092WPS_half r h`, `z:real`) THEN GEN_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&217 / &400`; `-- &3 / &4`; `-- &3 / &25`; `-- &15 / &4`; `&187 / &80`;
                `&5 / &12`; `z:real`] C1092G01Q_BERNSTEIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c1092g01q_poly] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(&1 + z pow 2) pow 2 *
    (&3 / &4 + (&3 / &4) * h * r - (&9 / &8) * h + (&3 / &4) * r pow 2 - (&359 / &400) * r -
     &3 / &50) =
    c1092g01q_poly (&217 / &400) (-- &3 / &4) (-- &3 / &25) (-- &15 / &4) (&187 / &80) z`
    ASSUME_TAC THENL
   [REWRITE_TAC[c1092g01q_poly] THEN
    MAP_EVERY UNDISCH_TAC [`(&1 + z pow 2) * r = &1 - z pow 2`; `(&1 + z pow 2) * h = &2 * z`] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + z pow 2) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= &3 / &4 + (&3 / &4) * h * r - (&9 / &8) * h + (&3 / &4) * r pow 2 -
          (&359 / &400) * r - &3 / &50` MP_TAC THENL
   [MATCH_MP_TAC C1092G01Q_NONNEG_OF_MUL THEN EXISTS_TAC `(&1 + z pow 2) pow 2` THEN
    ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;
