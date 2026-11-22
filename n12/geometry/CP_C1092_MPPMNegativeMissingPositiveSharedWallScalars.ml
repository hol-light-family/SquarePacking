(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeMissingPositiveSharedWall-   *)
(* Scalars.lean (N12Compact.C1092MPPMNegativeMissingPositiveSharedWall.      *)
(* Scalars).  NEGATIVE-MISSING-POSITIVE-SHARED-WALL §§3-4.                   *)
(* Normal: c977cc_normal; Quarter: c1092mcs_quarter; half: c1092mcbh_half    *)
(* (normal_half C1092MCBH_NORMAL_HALF, quarter_half C1092MCBH_QUARTER_HALF); *)
(* cosH / sinH: c1092sps_cosH / c1092sps_sinH; G01Quartic poly / bernstein:  *)
(* c1092g01q_poly / C1092G01Q_BERNSTEIN; Envelopes leftValue / circle_order  *)
(* / left_difference: c1092mpbes_leftValue / C1092MPBES_CIRCLE_ORDER /       *)
(* C1092MPBES_LEFT_DIFFERENCE.  Tag C1092NMPS_.                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeMissingPositiveCeilingScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundEnvelopesScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointBoundaryHalf.ml";;

(* Lean: F0, A1, B1, A2, B2 (definitions) *)
let c1092nmps_F0 = new_definition
 `c1092nmps_F0 (c:real) (s:real) = &3 / &2 - (&6 / &5) * c - (&36 / &25) * s + s * (c + s) / &2`;;
let c1092nmps_A1 = new_definition
 `c1092nmps_A1 (c:real) (s:real) = c + s - &2 + (&14 / &25) * s pow 2 - c * s`;;
let c1092nmps_B1 = new_definition
 `c1092nmps_B1 (c:real) (s:real) = c - s - &6 / &5 + s pow 2 + (&14 / &25) * c * s`;;
let c1092nmps_A2 = new_definition
 `c1092nmps_A2 (c:real) (s:real) = s - c - &1 - (&11 / &25) * s pow 2`;;
let c1092nmps_B2 = new_definition
 `c1092nmps_B2 (c:real) (s:real) = c + s - &6 / &5 - (&11 / &25) * c * s`;;

let C1092NMPS_LP hs = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false hs;;

let C1092NMPS_DEN = prove
 (`forall x. ~(&1 + x pow 2 = &0)`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN REAL_ARITH_TAC);;

(* identities in the half-angle parameter x (cosH x, sinH x) *)
let C1092NMPS_IDS = prove
 (`forall x. (&50 * (&1 + x pow 2) pow 2) * c1092nmps_F0 (c1092sps_cosH x) (c1092sps_sinH x) =
         &135 * x pow 4 - &194 * x pow 3 + &250 * x pow 2 - &94 * x + &15 /\
       (&25 * (&1 + x pow 2) pow 2) * (c1092nmps_B1 (c1092sps_cosH x) (c1092sps_sinH x) + &9 / &25) =
         c1092g01q_poly (&4) (--(&22)) (&58) (--(&78)) (--(&46)) x /\
       (&25 * (&1 + x pow 2) pow 2) * (--c1092nmps_A2 (c1092sps_cosH x) (c1092sps_sinH x) - &7 / &5) =
         c1092g01q_poly (&15) (--(&50)) (&24) (--(&50)) (--(&35)) x /\
       (&1 + x pow 2) * c1092sps_cosH x = &1 - x pow 2 /\
       (&1 - c1092sps_cosH x) pow 2 / &2 + c1092sps_sinH x * (c1092sps_cosH x / &2 - &9 / &25) =
         &2 * x * (x pow 3 - (&43 / &50) * x pow 2 + &7 / &50) / (&1 + x pow 2) pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` C1092NMPS_DEN) THEN
  REWRITE_TAC[c1092nmps_F0; c1092nmps_B1; c1092nmps_A2; c1092g01q_poly;
              c1092sps_cosH; c1092sps_sinH] THEN
  CONV_TAC REAL_FIELD);;

let C1092NMPS_HALF_TAC =
  FIRST_ASSUM(fun th -> if can (term_match [] `c977cc_normal c s`) (concl th)
    then STRIP_ASSUME_TAC(MATCH_MP C1092MCBH_NORMAL_HALF th) THEN
         STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
         STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else NO_TAC) THEN
  SUBGOAL_THEN `c1092mcbh_half c s <= &3 / &10` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092mcbh_half]; ALL_TAC] THEN
  MP_TAC(SPEC `c1092mcbh_half c s` C1092NMPS_IDS) THEN
  MP_TAC(SPEC `c1092mcbh_half c s` C1092SPS_HALF_DEN_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

(* Lean: bounds *)
let C1092NMPS_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ s / (&1 + c) <= &3 / &10 ==> &91 / &109 <= c /\ s <= &60 / &109`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NMPS_HALF_TAC THEN
  SUBGOAL_THEN `&0 <= (&3 / &10 - c1092mcbh_half c s) * (&3 / &10 + c1092mcbh_half c s)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&91 / &109 <= c` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 + c1092mcbh_half c s pow 2) * (c - &91 / &109)` MP_TAC THENL
     [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (c - &91 / &109) * (c + &91 / &109)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `s - &60 / &109`]);;

(* Lean: central_positive *)
let C1092NMPS_CENTRAL_POSITIVE = prove
 (`forall c s. c977cc_normal c s /\ s / (&1 + c) <= &3 / &10 ==> &0 < c1092nmps_F0 c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NMPS_HALF_TAC THEN
  SUBGOAL_THEN `&0 < (&50 * (&1 + c1092mcbh_half c s pow 2) pow 2) * c1092nmps_F0 c s` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= c1092mcbh_half c s pow 2 * (&3 / &10 - c1092mcbh_half c s) /\
                  &0 <= c1092mcbh_half c s pow 4`
      STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN RASM_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `c1092mcbh_half c s - &235 / &959`];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
  MATCH_MP_TAC(CONJUNCT1 REAL_LT_MUL_EQ) THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]);;

(* Lean: coefficients *)
let C1092NMPS_COEFFICIENTS = prove
 (`forall c s. c977cc_normal c s /\ s / (&1 + c) <= &3 / &10
     ==> --(&1) <= c1092nmps_A1 c s /\ --(&9 / &25) <= c1092nmps_B1 c s /\
         c1092nmps_A2 c s <= --(&7 / &5) /\ --(&1 / &5) <= c1092nmps_B2 c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NMPS_HALF_TAC THEN
  SUBGOAL_THEN `&0 < (&25 * (&1 + c1092mcbh_half c s pow 2) pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  let bern a0 a1 a2 a3 a4 =
    MP_TAC(SPECL [a0; a1; a2; a3; a4; `&3 / &10`; `c1092mcbh_half c s`] C1092G01Q_BERNSTEIN) THEN
    ASM_REWRITE_TAC[c1092g01q_poly] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM c1092g01q_poly] THEN DISCH_TAC in
  bern `&4` `--(&22)` `&58` `--(&78)` `--(&46)` THEN
  bern `&15` `--(&50)` `&24` `--(&50)` `--(&35)` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&0 <= (&1 + c) * (c1092nmps_A1 c s + &1)` MP_TAC THENL
     [SUBGOAL_THEN `(&1 + c) * (c1092nmps_A1 c s + &1) =
                    s pow 2 * ((&14 / &25) * (&1 + c) - &1 + s)` SUBST1_TAC THENL
       [REWRITE_TAC[c1092nmps_A1] THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
        CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN RASM_ARITH_TAC;
      SIMP_TAC[REAL_LE_MUL_EQ; REAL_ARITH `&7 / &10 <= c ==> &0 < &1 + c`;
               ASSUME `&7 / &10 <= c`] THEN REAL_ARITH_TAC];
    UNDISCH_TAC `&0 <= c1092g01q_poly (&4) (--(&22)) (&58) (--(&78)) (--(&46)) (c1092mcbh_half c s)` THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
       can (find_term ((=) `c1092nmps_B1 c s`)) (lhs (concl th)) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&0 <= c1092g01q_poly (&15) (--(&50)) (&24) (--(&50)) (--(&35)) (c1092mcbh_half c s)` THEN
    FIRST_X_ASSUM(fun th -> if is_eq (concl th) &&
       can (find_term ((=) `c1092nmps_A2 c s`)) (lhs (concl th)) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= (&1 + c + s) * (c1092nmps_B2 c s + &1 / &5)` MP_TAC THENL
     [SUBGOAL_THEN `(&1 + c + s) * (c1092nmps_B2 c s + &1 / &5) =
                    (c * s) * (&2 - (&11 / &25) * (&1 + c + s))` SUBST1_TAC THENL
       [REWRITE_TAC[c1092nmps_B2] THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
        CONV_TAC REAL_RING; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; RASM_ARITH_TAC];
      SIMP_TAC[REAL_LE_MUL_EQ; REAL_ARITH `&7 / &10 <= c /\ &0 <= s ==> &0 < &1 + c + s`;
               ASSUME `&7 / &10 <= c`; ASSUME `&0 <= s`] THEN REAL_ARITH_TAC]]);;

(* Lean: model_nonnegative *)
let C1092NMPS_MODEL_NONNEGATIVE = prove
 (`forall h r. c1092mcs_quarter h r ==> &0 <= (&1 - h) pow 2 / &2 + r * (h / &2 - &9 / &25)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092MCBH_QUARTER_HALF) THEN
  MP_TAC(SPEC `c1092mcbh_half h r` C1092NMPS_IDS) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (c1092mcbh_half h r - &43 / &75) pow 2 * (c1092mcbh_half h r + &43 / &150)`
    MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `&0 <= c1092mcbh_half h r` THEN
  SPEC_TAC(`c1092mcbh_half h r`, `z:real`) THEN REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  TRY(MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2]) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: northwest_before *)
let C1092NMPS_NORTHWEST_BEFORE = prove
 (`forall c s h r. c977cc_normal c s /\ s / (&1 + c) <= &3 / &10 /\ c1092mcs_quarter h r
     ==> &0 <= c1092mpbes_leftValue (&1) (c1092nmps_A1 c s) (c1092nmps_B1 c s) h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092NMPS_COEFFICIENTS) THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092NMPS_MODEL_NONNEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter h t`) o concl)) THEN
  SUBGOAL_THEN `&0 <= (c1092nmps_A1 c s + &1) * h /\ &0 <= (c1092nmps_B1 c s + &9 / &25) * r`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092mpbes_leftValue] THEN NLIN_TAC ~deg2:false []);;

(* Lean: northwest_after *)
let C1092NMPS_NORTHWEST_AFTER = prove
 (`forall c s h r. c977cc_normal c s /\ &0 < s /\ s / (&1 + c) <= &3 / &10 /\ c1092mcs_quarter h r /\
     &0 <= s * r - c * h
     ==> &0 < c1092mpbes_leftValue (&1) (c1092nmps_A2 c s) (c1092nmps_B2 c s) h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092NMPS_COEFFICIENTS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092NMPS_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092NMPS_CENTRAL_POSITIVE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal c s`) o concl)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter h t`) o concl)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092MPBES_CIRCLE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `r <= &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (--c1092nmps_A2 c s - &7 / &5) * ((r + c) / &2) /\
    &0 <= (c1092nmps_B2 c s + &1 / &5) * ((h + s) / &2) /\
    &0 <= (r + c) / &2 * (&7 / &5 - (h + s) / &2 - ((r + c) / &2) / &2 - &31 / &90) /\
    &0 <= ((r + c) / &2 - &5 / &6) * (&31 / &90)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= --((h + s) / &2) * (r + c) / &2 + (((h + s) / &2) pow 2 - ((r + c) / &2) pow 2) / &2 -
    c1092nmps_A2 c s * ((r + c) / &2) + c1092nmps_B2 c s * ((h + s) / &2)`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false [SQ_NONNEG `(h + s) / &2 - &1 / &5`]; ALL_TAC] THEN
  MP_TAC(SPECL [`&1`; `c1092nmps_A2 c s`; `c1092nmps_B2 c s`; `h:real`; `r:real`; `s:real`; `c:real`]
    C1092MPBES_LEFT_DIFFERENCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (h + s) / &2 *
     (c1092mpbes_leftValue (&1) (c1092nmps_A2 c s) (c1092nmps_B2 c s) h r -
      c1092mpbes_leftValue (&1) (c1092nmps_A2 c s) (c1092nmps_B2 c s) s c)`
    MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_MUL_EQ; REAL_ARITH `&0 < s /\ &0 <= h ==> &0 < (h + s) / &2`;
           ASSUME `&0 <= h`; ASSUME `&0 < s`] THEN
  SUBGOAL_THEN `c1092mpbes_leftValue (&1) (c1092nmps_A2 c s) (c1092nmps_B2 c s) s c = c1092nmps_F0 c s`
    SUBST1_TAC THENL
   [REWRITE_TAC[c1092mpbes_leftValue; c1092nmps_A2; c1092nmps_B2; c1092nmps_F0] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;
