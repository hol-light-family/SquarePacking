(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShallowCentralScalars.lean               *)
(* (N12Compact.C1092ShallowCentralScalars).  Same-face scalars for the       *)
(* actual shallow-positive wall order.  cosH / sinH: c1092sps_cosH /         *)
(* c1092sps_sinH; Normal: c977cc_normal.                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShallowBottom.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: b (definition) *)
let c1092scs_b = new_definition
 `c1092scs_b (a:real) (c:real) (s:real) (K:real) =
    (a * (&3 / &2 + c * (c + s) / &2) - K - &2 * c) / s`;;

(* Lean: ell (definition) *)
let c1092scs_ell = new_definition
 `c1092scs_ell (a:real) (c:real) (s:real) (K:real) =
    (K - &2 * s + (a / &2) * (&1 + s * (c + s))) / c`;;

let C1092SCS_NORMAL_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)
    else NO_TAC));;

(* Lean: bounds *)
let C1092SCS_BOUNDS = prove
 (`forall x. &0 < x /\ x <= &1 / &4
       ==> &15 / &17 <= c1092sps_cosH x /\ c1092sps_sinH x <= &8 / &17 /\
           &7 / &17 <= c1092sps_cosH x - c1092sps_sinH x`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `c1092sps_cosH x - c1092sps_sinH x = (&1 - x pow 2 - &2 * x) / (&1 + x pow 2)`
    SUBST1_TAC THENL
   [REWRITE_TAC[c1092sps_cosH; c1092sps_sinH; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  REPEAT CONJ_TAC THEN
  NLIN_TAC [SQ_NONNEG `x:real`]);;

(* Lean: arc *)
let C1092SCS_ARC = prove
 (`forall c s. c977cc_normal c s ==> &1 + (&4 / &5) * c * s <= c + s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092SCS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  NLIN_FACTS_TAC []
   [`&0 <= c * s`; `&0 <= ((c + s) - &1) * (&10 / &7 - (c + s))`] THEN
  NLIN_TAC ~deg2:false []);;

let C1092SCS_HALF_TAC =
  MP_TAC(SPECL [`x:real`] C1092SCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_COS_POS) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_SIN_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1092sps_cosH x`; `c1092sps_sinH x`] C1092SCS_ARC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* Lean: brackets *)
let C1092SCS_BRACKETS = prove
 (`forall x. &0 < x /\ x <= &1 / &4 /\ c977cc_normal (c1092sps_cosH x) (c1092sps_sinH x)
       ==> --c1092sps_cosH x + c1092sps_sinH x + &2 / &5 - c1092sps_sinH x pow 2 -
             (&1 / &2) * c1092sps_cosH x * c1092sps_sinH x < &0 /\
           &1 - c1092sps_cosH x - c1092sps_sinH x + c1092sps_cosH x * c1092sps_sinH x -
             c1092sps_sinH x pow 2 / &2 < &0 /\
           &0 < c1092sps_cosH x - c1092sps_sinH x + (&11 / &25) * c1092sps_sinH x pow 2 /\
           &0 < c1092sps_cosH x + c1092sps_sinH x - &1 -
             (&11 / &25) * c1092sps_cosH x * c1092sps_sinH x`,
  GEN_TAC THEN STRIP_TAC THEN C1092SCS_HALF_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPS_BOTTOM_FAR_ENDPOINT_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY ABBREV_TAC [`c = c1092sps_cosH x`; `s = c1092sps_sinH x`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: same_face_sum *)
let C1092SCS_SAME_FACE_SUM = prove
 (`forall a c s K. &1 < a /\ c977cc_normal c s /\ &0 < s /\ K <= s
     ==> &0 < c1092scs_b a c s K + c1092scs_ell a c s K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SCS_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * c1092scs_b a c s K = a * (&3 / &2 + c * (c + s) / &2) - K - &2 * c /\
                c * c1092scs_ell a c s K = K - &2 * s + (a / &2) * (&1 + s * (c + s))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092scs_b; c1092scs_ell] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC [`B = c1092scs_b a c s K`; `E = c1092scs_ell a c s K`] THEN
  SUBGOAL_THEN `c * s * (B + E) = a * (&2 * c + s) - (c - s) * K - &2` ASSUME_TAC THENL
   [UNDISCH_TAC `s * B = a * (&3 / &2 + c * (c + s) / &2) - K - &2 * c` THEN
    UNDISCH_TAC `c * E = K - &2 * s + (a / &2) * (&1 + s * (c + s))` THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + c) * (&2 * c + s - c * s + s pow 2 - &2) = s pow 2 * (c + s - &1)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  NLIN_FACTS_TAC []
   [`&0 < c * s`; `&1 < c + s`; `&0 < s * s`; `&0 < (s * s) * (c + s - &1)`;
    `&0 < &2 * c + s - c * s + s * s - &2`;
    `&0 < (a - &1) * (&2 * c + s)`; `&0 <= (c - s) * (s - K)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`(c * s) * (B + E) <= &0`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: small_left *)
let C1092SCS_SMALL_LEFT = prove
 (`forall a x. &1 < a /\ &0 < x /\ x <= &1 / &4 /\
         c977cc_normal (c1092sps_cosH x) (c1092sps_sinH x)
     ==> &0 < a * (c1092sps_cosH x + c1092sps_sinH x) -
              (&1 / &2) * c1092sps_cosH x * c1092sps_sinH x +
              (&14 / &25) * c1092sps_sinH x pow 2 - &1 /\
         &0 < (a * (c1092sps_cosH x + c1092sps_sinH x) -
               (&1 / &2) * c1092sps_cosH x * c1092sps_sinH x +
               (&14 / &25) * c1092sps_sinH x pow 2 - &1) +
              (a * (c1092sps_cosH x - c1092sps_sinH x) +
               (&14 / &25) * c1092sps_cosH x * c1092sps_sinH x -
               c1092sps_sinH x pow 2 / &2 - c1092sps_cosH x pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SCS_HALF_TAC THEN
  SUBGOAL_THEN `c1092sps_sinH x * x = &1 - c1092sps_cosH x` ASSUME_TAC THENL
   [REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
    MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_NZ) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `c977cc_normal x y`) (concl th)
    then STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) else NO_TAC) THEN
  MAP_EVERY ABBREV_TAC [`c = c1092sps_cosH x`; `s = c1092sps_sinH x`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  NLIN_FACTS_TAC []
   [`&0 < c * s`; `&0 < (a - &1) * (c + s)`; `&0 <= s * s`;
    `x * x <= &1 / &16`; `s * (x * x) <= s * (&1 / &16)`;
    `&0 < (&3 / &50) * (c + s) - s * (x * x)`;
    `&0 < s * ((&3 / &50) * (c + s) - s * (x * x))`;
    `&0 < (a - &1) * (&2 * c)`] THEN
  SUBGOAL_THEN `--((&1 - c) * (&1 - c)) + (&3 / &50) * s * (c + s) =
                s * ((&3 / &50) * (c + s) - s * (x * x))` ASSUME_TAC THENL
   [UNDISCH_TAC `s * x = &1 - c` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;
