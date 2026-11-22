(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointG01Quartic.lean    *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport.G01Quartic).               *)
(* NEGATIVE-WALL-SCALARS section 7: exact quartic tools.  half / quarter_data*)
(* are C1092WPS_half / C1092WPS_QUARTER_DATA; Quarter, P2, deltaE are the    *)
(* c1092mncs_* constants; UnitCircleChord.decreasing is CCUCC_DECREASING.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointCoefficients.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;

let C1092G01Q_LIN = NLIN_TAC ~deg2:false [];;

let C1092G01Q_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   TRY(MATCH_MP_TAC REAL_POW_LE) THEN TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   TRY(MATCH_ACCEPT_TAC REAL_LE_POW_2) THEN C1092G01Q_LIN; ALL_TAC];;

let C1092G01Q_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C1092G01Q_LIN; ALL_TAC];;

let C1092G01Q_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C1092G01Q_NONNEG_OF_MUL = prove
 (`forall x k. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < k * --x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: poly (definition) *)
let c1092g01q_poly = new_definition
 `c1092g01q_poly (a0:real) a1 a2 a3 a4 z = a0 + a1 * z + a2 * z pow 2 + a3 * z pow 3 + a4 * z pow 4`;;

(* Lean: T (definition) *)
let c1092g01q_T = new_definition
 `c1092g01q_T (c:real) s A B z =
    c1092g01q_poly (s - B) (&2 * (c + s - A)) (&4 * c - &2 * s) (--(&2) * (c + s + A)) (s + B) z`;;

(* Lean: endpoints *)
let C1092G01Q_ENDPOINTS = prove
 (`forall a0 a1 a2 a3 a4 l R z.
     &0 < R /\ &0 <= l /\ l < R /\ l <= z /\ z <= R /\
     a0 <= &0 /\ &0 <= a1 /\ &0 <= a4 /\ &0 <= --a3 - &3 * R * a4 /\
     &0 <= c1092g01q_poly a0 a1 a2 a3 a4 l /\ &0 <= c1092g01q_poly a0 a1 a2 a3 a4 R
     ==> &0 <= c1092g01q_poly a0 a1 a2 a3 a4 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092G01Q_PROD `&0 <= a4 * (&3 * R - (z + l + R))` THEN
  C1092G01Q_FACT `&0 <= --a3 - a4 * (z + l + R)` THEN
  ASM_CASES_TAC `l = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `a0 = &0` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `&0 <= c1092g01q_poly a0 a1 a2 a3 a4 (&0)` THEN
      REWRITE_TAC[c1092g01q_poly] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    C1092G01Q_PROD `&0 <= (R * z * (R - z)) * a1` THEN
    C1092G01Q_PROD `&0 <= (z * z) * c1092g01q_poly (&0) a1 a2 a3 a4 R` THEN
    C1092G01Q_PROD `&0 <= ((R * R) * (z * z) * (R - z)) * (--a3 - a4 * (z + R))` THEN
    SUBGOAL_THEN `(R * R) * c1092g01q_poly (&0) a1 a2 a3 a4 z =
                  (R * z * (R - z)) * a1 + (z * z) * c1092g01q_poly (&0) a1 a2 a3 a4 R +
                  ((R * R) * (z * z) * (R - z)) * (--a3 - a4 * (z + R))` ASSUME_TAC THENL
     [REWRITE_TAC[c1092g01q_poly] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC C1092G01Q_NONNEG_OF_MUL THEN EXISTS_TAC `R * R:real` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; C1092G01Q_LIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092G01Q_PROD `&0 <= (z * R * (R - z)) * c1092g01q_poly a0 a1 a2 a3 a4 l` THEN
  C1092G01Q_PROD `&0 <= (z * l * (z - l)) * c1092g01q_poly a0 a1 a2 a3 a4 R` THEN
  C1092G01Q_PROD `&0 <= (l * R * z) * (--a3 - a4 * (z + l + R))` THEN
  C1092G01Q_PROD `&0 <= ((R - l) * (z - l) * (R - z)) *
                        (--a0 + l * R * z * (--a3 - a4 * (z + l + R)))` THEN
  SUBGOAL_THEN
   `(l * R * (R - l)) * c1092g01q_poly a0 a1 a2 a3 a4 z =
    (z * R * (R - z)) * c1092g01q_poly a0 a1 a2 a3 a4 l +
    (z * l * (z - l)) * c1092g01q_poly a0 a1 a2 a3 a4 R +
    ((R - l) * (z - l) * (R - z)) * (--a0 + l * R * z * (--a3 - a4 * (z + l + R)))`
    ASSUME_TAC THENL [REWRITE_TAC[c1092g01q_poly] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC C1092G01Q_NONNEG_OF_MUL THEN EXISTS_TAC `l * R * (R - l):real` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC; C1092G01Q_LIN]);;

(* Lean: bernstein *)
let C1092G01Q_BERNSTEIN = prove
 (`forall a0 a1 a2 a3 a4 w z.
     &0 < w /\ &0 <= z /\ z <= w /\ &0 <= a0 /\ &0 <= a0 + a1 * w / &4 /\
     &0 <= a0 + a1 * w / &2 + a2 * w pow 2 / &6 /\
     &0 <= a0 + &3 * a1 * w / &4 + a2 * w pow 2 / &2 + a3 * w pow 3 / &4 /\
     &0 <= c1092g01q_poly a0 a1 a2 a3 a4 w
     ==> &0 <= c1092g01q_poly a0 a1 a2 a3 a4 z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092G01Q_PROD `&0 <= a0 * (w - z) pow 4` THEN
  C1092G01Q_PROD `&0 <= (a0 + a1 * w / &4) * z * (w - z) pow 3` THEN
  C1092G01Q_PROD `&0 <= (a0 + a1 * w / &2 + a2 * w pow 2 / &6) * z pow 2 * (w - z) pow 2` THEN
  C1092G01Q_PROD `&0 <= (a0 + &3 * a1 * w / &4 + a2 * w pow 2 / &2 + a3 * w pow 3 / &4) *
                        z pow 3 * (w - z)` THEN
  C1092G01Q_PROD `&0 <= c1092g01q_poly a0 a1 a2 a3 a4 w * z pow 4` THEN
  SUBGOAL_THEN
   `w pow 4 * c1092g01q_poly a0 a1 a2 a3 a4 z =
    a0 * (w - z) pow 4 + &4 * ((a0 + a1 * w / &4) * z * (w - z) pow 3) +
    &6 * ((a0 + a1 * w / &2 + a2 * w pow 2 / &6) * z pow 2 * (w - z) pow 2) +
    &4 * ((a0 + &3 * a1 * w / &4 + a2 * w pow 2 / &2 + a3 * w pow 3 / &4) * z pow 3 * (w - z)) +
    c1092g01q_poly a0 a1 a2 a3 a4 w * z pow 4` ASSUME_TAC THENL
   [REWRITE_TAC[c1092g01q_poly] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC C1092G01Q_NONNEG_OF_MUL THEN EXISTS_TAC `w pow 4` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) then SUBST1_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `x pow 3 = x * x pow 2 /\ x pow 4 = x pow 2 * x pow 2`]) THEN
  REWRITE_TAC[REAL_ARITH `x pow 3 = x * x pow 2 /\ x pow 4 = x pow 2 * x pow 2`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: steep_bounds *)
let C1092G01Q_STEEP_BOUNDS = prove
 (`forall c s. c977cc_normal c s /\ &3 / &5 <= s ==> c <= &4 / &5 /\ s <= &5 / &7 /\ &3 * c + s <= &3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `c:real`; `s:real`; `&3`; `&1`] CCUCC_DECREASING) THEN
  ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REPEAT CONJ_TAC THEN C1092G01Q_CONTRA THENL
   [C1092G01Q_PROD `&0 <= (s - &3 / &5) * (s + &3 / &5)` THEN
    C1092G01Q_PROD `&0 < (c - &4 / &5) * (c + &4 / &5)` THEN C1092G01Q_LIN;
    C1092G01Q_PROD `&0 <= (c - s) * (c + s)` THEN
    C1092G01Q_PROD `&0 < (s - &5 / &7) * (s + &5 / &7)` THEN C1092G01Q_LIN;
    ASM_REAL_ARITH_TAC]);;

let C1092G01Q_HALF_TAC c s z =
  MP_TAC(SPECL [c; s] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC); ALL_TAC] THEN
  SPEC_TAC(list_mk_comb(`C1092WPS_half`,[c; s]), z) THEN GEN_TAC THEN STRIP_TAC;;

(* Lean: half_bound *)
let C1092G01Q_HALF_BOUND = prove
 (`forall d t. c977cc_normal d t /\ &8 * t <= &3 * d ==> C1092WPS_half d t <= &2 / &11`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C1092G01Q_HALF_TAC `d:real` `t:real` `w:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092G01Q_PROD `&0 <= w * w` THEN
  C1092G01Q_PROD `&0 <= (&1 + w * w) * (&3 * d - &8 * t)` THEN
  C1092G01Q_FACT `&16 * w <= &3 - &3 * w * w` THEN
  C1092G01Q_CONTRA THEN
  C1092G01Q_PROD `&0 < (w - &2 / &11) * (&3 * w + &6 / &11 + &16)` THEN C1092G01Q_LIN);;

(* Lean: numerator (private) *)
let C1092G01Q_NUMERATOR = prove
 (`forall w. &0 <= w /\ w <= &2 / &11
       ==> &0 < &61 - &130 * w - &203 * w pow 2 - &390 * w pow 3 - &545 * w pow 4 -
                &525 * w pow 6`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `w pow 3 = w * w * w /\ w pow 4 = (w * w) * (w * w) /\
                          w pow 6 = (w * w * w) * (w * w * w)`; REAL_POW_2] THEN
  C1092G01Q_PROD `&0 <= (&2 / &11 - w) * (&2 / &11 + w)` THEN
  C1092G01Q_FACT `w * w <= &4 / &121` THEN
  C1092G01Q_PROD `&0 <= w * w` THEN
  C1092G01Q_PROD `&0 <= (&4 / &121 - w * w) * w` THEN
  C1092G01Q_PROD `&0 <= (&4 / &121) * (&2 / &11 - w)` THEN
  C1092G01Q_FACT `w * w * w <= &8 / &1331` THEN
  C1092G01Q_PROD `&0 <= (&4 / &121 - w * w) * (w * w)` THEN
  C1092G01Q_FACT `(w * w) * (w * w) <= &16 / &14641` THEN
  C1092G01Q_PROD `&0 <= w * w * w` THEN
  C1092G01Q_PROD `&0 <= (&8 / &1331 - w * w * w) * (w * w * w)` THEN
  C1092G01Q_PROD `&0 <= (&8 / &1331) * (&8 / &1331 - w * w * w)` THEN
  C1092G01Q_LIN);;

(* Lean: lower_coefficient *)
let C1092G01Q_LOWER_COEFFICIENT = prove
 (`forall d t. c977cc_normal d t /\ &8 * t <= &3 * d
         ==> &0 <= t * (&1 - (&61 / &100) * d - (&13 / &20) * t) +
                   (&3 / &2) * (&1 / &3 - c1092mncs_P2 d t) * C1092WPS_half d t -
                   (&21 / &8) * C1092WPS_half d t pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092G01Q_HALF_BOUND) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  UNDISCH_TAC `C1092WPS_half d t <= &2 / &11` THEN
  C1092G01Q_HALF_TAC `d:real` `t:real` `w:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 + w pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `w:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d = (&1 - w pow 2) / (&1 + w pow 2) /\ t = (&2 * w) / (&1 + w pow 2)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `t * (&1 - (&61 / &100) * d - (&13 / &20) * t) +
    (&3 / &2) * (&1 / &3 - c1092mncs_P2 d t) * w - (&21 / &8) * w pow 3 =
    (w * (&61 - &130 * w - &203 * w pow 2 - &390 * w pow 3 - &545 * w pow 4 - &525 * w pow 6)) /
    (&200 * (&1 + w pow 2) pow 2)` SUBST1_TAC THENL
   [REWRITE_TAC[c1092mncs_P2] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `d:real`)) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `t:real`)) THEN
    UNDISCH_TAC `&0 < &1 + w pow 2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC C1092G01Q_NUMERATOR THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC]);;

let C1092G01Q_QUARTER_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  SUBGOAL_THEN `r pow 2 + h pow 2 = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: parameter_identity *)
let C1092G01Q_PARAMETER_IDENTITY = prove
 (`forall c s A B h r. c1092mncs_quarter h r
     ==> c1092g01q_T c s A B (C1092WPS_half r h) =
         (&1 + C1092WPS_half r h pow 2) pow 2 *
         ((c - s) * h pow 2 + (c + s) * h * r + s - A * h - B * r)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092G01Q_QUARTER_TAC THEN
  C1092G01Q_HALF_TAC `r:real` `h:real` `z:real` THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r = (&1 - z pow 2) / (&1 + z pow 2) /\ h = (&2 * z) / (&1 + z pow 2)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092g01q_T; c1092g01q_poly] THEN
  UNDISCH_TAC `&0 < &1 + z pow 2` THEN CONV_TAC REAL_FIELD);;

(* Lean: parameter_bound *)
let C1092G01Q_PARAMETER_BOUND = prove
 (`forall h r. c1092mncs_quarter h r /\ h <= r ==> C1092WPS_half r h <= &5 / &12`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092G01Q_QUARTER_TAC THEN
  C1092G01Q_HALF_TAC `r:real` `h:real` `z:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092G01Q_PROD `&0 <= z * z` THEN
  C1092G01Q_PROD `&0 <= (&1 + z * z) * (r - h)` THEN
  C1092G01Q_FACT `z * z + &2 * z <= &1` THEN
  C1092G01Q_CONTRA THEN
  C1092G01Q_PROD `&0 < (z - &5 / &12) * (z + &5 / &12 + &2)` THEN C1092G01Q_LIN);;

(* Lean: parameter_order *)
let C1092G01Q_PARAMETER_ORDER = prove
 (`forall d t h r. c977cc_normal d t /\ c1092mncs_quarter h r
     ==> (&1 + C1092WPS_half d t pow 2) * (&1 + C1092WPS_half r h pow 2) *
         c1092mncs_deltaE d t h r =
         &2 * (C1092WPS_half d t - C1092WPS_half r h) *
         (&1 + C1092WPS_half d t * C1092WPS_half r h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C1092G01Q_QUARTER_TAC THEN
  C1092G01Q_HALF_TAC `d:real` `t:real` `wd:real` THEN
  C1092G01Q_HALF_TAC `r:real` `h:real` `wr:real` THEN
  REWRITE_TAC[c1092mncs_deltaE] THEN
  MAP_EVERY UNDISCH_TAC [`(&1 + wd pow 2) * d = &1 - wd pow 2`; `(&1 + wd pow 2) * t = &2 * wd`;
                         `(&1 + wr pow 2) * r = &1 - wr pow 2`; `(&1 + wr pow 2) * h = &2 * wr`] THEN
  CONV_TAC REAL_RING);;
