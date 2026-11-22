(* ========================================================================= *)
(* Port of Compact/Geometry/C977CornerHalfAngle.lean (Jatloe, N12-jatloe)    *)
(* (namespace N12Compact.C977CornerCubic, continued).                        *)
(* Rational half-angle parameter of a unit normal and the two corner         *)
(* projection inequalities obtained from the cubic chord.                    *)
(* Note: Lean variable T is renamed TT (T is truth in HOL).                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C977CHA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C977CHA_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: half (definition) *)
let c977cha_half = new_definition
 `c977cha_half (c:real) t = (&1 - t) / c`;;

(* Lean: half_data *)
let C977CHA_HALF_DATA = prove
 (`forall c t. c977cc_normal c t
     ==> &0 < c977cha_half c t /\ c977cha_half c t <= &1 /\
         c * c977cha_half c t = &1 - t /\
         c977cha_half c t * (&1 + t) = c /\
         (&1 + c977cha_half c t pow 2) * c = &2 * c977cha_half c t /\
         (&1 + c977cha_half c t pow 2) * t = &1 - c977cha_half c t pow 2 /\
         (&1 + c977cha_half c t pow 2) * c977cc_boundary c t =
           &2 + c977cha_half c t - c977cha_half c t pow 3`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CHA_NORMAL_TAC THEN
  SUBGOAL_THEN `t < &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c977cha_half; c977cc_boundary] THEN REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
   ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
   ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN
  (SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  CONV_TAC REAL_FIELD);;

let C977CHA_HALF_TAC (c:term) (t:term) =
  MP_TAC(SPECL [c; t] C977CHA_HALF_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

(* Lean: ordered_normals *)
let C977CHA_ORDERED_NORMALS = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ &0 <= c * TT - t * C
             ==> C <= c /\ t <= TT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CHA_NORMAL_TAC THEN
  SUBGOAL_THEN `C <= c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `TT < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
   NLIN_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC []);;

(* Lean: half_order *)
let C977CHA_HALF_ORDER = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ &0 <= c * TT - t * C
             ==> c977cha_half C TT <= c977cha_half c t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `TT:real`] C977CHA_ORDERED_NORMALS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C977CHA_HALF_TAC `c:real` `t:real` THEN C977CHA_HALF_TAC `C:real` `TT:real` THEN
  C977CHA_NORMAL_TAC THEN
  MATCH_MP_TAC C977CHA_LE_BY_POS THEN EXISTS_TAC `&1 + t` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN NLIN_TAC []);;

(* Lean: half_lower *)
let C977CHA_HALF_LOWER = prove
 (`forall C TT. c977cc_normal C TT ==> &2 / &5 <= c977cha_half C TT`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CHA_NORMAL_TAC THEN
  REWRITE_TAC[c977cha_half] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Lean: half_lower_small *)
let C977CHA_HALF_LOWER_SMALL = prove
 (`forall C TT. c977cc_normal C TT /\ TT <= &3 / &5 ==> &1 / &2 <= c977cha_half C TT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CHA_NORMAL_TAC THEN
  REWRITE_TAC[c977cha_half] THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MP_TAC(SPECL [`&1 - TT`; `&3 - &5 * TT`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN NLIN_TAC []);;

(* Lean: parallel_boundary *)
let C977CHA_PARALLEL_BOUNDARY = prove
 (`forall C TT. c977cc_normal C TT ==> &2 * (C + TT) - &1 <= c977cc_boundary C TT`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CHA_NORMAL_TAC THEN
  SUBGOAL_THEN `C * c977cc_boundary C TT = C + C * TT + TT * (&1 - TT)` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_boundary] THEN
   SUBGOAL_THEN `~(C = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC C977CHA_LE_BY_POS THEN EXISTS_TAC `C:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 - C`; `TT - (&1 - C)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN NLIN_TAC []);;

(* (1 + r^2) * (boundary - c f - t g) = H f g r, r the half parameter.      *)
let C977CHA_H_IDENTITY = prove
 (`forall c t f g. c977cc_normal c t
     ==> (&1 + c977cha_half c t pow 2) * (c977cc_boundary c t - (c * f + t * g)) =
         c977cc_h f g (c977cha_half c t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CHA_HALF_TAC `c:real` `t:real` THEN
  REWRITE_TAC[c977cc_h] THEN
  MAP_EVERY UNDISCH_TAC
   [`(&1 + c977cha_half c t pow 2) * c = &2 * c977cha_half c t`;
    `(&1 + c977cha_half c t pow 2) * t = &1 - c977cha_half c t pow 2`;
    `(&1 + c977cha_half c t pow 2) * c977cc_boundary c t =
       &2 + c977cha_half c t - c977cha_half c t pow 3`] THEN
  SPEC_TAC(`c977cha_half c t`,`r:real`) THEN
  SPEC_TAC(`c977cc_boundary c t`,`B:real`) THEN
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

(* Lean: compare_from_cubic *)
let C977CHA_COMPARE_FROM_CUBIC = prove
 (`forall c t C TT f g. c977cc_normal c t /\ c977cc_normal C TT /\ &0 < TT /\
                 &0 <= c * TT - t * C /\ &0 <= c977cc_h f g (c977cha_half c t)
                 ==> c * f + t * g <= c977cc_boundary c t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C977CHA_LE_BY_POS THEN
  EXISTS_TAC `&1 + c977cha_half c t pow 2` THEN
  ASM_SIMP_TAC[C977CHA_H_IDENTITY] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

(* Lean: endpoint_cubic *)
let C977CHA_ENDPOINT_CUBIC = prove
 (`forall C TT f g. c977cc_normal C TT /\ C * f + TT * g = &2 * (C + TT) - &1
             ==> &0 <= c977cc_h f g (c977cha_half C TT)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP C977CHA_H_IDENTITY th)]) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[REAL_ARITH `&0 <= &1 + x <=> -- &1 <= x`] THEN
  CONJ_TAC THENL
  [MP_TAC(SPEC `c977cha_half C TT` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `TT:real`] C977CHA_PARALLEL_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: left_projection *)
let C977CHA_LEFT_PROJECTION = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ &0 < TT /\
             &0 <= c * TT - t * C
             ==> c * (&2 + (TT - &1) / C - TT) + t * (&1 + C) <= c977cc_boundary c t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C977CHA_COMPARE_FROM_CUBIC THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `TT:real`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `TT:real`] C977CHA_HALF_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977CHA_HALF_TAC `c:real` `t:real` THEN C977CHA_HALF_TAC `C:real` `TT:real` THEN
  C977CHA_NORMAL_TAC THEN
  SUBGOAL_THEN `C * (&2 + (TT - &1) / C - TT) = &2 * C + TT - &1 - C * TT` ASSUME_TAC THENL
  [SUBGOAL_THEN `~(C = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC C977CC_CUBIC_CHORD THEN EXISTS_TAC `c977cha_half C TT` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [(* rho < 1 *)
   REWRITE_TAC[c977cha_half] THEN
   SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN NLIN_TAC [];
   (* endpoint *)
   MATCH_MP_TAC C977CHA_ENDPOINT_CUBIC THEN ASM_REWRITE_TAC[] THEN
   ASM_REAL_ARITH_TAC;
   (* H at 1 *)
   SUBGOAL_THEN `&2 + (TT - &1) / C - TT <= &1` MP_TAC THENL
   [MATCH_MP_TAC C977CHA_LE_BY_POS THEN EXISTS_TAC `C:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`&1 - TT`; `&1 - C`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[c977cc_h; REAL_POW_ONE; REAL_MUL_RID] THEN REAL_ARITH_TAC;
   (* chord factor *)
   SUBGOAL_THEN `C <= &2 * c977cha_half C TT` MP_TAC THENL
   [MATCH_MP_TAC C977CHA_LE_BY_POS THEN EXISTS_TAC `C:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC [SQ_NONNEG `&1 - TT`]; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

(* Lean: near_projection *)
let C977CHA_NEAR_PROJECTION = prove
 (`forall c t C TT. c977cc_normal c t /\ c977cc_normal C TT /\ &0 < TT /\
             &0 <= c * TT - t * C
             ==> c * (&2 - (&22 / &25) * TT pow 2 + C * TT - C - TT) +
                 t * (&1 + TT pow 2 + (&22 / &25) * C * TT + C - TT)
                 <= c977cc_boundary c t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C977CHA_COMPARE_FROM_CUBIC THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `TT:real`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `C:real`; `TT:real`] C977CHA_HALF_ORDER) THEN
  MP_TAC(SPECL [`C:real`; `TT:real`] C977CC_LOW_COEFFICIENT) THEN
  MP_TAC(SPECL [`C:real`; `TT:real`] C977CC_WING_COEFFICIENT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C977CHA_HALF_TAC `c:real` `t:real` THEN C977CHA_HALF_TAC `C:real` `TT:real` THEN
  C977CHA_NORMAL_TAC THEN
  ASM_CASES_TAC `TT <= &3 / &5` THENL
  [MP_TAC(SPECL [`C:real`; `TT:real`] C977CHA_HALF_LOWER_SMALL) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC C977CC_CUBIC_CHORD THEN EXISTS_TAC `c977cha_half C TT` THEN
   ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[c977cha_half] THEN
    SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN NLIN_TAC [];
    MATCH_MP_TAC C977CHA_ENDPOINT_CUBIC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `C pow 2 + TT pow 2 = &1` THEN CONV_TAC REAL_RING;
    REWRITE_TAC[c977cc_h; REAL_POW_ONE; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(SPECL [`C:real`; `TT:real`] C977CHA_HALF_LOWER) THEN
  MP_TAC(SPECL [`C:real`; `TT:real`] C977CC_HIGH_TILT_COEFFICIENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `r = c977cha_half c t` THEN
  ABBREV_TAC `f = &2 - (&22 / &25) * TT pow 2 + C * TT - C - TT` THEN
  ABBREV_TAC `g = &1 + TT pow 2 + (&22 / &25) * C * TT + C - TT` THEN
  SUBGOAL_THEN `c977cc_h f g r =
                r * (&1 - &2 * f + &2 * r - r pow 2) + (&2 - g) * (&1 - r pow 2)`
  SUBST1_TAC THENL [REWRITE_TAC[c977cc_h] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN NLIN_TAC []);;
