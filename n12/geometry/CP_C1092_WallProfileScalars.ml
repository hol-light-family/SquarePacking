(* ========================================================================= *)
(* Port of Compact/Completion/C1092/WallProfileScalars.lean                  *)
(* (N12Compact.C1092WallProfileScalars).  The continuous two-angle envelope  *)
(* of the direct corner-to-wall transfer (pure scalar algebra).              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

let C1092WPS_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092WPS_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092WPS_LIN_TAC; DISCH_TAC];;

(* REAL_ARITH using only the assumptions mentioning pat *)
let C1092WPS_RA_WITH pat (asl,w as g) =
  let hs = filter (fun (_,th) -> can (find_term ((=) pat)) (concl th)) asl in
  (MAP_EVERY (MP_TAC o snd) hs THEN REAL_ARITH_TAC) g;;

(* Lean: half *)
let C1092WPS_half = new_definition
 `C1092WPS_half (c:real) (s:real) = s / (&1 + c)`;;

(* Lean: profile *)
let C1092WPS_profile = new_definition
 `C1092WPS_profile (c:real) (s:real) = c - s * (c + s) / (&1 + c)`;;

(* helper: cancellation of a positive factor *)
let C1092WPS_CANCEL = prove
 (`(forall f l. &0 < l /\ &0 <= f * l ==> &0 <= f) /\
   (forall f l. &0 < l /\ f * l <= &0 ==> f <= &0)`,
  CONJ_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`--f`; `l:real`] REAL_LT_MUL); MP_TAC(SPECL [`f:real`; `l:real`] REAL_LT_MUL)] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: quarter_data *)
let C1092WPS_QUARTER_DATA = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> &0 <= C1092WPS_half c s /\ C1092WPS_half c s <= &1 /\
             C1092WPS_half c s * (&1 + c) = s /\
             (&1 + C1092WPS_half c s pow 2) * c = &1 - C1092WPS_half c s pow 2 /\
             (&1 + C1092WPS_half c s pow 2) * s = &2 * C1092WPS_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C1092WPS_half] THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [C1092WPS_LIN_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s - &1`] [`s <= &1`] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_DIV_RMUL;
               REAL_ARITH `&0 < x ==> ~(x = &0)`] THEN
  CONJ_TAC THENL [C1092WPS_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&1 + c = &0)` MP_TAC THENL [C1092WPS_LIN_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_FIELD);;

(* Lean: cubic (private) *)
let C1092WPS_CUBIC = prove
 (`forall a b c d z. &0 <= z /\ z <= &1 /\
     &0 <= &3 * a /\ &0 <= &3 * a + b /\ &0 <= &3 * a + &2 * b + c /\
     &0 <= &3 * (a + b + c + d)
     ==> &0 <= a + b * z + c * z pow 2 + d * z pow 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - z) pow 3 /\ &0 <= z * (&1 - z) pow 2 /\
                &0 <= z pow 2 * (&1 - z) /\ &0 <= z pow 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN C1092WPS_LIN_TAC;
    ALL_TAC] THEN
  C1092WPS_LE_MUL_TAC `&3 * a` `(&1 - z) pow 3` THEN
  C1092WPS_LE_MUL_TAC `&3 * a + b` `z * (&1 - z) pow 2` THEN
  C1092WPS_LE_MUL_TAC `&3 * a + &2 * b + c` `z pow 2 * (&1 - z)` THEN
  C1092WPS_LE_MUL_TAC `&3 * (a + b + c + d)` `z pow 3` THEN
  C1092WPS_LIN_TAC);;

(* Lean: plus (private def) *)
let C1092WPS_plus = new_definition
 `C1092WPS_plus (x:real) (y:real) =
    y pow 2 * (&2 - y) + &2 * x * (&1 - y - y pow 2) +
    x pow 2 * (-- &2 - &4 * y + &4 * y pow 2 - y pow 3) + &2 * y * x pow 3`;;

(* Lean: minus (private def) *)
let C1092WPS_minus = new_definition
 `C1092WPS_minus (x:real) (y:real) =
    -- &1 + &3 * y pow 2 - y pow 3 + &2 * x * (&1 + y - y pow 2) +
    x pow 2 * (-- &1 - &4 * y + &3 * y pow 2 - y pow 3) + &2 * y * x pow 3`;;

(* power facts for y in [0,1] *)
let C1092WPS_POWERS = prove
 (`forall y. &0 <= y /\ y <= &1
       ==> &0 <= y pow 2 /\ &0 <= y pow 3 /\ &0 <= y pow 4 /\ &0 <= y pow 5 /\
           y pow 2 <= &1 /\ y pow 3 <= &1 /\ y pow 4 <= &1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POW_1_LE]);;

(* Lean: coefficient_bounds (private) *)
let C1092WPS_COEFFICIENT_BOUNDS = prove
 (`forall y. &0 <= y /\ y <= &1
       ==> &0 <= &2 + y pow 3 * (&13 + &13 * y - y pow 2 - &3 * y pow 3) /\
           &0 <= &2 * (&1 - y) + &4 * y pow 2 + &8 * y pow 3 + &10 * y pow 4 +
                 y pow 5 * (&6 - &4 * y) /\
           &0 <= y pow 2 * (&8 + &18 * y + y pow 2 * (&14 - &2 * y pow 2) + &2 * y pow 3) /\
           &0 <= y pow 2 * (&12 - &2 * y pow 4 + &22 * y + &6 * y pow 2 * (&1 - y))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092WPS_POWERS) THEN
  POP_ASSUM_LIST(MAP_EVERY STRIP_ASSUME_TAC) THEN
  C1092WPS_LE_MUL_TAC `y pow 3` `&13 + &13 * y - y pow 2 - &3 * y pow 3` THEN
  C1092WPS_LE_MUL_TAC `y pow 5` `&6 - &4 * y` THEN
  C1092WPS_LE_MUL_TAC `y pow 2` `&1 - y` THEN
  C1092WPS_LE_MUL_TAC `y pow 2` `&14 - &2 * y pow 2` THEN
  REPEAT CONJ_TAC THEN TRY C1092WPS_LIN_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN C1092WPS_LIN_TAC);;

(* Lean: plus_nonneg (private) *)
let C1092WPS_PLUS_NONNEG = prove
 (`forall x y. &0 <= x /\ &0 <= y /\ y <= &1 /\ x * (&1 + y) <= &1 - y
         ==> &0 <= C1092WPS_plus x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `y = &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `x = &0` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN C1092WPS_LIN_TAC; ALL_TAC] THEN
    REWRITE_TAC[C1092WPS_plus] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - y` ASSUME_TAC THENL
   [UNDISCH_TAC `~(y = &1)` THEN UNDISCH_TAC `y <= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists z. z * (&1 - y) = x * (&1 + y) /\ &0 <= z /\ z <= &1` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(x * (&1 + y)) / (&1 - y)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C1092WPS_LIN_TAC; C1092WPS_LIN_TAC];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN C1092WPS_LIN_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real` C1092WPS_COEFFICIENT_BOUNDS) THEN
  MP_TAC(SPEC `y:real` C1092WPS_POWERS) THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`y pow 2 * (&2 - y) * (&1 + y) pow 3`;
    `&2 * (&1 - y - y pow 2) * (&1 - y) * (&1 + y) pow 2`;
    `(-- &2 - &4 * y + &4 * y pow 2 - y pow 3) * (&1 - y) pow 2 * (&1 + y)`;
    `&2 * y * (&1 - y) pow 3`; `z:real`] C1092WPS_CUBIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= y pow 2 * (&2 - y) * (&1 + y) pow 3 /\
                  &0 <= y pow 3 * (&3 - y) * (&1 + y pow 2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN C1092WPS_LIN_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN C1092WPS_LIN_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `(&1 + y) pow 3 * C1092WPS_plus x y =
    y pow 2 * (&2 - y) * (&1 + y) pow 3 +
    (&2 * (&1 - y - y pow 2) * (&1 - y) * (&1 + y) pow 2) * z +
    ((-- &2 - &4 * y + &4 * y pow 2 - y pow 3) * (&1 - y) pow 2 * (&1 + y)) * z pow 2 +
    (&2 * y * (&1 - y) pow 3) * z pow 3` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_plus] THEN UNDISCH_TAC `z * (&1 - y) = x * (&1 + y)` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(CONJUNCT1 C1092WPS_CANCEL) THEN EXISTS_TAC `(&1 + y) pow 3` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN C1092WPS_LIN_TAC; C1092WPS_LIN_TAC]);;

(* Lean: minus_nonneg (private) *)
let C1092WPS_MINUS_NONNEG = prove
 (`forall x y. x <= &1 /\ &0 <= y /\ y <= &1 /\ &1 - y <= x * (&1 + y)
         ==> &0 <= C1092WPS_minus x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `y = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `x = &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN C1092WPS_LIN_TAC; ALL_TAC] THEN
    REWRITE_TAC[C1092WPS_minus] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * y` ASSUME_TAC THENL
   [UNDISCH_TAC `~(y = &0)` THEN UNDISCH_TAC `&0 <= y` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092WPS_LE_MUL_TAC `&1 - x` `&1 + y` THEN
  SUBGOAL_THEN `exists z. z * (&2 * y) = x * (&1 + y) - (&1 - y) /\ &0 <= z /\ z <= &1`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(x * (&1 + y) - (&1 - y)) / (&2 * y)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN C1092WPS_LIN_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN C1092WPS_LIN_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `y:real` C1092WPS_COEFFICIENT_BOUNDS) THEN
  MP_TAC(SPEC `y:real` C1092WPS_POWERS) THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  let pA = `-- &1 + &3 * y pow 2 - y pow 3` and pB = `&2 * (&1 + y - y pow 2)`
  and pC = `-- &1 - &4 * y + &3 * y pow 2 - y pow 3` and pD = `&2 * y` in
  let sb = subst [pA,`AA:real`; pB,`BB:real`; pC,`CC:real`; pD,`DD:real`] in
  let ta = sb `AA * (&1 + y) pow 3 + BB * (&1 - y) * (&1 + y) pow 2 +
               CC * (&1 - y) pow 2 * (&1 + y) + DD * (&1 - y) pow 3`
  and tb = sb `BB * (&2 * y) * (&1 + y) pow 2 + &2 * CC * (&1 - y) * (&2 * y) * (&1 + y) +
               &3 * DD * (&1 - y) pow 2 * (&2 * y)`
  and tc = sb `CC * (&2 * y) pow 2 * (&1 + y) + &3 * DD * (&1 - y) * (&2 * y) pow 2`
  and td = sb `DD * (&2 * y) pow 3` in
  MP_TAC(SPECL [ta; tb; tc; td; `z:real`] C1092WPS_CUBIC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= y pow 3 * (&3 - y) * (&1 + y pow 2) /\
                  &0 <= y pow 2 * (&2 - y) * (&1 + y) pow 3` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN C1092WPS_LIN_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN C1092WPS_LIN_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN (mk_eq(`(&1 + y) pow 3 * C1092WPS_minus x y`,
    list_mk_binop `(+):real->real->real`
     [ta; mk_binop `( * ):real->real->real` tb `z:real`;
      mk_binop `( * ):real->real->real` tc `z pow 2`;
      mk_binop `( * ):real->real->real` td `z pow 3`])) ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_minus] THEN
    UNDISCH_TAC `z * (&2 * y) = x * (&1 + y) - (&1 - y)` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(CONJUNCT1 C1092WPS_CANCEL) THEN EXISTS_TAC `(&1 + y) pow 3` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN C1092WPS_LIN_TAC; C1092WPS_LIN_TAC]);;

(* common setup: half-angle variables for (c,s) and (r,t) *)
let C1092WPS_HALF_TAC (c,s,r,t) =
  MP_TAC(SPECL [r; t] C1092WPS_QUARTER_DATA) THEN
  MP_TAC(SPECL [c; s] C1092WPS_QUARTER_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC (mk_eq(`x:real`, list_mk_comb(`C1092WPS_half`,[r; t]))) THEN
  ABBREV_TAC (mk_eq(`y:real`, list_mk_comb(`C1092WPS_half`,[c; s]))) THEN
  REPEAT STRIP_TAC;;

(* profile c s = 2c - 1 - c y *)
let C1092WPS_PROFILE_FORM = prove
 (`forall c s y. &0 <= c /\ y * (&1 + c) = s /\ (&1 + y pow 2) * c = &1 - y pow 2
           ==> C1092WPS_profile c s = &2 * c - &1 - c * y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092WPS_profile] THEN
  SUBGOAL_THEN `s * (c + s) / (&1 + c) = y * (c + s)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(K ALL_TAC) THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `~(&1 + c = &0)` MP_TAC THENL
     [UNDISCH_TAC `&0 <= c` THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

(* Lean: envelope *)
let C1092WPS_ENVELOPE = prove
 (`forall c s r t. &0 <= c /\ &0 <= s /\ &0 <= r /\ &0 <= t /\
             c pow 2 + s pow 2 = &1 /\ r pow 2 + t pow 2 = &1
             ==> C1092WPS_profile c s <=
                 c * t + s * r + max (c * r - s * t) (&0) + s * t / (&1 + r) -
                 (&3 / &2) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092WPS_HALF_TAC (`c:real`,`s:real`,`r:real`,`t:real`) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `y:real`] C1092WPS_PROFILE_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `s * t / (&1 + r) = s * x` SUBST1_TAC THENL
   [UNDISCH_TAC `x * (&1 + r) = t` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `~(&1 + r = &0)` MP_TAC THENL
     [UNDISCH_TAC `&0 <= r` THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + x pow 2) * (&1 + y pow 2) * (c * r - s * t) =
                (&1 - y - x * (&1 + y)) * (&1 + y + x * (&1 - y))` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th)))) THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092WPS_LE_MUL_TAC `x:real` `&1 - y` THEN
  SUBGOAL_THEN `&0 < &1 + y + x * (&1 - y) /\ &0 < (&1 + x pow 2) * (&1 + y pow 2)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [C1092WPS_LIN_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c * r - s * t` THENL
   [SUBGOAL_THEN `max (c * r - s * t) (&0) = c * r - s * t` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[real_max] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `x * (&1 + y) <= &1 - y` ASSUME_TAC THENL
     [MP_TAC(SPECL [`&1 - y - x * (&1 + y)`; `&1 + y + x * (&1 - y)`]
        (CONJUNCT1 C1092WPS_CANCEL)) THEN
      MP_TAC(SPECL [`(&1 + x pow 2) * (&1 + y pow 2)`; `c * r - s * t`] REAL_LE_MUL) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC]; DISCH_TAC] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [C1092WPS_LIN_TAC; C1092WPS_RA_WITH `c * r - s * t`];
        DISCH_TAC THEN C1092WPS_LIN_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`x:real`; `y:real`] C1092WPS_PLUS_NONNEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(&1 + x pow 2) * (&1 + y pow 2) *
      (c * t + s * r + (c * r - s * t) + s * x - (&3 / &2) * s - (&2 * c - &1 - c * y)) =
      C1092WPS_plus x y` ASSUME_TAC THENL
     [REWRITE_TAC[C1092WPS_plus] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        not (can (find_term ((=) `c * r - s * t`)) (concl th))))) THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MP_TAC(SPECL
     [`c * t + s * r + (c * r - s * t) + s * x - (&3 / &2) * s - (&2 * c - &1 - c * y)`;
      `(&1 + x pow 2) * (&1 + y pow 2)`] (CONJUNCT1 C1092WPS_CANCEL)) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [C1092WPS_LIN_TAC; C1092WPS_RA_WITH `C1092WPS_plus x y`];
                    REAL_ARITH_TAC];
    SUBGOAL_THEN `max (c * r - s * t) (&0) = &0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[real_max] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 - y <= x * (&1 + y)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`&1 - y - x * (&1 + y)`; `&1 + y + x * (&1 - y)`]
        (CONJUNCT2 C1092WPS_CANCEL)) THEN
      MP_TAC(SPECL [`(&1 + x pow 2) * (&1 + y pow 2)`; `--(c * r - s * t)`] REAL_LE_MUL) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC]; DISCH_TAC] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [C1092WPS_LIN_TAC; C1092WPS_RA_WITH `c * r - s * t`];
        DISCH_TAC THEN C1092WPS_LIN_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`x:real`; `y:real`] C1092WPS_MINUS_NONNEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(&1 + x pow 2) * (&1 + y pow 2) *
      (c * t + s * r + s * x - (&3 / &2) * s - (&2 * c - &1 - c * y)) =
      C1092WPS_minus x y` ASSUME_TAC THENL
     [REWRITE_TAC[C1092WPS_minus] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        not (can (find_term ((=) `c * r - s * t`)) (concl th))))) THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MP_TAC(SPECL
     [`c * t + s * r + s * x - (&3 / &2) * s - (&2 * c - &1 - c * y)`;
      `(&1 + x pow 2) * (&1 + y pow 2)`] (CONJUNCT1 C1092WPS_CANCEL)) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [C1092WPS_LIN_TAC; C1092WPS_RA_WITH `C1092WPS_minus x y`];
                    REAL_ARITH_TAC]]);;

(* Lean: boundary_cap *)
let C1092WPS_BOUNDARY_CAP = prove
 (`forall c s p q. &0 <= c /\ &0 <= s /\ &0 <= p /\ &0 <= q /\
             c pow 2 + s pow 2 = &1 /\ p pow 2 + q pow 2 = &1
             ==> c * (&2 - p - C1092WPS_half p q) - s * q + min (c * q - s * p) (&0) <=
                 C1092WPS_profile c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092WPS_HALF_TAC (`c:real`,`s:real`,`p:real`,`q:real`) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `y:real`] C1092WPS_PROFILE_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c:real`] [`c <= &1`; `s <= &1`] THEN
  C1092WPS_LE_MUL_TAC `c:real` `s:real` THEN
  NLIN_FACTS_TAC [] [`&1 <= c + s`] THEN
  SUBGOAL_THEN `(&1 + x pow 2) * (&1 + y pow 2) * (c * q - s * p) =
                (x - y) * (&2 * (&1 + x * y))` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th)))) THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092WPS_LE_MUL_TAC `x:real` `y:real` THEN
  SUBGOAL_THEN `&0 < &2 * (&1 + x * y) /\ &0 < (&1 + x pow 2) * (&1 + y pow 2) /\
                &0 < &1 + x pow 2` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [C1092WPS_LIN_TAC; MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= c * q - s * p` THENL
   [SUBGOAL_THEN `min (c * q - s * p) (&0) = &0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= x - y` ASSUME_TAC THENL
     [MP_TAC(SPECL [`(&1 + x pow 2) * (&1 + y pow 2)`; `c * q - s * p`] REAL_LE_MUL) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC]; DISCH_TAC] THEN
      MATCH_MP_TAC(CONJUNCT1 C1092WPS_CANCEL) THEN EXISTS_TAC `&2 * (&1 + x * y)` THEN
      CONJ_TAC THENL [C1092WPS_LIN_TAC; C1092WPS_RA_WITH `c * q - s * p`];
      ALL_TAC] THEN
    C1092WPS_LE_MUL_TAC `c:real` `x:real` THEN
    C1092WPS_LE_MUL_TAC `&1 - c` `x:real` THEN
    C1092WPS_LE_MUL_TAC `&1 - x` `&1 - c * x` THEN
    C1092WPS_LE_MUL_TAC `x - y` `c * x pow 2 - (&1 + c) * x + c + s` THEN
    SUBGOAL_THEN
     `(&1 + x pow 2) * ((&2 * c - &1 - c * y) - (c * (&2 - p - x) - s * q)) =
      (x - y) * (c * x pow 2 - (&1 + c) * x + c + s)` ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        not (can (find_term ((=) `c * q - s * p`)) (concl th))))) THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MP_TAC(SPECL [`(&2 * c - &1 - c * y) - (c * (&2 - p - x) - s * q)`; `&1 + x pow 2`]
      (CONJUNCT1 C1092WPS_CANCEL)) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [C1092WPS_LIN_TAC; C1092WPS_RA_WITH `x - y`];
                    REAL_ARITH_TAC];
    SUBGOAL_THEN `min (c * q - s * p) (&0) = c * q - s * p` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= y - x` ASSUME_TAC THENL
     [MP_TAC(SPECL [`(&1 + x pow 2) * (&1 + y pow 2)`; `--(c * q - s * p)`] REAL_LE_MUL) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ASM_REAL_ARITH_TAC]; DISCH_TAC] THEN
      MATCH_MP_TAC(CONJUNCT1 C1092WPS_CANCEL) THEN EXISTS_TAC `&2 * (&1 + x * y)` THEN
      CONJ_TAC THENL [C1092WPS_LIN_TAC; C1092WPS_RA_WITH `c * q - s * p`];
      ALL_TAC] THEN
    C1092WPS_LE_MUL_TAC `c:real` `&1 - x` THEN
    C1092WPS_LE_MUL_TAC `x:real` `&1 + s + c * (&1 - x)` THEN
    C1092WPS_LE_MUL_TAC `y - x` `--c * x pow 2 + (&1 + c + s) * x + &1 - s` THEN
    SUBGOAL_THEN
     `(&1 + x pow 2) * ((&2 * c - &1 - c * y) -
        (c * (&2 - p - x) - s * q + (c * q - s * p))) =
      (y - x) * (--c * x pow 2 + (&1 + c + s) * x + &1 - s)` ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        not (can (find_term ((=) `c * q - s * p`)) (concl th))))) THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MP_TAC(SPECL [`(&2 * c - &1 - c * y) - (c * (&2 - p - x) - s * q + (c * q - s * p))`;
                  `&1 + x pow 2`] (CONJUNCT1 C1092WPS_CANCEL)) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [C1092WPS_LIN_TAC; C1092WPS_RA_WITH `y - x`];
                    REAL_ARITH_TAC]]);;
