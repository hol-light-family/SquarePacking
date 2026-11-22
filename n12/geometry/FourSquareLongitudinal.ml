(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareLongitudinal.lean                      *)
(* (namespace N12Compact.FourSquareLongitudinal).                            *)
(* Exact scalar support inequalities for the positive four-square branch.    *)
(* All statements are purely scalar; no square representation is needed.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* p * (l - r) = 0 from |- l = r : a hint for linear combinations.          *)
let FSL_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Case split on the sign of x, replacing abs x everywhere.                 *)
let FSL_ABS_CASES_TAC x =
  ASM_CASES_TAC (mk_binop `(<=):real->real->bool` `&0` x) THENL
   [SUBGOAL_THEN (mk_eq(mk_comb(`abs`,x),x)) SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC];
    SUBGOAL_THEN (mk_eq(mk_comb(`abs`,x),mk_comb(`(--):real->real`,x))) SUBST_ALL_TAC THENL
     [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC]];;

(* Lean: canonical_bounds (private) *)
let FSL_CANONICAL_BOUNDS = prove
 (`forall C S. &0 < C /\ abs S <= C /\ C pow 2 + S pow 2 = &1
         ==> &7 / &10 <= C /\ C <= &1 /\ abs S <= &1 /\ C >= &1 - (&3 / &5) * S pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(SPEC `S:real` REAL_ABS_POS) THEN
  ASSUME_TAC(SPEC `S:real` REAL_POW2_ABS) THEN
  NLIN_FACTS_TAC [] [`abs S pow 2 <= C pow 2`; `C <= &1`; `&7 / &10 <= C`] THEN
  REWRITE_TAC[real_ge] THEN REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: positive_slope_margin *)
let FSL_POSITIVE_SLOPE_MARGIN = prove
 (`forall C S. &0 < C /\ &0 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1
         ==> &0 < (&1 - (&19 / &25) * S) * (&1 + C) + S * C - (&24 / &25) * C * (&1 + C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] FSL_CANONICAL_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= S ==> abs S = S`; real_ge] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (C - &1 + (&3 / &5) * S pow 2) * (&1 / &25 + (&6 / &25) * S)`] THEN
  ASM_CASES_TAC `S <= &1 / &2` THENL
   [NLIN_FACTS_TAC [SQ_NONNEG `S:real`] [`&0 <= S pow 2 * (&1 / &2 - S)`] THEN
    NLIN_TAC [SQ_NONNEG `&216 * S - &65`];
    NLIN_FACTS_TAC [SQ_NONNEG `S:real`] [`&0 <= S pow 2 * (&1 - S)`] THEN
    NLIN_TAC [SQ_NONNEG `S - &1 / &2`]]);;

(* y <= x from a positive multiple of x - y.                                  *)
let FSL_POS_MUL = prove
 (`forall x y. (exists k. &0 < k /\ &0 <= k * (x - y)) ==> y <= x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN NLIN_TAC []);;

let FSL_POS_MUL_TAC k = MATCH_MP_TAC FSL_POS_MUL THEN EXISTS_TAC k THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC];;

(* Lean: support_kernel (private) *)
let FSL_SUPPORT_KERNEL = prove
 (`forall c s C S. &0 < c /\ &0 <= s /\ s <= c /\ &0 < C /\ abs S <= C /\ C pow 2 + S pow 2 = &1
     ==> &2 * C * (c + (&24 / &25) * s) <=
         (c * C + s * S) * (C + abs S) + s + C * (c * C + s * S + abs(c * S - s * C)) -
         (&38 / &25) * s * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] FSL_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[real_ge] THEN STRIP_TAC THEN
  FSL_ABS_CASES_TAC `S:real` THENL
   [MP_TAC(SPECL [`C:real`; `S:real`] FSL_POSITIVE_SLOPE_MARGIN) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= s * ((&1 - (&19 / &25) * S) * (&1 + C) + S * C - (&24 / &25) * C * (&1 + C))`] THEN
    FSL_ABS_CASES_TAC `c * S - s * C` THEN FSL_POS_MUL_TAC `&1 + C` THENL
     [NLIN_FACTS_TAC [] [`&0 <= C * (&1 + C - S)`;
                         `&0 <= (C * (&1 + C - S)) * (c * S - s * C)`];
      NLIN_FACTS_TAC [] [`&0 <= S * C`; `&0 <= (S * C) * --(c * S - s * C)`]] THEN
    NLIN_TAC ~deg2:false
      [FSL_EQ_HINT `c * C + s * (&1 + C) / &2` (ASSUME `C pow 2 + S pow 2 = &1`)];
    NLIN_FACTS_TAC [SQ_NONNEG `C + S`]
     [`&0 <= C * --S`; `&1 <= C - S`; `&2 * C * --S <= &1`; `c * S - s * C <= &0`] THEN
    SUBGOAL_THEN `abs(c * S - s * C) = --(c * S - s * C)` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    FSL_POS_MUL_TAC `&1 + C` THEN
    NLIN_FACTS_TAC []
     [`&0 <= (c - s) * C`; `&0 <= ((c - s) * C) * (C - S - &1)`;
      `&0 <= (((c - s) * C) * (C - S - &1)) * (&1 + C)`;
      `&0 <= s * --S`; `&0 <= (s * --S) * ((&19 / &25) * (&1 + C) - &2 * C * --S)`;
      `&0 <= C * s`; `&0 <= (C * s) * (&1 + C)`] THEN
    NLIN_TAC ~deg2:false
      [FSL_EQ_HINT `s * (&3 * C - &1) / &2` (ASSUME `C pow 2 + S pow 2 = &1`)]]);;

(* Lean: left_support *)
let FSL_LEFT_SUPPORT = prove
 (`forall a c s C S X Y.
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\ &0 < C /\ abs S <= C /\
     C pow 2 + S pow 2 = &1 /\
     a * (C + abs S) / &2 <= X /\
     --S * (&19 / &25) + C * (&187 / &100) <= --S * X + C * Y - a / &2
     ==> c + (&283 / &100) * s <=
         c * X + s * Y + a / &2 * (c * C + s * S + abs(c * S - s * C))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C:real`; `S:real`] FSL_SUPPORT_KERNEL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASSUME_TAC(SPEC `S:real` REAL_ABS_POS) THEN
  ASSUME_TAC(SPEC `c * S - s * C` REAL_ABS_POS) THEN
  SUBGOAL_THEN `--C <= S /\ S <= C` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= C + S`; `&0 <= (c - s) * C`; `&0 <= s * (C + S)`; `&0 <= c * C + s * S`;
    `&0 <= c * C + s * S + abs(c * S - s * C)`;
    `&0 <= (c * C + s * S) * (C + abs S)`;
    `&0 <= C * (c * C + s * S + abs(c * S - s * C))`;
    `&0 <= (c * C + s * S) * (C + abs S) + s + C * (c * C + s * S + abs(c * S - s * C))`;
    `&0 <= (c * C + s * S) * (X - a * (C + abs S) / &2)`;
    `&0 <= s * (--S * X + C * Y - a / &2 + S * (&19 / &25) - C * (&187 / &100))`;
    `&0 <= (a - &1) * ((c * C + s * S) * (C + abs S) + s +
                       C * (c * C + s * S + abs(c * S - s * C)))`] THEN
  FSL_POS_MUL_TAC `C:real` THEN NLIN_TAC ~deg2:false []);;

(* Lean: b_axis_impossible *)
let FSL_B_AXIS_IMPOSSIBLE = prove
 (`forall a c s C S X Y.
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\ &0 < C /\ abs S <= C /\
     c pow 2 + s pow 2 = &1 /\ C pow 2 + S pow 2 = &1 /\
     a * (C + abs S) / &2 <= X /\
     --S * (&19 / &25) + C * (&187 / &100) <= --S * X + C * Y - a / &2 /\
     a <= s + (&293 / &500) * c /\
     c * X + s * Y + a / &2 * (c * C + s * S + abs(c * S - s * C)) + a <=
       &2 * c + (&1543 / &500) * s
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `c:real`; `s:real`; `C:real`; `S:real`; `X:real`; `Y:real`]
    FSL_LEFT_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `&10 < (&4379 / &500) * c + (&599 / &125) * s` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_TAC [SQ_NONNEG `(&599 / &125) * c - (&4379 / &500) * s`;
            SQ_NONNEG `(&4379 / &500) * c + (&599 / &125) * s - &10`]);;

(* Lean: smaller_angle_margin *)
let FSL_SMALLER_ANGLE_MARGIN = prove
 (`forall C S. &0 < C /\ &0 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1
         ==> &0 < C * (&1 - (&1157 / &1000) * S) + S + (&129 / &1000) * S pow 2 - &889 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`S <= &71 / &100`; `&0 <= S * (&71 / &100 - S)`;
    `&19 / &100 < &1706923 / &5000000 - (&149587 / &125000) * (S - &3 / &5) -
                  (&135529 / &100000) * (S - &3 / &5) pow 2`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `S - &3 / &5`]
   [`&0 <= (S - &3 / &5) pow 2 *
       ((&1706923 / &5000000 - (&149587 / &125000) * (S - &3 / &5) -
         (&135529 / &100000) * (S - &3 / &5) pow 2) - &19 / &100)`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&38 / &100) * (S - &3 / &5) - &60967 / &12500000`]
   [`&0 < &209679 / &1000000 - (&67 / &125) * S - (&431989 / &1000000) * S pow 2 +
         (&257 / &125) * S pow 3 - (&135529 / &100000) * S pow 4`;
    `&0 <= &1 - (&1157 / &1000) * S`;
    `&0 <= C * (&1 - (&1157 / &1000) * S)`] THEN
  REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&889 / &1000 - S - (&129 / &1000) * S pow 2) - C * (&1 - (&1157 / &1000) * S)`;
    `&0 <= (&889 / &1000 - S - (&129 / &1000) * S pow 2) + C * (&1 - (&1157 / &1000) * S)`;
    `&0 <= ((&889 / &1000 - S - (&129 / &1000) * S pow 2) - C * (&1 - (&1157 / &1000) * S)) *
           ((&889 / &1000 - S - (&129 / &1000) * S pow 2) + C * (&1 - (&1157 / &1000) * S))`] THEN
  NLIN_TAC ~deg2:false
    [FSL_EQ_HINT `(&1 - (&1157 / &1000) * S) pow 2` (ASSUME `C pow 2 + S pow 2 = &1`)]);;

(* Lean: shape_coefficients (private) *)
let FSL_SHAPE_COEFFICIENTS = prove
 (`forall c s. &0 < c /\ &0 <= s /\ s <= c /\ c pow 2 + s pow 2 = &1 /\ &34 / &25 < c + s
         ==> -- &889 / &1000 < c + s - &2 - (&293 / &500) * c * s /\
             c - s + (&293 / &500) * s pow 2 < &527 / &1000 /\ &12 / &25 < s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s - &97 / &250`; SQ_NONNEG `c - s`]
   [`&0 < (c + s - &34 / &25) * (c + s + &34 / &25)`; `c - s < &97 / &250`;
    `c + s <= &283 / &200`;
    `&0 <= (c + s - &34 / &25) * (&1 - (&293 / &1000) * (c + s + &34 / &25))`;
    `&0 <= (c - s) * (c + s - &34 / &25)`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: larger_angle_margin *)
let FSL_LARGER_ANGLE_MARGIN = prove
 (`forall C S. &0 < C /\ &0 <= S /\ S <= C /\ C pow 2 + S pow 2 = &1 /\ &12 / &25 <= S
         ==> &0 < &2 * C - &2 + S - (&152 / &125) * C * S + (&31 / &25) * S pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] FSL_CANONICAL_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= S ==> abs S = S`; real_ge] THEN STRIP_TAC THEN
  ASM_CASES_TAC `S <= &3 / &5` THENL
   [NLIN_FACTS_TAC []
     [`&0 <= S * (&3 / &5 - S)`; `&4 / &5 <= C`;
      `&0 <= (&1 - C) * ((&5 / &9) * C - &4 / &9)`;
      `&0 <= C - &1 + (&5 / &9) * S pow 2`;
      `&0 <= (C - &1 + (&5 / &9) * S pow 2) * (&2 - (&152 / &125) * S)`;
      `&0 <= (S - &12 / &25) * (S + &12 / &25)`;
      `&0 < -- &27 / &125 + (&29 / &225) * S + (&152 / &225) * S pow 2`;
      `&0 < S * (-- &27 / &125 + (&29 / &225) * S + (&152 / &225) * S pow 2)`];
    NLIN_FACTS_TAC []
     [`&0 <= (C - &1 + (&3 / &5) * S pow 2) * (&2 - (&152 / &125) * S)`;
      `&0 <= (S - &3 / &5) * (S + &3 / &5)`;
      `&0 < -- &27 / &125 + S / &25 + (&456 / &625) * S pow 2`;
      `&0 < S * (-- &27 / &125 + S / &25 + (&456 / &625) * S pow 2)`]] THEN
  NLIN_TAC []);;

let FSL_DIV_CANCEL = REAL_FIELD `forall x C. &0 < C ==> C * (x / C) = x`;;

(* Lean: l_axis_impossible *)
let FSL_L_AXIS_IMPOSSIBLE = prove
 (`forall a c s C S U.
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\ &0 < C /\ abs S <= C /\
     c pow 2 + s pow 2 = &1 /\ C pow 2 + S pow 2 = &1 /\
     &34 / &25 < c + s /\
     (&0 <= S ==> a * (&1 + S / C) + (&187 / &100) * S - ((&19 / &25) * S pow 2) / C <= U) /\
     (S <= &0 ==> a - ((&457 / &500) * S pow 2) / C + &2 * S <= U) /\
     (&0 <= c * S - s * C
      ==> U <= C * (&1 + c pow 2) + S * (&1543 / &500 + c * s) -
               a * (c * C + s * S + c * S - s * C)) /\
     (c * S - s * C <= &0
      ==> U <= C * (&2 + (&293 / &500) * c * s) + S * (&5 / &2 + (&293 / &500) * s pow 2) -
               a * (c * C + s * S - (c * S - s * C)))
     ==> false`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "ha hc hs hsc hC hSC hunit hLunit hw hwallPos hwallNeg hcapPos hcapNeg" THEN
  MP_TAC(SPECL [`C:real`; `S:real`] FSL_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[real_ge] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FSL_CANONICAL_BOUNDS) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= s ==> abs s = s`; real_ge] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FSL_SHAPE_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--C <= S /\ S <= C` STRIP_ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= C + S`; `&0 <= (c - s) * C`; `&0 <= s * (C + S)`;
                     `&0 <= c * C + s * S`; `&0 <= a - &1`] THEN
  MAP_EVERY (fun t -> ASSUME_TAC(UNDISCH(SPECL [t; `C:real`] FSL_DIV_CANCEL)))
    [`S:real`; `(&19 / &25) * S pow 2`; `(&457 / &500) * S pow 2`] THEN
  ASM_CASES_TAC `&0 <= c * S - s * C` THENL
   [(* positive relative angle *)
    NLIN_FACTS_TAC [] [`&0 < s * C`; `&0 < S`] THEN
    SUBGOAL_THEN `s <= S` ASSUME_TAC THENL
     [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      NLIN_FACTS_TAC [] [`&0 < (s - S) * (s + S)`; `c < C`;
                         `c * (S - s) < &0`; `&0 <= s * (C - c)`] THEN
      NLIN_TAC ~deg2:false [];
      ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (S - s) * (S + s)`; `C <= c`;
      `&0 <= (c - s) * C`; `&0 <= s * (C - S)`; `&0 <= c * C - s * S`;
      `&0 <= (c * S - s * C) * (c * C - s * S)`] THEN
    SUBGOAL_THEN `(c * S - s * C) * (c * C - s * S) = C * S - c * s` ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `c + s <= C + S` ASSUME_TAC THENL
     [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      NLIN_FACTS_TAC [] [`&0 < (c + s - (C + S)) * (c + s + (C + S))`] THEN
      NLIN_TAC ~deg2:false [];
      ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (c - C) * (&2 - c - C)`;
      `C - S - &1 - C pow 2 <= c - s - &1 - c pow 2`;
      `&0 <= (C + S - (c + s)) * (C + S + c + s - &2)`;
      `C + S - &152 / &125 - C * S <= c + s - &152 / &125 - c * s`;
      `&0 <= C pow 2 * ((c - s - &1 - c pow 2) - (C - S - &1 - C pow 2))`;
      `&0 <= S * C`;
      `&0 <= (S * C) * ((c + s - &152 / &125 - c * s) - (C + S - &152 / &125 - C * S))`] THEN
    MP_TAC(SPECL [`C:real`; `S:real`] FSL_LARGER_ANGLE_MARGIN) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= S / C` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN RASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "hwallPos" (fun th -> MP_TAC(MATCH_MP th
      (MATCH_MP REAL_LT_IMP_LE (ASSUME `&0 < S`)))) THEN
    USE_THEN "hcapPos" (fun th -> MP_TAC(MATCH_MP th (ASSUME `&0 <= c * S - s * C`))) THEN
    REPEAT DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= &1 + S / C + (c * C + s * S) + (c * S - s * C)`;
      `&0 <= (a - &1) * (&1 + S / C + (c * C + s * S) + (c * S - s * C))`] THEN
    SUBGOAL_THEN `&1 + S / C + (c * C + s * S) + (c * S - s * C) <=
        C * (&1 + c pow 2) + S * (&152 / &125 + c * s) + ((&19 / &25) * S pow 2) / C`
      ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= C * ((C * (&1 + c pow 2) + S * (&152 / &125 + c * s) +
                   ((&19 / &25) * S pow 2) / C) -
                  (&1 + S / C + (c * C + s * S) + (c * S - s * C)))`] THEN
    NLIN_TAC ~deg2:false
      [FSL_EQ_HINT `C - C pow 2 - &2` (ASSUME `C pow 2 + S pow 2 = &1`)];
    ALL_TAC] THEN
  POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
  SUBGOAL_THEN `c * S - s * C <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "hcapNeg" (fun th -> MP_TAC(MATCH_MP th (ASSUME `c * S - s * C <= &0`))) THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `S <= &0` THENL
   [(* negative relative angle, S <= 0 *)
    USE_THEN "hwallNeg" (fun th -> MP_TAC(MATCH_MP th (ASSUME `S <= &0`))) THEN
    DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= &1 + (c * C + s * S) - (c * S - s * C)`;
      `&0 <= (a - &1) * (&1 + (c * C + s * S) - (c * S - s * C))`] THEN
    SUBGOAL_THEN `&1 + (c * C + s * S) - (c * S - s * C) <=
        C * (&2 + (&293 / &500) * c * s) + S * (&1 / &2 + (&293 / &500) * s pow 2) +
        ((&457 / &500) * S pow 2) / C`
      ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `s:real`; SQ_NONNEG `C:real`]
     [`&0 <= C * ((C * (&2 + (&293 / &500) * c * s) + S * (&1 / &2 + (&293 / &500) * s pow 2) +
                   ((&457 / &500) * S pow 2) / C) -
                  (&1 + (c * C + s * S) - (c * S - s * C)))`;
      `c * s <= &1 / &2`;
      `&0 <= C pow 2 * (c + s - &2 - (&293 / &500) * c * s + &943 / &1000)`;
      `&0 <= c - s + (&293 / &500) * s pow 2`;
      `&0 <= --S * C`; `&0 <= (--S * C) * (c - s + (&293 / &500) * s pow 2)`;
      `&0 <= (C + S) * (C - S)`; `&0 <= --S * (C + S)`; `&0 < C * C`;
      `&0 < C - (&943 / &1000) * C pow 2 - S * C / &2 - (&457 / &500) * S pow 2`] THEN
    NLIN_TAC ~deg2:false [];
    (* negative relative angle, S >= 0 *)
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "hwallPos" (fun th -> MP_TAC(MATCH_MP th (ASSUME `&0 <= S`))) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= S / C` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= &1 + S / C + (c * C + s * S) - (c * S - s * C)`;
      `&0 <= (a - &1) * (&1 + S / C + (c * C + s * S) - (c * S - s * C))`] THEN
    SUBGOAL_THEN `&1 + S / C + (c * C + s * S) - (c * S - s * C) <=
        C * (&2 + (&293 / &500) * c * s) + S * (&63 / &100 + (&293 / &500) * s pow 2) +
        ((&19 / &25) * S pow 2) / C`
      ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    MP_TAC(SPECL [`C:real`; `S:real`] FSL_SMALLER_ANGLE_MARGIN) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `C:real`]
     [`&0 <= C * ((C * (&2 + (&293 / &500) * c * s) + S * (&63 / &100 + (&293 / &500) * s pow 2) +
                   ((&19 / &25) * S pow 2) / C) -
                  (&1 + S / C + (c * C + s * S) - (c * S - s * C)))`;
      `&0 <= C pow 2 * (c + s - &2 - (&293 / &500) * c * s + &889 / &1000)`;
      `&0 <= S * C`;
      `&0 <= (S * C) * (&527 / &1000 - (c - s + (&293 / &500) * s pow 2))`] THEN
    NLIN_TAC ~deg2:false []]);;
