(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeForeignFaces.lean      *)
(* (N12Compact.Completion.OtherCases.C983.NegativeForeignFaces).  The branch *)
(* in which the southeast and northeast separating faces belong to those two *)
(* squares; a unit-circle chord bound reduces the right square's angle to    *)
(* four endpoints.  Squares E, N, R are cE sE uE vE aE, cN sN uN vN aN,      *)
(* cR sR uR vR aR (unit normals / positive sides explicit).                  *)
(* RightTripleData.Input = ocrtd_input; NegativeTripleFaces.Data =           *)
(* ccntf_data; TopOnlyQuadrantProfile.Data = octoqp_data; upper / lower /    *)
(* ownU / ownV = ABT_upper / ABT_lower / ABT_OWNU / ABT_OWNV;                *)
(* C981CompletionSupportForms.lower_in_bands = C981SF_LOWER_IN_BANDS;        *)
(* NegativeCentralOrder.* = C983NCO_*; TopOnlyQuadrantScalars.profile_bounds *)
(* = OCTOQS_PROFILE_BOUNDS.  Lean `let` abbreviations are written out.       *)
(* Tag C983NFF_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeCentralOrder.ml";;
needs "n12/geometry/CP_OtherCases_RightTripleData.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyQuadrantScalars.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/ABTransverse.ml";;

let C983NFF_LIN = NLIN_TAC ~deg2:false [];;

let C983NFF_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; C983NFF_LIN]; ALL_TAC];;

let C983NFF_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C983NFF_LIN; ALL_TAC];;

let C983NFF_RING tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
     type_of(lhs(concl th)) = `:real`))) THEN CONV_TAC REAL_RING; ALL_TAC];;

let C983NFF_MIN0 = prove
 (`forall x. min x (&0) = (x - abs x) / &2`,
  GEN_TAC THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let C983NFF_POS_CANCEL = prove
 (`forall c g. &0 < c /\ &0 < c * g ==> &0 < g`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

let C983NFF_SPAN = prove
 (`forall A B D j. &0 <= A /\ &0 <= B /\ &0 < D /\ j <= &1 /\
     D pow 2 = (A + B) pow 2 - &2 * A * B * (&1 - j) ==> D <= A + B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983NFF_PROD `&0 <= A * B` THEN
  C983NFF_PROD `&0 <= (A * B) * (&1 - j)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C983NFF_PROD `&0 < (D - (A + B)) * (D + (A + B))` THEN C983NFF_LIN);;

let C983NFF_SCALE = prove
 (`forall A B D m X Y Z. &0 <= A /\ &0 <= B /\ &0 < D /\ D <= A + B /\ &0 <= m /\
     m <= X /\ m <= Y /\ D * Z = A * X + B * Y ==> m <= Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983NFF_PROD `&0 <= A * (X - m)` THEN C983NFF_PROD `&0 <= B * (Y - m)` THEN
  C983NFF_PROD `&0 <= m * ((A + B) - D)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C983NFF_PROD `&0 < D * (m - Z)` THEN C983NFF_LIN);;

(* Lean: arc_lower (private) *)
let C983NFF_ARC_LOWER = prove
 (`forall x y z w a b p q m.
     x pow 2 + y pow 2 = &1 /\ z pow 2 + w pow 2 = &1 /\ a pow 2 + b pow 2 = &1 /\
     &0 < x * w - y * z /\ &0 <= a * w - b * z /\ &0 <= x * b - y * a /\
     &0 <= m /\ m <= p * x + q * y /\ m <= p * z + q * w
     ==> m <= p * a + q * b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C983NFF_SCALE THEN
  MAP_EVERY EXISTS_TAC [`a * w - b * z`; `x * b - y * a`; `x * w - y * z`;
                        `p * x + q * y`; `p * z + q * w`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C983NFF_SPAN THEN EXISTS_TAC `x * z + y * w` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [NLIN_TAC ~deg2:false [SQ_NONNEG `x - z:real`; SQ_NONNEG `y - w:real`];
      UNDISCH_TAC `x pow 2 + y pow 2 = &1` THEN UNDISCH_TAC `z pow 2 + w pow 2 = &1` THEN
      UNDISCH_TAC `a pow 2 + b pow 2 = &1` THEN CONV_TAC REAL_RING];
    REAL_ARITH_TAC]);;

(* Lean: ordered (private) *)
let C983NFF_ORDERED = prove
 (`forall c t d r. &0 < c /\ &0 < t /\ &0 < d /\ &0 < r /\
     c pow 2 + t pow 2 = &1 /\ d pow 2 + r pow 2 = &1 /\ t < r
     ==> d < c /\ &0 < c * r - d * t /\ c * d + t * r <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983NFF_PROD `&0 < (r - t) * (r + t)` THEN
  SUBGOAL_THEN `d < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983NFF_PROD `&0 <= (d - c) * (d + c)` THEN C983NFF_LIN; ALL_TAC] THEN
  C983NFF_RING `(c * r - d * t) * (c * r + d * t) = r pow 2 - t pow 2` THEN
  C983NFF_PROD `&0 < c * r` THEN C983NFF_PROD `&0 < d * t` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983NFF_PROD `&0 <= (d * t - c * r) * (c * r + d * t)` THEN C983NFF_LIN;
    NLIN_TAC ~deg2:false [SQ_NONNEG `c - d:real`; SQ_NONNEG `t - r:real`]]);;
let C983NFF_UNIT_LT = prove
 (`forall x y. x pow 2 + y pow 2 = &1 /\ &0 < y ==> x < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983NFF_PROD `&0 < y * y` THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `x - &1`]);;

let C983NFF_UNIT_LE = prove
 (`forall x y. x pow 2 + y pow 2 = &1 ==> x <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `x - &1`; SQ_NONNEG `y:real`]);;

(* Lean: second_margins (private) *)
let C983NFF_SECOND_MARGINS = prove
 (`forall c t d r H.
     &3 / &4 < c /\ &0 < t /\ &0 < d /\ &0 < r /\
     c pow 2 + t pow 2 = &1 /\ d pow 2 + r pow 2 = &1 /\ t < r /\
     c + t - &1 < c * H
     ==> &0 < r * H + c - r * c + (c * d + t * r + c * r) - &2 * (c * d + t * r) /\
         &0 < r * H + c - r * c + (c * (c * d + t * r) + r) - &2 * (c * d + t * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983NFF_FACT `&0 < c` THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C983NFF_UNIT_LE) THEN
  MP_TAC(SPECL [`t:real`; `c:real`] C983NFF_UNIT_LT) THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C983NFF_UNIT_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `d:real`; `r:real`] C983NFF_ORDERED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C983NFF_RING `(c * r - d * t) pow 2 - (r - t) pow 2 = &2 * t * r * (&1 - (c * d + t * r))` THEN
  C983NFF_PROD `&0 < t * r` THEN
  C983NFF_PROD `&0 <= (t * r) * (&1 - (c * d + t * r))` THEN
  SUBGOAL_THEN `r - t <= c * r - d * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NFF_PROD `&0 < ((r - t) - (c * r - d * t)) * ((r - t) + (c * r - d * t))` THEN
    C983NFF_LIN; ALL_TAC] THEN
  C983NFF_FACT `r * (&1 - c) <= t * (&1 - d)` THEN
  C983NFF_PROD `&0 <= (&1 - t) * (t * (&1 - d) - r * (&1 - c))` THEN
  C983NFF_PROD `&0 < (&1 - t) * (&1 - d)` THEN
  C983NFF_RING `c pow 2 * (&1 - d) - t * (&1 - t) * (&1 - d) = (&1 - t) * (&1 - d)` THEN
  C983NFF_FACT `&0 < c pow 2 * (&1 - d) - r * (&1 - t) * (&1 - c)` THEN
  C983NFF_PROD `&0 <= (&1 - t) * (&1 - c) pow 2` THEN
  C983NFF_PROD `&0 < c * t` THEN
  SUBGOAL_THEN `&1 < c + t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983NFF_PROD `&0 <= (&1 - (c + t)) * (&1 + (c + t))` THEN C983NFF_LIN; ALL_TAC] THEN
  C983NFF_PROD `&0 <= (&1 - c) * (t - (&1 - c))` THEN
  C983NFF_PROD `&0 <= t * (&1 / &4 - (&1 - c))` THEN
  C983NFF_PROD `&0 <= t * (&1 - c) pow 2` THEN
  C983NFF_FACT `(&1 - t) * (&1 - c) pow 2 <= t / &4` THEN
  C983NFF_PROD `&0 < (c - &3 / &4) * (c + &3 / &4)` THEN
  C983NFF_PROD `&0 <= (&1 - c) * c pow 2` THEN
  C983NFF_FACT `&1 / &2 <= (&2 - c) * c pow 2` THEN
  C983NFF_PROD `&0 <= ((&2 - c) * c pow 2 - &1 / &2) * (r + t)` THEN
  C983NFF_PROD `&0 <= (t / &4 - (&1 - t) * (&1 - c) pow 2) * (c + d)` THEN
  C983NFF_PROD `&0 <= t * (&2 - (c + d))` THEN
  C983NFF_FACT `&0 <= (&2 - c) * c pow 2 * (r + t) - ((&1 - t) * (&1 - c) pow 2) * (c + d)` THEN
  C983NFF_RING `(c + d) * (c pow 2 - (&2 - c) * c pow 2 * d - r * ((&1 - t) * (&1 - c) pow 2) -
                 (&1 - t) * (&1 - c) pow 2) =
                (r - t) * ((&2 - c) * c pow 2 * (r + t) - ((&1 - t) * (&1 - c) pow 2) * (c + d))` THEN
  C983NFF_PROD `&0 <= (r - t) * ((&2 - c) * c pow 2 * (r + t) -
                                 ((&1 - t) * (&1 - c) pow 2) * (c + d))` THEN
  SUBGOAL_THEN `&0 <= c pow 2 - (&2 - c) * c pow 2 * d - r * ((&1 - t) * (&1 - c) pow 2)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NFF_PROD `&0 < (c + d) * (((&1 - t) * (&1 - c) pow 2) -
       (c pow 2 - (&2 - c) * c pow 2 * d - r * ((&1 - t) * (&1 - c) pow 2)))` THEN
    C983NFF_LIN; ALL_TAC] THEN
  C983NFF_PROD `&0 < r * (c * H - (c + t - &1))` THEN
  CONJ_TAC THEN MATCH_MP_TAC C983NFF_POS_CANCEL THEN EXISTS_TAC `c:real` THEN
  ASM_REWRITE_TAC[] THEN C983NFF_LIN);;
let C983NFF_ANGLE_FLOOR_CORE = prove
 (`forall c t d r a b m.
     &0 < c /\ &0 < t /\ &0 < d /\ &0 < r /\ &0 < a /\ &0 <= b /\
     c pow 2 + t pow 2 = &1 /\ d pow 2 + r pow 2 = &1 /\ a pow 2 + b pow 2 = &1 /\
     &0 < c * r - d * t /\ r <= c /\
     &0 <= m /\ m <= (c * d + t * r) + c * r /\ m <= c * (c * d + t * r) + r
     ==> m <= (c * d + t * r) * (a + b) - r * min (a * t - b * c) (&0) -
              c * min (b * d - a * r) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c * d + t * r <= &1` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [SQ_NONNEG `c - d:real`; SQ_NONNEG `t - r:real`]; ALL_TAC] THEN
  C983NFF_PROD `&0 <= (c - r) * (&1 - (c * d + t * r))` THEN
  C983NFF_FACT `m <= c + r * (c * d + t * r)` THEN
  C983NFF_RING `r * c pow 2 + r * t pow 2 = r` THEN
  C983NFF_RING `c * d pow 2 + c * r pow 2 = c` THEN
  ASM_CASES_TAC `&0 <= a * t - b * c` THENL
   [C983NFF_PROD `&0 < a * (c * r - d * t)` THEN
    C983NFF_PROD `&0 <= d * (a * t - b * c)` THEN
    SUBGOAL_THEN `b * d - a * r <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NFF_PROD `&0 < c * (b * d - a * r)` THEN C983NFF_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `min (a * t - b * c) (&0) = &0 /\ min (b * d - a * r) (&0) = b * d - a * r`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&1`; `&0`; `c:real`; `t:real`; `a:real`; `b:real`;
      `(c * d + t * r) + c * r`; `r * t`; `m:real`] C983NFF_ARC_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN C983NFF_LIN;
      DISCH_TAC THEN C983NFF_LIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `a * t - b * c <= &0` ASSUME_TAC THENL [C983NFF_LIN; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= b * d - a * r` THENL
   [SUBGOAL_THEN `min (a * t - b * c) (&0) = a * t - b * c /\ min (b * d - a * r) (&0) = &0`
      (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`d:real`; `r:real`; `&0`; `&1`; `a:real`; `b:real`;
      `c * d`; `(c * d + t * r) + c * r`; `m:real`] C983NFF_ARC_LOWER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN C983NFF_LIN;
      DISCH_TAC THEN C983NFF_LIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `min (a * t - b * c) (&0) = a * t - b * c /\
                min (b * d - a * r) (&0) = b * d - a * r`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `d:real`; `r:real`; `a:real`; `b:real`;
    `c * (d + r)`; `r * (c + t)`; `m:real`] C983NFF_ARC_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NFF_LIN;
    DISCH_TAC THEN C983NFF_LIN]);;

(* Lean: angle_floor (private) *)
let C983NFF_ANGLE_FLOOR = prove
 (`forall c t d r a b.
     &0 < c /\ &0 < t /\ &0 < d /\ &0 < r /\ &0 < a /\ &0 <= b /\
     c pow 2 + t pow 2 = &1 /\ d pow 2 + r pow 2 = &1 /\ a pow 2 + b pow 2 = &1 /\
     &0 < c * r - d * t /\ r <= c
     ==> min ((c * d + t * r) + c * r) (c * (c * d + t * r) + r) <=
         (c * d + t * r) * (a + b) - r * min (a * t - b * c) (&0) -
         c * min (b * d - a * r) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C983NFF_ANGLE_FLOOR_CORE THEN
  ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
  C983NFF_PROD `&0 < c * d` THEN C983NFF_PROD `&0 < t * r` THEN C983NFF_PROD `&0 < c * r` THEN
  C983NFF_PROD `&0 < c * (c * d + t * r)` THEN
  REWRITE_TAC[REAL_LE_MIN] THEN CONJ_TAC THEN C983NFF_LIN);;
(* Lean: first_shallow_margins (private) *)
let C983NFF_FIRST_SHALLOW_MARGINS = prove
 (`forall c t d r H.
     &0 < c /\ &0 < t /\ &0 < d /\ &29 / &100 < r /\ r < &3 / &4 /\
     c pow 2 + t pow 2 = &1 /\ d pow 2 + r pow 2 = &1 /\ t <= &9 / &41 /\
     &1 + (&4 / &5) * t - c < H
     ==> &0 < r * H + c - r * c + (c * d + t * r + c * r) - &2 * (c * d + t * r) /\
         &0 < r * H + c - r * c + (c * (c * d + t * r) + r) - &2 * (c * d + t * r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983NFF_FACT `&0 < r` THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C983NFF_UNIT_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C983NFF_FACT `t < &1` THEN
  C983NFF_PROD `&0 <= (&9 / &41 - t) * (&9 / &41 + t)` THEN
  SUBGOAL_THEN `&40 / &41 <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NFF_PROD `&0 < (&40 / &41 - c) * (&40 / &41 + c)` THEN C983NFF_LIN; ALL_TAC] THEN
  C983NFF_PROD `&0 < (r - &29 / &100) * (r + &29 / &100)` THEN
  SUBGOAL_THEN `d < &24 / &25` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983NFF_PROD `&0 <= (d - &24 / &25) * (d + &24 / &25)` THEN C983NFF_LIN; ALL_TAC] THEN
  C983NFF_PROD `&0 < (&1 - d) * (&7 * r - (&1 + d))` THEN
  SUBGOAL_THEN `r <= &7 * (&1 - d)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NFF_PROD `&0 < r * (r - &7 * (&1 - d))` THEN C983NFF_LIN; ALL_TAC] THEN
  C983NFF_PROD `&0 < r * (H - (&1 + (&4 / &5) * t - c))` THEN
  C983NFF_PROD `&0 <= (c - &40 / &41) * (&1 - d)` THEN
  C983NFF_PROD `&0 <= r * (&1 - c)` THEN
  C983NFF_PROD `&0 <= r * (&9 / &41 - t)` THEN
  C983NFF_FACT `&0 < c * (&1 - d) + r * (&1 - c - t / &5)` THEN
  C983NFF_PROD `&0 <= (&1 / &41 - (&1 - c)) * (&1 / &41 + (&1 - c))` THEN
  C983NFF_FACT `&2 / &3 <= c * (&2 - c) - (&7 / &5) * t` THEN
  C983NFF_PROD `&0 <= (&1 - c) * (&1 - c)` THEN
  C983NFF_FACT `c * (&1 - c) <= &1 / &41` THEN
  C983NFF_PROD `&0 <= (r * (&1 - c)) * (&2 - t)` THEN
  C983NFF_PROD `&0 <= t * (&7 * (&1 - d) - r)` THEN
  C983NFF_PROD `&0 <= (c * (&2 - c) - (&7 / &5) * t - &2 / &3) * (&1 - d)` THEN
  C983NFF_FACT `&0 < --(c * (&1 - c)) + c * (&2 - c) * (&1 - d) + r * (&1 - c) * (&2 - t) - r * t / &5` THEN
  CONJ_TAC THEN C983NFF_LIN);;
(* Lean: endpoint_margins (private) *)
let C983NFF_ENDPOINT_MARGINS = prove
 (`forall cE sE uE vE aE cN sN uN vN aN t.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     ccntf_data cE sE uE vE aE t /\ octoqp_data cN sN uN vN aN /\
     &1 < aN /\ t < --sN
     ==> &0 < (--sN) * (vE + aE) + cE - (--sN) * cE +
              (cE * cN + t * (--sN) + cE * (--sN)) - &2 * (cE * cN + t * (--sN)) /\
         &0 < (--sN) * (vE + aE) + cE - (--sN) * cE +
              (cE * (cE * cN + t * (--sN)) + (--sN)) - &2 * (cE * cN + t * (--sN))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`]
    C983NCO_COSINE_GT_SIX_SEVENTHS) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] C983NCO_NORTH_SINE_GT) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] OCTOQS_PROFILE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `octoqp_data cN sN uN vN aN` THEN REWRITE_TAC[octoqp_data] THEN STRIP_TAC THEN
  UNDISCH_TAC `ccntf_data cE sE uE vE aE t` THEN REWRITE_TAC[ccntf_data; IMP_CONJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `cE pow 2 + t pow 2 = &1 /\ cN pow 2 + (--sN) pow 2 = &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `cE * cE + --t * --t = &1` THEN UNDISCH_TAC `cN * cN + sN * sN = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [ASM_CASES_TAC `t <= &9 / &41` THENL
     [MATCH_MP_TAC C983NFF_FIRST_SHALLOW_MARGINS THEN ASM_REWRITE_TAC[] THEN C983NFF_LIN;
      ALL_TAC] THEN
    MATCH_MP_TAC C983NFF_SECOND_MARGINS THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY C983NFF_LIN THEN
    MP_TAC(SPECL [`t:real`; `cE:real`] C983NFF_UNIT_LT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cE pow 2 + t pow 2 = &1` THEN
      REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `&1 <= t + (&4 / &5) * cE` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NFF_PROD `&0 < (&1 - (t + (&4 / &5) * cE)) * (&1 - t + (&4 / &5) * cE)` THEN
      C983NFF_PROD `&0 <= (&41 * t - &9) * (&1 - t)` THEN C983NFF_LIN; ALL_TAC] THEN
    C983NFF_PROD `&0 <= t * ((t + (&4 / &5) * cE) - &1)` THEN
    C983NFF_PROD `&0 < cE * ((vE + aE) - (&1 + (&4 / &5) * t - cE))` THEN
    C983NFF_LIN;
    MATCH_MP_TAC C983NFF_SECOND_MARGINS THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY C983NFF_LIN THEN
    C983NFF_PROD `&0 < cE * (aE - &1)` THEN
    C983NFF_PROD `&0 < t * ((uE + aE) - &1)` THEN
    C983NFF_LIN]);;

(* Lean: lower_min (private) *)
let C983NFF_LOWER_MIN = prove
 (`forall c s u v a nx ny.
     ABT_lower c s u v a nx ny =
       (nx * c + ny * s) * u + (--nx * s + ny * c) * v +
       a * (min (nx * c + ny * s) (&0) + min (--nx * s + ny * c) (&0))`,
  REWRITE_TAC[C981SF_LOWER_IN_BANDS; C983NFF_MIN0] THEN REAL_ARITH_TAC);;
(* Lean: impossible *)
let C983NFF_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     ldisj cE sE uE vE aE cN sN uN vN aN /\
     ABT_upper cN sN uN vN aN cN sN <= ABT_lower cR sR uR vR aR cN sN /\
     ABT_upper cE sE uE vE aE (--sE) cE <= ABT_lower cR sR uR vR aR (--sE) cE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocrtd_input; ocrtd_rightprofile] o
    check (fun th -> can (term_match [] `ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR`) (concl th))) THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[ccntf_data] o
    check (fun th -> concl th = `ccntf_data cE sE uE vE aE (--sE)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[octoqp_data] o
    check (fun th -> concl th = `octoqp_data cN sN uN vN aN`)) THEN
  SUBGOAL_THEN `&1 < aN /\ &1 < aR` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `--sE`]
    C983NCO_SINE_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`]
    C983NCO_COSINE_GT_SIX_SEVENTHS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] OCTOQS_PROFILE_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `--sE`]
    C983NFF_ENDPOINT_MARGINS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `cE pow 2 + (--sE) pow 2 = &1 /\ cN pow 2 + (--sN) pow 2 = &1 /\
                cR pow 2 + (--sR) pow 2 = &1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `--sE`; `cN:real`; `--sN`] C983NFF_ORDERED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NFF_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `--sE`; `cN:real`; `--sN`; `cR:real`; `--sR`] C983NFF_ANGLE_FLOOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NFF_LIN; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `cR * --sE - --sR * cE = --sE * cR + cE * sR`;
              REAL_ARITH `--sR * cN - cR * --sN = --cN * sR + sN * cR`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] ABT_OWNU) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `ABT_upper cN sN uN vN aN cN sN <= ABT_lower cR sR uR vR aR cN sN` THEN
  UNDISCH_TAC `ABT_upper cE sE uE vE aE (--sE) cE <= ABT_lower cR sR uR vR aR (--sE) cE` THEN
  REWRITE_TAC[C983NFF_LOWER_MIN; ASSUME `ABT_upper cE sE uE vE aE (--sE) cE = vE + aE`;
              ASSUME `ABT_upper cN sN uN vN aN cN sN = uN + aN`] THEN
  C983NFF_PROD `&0 <= --sE * --sR` THEN C983NFF_PROD `&0 < cE * cR` THEN
  C983NFF_PROD `&0 <= --sN * --sR` THEN C983NFF_PROD `&0 < cN * cR` THEN
  SUBGOAL_THEN `min (-- --sE * sR + cE * cR) (&0) = &0 /\ min (cN * cR + sN * sR) (&0) = &0`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> min x (&0) = &0`) THEN C983NFF_LIN;
    ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `m = min ((cE * cN + --sE * --sN) + cE * --sN) (cE * (cE * cN + --sE * --sN) + --sN)` THEN
  ABBREV_TAC `m3 = min (--sE * cR + cE * sR) (&0)` THEN
  ABBREV_TAC `m6 = min (--cN * sR + sN * cR) (&0)` THEN
  SUBGOAL_THEN `m = (cE * cN + --sE * --sN) + cE * --sN \/ m = cE * (cE * cN + --sE * --sN) + --sN`
    ASSUME_TAC THENL [EXPAND_TAC "m" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m <= (cE * cN + --sE * --sN) + cE * --sN /\ m <= cE * (cE * cN + --sE * --sN) + --sN`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "m" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C983NFF_PROD `&0 < cE * cN` THEN C983NFF_PROD `&0 < --sE * --sN` THEN
  C983NFF_PROD `&0 < cE * --sN` THEN C983NFF_PROD `&0 < cE * (cE * cN + --sE * --sN)` THEN
  SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th -> is_disj(concl th) && is_eq(lhand(concl th)))) THEN
    C983NFF_LIN; ALL_TAC] THEN
  C983NFF_PROD `&0 <= ((cE * cN + --sE * --sN) * (cR + --sR) - --sN * m3 - cE * m6) * (aR - &1)` THEN
  C983NFF_PROD `&0 <= --sN * ((--sE * cR + cE * sR) * uR + (-- --sE * sR + cE * cR) * vR + aR * (m3 + &0) - (vE + aE))` THEN
  C983NFF_PROD `&0 <= cE * ((cN * cR + sN * sR) * uR + (--cN * sR + sN * cR) * vR + aR * (&0 + m6) - (uN + aN))` THEN
  C983NFF_PROD `&0 <= (cE * cN + --sE * --sN) * (&2 - (cR * (uR + aR) - sR * (vR + aR)))` THEN
  C983NFF_PROD `&0 < cE * ((uN + aN) - (&1 - --sN))` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) && is_eq(lhand(concl th)))) THEN
  C983NFF_LIN);;
