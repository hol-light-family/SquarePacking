(* ========================================================================= *)
(* Port of Compact/Geometry/WallChain.lean (N12Compact.WallChain).           *)
(* Algebraic wall-chain summation: n+1 centres, n edges, selected normals.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: variation  (sum over Finset.range n = {i | i < n}) *)
let WCH_variation = new_definition
 `WCH_variation (s:num->real) n = sum {i | i < n} (\i. abs(s(i + 1) - s i))`;;

(* Lean: transverseLoss *)
let WCH_transverseLoss = new_definition
 `WCH_transverseLoss (b:num->real) (y:num->real) n =
    sum {i | i < n} (\i. b i * (y(i + 1) - y i))`;;

let WCH_VARIATION_CLAUSES = prove
 (`(forall s. WCH_variation s 0 = &0) /\
   (forall s n. WCH_variation s (SUC n) = WCH_variation s n + abs(s(n + 1) - s n))`,
  REWRITE_TAC[WCH_variation] THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  REWRITE_TAC[REAL_ADD_SYM]);;

let WCH_TRANSVERSELOSS_CLAUSES = prove
 (`(forall b y. WCH_transverseLoss b y 0 = &0) /\
   (forall b y n. WCH_transverseLoss b y (SUC n) =
            WCH_transverseLoss b y n + b n * (y(n + 1) - y n))`,
  REWRITE_TAC[WCH_transverseLoss] THEN
  SIMP_TAC[NUMSEG_CLAUSES_LT; SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  REWRITE_TAC[REAL_ADD_SYM]);;

(* Lean: product_le_abs_width (private) *)
let WCH_PRODUCT_LE_ABS_WIDTH = prove
 (`forall v d h. abs d <= h ==> v * d <= abs v * h`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `abs v * abs d` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]]);;

(* Lean: height_distance *)
let WCH_HEIGHT_DISTANCE = prove
 (`forall lower h u v. (lower <= u /\ u <= lower + h) /\ (lower <= v /\ v <= lower + h)
                 ==> abs(u - v) <= h`,
  REAL_ARITH_TAC);;

(* Lean: selected_edge_loss *)
let WCH_SELECTED_EDGE_LOSS = prove
 (`forall s t b y z base h.
     (b = s \/ b = t) /\ abs(y - base) <= h /\ abs(z - base) <= h
     ==> b * (z - y) - (t * (z - base) - s * (y - base)) <= h * abs(t - s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REPEAT DISCH_TAC THENL
   [MP_TAC(SPECL [`s - t:real`; `z - base:real`; `h:real`] WCH_PRODUCT_LE_ABS_WIDTH);
    MP_TAC(SPECL [`s - t:real`; `y - base:real`; `h:real`] WCH_PRODUCT_LE_ABS_WIDTH)] THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [REAL_ABS_SUB] THEN
  SPEC_TAC(`abs(s - t:real)`,`w:real`) THEN REAL_ARITH_TAC);;

(* Lean: selected_loss_le *)
let WCH_SELECTED_LOSS_LE = prove
 (`forall n (s:num->real) b y h.
     (forall i. i < n ==> b i = s i \/ b i = s (i + 1)) /\
     (forall i. i <= n ==> abs(y i - y 0) <= h)
     ==> WCH_transverseLoss b y n <= h * (abs(s n) + WCH_variation s n)`,
  SUBGOAL_THEN
   `forall m (s:num->real) b y h.
     (forall i. i < m ==> b i = s i \/ b i = s (i + 1)) /\
     (forall i. i <= m ==> abs(y i - y 0) <= h)
     ==> WCH_transverseLoss b y m <= s m * (y m - y 0) + h * WCH_variation s m`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[WCH_VARIATION_CLAUSES; WCH_TRANSVERSELOSS_CLAUSES] THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:num->real`; `b:num->real`; `y:num->real`; `h:real`]) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`(s:num->real) m`; `(s:num->real) (m + 1)`; `(b:num->real) m`;
                  `(y:num->real) m`; `(y:num->real) (m + 1)`; `(y:num->real) 0`; `h:real`]
           WCH_SELECTED_EDGE_LOSS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `s:num->real`; `b:num->real`; `y:num->real`;
                                  `h:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`(s:num->real) n`; `(y:num->real) n - y 0`; `h:real`]
           WCH_PRODUCT_LE_ABS_WIDTH) THEN
    ASM_SIMP_TAC[LE_REFL] THEN REAL_ARITH_TAC]);;

(* Lean: pair_sum *)
let WCH_PAIR_SUM = prove
 (`forall n (x:num->real) (y:num->real) (s:num->real) (b:num->real) a k.
     (forall i. i < n ==>
          a + a * k * abs(s(i + 1) - s i) - b i * (y(i + 1) - y i) <= x(i + 1) - x i)
     ==> &n * a + a * k * WCH_variation s n - WCH_transverseLoss b y n <= x n - x 0`,
  INDUCT_TAC THEN
  REWRITE_TAC[WCH_VARIATION_CLAUSES; WCH_TRANSVERSELOSS_CLAUSES] THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num->real`; `y:num->real`; `s:num->real`;
                                `b:num->real`; `a:real`; `k:real`]) THEN
  ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT_SUC_LE; LE_REFL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; ADD1] THEN REAL_ARITH_TAC);;

let WCH_VARIATION_NONNEG = prove
 (`forall s n. &0 <= WCH_variation s n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[WCH_VARIATION_CLAUSES; REAL_LE_REFL; REAL_LE_ADD; REAL_ABS_POS]);;

(* Lean: first_center_cut *)
let WCH_FIRST_CENTER_CUT = prove
 (`forall n (x:num->real) (y:num->real) (s:num->real) (b:num->real) a k lower h width.
     &1 < a /\ &0 <= k /\ h <= k /\
     (forall i. i < n ==> b i = s i \/ b i = s (i + 1)) /\
     (forall i. i <= n ==> lower <= y i /\ y i <= lower + h) /\
     (forall i. i < n ==>
          a + a * k * abs(s(i + 1) - s i) - b i * (y(i + 1) - y i) <= x(i + 1) - x i) /\
     a / &2 + a * k * abs(s n) <= width - x n
     ==> x 0 < width - (&n + &1 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall i. i <= n ==> abs((y:num->real) i - y 0) <= h` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WCH_HEIGHT_DISTANCE THEN
    EXISTS_TAC `lower:real` THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `s:num->real`; `b:num->real`; `y:num->real`; `h:real`]
         WCH_SELECTED_LOSS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `y:num->real`; `s:num->real`; `b:num->real`;
                `a:real`; `k:real`] WCH_PAIR_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:num->real`; `n:num`] WCH_VARIATION_NONNEG) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= &n` ASSUME_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a * k - h` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a - &1`; `k:real`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`a * k - h`; `abs((s:num->real) n) + WCH_variation s n`] REAL_LE_MUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`&n + &1 / &2`; `a - &1`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  RASM_ARITH_TAC);;
