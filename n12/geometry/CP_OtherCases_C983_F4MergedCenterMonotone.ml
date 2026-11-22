(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4MergedCenterMonotone.lean    *)
(* (N12Compact.Completion.OtherCases.C983.F4MergedCenter, sections 4-5).     *)
(* Lean header: "Source only: no compiler replay has been performed."        *)
(*                                                                           *)
(* PARTIAL PORT.  The Lean file proves PositiveComparisons by one-variable   *)
(* monotonicity in the angle q = arctan(t/b) (Real.cos/sin/arctan, MVT).     *)
(* HOL's transcendentals/realanalysis are not part of the port's base (and   *)
(* cannot be loaded after the Phase-1 chain: the OCaml value `frontier` of   *)
(* n12/phase1/families_check.ml shadows HOL's `frontier` theorem used by       *)
(* Multivariate/paths.ml).  The trigonometric items                          *)
(*   canonical_angle, Bminus, Bplus, G, quarter_bounds, quotient_derivative, *)
(*   Bminus_derivative, Bplus_derivative, G_derivative, Bminus_antitone,     *)
(*   Bplus_monotone, G_antitone, G_monotone, Bminus_normal, Bplus_normal,    *)
(*   G_normal, Gminus_normal, Gplus_normal                                   *)
(* are therefore NOT ported; nothing downstream uses them (the importers     *)
(* F4MergedCenterEnding and F4BarAngleScalars use only positive_comparisons).*)
(*                                                                           *)
(* positive_comparisons (purely algebraic statement) is proved here by the   *)
(* half-angle substitution instead: z = r/(1+d) = tan(p/2) is already a      *)
(* hypothesis, and w = t/(1+b) = tan(q/2) for the unit normal (b,t).  Then   *)
(* b,t,d,r are rational in w,z, the relative sign d*t-r*b has the sign of    *)
(* w-z, and each of the three inequalities becomes a polynomial inequality   *)
(* in (w,z) on 0<=w<=z or z<=w<=5/12, 1/4<z<13/50 (the B ones factor with a  *)
(* (z-w) factor; the G ones are proved by a degree-7 Handelman certificate   *)
(* found by NLIN's LP and checked by the kernel).                            *)
(* PositiveComparisons d r = c983fmcp_comparisons d r                        *)
(* (CP_OtherCases_C983_F4MergedCenterPositive.ml).  Tag C983FMCM_.           *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4MergedCenterPositive.ml";;

let c983fmcm_nbm_s = "(((b pow 2) * (d pow 2)) + ((-- &1) * b * (d pow 2)) + (b * d * r * t) + ((-- &1) * b * d) + ((-- &1) * b * r) + b + ((-- &1) * d * r * t) + (d * r))";;
let c983fmcm_nbm = parse_term c983fmcm_nbm_s;;
let c983fmcm_nbp_s = "(((b pow 2) * (d pow 2)) + ((-- &1) * (b pow 2) * d * r) + (b * (d pow 2) * t) + ((-- &1) * b * (d pow 2)) + (b * d * r * t) + ((-- &1) * b * d) + ((-- &1) * b * r) + b + ((-- &1) * d * r * t) + (d * r))";;
let c983fmcm_nbp = parse_term c983fmcm_nbp_s;;
let c983fmcm_ngm_s = "(((&7 / &20) * (b pow 2) * (d pow 2) * r) + ((b pow 2) * (d pow 2)) + ((&7 / &20) * (b pow 2) * d * (r pow 2)) + ((-- &1) * (b pow 2) * d) + ((-- &1) * (&7 / &20) * b * (d pow 3) * t) + ((-- &1) * (&7 / &20) * b * (d pow 2) * r * t) + (b * d * r * t) + ((-- &1) * (&543 / &500) * b * d * t) + (b * d) + (d * t) + ((-- &1) * d))";;
let c983fmcm_ngm = parse_term c983fmcm_ngm_s;;
let c983fmcm_ngp_s = "(((-- &1) * (&7 / &20) * (b pow 2) * (d pow 2) * r) + ((b pow 2) * (d pow 2)) + ((&7 / &20) * (b pow 2) * d * (r pow 2)) + ((-- &1) * (b pow 2) * d) + ((&7 / &20) * b * (d pow 3) * t) + ((-- &1) * (&7 / &20) * b * (d pow 2) * r * t) + (b * d * r * t) + ((-- &1) * (&543 / &500) * b * d * t) + (b * d) + (d * t) + ((-- &1) * d))";;
let c983fmcm_ngp = parse_term c983fmcm_ngp_s;;
let c983fmcm_pgm_s = "((&1000 * (w pow 3) * (z pow 4)) + (&175 * (w pow 3) * (z pow 3)) + (&1150 * (w pow 3) * (z pow 2)) + ((-- &1) * &175 * (w pow 3) * z) + (&500 * (w pow 3)) + ((-- &1) * &218 * (w pow 2) * (z pow 4)) + (&1525 * (w pow 2) * (z pow 3)) + ((-- &1) * &586 * (w pow 2) * (z pow 2)) + (&475 * (w pow 2) * z) + ((-- &1) * &718 * (w pow 2)) + ((-- &1) * &718 * w * (z pow 4)) + (&1175 * w * (z pow 3)) + (&114 * w * (z pow 2)) + (&825 * w * z) + ((-- &1) * &218 * w) + ((-- &1) * &500 * (z pow 4)) + ((-- &1) * &175 * (z pow 3)) + ((-- &1) * &150 * (z pow 2)) + (&175 * z))";;
let c983fmcm_pgm = parse_term c983fmcm_pgm_s;;
let c983fmcm_pgp_s = "((&1000 * (w pow 3) * (z pow 4)) + ((-- &1) * &175 * (w pow 3) * (z pow 3)) + (&1150 * (w pow 3) * (z pow 2)) + (&175 * (w pow 3) * z) + (&500 * (w pow 3)) + (&132 * (w pow 2) * (z pow 4)) + (&1175 * (w pow 2) * (z pow 3)) + ((-- &1) * &1286 * (w pow 2) * (z pow 2)) + (&825 * (w pow 2) * z) + ((-- &1) * &368 * (w pow 2)) + ((-- &1) * &368 * w * (z pow 4)) + (&1525 * w * (z pow 3)) + ((-- &1) * &586 * w * (z pow 2)) + (&475 * w * z) + (&132 * w) + ((-- &1) * &500 * (z pow 4)) + (&175 * (z pow 3)) + ((-- &1) * &150 * (z pow 2)) + ((-- &1) * &175 * z))";;
let c983fmcm_pgp = parse_term c983fmcm_pgp_s;;
let c983fmcm_q_s = "((&3 * (w pow 2) * z) + (w pow 2) + ((-- &1) * w * (z pow 2)) + w + ((-- &1) * (z pow 2)) + z)";;
let c983fmcm_q = parse_term c983fmcm_q_s;;
let c983fmcm_r_s = "(((w pow 2) * (z pow 2)) + ((-- &1) * &2 * (w pow 2) * z) + ((-- &1) * (w pow 2)) + (&2 * w * (z pow 2)) + (&2 * w * z) + (z pow 2) + &1)";;
let c983fmcm_r = parse_term c983fmcm_r_s;;

let C983FMCM_FACT t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;

(* sign transfer through a positive multiplier *)
let C983FMCM_SGN = prove
 (`forall x m y. &0 < m /\ x * m = y
           ==> (x <= &0 <=> y <= &0) /\ (&0 <= x <=> &0 <= y) /\ (&0 < x <=> &0 < y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REPEAT CONJ_TAC THEN EQ_TAC THEN DISCH_TAC THEN NLIN_TAC []);;

let C983FMCM_MULT_POS = prove
 (`forall w z k. &0 < (&1 + w * w) pow 2 * (&1 + z * z) pow k`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_ARITH `&0 < &1 + x <=> -- &1 < x`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> -- &1 < x`) THEN REWRITE_TAC[REAL_LE_SQUARE]);;

(* half-angle coordinates of a canonical unit normal (b,t), w = t/(1+b) *)
let C983FMCM_HALF_ANGLE = prove
 (`forall b t. &0 < b /\ &0 <= t /\ t <= b /\ b pow 2 + t pow 2 = &1
         ==> exists w. &0 <= w /\ w <= &5 / &12 /\
                 b * (&1 + w * w) = &1 - w * w /\ t * (&1 + w * w) = &2 * w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `t / (&1 + b)` THEN
  ABBREV_TAC `w = t / (&1 + b)` THEN
  C983FMCM_FACT `(&1 + b) * w = t`
    (EXPAND_TAC "w" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN RASM_ARITH_TAC) THEN
  C983FMCM_FACT `&0 <= w`
    (EXPAND_TAC "w" THEN MATCH_MP_TAC REAL_LE_DIV THEN RASM_ARITH_TAC) THEN
  C983FMCM_FACT `(&1 + b) * (b * (&1 + w * w) - (&1 - w * w)) = &0`
    (UNDISCH_TAC `(&1 + b) * w = t` THEN UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN
     CONV_TAC REAL_RING) THEN
  C983FMCM_FACT `b * (&1 + w * w) = &1 - w * w`
    (POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN UNDISCH_TAC `&0 < b` THEN REAL_ARITH_TAC) THEN
  C983FMCM_FACT `t * (&1 + w * w) = &2 * w`
    (UNDISCH_TAC `(&1 + b) * w = t` THEN
     UNDISCH_TAC `b * (&1 + w * w) = &1 - w * w` THEN CONV_TAC REAL_RING) THEN
  C983FMCM_FACT `w * w + &2 * w - &1 <= &0`
    (MP_TAC(SPECL [`t - b`; `&1 + w * w`; `w * w + &2 * w - &1`] C983FMCM_SGN) THEN
     ANTS_TAC THENL
      [CONJ_TAC THENL
        [MP_TAC(SPEC `w:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC;
         UNDISCH_TAC `b * (&1 + w * w) = &1 - w * w` THEN
         UNDISCH_TAC `t * (&1 + w * w) = &2 * w` THEN CONV_TAC REAL_RING];
       DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1 th)]) THEN RASM_ARITH_TAC]) THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC []);;

(* positivity of the two G polynomials: degree-7 Handelman certificates
   (P = 1 + sum of nonnegative multiples of products of the region's linear
   constraints; coefficients from an LP, identity checked by REAL_RING) *)
let c983fmcm_hm_s = "&1 + (&532439065491 / &362500000000) * ((&26 - &100 * z)) +   (&203380946003 / &72500000000) * ((&100 * z - &25)) +   (&43768426672327 / &435000000000) * ((z - w)) +   (&731379458849 / &21750000000000) * (((&100 * z - &25) pow 2)) +   (&3590923913447 / &435000000000) * ((z - w) * (&26 - &100 * z)) +   (&7482842531 / &22656250) * (w * (z - w)) +   (&3972999019 / &5800000000000) * (((&26 - &100 * z) pow 3)) +   (&74610210151 / &435000000000) * (w * ((&100 * z - &25) pow 2)) +   (&11047867133 / &725000000) * (w * (z - w) * (&26 - &100 * z)) +   (&34225 / &64) * (w * ((z - w) pow 2)) +   (&16027279 / &36250000000) * (w * ((&100 * z - &25) pow 3)) +   (&17255109 / &362500000) * ((w pow 2) * ((&100 * z - &25) pow 2)) +   (&317 / &64) * ((w pow 3) * (&100 * z - &25)) +   (&3625327 / &2175000000000) * ((&100 * z - &25) * ((&26 - &100 * z) pow 4)) +   (&29000327 / &17400000000000) * (((&100 * z - &25) pow 4) * (&26 - &100 * z)) +   (&59203 / &45312500) * ((w pow 2) * ((&100 * z - &25) pow 3)) +   (&53 / &320) * ((w pow 3) * ((&100 * z - &25) pow 2)) +   (&109 / &1450000000000) * ((&100 * z - &25) * ((&26 - &100 * z) pow 5)) +   (&1077397 / &435000000000) * (w * (&100 * z - &25) * ((&26 - &100 * z) pow 4)) +   (&1086553 / &435000000000) * (w * ((&100 * z - &25) pow 4) * (&26 - &100 * z)) +   (&47 / &40000) * ((w pow 3) * ((&100 * z - &25) pow 3)) +   (&109 / &29000000000000) * (((&100 * z - &25) pow 6) * (&26 - &100 * z)) +   (&109 / &290000000000) * ((z - w) * ((&26 - &100 * z) pow 6)) +   (&109 / &29000000) * (w * ((z - w) pow 2) * ((&100 * z - &25) pow 4)) +   (&109 / &1450000000) * ((w pow 2) * (&100 * z - &25) * ((&26 - &100 * z) pow 4)) +   (&181 / &29000000) * ((w pow 3) * ((&100 * z - &25) pow 4))";;
let c983fmcm_hm = parse_term c983fmcm_hm_s;;
let c983fmcm_hp_s = "&1 + (&642886020893 / &437500000000) * ((&26 - &100 * z)) +   (&20169556939757 / &7000000000000) * ((&100 * z - &25)) +   (&246313 / &1024) * ((w - z)) +   (&1456718601 / &15625000000) * (((&100 * z - &25) pow 2)) +   (&326427 / &25600) * ((w - z) * (&100 * z - &25)) +   (&61273 / &256) * (((w - z) pow 2)) +   (&457810629 / &200000000000) * (((&100 * z - &25) pow 3)) +   (&8689 / &20000) * ((w - z) * ((&100 * z - &25) pow 2)) +   (&91063 / &3200) * (((w - z) pow 2) * (&100 * z - &25)) +   (&39475 / &64) * (((w - z) pow 3)) +   (&2865959 / &100000000000) * (((&26 - &100 * z) pow 4)) +   (&1819 / &320000) * ((w - z) * ((&100 * z - &25) pow 3)) +   (&24233 / &80000) * (((w - z) pow 2) * ((&100 * z - &25) pow 2)) +   (&499 / &64) * (((w - z) pow 3) * (&100 * z - &25)) +   (&325621 / &1000000000000) * (((&100 * z - &25) pow 5)) +   (&31673 / &400000000) * ((w - z) * ((&100 * z - &25) pow 4)) +   (&6107 / &1000000) * (((w - z) pow 2) * ((&100 * z - &25) pow 3)) +   (&223 / &1600) * (((w - z) pow 3) * ((&100 * z - &25) pow 2)) +   (&4239 / &10000000000) * ((w - z) * ((&100 * z - &25) pow 5)) +   (&3357 / &100000000) * (((w - z) pow 2) * ((&100 * z - &25) pow 4)) +   (&33 / &40000) * (((w - z) pow 3) * ((&100 * z - &25) pow 3)) +   (&1707 / &7000000000000) * (((&26 - &100 * z) pow 7)) +   (&1777 / &7000000000000) * (((&100 * z - &25) pow 7)) +   (&3 / &1000000000) * ((w - z) * ((&100 * z - &25) pow 6)) +   (&3 / &10000000) * (((w - z) pow 2) * ((&100 * z - &25) pow 5)) +   (&1 / &100000) * (((w - z) pow 3) * ((&100 * z - &25) pow 4))";;
let c983fmcm_hp = parse_term c983fmcm_hp_s;;

let C983FMCM_HANDELMAN_TAC pcert (asl,g as gl) =
  (SUBGOAL_THEN (mk_eq(rand g, pcert)) SUBST1_TAC THENL
    [CONV_TAC REAL_RING;
     MATCH_MP_TAC(REAL_ARITH `forall x. &0 <= x ==> &0 < &1 + x`) THEN
     REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
     REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
     (RASM_ARITH_TAC ORELSE (MATCH_MP_TAC REAL_POW_LE THEN RASM_ARITH_TAC))]) gl;;

(* helper: section 5.1 positivity in half-angle form *)
let C983FMCM_PGM_POS = prove
 ((parse_term ("!w z. &0 <= w /\\ w <= z /\\ &1 / &4 < z /\\ z < &13 / &50 ==> &0 < " ^ c983fmcm_pgm_s ^ "")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C983FMCM_HANDELMAN_TAC c983fmcm_hm);;

(* helper: section 5.2 positivity in half-angle form *)
let C983FMCM_PGP_POS = prove
 ((parse_term ("!w z. z <= w /\\ w <= &5 / &12 /\\ &1 / &4 < z /\\ z < &13 / &50 ==> &0 < " ^ c983fmcm_pgp_s ^ "")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C983FMCM_HANDELMAN_TAC c983fmcm_hp);;

(* goal &0 <= e (or &0 < e) with e rational in b,t,d,r (denominators b, d):
   e = n / (b * d), n * M = p in half-angle coordinates (M > 0), then ptac
   proves &0 <= p (or &0 < p) *)
let C983FMCM_CLOSE_TAC strict n k p ptac (asl,g as gl) =
  let e = rand g in
  let m = subst [mk_small_numeral k, `k:num`] `(&1 + w * w) pow 2 * (&1 + z * z) pow k` in
  (SUBGOAL_THEN (mk_eq(e, mk_binop `(/):real->real->real` n `b * d:real`)) SUBST1_TAC THENL
    [MP_TAC(MATCH_MP REAL_LT_IMP_NZ (ASSUME `&0 < b`)) THEN
     MP_TAC(MATCH_MP REAL_LT_IMP_NZ (ASSUME `&0 < d`)) THEN CONV_TAC REAL_FIELD;
     ALL_TAC] THEN
   MATCH_MP_TAC (if strict then REAL_LT_DIV else REAL_LE_DIV) THEN CONJ_TAC THENL
    [MP_TAC(SPECL [n; m; p] C983FMCM_SGN) THEN ANTS_TAC THENL
      [REWRITE_TAC[C983FMCM_MULT_POS] THEN
       MAP_EVERY UNDISCH_TAC [`b * (&1 + w * w) = &1 - w * w`; `t * (&1 + w * w) = &2 * w`;
                              `d * (&1 + z * z) = &1 - z * z`; `r * (&1 + z * z) = &2 * z`] THEN
       CONV_TAC REAL_RING;
       DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN ptac;
     (if strict then MATCH_MP_TAC REAL_LT_MUL else MATCH_MP_TAC REAL_LE_MUL) THEN
     CONJ_TAC THEN RASM_ARITH_TAC]) gl;;

let C983FMCM_PROD_TAC strict leaf =
  REPEAT((if strict then MATCH_MP_TAC REAL_LT_MUL else MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC) THEN
  (leaf ORELSE FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);;

(* Lean: positive_comparisons *)
let C983FMCM_POSITIVE_COMPARISONS = prove
 (`forall d r z. &0 < d /\ &0 < r /\ r <= d /\ d pow 2 + r pow 2 = &1 /\
           r * z = &1 - d /\ z * (&1 + d) = r /\
           &1 / &4 < z /\ z < &13 / &50 /\
           &87 / &100 < d /\ &47 / &100 < r /\ r < &49 / &100 /\
           &27 / &20 < d + r /\ &19 / &50 < d - r
           ==> c983fmcp_comparisons d r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983FMCM_FACT `d * (&1 + z * z) = &1 - z * z`
    (UNDISCH_TAC `r * z = &1 - d` THEN UNDISCH_TAC `z * (&1 + d) = r` THEN CONV_TAC REAL_RING) THEN
  C983FMCM_FACT `r * (&1 + z * z) = &2 * z`
    (UNDISCH_TAC `d * (&1 + z * z) = &1 - z * z` THEN UNDISCH_TAC `z * (&1 + d) = r` THEN
     CONV_TAC REAL_RING) THEN
  REWRITE_TAC[c983fmcp_comparisons] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C983FMCM_HALF_ANGLE) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  C983FMCM_FACT `(d * t - r * b) * ((&1 + w * w) * (&1 + z * z)) = (w - z) * (&2 * (w * z + &1))`
    (MAP_EVERY UNDISCH_TAC [`b * (&1 + w * w) = &1 - w * w`; `t * (&1 + w * w) = &2 * w`;
                            `d * (&1 + z * z) = &1 - z * z`; `r * (&1 + z * z) = &2 * z`] THEN
     CONV_TAC REAL_RING) THEN
  C983FMCM_FACT `&0 < (&1 + w * w) * (&1 + z * z)`
    (MATCH_MP_TAC REAL_LT_MUL THEN MP_TAC(SPEC `w:real` REAL_LE_SQUARE) THEN
     MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC) THEN
  C983FMCM_FACT `&0 < &2 * (w * z + &1)`
    (MP_TAC(SPECL [`w:real`; `z:real`] REAL_LE_MUL) THEN RASM_ARITH_TAC) THEN
  C983FMCM_FACT `(w - z <= &0 <=> d * t - r * b <= &0) /\ (&0 <= w - z <=> &0 <= d * t - r * b)`
    (MP_TAC(SPECL [`w - z`; `&2 * (w * z + &1)`; `(w - z) * (&2 * (w * z + &1))`] C983FMCM_SGN) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MP_TAC(SPECL [`d * t - r * b`; `(&1 + w * w) * (&1 + z * z)`;
                   `(w - z) * (&2 * (w * z + &1))`] C983FMCM_SGN) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN MESON_TAC[]) THEN
  POP_ASSUM(LABEL_TAC "ord") THEN
  C983FMCM_FACT `&0 <= w pow 2 * z /\ &0 <= w * (&1 - z pow 2) /\ &0 <= z * (&1 - z) /\
                 &0 <= w pow 2 * z pow 2 /\ &0 <= w * z pow 2 /\ &0 <= w * z /\ &0 <= z pow 2 /\
                 &0 <= (&25 / &144 - w pow 2) * z /\ &0 <= w pow 2 /\ &0 <= &25 / &144 - w pow 2`
    (let sq = REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN NO_TAC in
     REPEAT CONJ_TAC THEN
     (sq ORELSE RASM_ARITH_TAC ORELSE NLIN_TAC [] ORELSE
      (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN (sq ORELSE RASM_ARITH_TAC ORELSE NLIN_TAC [])))) THEN
  C983FMCM_FACT (parse_term ("&0 <= " ^ c983fmcm_q_s ^ "")) (NLIN_TAC ~deg2:false []) THEN
  C983FMCM_FACT (parse_term ("&0 <= " ^ c983fmcm_r_s ^ "")) (NLIN_TAC ~deg2:false []) THENL
   [(* wallNormal *)
    ASM_CASES_TAC `d * t - r * b <= &0` THENL
     [C983FMCM_FACT `w - z <= &0`
        (USE_THEN "ord" (MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]) THEN
      REWRITE_TAC[MATCH_MP (REAL_ARITH `forall x. x <= &0 ==> max x (&0) = &0`)
                    (ASSUME `d * t - r * b <= &0`); REAL_ADD_RID] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      C983FMCM_CLOSE_TAC false c983fmcm_nbm 2
        (parse_term ("&2 * (z - w) * (&1 - w) * (&1 - z) * " ^ c983fmcm_q_s ^ "")) (C983FMCM_PROD_TAC false NO_TAC);
      C983FMCM_FACT `&0 <= w - z`
        (USE_THEN "ord" (MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC) THEN
      REWRITE_TAC[MATCH_MP (REAL_ARITH `forall x. ~(x <= &0) ==> max x (&0) = x`)
                    (ASSUME `~(d * t - r * b <= &0)`)] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      C983FMCM_CLOSE_TAC false c983fmcm_nbp 2
        (parse_term ("&2 * (w - z) * (&1 - w) * (&1 - z) * " ^ c983fmcm_r_s ^ "")) (C983FMCM_PROD_TAC false NO_TAC)];
    (* lowerOrder *)
    C983FMCM_FACT `w - z <= &0`
      (USE_THEN "ord" (MP_TAC o CONJUNCT1) THEN DISCH_THEN SUBST1_TAC THEN RASM_ARITH_TAC) THEN
    C983FMCM_CLOSE_TAC true c983fmcm_ngm 3
      (parse_term ("(&1 - w) * (&1 - z) * (&1 + z) * (&1 / &250 * " ^ c983fmcm_pgm_s ^ ")"))
      (C983FMCM_PROD_TAC true (MATCH_MP_TAC C983FMCM_PGM_POS THEN RASM_ARITH_TAC));
    (* upperOrder *)
    C983FMCM_FACT `&0 <= w - z`
      (USE_THEN "ord" (MP_TAC o CONJUNCT2) THEN DISCH_THEN SUBST1_TAC THEN RASM_ARITH_TAC) THEN
    C983FMCM_CLOSE_TAC true c983fmcm_ngp 3
      (parse_term ("(&1 - w) * (&1 - z) * (&1 + z) * (&1 / &250 * " ^ c983fmcm_pgp_s ^ ")"))
      (C983FMCM_PROD_TAC true (MATCH_MP_TAC C983FMCM_PGP_POS THEN RASM_ARITH_TAC))]);;
