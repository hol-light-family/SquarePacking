(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralPositiveLeftArc.lean (Jatloe,     *)
(* N12-jatloe; namespace N12Compact.PositiveCentralPositiveLeftArc).         *)
(* The other positive-left longitudinal support, bounded continuously over   *)
(* three relative-angle ranges.  Normal is c977cc_normal; B is pceo_b;       *)
(* CornerWallMarkerMixedBounds.G/boundary/g_order are cwmmb_g/               *)
(* cwmmb_boundary/CWMMB_G_ORDER; CornerWallCycleBounds.arc_nonnegative is    *)
(* CWCB_ARC_NONNEGATIVE; cosine_order/dot_le_one/linear_arc_max are          *)
(* C977CSB_COSINE_ORDER/C977CSB_DOT_LE_ONE/C977CSB_LINEAR_ARC_MAX.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/PositiveCentralEscapeOrder.ml";;
needs "n12/geometry/PositiveCentralPositiveLeftBounds.ml";;
needs "n12/geometry/CornerWallCycleBounds.ml";;
needs "n12/geometry/CornerWallMarkerMixedBounds.ml";;

let PCPLA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCPLA_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PCPLA_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCPLA_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PCPLA_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let PCPLA_SQ_LE = prove
 (`forall T X. &0 <= T /\ &0 <= X /\ T pow 2 <= X pow 2 ==> T <= X`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: arc_between (private) *)
let PCPLA_ARC_BETWEEN = prove
 (`forall p q C S l r b u v.
     c977cc_normal p q /\ c977cc_normal C S /\ c977cc_normal l r /\
     q <= r /\ r <= S /\ &0 <= u /\
     &0 <= b + u * p + v * q /\ &0 <= b + u * C + v * S
     ==> &0 <= b + u * l + v * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCPLA_NORMAL_TAC THEN
  ASM_CASES_TAC `S:real = q` THENL
  [SUBGOAL_THEN `r:real = q` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `l:real = p` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `l <= p /\ p <= l ==> l = p`) THEN
    CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
   FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < S - q` ASSUME_TAC THENL
  [UNDISCH_TAC `~(S:real = q)` THEN RASM_ARITH_TAC; ALL_TAC] THEN
  PCPLA_PROD_TAC `S - r` `p:real` THEN PCPLA_PROD_TAC `r - q` `C:real` THEN
  PCPLA_PROD_TAC `S - q` `l:real` THEN
  PCPLA_PROD_TAC `r - q` `S - r` THEN
  SUBGOAL_THEN `&0 <= (p - C) pow 2 + (S - q) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  PCPLA_PROD_TAC `(r - q) * (S - r)` `(p - C) pow 2 + (S - q) pow 2` THEN
  SUBGOAL_THEN
   `((S - q) * l) pow 2 - ((S - r) * p + (r - q) * C) pow 2 =
    (r - q) * (S - r) * ((p - C) pow 2 + (S - q) pow 2)` ASSUME_TAC THENL
  [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`(S - r) * p + (r - q) * C`; `(S - q) * l`] PCPLA_SQ_LE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  PCPLA_PROD_TAC `S - r` `b + u * p + v * q` THEN
  PCPLA_PROD_TAC `r - q` `b + u * C + v * S` THEN
  PCPLA_PROD_TAC `u:real` `(S - q) * l - ((S - r) * p + (r - q) * C)` THEN
  MATCH_MP_TAC PCPLA_NONNEG_OF_MUL THEN EXISTS_TAC `S - q` THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []);;

(* Rewrite every x / d as x * inv d (d fixed), and name
   inv d (for the positive denominator d) as id with d * id = &1. *)
let PCPLA_DIV_TAC d id =
  SUBGOAL_THEN (mk_forall(`x:real`,mk_eq(mk_comb(mk_comb(`(/):real->real->real`,`x:real`),d),
      mk_comb(mk_comb(`( * ):real->real->real`,`x:real`),mk_comb(`inv:real->real`,d)))))
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
    [REWRITE_TAC[real_div]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(mk_comb(`( * ):real->real->real`,d),mk_comb(`inv:real->real`,d)),`&1`))
    MP_TAC THENL [MATCH_MP_TAC REAL_MUL_RINV THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):real->real->bool`,`&0`),mk_comb(`inv:real->real`,d)))
    MP_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(id,mk_comb(`inv:real->real`,d))) THEN REPEAT DISCH_TAC;;

(* Lean: self_margin (private) *)
let PCPLA_SELF_MARGIN = prove
 (`forall p q. c977cc_normal p q ==> &0 <= &2 - &2 * (p + q) + (q / p) * (pceo_b p q + &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCPLA_NORMAL_TAC THEN
  SUBGOAL_THEN `&2 - &2 * (p + q) + (q / p) * (pceo_b p q + &1) =
                ((&1 - p) pow 2 * (&1 - q)) / p pow 2` SUBST1_TAC THENL
  [REWRITE_TAC[pceo_b] THEN UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN
   SUBGOAL_THEN `~(p = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN RASM_ARITH_TAC);;

(* Lean: zero_margin (private) *)
let PCPLA_ZERO_MARGIN = prove
 (`forall p q C S. c977cc_normal p q /\ c977cc_normal C S /\ q <= S
     ==> &0 <= &1 - C - S + (S / p) * (pceo_b p q + q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCPLA_NORMAL_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] PCEO_P_B) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `B = pceo_b p q` THEN
  PCPLA_DIV_TAC `p:real` `ip:real` THEN
  SUBGOAL_THEN `p pow 2 * (ip * (B + q)) = p - p * q + q - q pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `p * ip = &1` THEN UNDISCH_TAC `p * B = p - &2 * p * q + q * (&1 - q)` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  PCPLA_PROD_TAC `&1 - p` `p - &7 / &10` THEN
  SUBGOAL_THEN `&0 <= p - &1 + q / &2 + q pow 2 / &2` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  PCPLA_PROD_TAC `&1 - q` `p - &1 + q / &2 + q pow 2 / &2` THEN
  SUBGOAL_THEN `p - p * q + q - q pow 2 - p pow 2 * (&1 - q / &2) =
                (&1 - q) * (p - &1 + q / &2 + q pow 2 / &2)` ASSUME_TAC THENL
  [UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < p pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - q / &2 <= ip * (B + q)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   PCPLA_PRODLT_TAC `p pow 2` `(&1 - q / &2) - ip * (B + q)` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLA_PROD_TAC `S:real` `ip * (B + q) - (&1 - q / &2)` THEN
  PCPLA_PROD_TAC `S:real` `S - q` THEN
  NLIN_TAC [SQ_NONNEG `&1 - C`]);;

(* Lean: bottom_margin (private) *)
let PCPLA_BOTTOM_MARGIN = prove
 (`forall p q C S. c977cc_normal p q /\ c977cc_normal C S /\ q <= S
     ==> &0 <= &1 - &2 * (C + S) + (S / p) * pceo_b p q + p * (C + S) +
               (S * q / p) * (p + q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPLA_USE PCPLA_SELF_MARGIN [`p:real`; `q:real`] THEN
  PCPLA_USE C977CSB_DOT_LE_ONE [`p:real`; `q:real`; `C:real`; `S:real`] THEN
  PCPLA_NORMAL_TAC THEN
  MP_TAC(SPECL [`p:real`; `q:real`] PCEO_P_B) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `&0 <= &2 - &2 * (p + q) + (q / p) * (pceo_b p q + &1)` THEN
  ABBREV_TAC `B = pceo_b p q` THEN
  PCPLA_DIV_TAC `p:real` `ip:real` THEN
  PCPLA_PROD_TAC `q:real` `&1 - q` THEN
  PCPLA_PROD_TAC `q * (&1 - q)` `ip:real` THEN
  PCPLA_PROD_TAC `&2 - p` `&1 - (p * C + q * S)` THEN
  PCPLA_PROD_TAC `&2 * (&1 - p) + q * (&1 - q) * ip` `S - q` THEN
  SUBGOAL_THEN
   `p * ((&1 - &2 * (C + S) + (S * ip) * B + p * (C + S) + (S * q * ip) * (p + q)) -
         (&2 - &2 * (p + q) + (q * ip) * (B + &1))) =
    (&2 - p) * (&1 - (p * C + q * S)) + (&2 * (&1 - p) + q * (&1 - q) * ip) * (S - q)`
   ASSUME_TAC THENL
  [UNDISCH_TAC `p * ip = &1` THEN UNDISCH_TAC `p * B = p - &2 * p * q + q * (&1 - q)` THEN
   UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&1 - &2 * (C + S) + (S * ip) * B + p * (C + S) + (S * q * ip) * (p + q)) -
         (&2 - &2 * (p + q) + (q * ip) * (B + &1))` ASSUME_TAC THENL
  [MATCH_MP_TAC PCPLA_NONNEG_OF_MUL THEN EXISTS_TAC `p:real` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

let PCPLA_G_FORM = prove
 (`forall p q. &0 < p ==> cwmmb_g p q = (pceo_b p q + q) / p + (&43 / &500) * (q / p) pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CWMMB_G_DEF; CWMMB_BOUNDARY_DEF; pceo_b] THEN
  SUBGOAL_THEN `~(p = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* Lean: central_margin (private) *)
let PCPLA_CENTRAL_MARGIN = prove
 (`forall p q C S. c977cc_normal p q /\ c977cc_normal C S /\ q <= S /\
     &4 / &5 <= C /\ S <= &3 / &5
     ==> &0 <= &2 - &2 * (C + S) + C * S + (S / p) * (pceo_b p q + q * S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPLA_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `p:real`; `q:real`] THEN
  PCPLA_USE CWMMB_G_ORDER [`p:real`; `q:real`; `C:real`; `S:real`] THEN
  PCPLA_USE PCPLA_SELF_MARGIN [`C:real`; `S:real`] THEN
  PCPLA_NORMAL_TAC THEN
  UNDISCH_TAC `cwmmb_g C S <= cwmmb_g p q` THEN
  MP_TAC(SPECL [`p:real`; `q:real`] PCPLA_G_FORM) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`C:real`; `S:real`] PCPLA_G_FORM) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `&0 <= &2 - &2 * (C + S) + (S / C) * (pceo_b C S + &1)` THEN
  ABBREV_TAC `Bp = pceo_b p q` THEN ABBREV_TAC `BC = pceo_b C S` THEN
  PCPLA_DIV_TAC `p:real` `ip:real` THEN
  PCPLA_DIV_TAC `C:real` `iC:real` THEN
  PCPLA_PROD_TAC `C:real` `S - q` THEN PCPLA_PROD_TAC `S:real` `p - C` THEN
  SUBGOAL_THEN `q * C <= S * p` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLA_PROD_TAC `ip:real` `iC:real` THEN
  PCPLA_PROD_TAC `ip * iC` `S * p - q * C` THEN
  SUBGOAL_THEN `ip * iC * (S * p - q * C) = S * iC - q * ip` ASSUME_TAC THENL
  [UNDISCH_TAC `p * ip = &1` THEN UNDISCH_TAC `C * iC = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `q * ip <= S * iC` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCPLA_PROD_TAC `q:real` `ip:real` THEN PCPLA_PROD_TAC `S:real` `iC:real` THEN
  PCPLA_PROD_TAC `S * iC - q * ip` `S * iC + q * ip` THEN
  SUBGOAL_THEN `(BC + S) * iC <= (Bp + q) * ip` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLA_PROD_TAC `&1 - S` `S * iC - q * ip` THEN
  SUBGOAL_THEN `(BC + S pow 2) * iC <= (Bp + q * S) * ip` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLA_PROD_TAC `S:real` `(Bp + q * S) * ip - (BC + S pow 2) * iC` THEN
  SUBGOAL_THEN `C * S + (S * iC) * (BC + S pow 2) = (S * iC) * (BC + &1)` ASSUME_TAC THENL
  [UNDISCH_TAC `C * iC = &1` THEN UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

let PCPLA_USE2 th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC; NLIN_TAC ~deg2:false []];
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* Lean: central_axis_margin *)
let PCPLA_CENTRAL_AXIS_MARGIN = prove
 (`forall p q C S l r.
     c977cc_normal p q /\ c977cc_normal C S /\ c977cc_normal l r /\
     q <= S /\ &4 / &5 <= C /\ S <= &3 / &5
     ==> p * (&2 * (C + S) - &1) <=
         S * pceo_b p q +
         ((p * C + q * S) * (l + r) + p * (C * l + S * r + abs(S * l - C * r)) +
          S * (abs(p * r - q * l) + p * l + q * r)) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCPLA_USE PCPLA_ZERO_MARGIN [`p:real`; `q:real`; `C:real`; `S:real`] THEN
  PCPLA_USE PCPLA_BOTTOM_MARGIN [`p:real`; `q:real`; `C:real`; `S:real`] THEN
  PCPLA_USE PCPLA_CENTRAL_MARGIN [`p:real`; `q:real`; `C:real`; `S:real`] THEN
  PCPLA_NORMAL_TAC THEN
  UNDISCH_TAC `&0 <= &1 - C - S + (S / p) * (pceo_b p q + q)` THEN
  UNDISCH_TAC `&0 <= &1 - &2 * (C + S) + (S / p) * pceo_b p q + p * (C + S) +
               (S * q / p) * (p + q)` THEN
  UNDISCH_TAC `&0 <= &2 - &2 * (C + S) + C * S + (S / p) * (pceo_b p q + q * S)` THEN
  ABBREV_TAC `B = pceo_b p q` THEN
  PCPLA_DIV_TAC `p:real` `ip:real` THEN
  PCPLA_PROD_TAC `S:real` `q:real` THEN PCPLA_PROD_TAC `S * q` `ip:real` THEN
  ASM_CASES_TAC `r <= q` THENL
  [PCPLA_USE C977CSB_COSINE_ORDER [`p:real`; `q:real`; `l:real`; `r:real`] THEN
   PCPLA_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `l:real`; `r:real`] THEN
   PCPLA_PROD_TAC `p:real` `q - r` THEN PCPLA_PROD_TAC `q:real` `l - p` THEN
   PCPLA_PROD_TAC `C:real` `S - r` THEN PCPLA_PROD_TAC `S:real` `l - C` THEN
   SUBGOAL_THEN `&0 <= S * l - C * r /\ p * r - q * l <= &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`;
     ASSUME `&0 <= S * l - C * r`; ASSUME `p * r - q * l <= &0`] THEN
   PCPLA_USE2 CWCB_ARC_NONNEGATIVE
     [`p:real`; `q:real`; `l:real`; `r:real`; `&1 - &2 * (C + S) + S * ip * B`;
      `C + S + S * q * ip`; `S * q * ip`] THEN
   PCPLA_PROD_TAC `p:real`
     `(&1 - &2 * (C + S) + S * ip * B) + (C + S + S * q * ip) * l + (S * q * ip) * r` THEN
   SUBGOAL_THEN
    `p * ((&1 - &2 * (C + S) + S * ip * B) + (C + S + S * q * ip) * l + (S * q * ip) * r) =
     S * B + ((p * C + q * S) * (l + r) + p * (C * l + S * r + (S * l - C * r)) +
              S * (--(p * r - q * l) + p * l + q * r)) * &1 / &2 -
     p * (&2 * (C + S) - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `p * ip = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  PCPLA_USE C977CSB_COSINE_ORDER [`l:real`; `r:real`; `p:real`; `q:real`] THEN
  PCPLA_PROD_TAC `l:real` `r - q` THEN PCPLA_PROD_TAC `r:real` `p - l` THEN
  SUBGOAL_THEN `&0 <= p * r - q * l` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `r <= S` THENL
  [PCPLA_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `l:real`; `r:real`] THEN
   PCPLA_PROD_TAC `C:real` `S - r` THEN PCPLA_PROD_TAC `S:real` `l - C` THEN
   SUBGOAL_THEN `&0 <= S * l - C * r` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; ASSUME `&0 <= S * l - C * r`; ASSUME `&0 <= p * r - q * l`] THEN
   SUBGOAL_THEN
    `(&1 - &2 * (C + S) + S * ip * B) + (C + S) * p + (S * (&1 + q * ip)) * q =
     &1 - &2 * (C + S) + S * ip * B + p * (C + S) + (S * q * ip) * (p + q)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `p * ip = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   PCPLA_USE2 PCPLA_ARC_BETWEEN
     [`p:real`; `q:real`; `C:real`; `S:real`; `l:real`; `r:real`;
      `&1 - &2 * (C + S) + S * ip * B`; `C + S:real`; `S * (&1 + q * ip)`] THEN
   PCPLA_PROD_TAC `p:real`
     `(&1 - &2 * (C + S) + S * ip * B) + (C + S) * l + (S * (&1 + q * ip)) * r` THEN
   SUBGOAL_THEN
    `p * ((&1 - &2 * (C + S) + S * ip * B) + (C + S) * l + (S * (&1 + q * ip)) * r) =
     S * B + ((p * C + q * S) * (l + r) + p * (C * l + S * r + (S * l - C * r)) +
              S * ((p * r - q * l) + p * l + q * r)) * &1 / &2 -
     p * (&2 * (C + S) - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `p * ip = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  PCPLA_USE C977CSB_COSINE_ORDER [`l:real`; `r:real`; `C:real`; `S:real`] THEN
  PCPLA_PROD_TAC `l:real` `r - S` THEN PCPLA_PROD_TAC `r:real` `C - l` THEN
  SUBGOAL_THEN `S * l - C * r <= &0` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`;
    ASSUME `S * l - C * r <= &0`; ASSUME `&0 <= p * r - q * l`] THEN
  PCPLA_PROD_TAC `C:real` `l - r` THEN PCPLA_PROD_TAC `S + S * q * ip` `l:real` THEN
  PCPLA_USE2 C977CSB_LINEAR_ARC_MAX
    [`l:real`; `r:real`; `C:real`; `S:real`; `C:real`; `C + S + S * q * ip`] THEN
  SUBGOAL_THEN `&0 <= (&1 - &2 * (C + S) + S * ip * B) + C * l + (C + S + S * q * ip) * r`
    ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPLA_PROD_TAC `p:real`
    `(&1 - &2 * (C + S) + S * ip * B) + C * l + (C + S + S * q * ip) * r` THEN
  SUBGOAL_THEN
   `p * ((&1 - &2 * (C + S) + S * ip * B) + C * l + (C + S + S * q * ip) * r) =
    S * B + ((p * C + q * S) * (l + r) + p * (C * l + S * r + --(S * l - C * r)) +
             S * ((p * r - q * l) + p * l + q * r)) * &1 / &2 -
    p * (&2 * (C + S) - &1)` ASSUME_TAC THENL
  [UNDISCH_TAC `p * ip = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;
