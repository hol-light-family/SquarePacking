(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralNegativeLeft.lean (Jatloe,        *)
(* N12-jatloe; namespace N12Compact.PositiveCentralNegativeLeft).            *)
(* A whole signed missing-west-point sector.  Lean upper/lower are           *)
(* ABT_upper/ABT_lower; B is pceo_b; the private transpose of a square       *)
(* (c,s,u,v,a) is (c, --s, v, u, a).  Lean's OpenSquare invariants are the   *)
(* explicit hypotheses c * c + s * s = &1 and &0 < a where needed.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/C696CornerMargins.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/PositiveCentralLeftBand.ml";;
needs "n12/geometry/PositiveCentralPositiveBottom.ml";;
needs "n12/geometry/PositiveCentralEscapeOrder.ml";;
needs "n12/geometry/CornerSingletonPair.ml";;
needs "n12/geometry/PositiveCentralEscapeLeft.ml";;

let PCNL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCNL_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let PCNL_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PCNL_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

(* REAL_ARITH over all assumptions built from real relations by ~ /\ \/ ==> *)
let PCNL_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let PCNL_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let PCNL_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: inside_transpose (private) *)
let PCNL_INSIDE_TRANSPOSE = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: lower_transpose (private) *)
let PCNL_LOWER_TRANSPOSE = prove
 (`forall c s u v a x y. ABT_lower c (--s) v u a x y = ABT_lower c s u v a y x`,
  REWRITE_TAC[ABT_lower; tss_support_radius; lcx; lcy] THEN
  REWRITE_TAC[REAL_ARITH `abs(x * c + y * --s) = abs(y * --s + x * c)`] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `abs(x * c + y * --s) = abs(--y * s + x * c) /\
                abs(--x * --s + y * c) = abs(y * c + x * s)` (fun th -> REWRITE_TAC[th]) THENL
  [CONJ_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: upper_transpose (private) *)
let PCNL_UPPER_TRANSPOSE = prove
 (`forall c s u v a x y. ABT_upper c (--s) v u a x y = ABT_upper c s u v a y x`,
  REWRITE_TAC[ABT_upper; tss_support_radius; lcx; lcy] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `abs(x * c + y * --s) = abs(--y * s + x * c) /\
                abs(--x * --s + y * c) = abs(y * c + x * s)` (fun th -> REWRITE_TAC[th]) THENL
  [CONJ_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: left_alternatives *)
let PCNL_LEFT_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cA sA uA vA aA r.
     c977cc_normal cL r /\ sL = --r /\ &0 < r /\ c977cc_normal cA sA /\
     aL = aA /\ &1 < aA /\
     linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     uA + aA <= &2 * (cA + sA) /\
     ldisj cL sL uL vL aL cA sA uA vA aA
     ==> uL + aL <= ABT_lower cA sA uA vA aA cL sL \/ ABT_upper cL sL uL vL aL cA sA <= uA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  MP_TAC(SPECL [`cL:real`; `r:real`; `vL:real`; `uL:real`; `aL:real`;
                `cA:real`; `--sA`; `vA:real`; `uA:real`; `aA:real`; `sA:real`]
    C696PC_TRANSVERSE) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY RASM_ARITH_TAC THEN
   FIRST
   [REWRITE_TAC[ldisj] THEN MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
    UNDISCH_TAC `ldisj cL (--r) uL vL aL cA sA uA vA aA` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`y:real`; `x:real`]) THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
    PCNL_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `--r`; `cL:real`]
    PCNL_LOWER_TRANSPOSE) THEN
  MP_TAC(SPECL [`cL:real`; `--r`; `uL:real`; `vL:real`; `aL:real`; `sA:real`; `cA:real`]
    PCNL_UPPER_TRANSPOSE) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN REAL_ARITH_TAC);;

(* Lean: northwest_vertex *)
let PCNL_NORTHWEST_VERTEX = prove
 (`forall cA sA uA vA aA.
     c977cc_normal cA sA /\ &1 < aA /\ aA <= &1001 / &1000 /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     uA + aA <= &2 * (cA + sA) /\
     &1 + (cA + sA) * (&1 - &2 * sA) < cA * (vA + aA) /\ &81 / &100 < cA
     ==> cA * uA - sA * (vA + aA) < &1 /\ &1 < sA * uA + cA * (vA + aA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCNL_NORMAL_TAC THEN
  SUBGOAL_THEN `sA < &3 / &5` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PCNL_PRODLT_TAC `cA - &81 / &100` `cA + &81 / &100` THEN
   PCNL_PROD_TAC `sA - &3 / &5` `sA + &3 / &5` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCNL_PRODLT_TAC `cA:real` `cA:real` THEN
  PCNL_PRODLT_TAC `cA * cA` `(&2 * (cA + sA) - &1) - uA` THEN
  PCNL_PROD_TAC `sA:real` `cA * (vA + aA) - (&1 + (cA + sA) * (&1 - &2 * sA))` THEN
  SUBGOAL_THEN
   `cA - cA pow 2 * (&2 * (cA + sA) - &1) + sA * (&1 + (cA + sA) * (&1 - &2 * sA)) =
    (cA + sA - &1) pow 2 / &2` ASSUME_TAC THENL
  [UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cA * (&1 - (cA * uA - sA * (vA + aA)))` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SQ_NONNEG `cA + sA - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - (cA * uA - sA * (vA + aA))` ASSUME_TAC THENL
  [MATCH_MP_TAC PCNL_POS_OF_MUL THEN EXISTS_TAC `cA:real` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cA sA uA vA aA (&33 / &20) (&33 / &20)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  PCNL_PROD_TAC `sA:real` `(uA + aA) - (&33 / &20) * (cA + sA)` THEN
  PCNL_PRODLT_TAC `cA:real` `(vA + aA) - (&33 / &20) * (cA - sA)` THEN
  PCNL_PROD_TAC `sA:real` `&1001 / &1000 - aA` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: vertex_closed (private) *)
let PCNL_VERTEX_CLOSED = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> lclosed c s u v a (c * u - s * (v + a)) (s * u + c * (v + a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lclosed] THEN
  SUBGOAL_THEN `c * (c * u - s * (v + a)) + s * (s * u + c * (v + a)) = u /\
                --s * (c * u - s * (v + a)) + c * (s * u + c * (v + a)) = v + a`
  (fun th -> REWRITE_TAC[th]) THENL
  [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: left_axis_impossible (private) *)
let PCNL_LEFT_AXIS_IMPOSSIBLE = prove
 (`forall cL sL uL vL aL cA sA uA vA aA r.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cL r /\ sL = --r /\ linside cL sL uL vL aL (&1) (&1) /\
     cA * uA - sA * (vA + aA) < &1 /\ &1 < sA * uA + cA * (vA + aA)
     ==> ~(uL + aL <= ABT_lower cA sA uA vA aA cL sL)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PCNL_NORMAL_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] PCNL_VERTEX_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABT_CB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    `cA * uA - sA * (vA + aA)` `sA * uA + cA * (vA + aA)` `cL:real` `--r` THEN
  MP_TAC(ASSUME `linside cL (--r) uL vL aL (&1) (&1)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  PCNL_PRODLT_TAC `cL:real` `&1 - (cA * uA - sA * (vA + aA))` THEN
  PCNL_PROD_TAC `r:real` `(sA * uA + cA * (vA + aA)) - &1` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: circle_chord (private) *)
let PCNL_CIRCLE_CHORD = prove
 (`forall l r. c977cc_normal l r ==> &1 - l <= (&3 / &7) * r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCNL_NORMAL_TAC THEN
  PCNL_PROD_TAC `r:real` `(&3 / &7) * (&1 + l) - r` THEN
  SUBGOAL_THEN `(&1 + l) * ((&3 / &7) * r - (&1 - l)) = r * ((&3 / &7) * (&1 + l) - r)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&3 / &7) * r - (&1 - l)` MP_TAC THENL
  [MATCH_MP_TAC PCNL_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + l` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: negative_left_margin *)
let PCNL_NEGATIVE_LEFT_MARGIN = prove
 (`forall p q C S l r.
     c977cc_normal p q /\ c977cc_normal C S /\ c977cc_normal l r /\
     &9 / &10 < p /\ &81 / &100 < C /\ q <= S
     ==> p * (&2 * (C + S) - &1) <= S * pceo_b p q + p * C * (l + r) + S * l * (p + q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PCNL_USE PCNL_CIRCLE_CHORD [`l:real`; `r:real`] THEN
  PCNL_USE C977CSB_COSINE_ORDER [`C:real`; `S:real`; `p:real`; `q:real`] THEN
  PCNL_USE PCEO_P_B [`p:real`; `q:real`] THEN
  PCNL_NORMAL_TAC THEN
  SUBGOAL_THEN `q < &11 / &25` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PCNL_PRODLT_TAC `p - &9 / &10` `p + &9 / &10` THEN
   PCNL_PROD_TAC `q - &11 / &25` `q + &11 / &25` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `S < &3 / &5` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PCNL_PRODLT_TAC `C - &81 / &100` `C + &81 / &100` THEN
   PCNL_PROD_TAC `S - &3 / &5` `S + &3 / &5` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCNL_PROD_TAC `S:real` `p / &2 - q` THEN
  PCNL_PROD_TAC `(&3 / &2) * p` `(&3 / &4) * C - S` THEN
  SUBGOAL_THEN `p * C + S * (p + q) <= (&17 / &8) * p * C` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCNL_PROD_TAC `p:real` `C:real` THEN PCNL_PROD_TAC `S:real` `p + q` THEN
  PCNL_PROD_TAC `p * C + S * (p + q)` `(&3 / &7) * r - (&1 - l)` THEN
  PCNL_PROD_TAC `(&3 / &7) * r` `(&17 / &8) * p * C - (p * C + S * (p + q))` THEN
  PCNL_PROD_TAC `p * C` `r:real` THEN
  SUBGOAL_THEN `p * (C + S) + S * q <= p * C * (l + r) + S * l * (p + q)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCNL_PROD_TAC `p pow 2` `p - C` THEN
  PCNL_PROD_TAC `S:real` `q:real` THEN
  SUBGOAL_THEN `&0 <= p pow 2 - S * (&1 - q)` ASSUME_TAC THENL
  [PCNL_PRODLT_TAC `p - &9 / &10` `p + &9 / &10` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCNL_PROD_TAC `&1 - p` `p pow 2 - S * (&1 - q)` THEN
  SUBGOAL_THEN
   `p * (S * pceo_b p q + p * (C + S) + S * q - p * (&2 * (C + S) - &1)) =
    p pow 2 * (&1 - C) - S * (&1 - p) * (&1 - q)` ASSUME_TAC THENL
  [UNDISCH_TAC `p * pceo_b p q = p - &2 * p * q + q * (&1 - q)` THEN
   UNDISCH_TAC `p pow 2 + q pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= S * pceo_b p q + p * (C + S) + S * q - p * (&2 * (C + S) - &1)`
  ASSUME_TAC THENL
  [MATCH_MP_TAC PCNL_NONNEG_OF_MUL THEN EXISTS_TAC `p:real` THEN
   CONJ_TAC THENL [RASM_ARITH_TAC; NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: support_impossible *)
let PCNL_SUPPORT_IMPOSSIBLE = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cA sA uA (vA:real) aA r.
     c977cc_normal cO sO /\ c977cc_normal cL r /\ sL = --r /\ c977cc_normal cA sA /\
     aL = aA /\ &1 < aA /\ lcont cL sL uL vL aL /\
     &9 / &10 < cO /\ &81 / &100 < cA /\ sO <= sA /\
     pceo_b cO sO < vO + aO /\ uA + aA <= &2 * (cA + sA) /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     ABT_upper cL sL uL vL aL cA sA <= uA
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aA`)) THEN
  PCNL_USE PCNL_NEGATIVE_LEFT_MARGIN
    [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `cL:real`; `r:real`] THEN
  PCNL_NORMAL_TAC THEN
  PCNL_PROD_TAC `sO:real` `cL:real` THEN PCNL_PROD_TAC `cO:real` `r:real` THEN
  PCNL_PROD_TAC `cA:real` `r:real` THEN PCNL_PROD_TAC `sA:real` `cL:real` THEN
  PCNL_PROD_TAC `cO:real` `cL - r` THEN PCNL_PROD_TAC `r:real` `cO - sO` THEN
  PCNL_PROD_TAC `cA:real` `cL - r` THEN PCNL_PROD_TAC `r:real` `cA - sA` THEN
  PCNL_USE C977NCO_LOWER_NEGATIVE_NONPOS
    [`cL:real`; `--r`; `uL:real`; `vL:real`; `aA:real`; `r:real`; `--sO`; `cO:real`] THEN
  PCNL_USE C977NCO_UPPER_NEGATIVE_POS
    [`cL:real`; `--r`; `uL:real`; `vL:real`; `aA:real`; `r:real`; `cA:real`; `sA:real`] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if can (term_match [] `ABT_upper c s u v a nx ny = e`) (concl th) ||
                                    can (term_match [] `ABT_lower c s u v a nx ny = e`) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "")) THEN
  SUBGOAL_THEN `cL * cL + --r * --r = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `cL pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `--r`; `uL:real`; `vL:real`; `aA:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcx; REAL_ABS_NEG]) THEN
  SUBGOAL_THEN `abs r = r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cL * uL + r * vL` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cO * ((cA * cL - sA * r) * (uL + aA) + (cA * r + sA * cL) * (vL + aA)) - sA * ((--sO * cL - cO * r) * (uL + aA) + (--sO * r + cO * cL) * vL) - aA * (cO * cA * (cL + r) + sA * cL * (cO + sO)) = (cO * cA + sO * sA) * (cL * uL + r * vL)` ASSUME_TAC THENL
  [CONV_TAC REAL_RING; ALL_TAC] THEN
  PCNL_PROD_TAC `cO:real` `cA:real` THEN PCNL_PROD_TAC `sO:real` `sA:real` THEN
  PCNL_PROD_TAC `(cO * cA + sO * sA)` `cL * uL + r * vL` THEN
  PCNL_PROD_TAC `sA:real` `((--sO * cL - cO * r) * (uL + aA) + (--sO * r + cO * cL) * vL) - pceo_b cO sO` THEN
  PCNL_PROD_TAC `cO * cA` `cL + r` THEN PCNL_PROD_TAC `sA * cL` `cO + sO` THEN
  PCNL_PROD_TAC `(cO * cA * (cL + r) + sA * cL * (cO + sO))` `aA - &1` THEN
  PCNL_PRODLT_TAC `cO:real` `(&2 * (cA + sA) - &1) - uA` THEN
  PCNL_PROD_TAC `cO:real` `uA - ((cA * cL - sA * r) * (uL + aA) + (cA * r + sA * cL) * (vL + aA))` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: west *)
let PCNL_WEST = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cA sA uA vA aA r.
     c977cc_normal cO sO /\ c977cc_normal cL r /\ sL = --r /\ &0 < r /\
     c977cc_normal cA sA /\ aO = aA /\ aL = aA /\ &1 < aA /\ aA <= &1001 / &1000 /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&28 / &25) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     ~linside cO sO uO vO aO (&1) (&1) /\ ~linside cO sO uO vO aO (&2) (&457 / &500) /\
     linside cL sL uL vL aL (&1) (&1) /\ linside cL sL uL vL aL (&1) (&28 / &25) /\
     linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     uA + aA <= &2 * (cA + sA) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ldisj cO sO uO vO aO cA sA uA vA aA /\
     ldisj cO sO uO vO aO cL sL uL vL aL /\
     ldisj cL sL uL vL aL cA sA uA vA aA
     ==> linside cA sA uA vA aA (&1) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN PCNL_NORMAL_TAC THEN
  SUBGOAL_THEN `cO * cO + sO * sO = &1 /\ cA * cA + sA * sA = &1 /\
                cL * cL + sL * sL = &1 /\ &0 < aA /\ &0 < aO /\ &0 < aL /\
                abs sO <= cO` STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THENL
   [UNDISCH_TAC `cO pow 2 + sO pow 2 = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `cA pow 2 + sA pow 2 = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `cL pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING;
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]]; ALL_TAC] THEN
  PCNL_USE PCPB_ONLY_BOTTOM_AXIS
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
     `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCNL_USE PCLB_UPPER_FACE [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCNL_USE PCPB_OWN_AXIS_ANGLE
    [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
     `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCNL_USE PCLB_NORTHWEST_CAP [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  PCNL_USE C696PC_CORNER_FACES [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] THEN
  SUBGOAL_THEN `pceo_b cO sO <= c696cm_boundary cO sO` ASSUME_TAC THENL
  [PCNL_USE PCEO_P_B [`cO:real`; `sO:real`] THEN
   SUBGOAL_THEN `cO * c696cm_boundary cO sO =
                 cO + sO - &2 * cO * sO - (&457 / &500) * sO pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[c696cm_boundary] THEN
    (SUBGOAL_THEN `~(cO = &0)` MP_TAC THENL [RASM_ARITH_TAC; ALL_TAC]) THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= c696cm_boundary cO sO - pceo_b cO sO` MP_TAC THENL
   [MATCH_MP_TAC PCNL_NONNEG_OF_MUL THEN EXISTS_TAC `cO:real` THEN
    CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `sO:real`]; REAL_ARITH_TAC]; ALL_TAC] THEN
  PCNL_USE C977CSB_COSINE_ORDER [`cA:real`; `sA:real`; `cO:real`; `sO:real`] THEN
  PCNL_PROD_TAC `sO:real` `cO - cA` THEN PCNL_PROD_TAC `cO:real` `sA - sO` THEN
  SUBGOAL_THEN `&0 <= cO * sA - sO * cA` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCNL_PROD_TAC `cO:real` `cA:real` THEN PCNL_PROD_TAC `sO:real` `sA:real` THEN
  PCNL_USE PCEO_LOWER_PP
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `--sO`; `cO:real`] THEN
  PCNL_PROD_TAC `cO * sA - sO * cA` `(&2 * (cA + sA) - &1) - uA` THEN
  PCNL_PROD_TAC `cO * cA + sO * sA` `aA - &1` THEN
  SUBGOAL_THEN
   `pceo_b cO sO < (cO * sA - sO * cA) * (&2 * (cA + sA) - &1) +
                   (cO * cA + sO * sA) * ((vA + aA) - &1)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCNL_USE PCEL_BOTTOM_COSINE [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `vA + aA`] THEN
  PCNL_USE PCEO_BASE_BOUND [`cO:real`; `sO:real`; `cA:real`; `sA:real`; `vA + aA`] THEN
  PCNL_USE PCEO_NORTHWEST_THRESHOLD [`cA:real`; `sA:real`; `vA + aA`] THEN
  PCNL_USE PCNL_NORTHWEST_VERTEX [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  SUBGOAL_THEN `ABT_upper cL sL uL vL aL cA sA <= uA` ASSUME_TAC THENL
  [MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                 `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `r:real`]
     PCNL_LEFT_ALTERNATIVES) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
   MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                 `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `r:real`]
     PCNL_LEFT_AXIS_IMPOSSIBLE) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
   MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO` ASSUME_TAC THENL
  [MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                 `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] CSP_ALTERNATIVES) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
   MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                 `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`]
     PCEL_NEGATIVE_LEFT_AXIS_IMPOSSIBLE) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC); ALL_TAC] THEN
   MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`] ABT_OWNV) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[CSP_directed] THEN
   POP_ASSUM_LIST(fun ths -> MP_TAC(end_itlist CONJ (filter (fun th ->
     let t = concl th in is_real_rel t) ths))) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `r:real`]
    PCNL_SUPPORT_IMPOSSIBLE) THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC));;
