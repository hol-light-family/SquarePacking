(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MixedCornerSupports.lean                  *)
(* (namespace N12Compact.C1092MixedCornerSupports).                          *)
(* lower/upper: ABT_lower/ABT_upper; formulas, upper_np: C1092WS_*;          *)
(* MixedCornerScalars.common: C1092MCS_COMMON; Normal: c977cc_normal.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MixedCornerScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/ABTransverse.ml";;

let C1092MCSUP_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092MCSUP_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C1092MCSUP_LIN_TAC; ALL_TAC]) tms;;

(* Lean: upper_nn *)
let C1092MCSUP_UPPER_NN = prove
 (`forall c s u v a nx ny d e.
     c * c + s * s = &1 /\ &0 < a /\
     nx * c + ny * s = d /\ --nx * s + ny * c = e /\ &0 <= d /\ &0 <= e
     ==> ABT_upper c s u v a nx ny = d * (u + a) + e * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092WS_FORMULAS) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> max d (&0) = d`] THEN REAL_ARITH_TAC);;

(* Lean: negative_support *)
let C1092MCSUP_NEGATIVE_SUPPORT = prove
 (`forall c s u v a nx ny.
     ABT_lower c s u v a (--nx) (--ny) = --ABT_upper c s u v a nx ny /\
     ABT_upper c s u v a (--nx) (--ny) = --ABT_lower c s u v a nx ny`,
  REWRITE_TAC[ABT_lower; ABT_upper; tss_support_radius;
    REAL_ARITH `--nx * c + --ny * s = --(nx * c + ny * s)`;
    REAL_ARITH `-- --nx * s + --ny * c = --(--nx * s + ny * c)`; REAL_ABS_NEG] THEN
  REAL_ARITH_TAC);;

(* Lean: upper_cap *)
let C1092MCSUP_UPPER_CAP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c s /\ &0 < s /\
     linside c s u v a (&0) (&2 / &5) /\ --(&2 / &5) * c <= v /\
     ~linside c s u v a (&0) (&1 / &2)
     ==> u + a <= s / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th
                           else REWRITE_RULE[linside; c977cc_normal] th) THEN
  UNDISCH_TAC `~linside c s u v a (&0) (&1 / &2)` THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MCSUP_LIN_TAC);;

(* Lean: up_left (the foreign normal c, s is written p, q) *)
let C1092MCSUP_UP_LEFT = prove
 (`forall c s u v a p q.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c s /\ &0 < s /\
     linside c s u v a (&0) (&2 / &5) /\ --(&2 / &5) * c <= v /\
     u + a <= s / &2 /\ &0 < p /\ &0 <= q
     ==> p / &2 < ABT_upper c s u v a (--q) p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCS_COMMON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th
                           else REWRITE_RULE[linside] th) THEN
  C1092MCSUP_PROD_TAC [`&0 < p * c`; `&0 <= q * s`] THEN
  ASM_CASES_TAC `&0 <= p * s - q * c` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--q:real`; `p:real`;
                  `p * s - q * c`; `p * c + q * s`] C1092MCSUP_UPPER_NN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MCSUP_LIN_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    C1092MCSUP_PROD_TAC
     [`&0 <= (p * s - q * c) * ((u + a) - (&2 / &5) * s)`;
      `&0 < (p * c + q * s) * ((v + a) - (&1 - (&2 / &5) * c))`;
      `&0 < p * (c - &9 / &10 + (&4 / &5) * s pow 2)`;
      `&0 <= q * (s * (&1 - (&4 / &5) * c))`] THEN
    SUBGOAL_THEN
     `(p * s - q * c) * ((&2 / &5) * s) + (p * c + q * s) * (&1 - (&2 / &5) * c) - p / &2 =
      p * (c - &9 / &10 + (&4 / &5) * s pow 2) + q * (s * (&1 - (&4 / &5) * c))`
      ASSUME_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MCSUP_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--q:real`; `p:real`;
                `p * s - q * c`; `p * c + q * s`] C1092WS_UPPER_NP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C1092MCSUP_LIN_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  C1092MCSUP_PROD_TAC
   [`&0 <= --(p * s - q * c) * ((s / &2 - a) - u)`;
    `&0 <= (p * c + q * s) * ((v + a) - (a - (&2 / &5) * c))`;
    `&0 < (a - &1) * ((p * c + q * s) - (p * s - q * c))`;
    `&0 < p * (&1 - (&9 / &10) * c)`;
    `&0 < (c + s - (&9 / &10) * c * s) * (q * c - p * s)`] THEN
  SUBGOAL_THEN
   `c * (p * (c - s - (&9 / &10) * c pow 2) + q * (c + s - (&9 / &10) * c * s)) =
    p * (&1 - (&9 / &10) * c) + (c + s - (&9 / &10) * c * s) * (q * c - p * s)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < p * (c - s - (&9 / &10) * c pow 2) + q * (c + s - (&9 / &10) * c * s)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MCSUP_PROD_TAC
     [`&0 <= c * --(p * (c - s - (&9 / &10) * c pow 2) +
                    q * (c + s - (&9 / &10) * c * s))`] THEN
    C1092MCSUP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(p * s - q * c) * (s / &2 - &1) + (p * c + q * s) * (&1 - (&2 / &5) * c) - p / &2 =
    p * (c - s - (&9 / &10) * c pow 2) + q * (c + s - (&9 / &10) * c * s)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MCSUP_LIN_TAC);;

(* Lean: upward *)
let C1092MCSUP_UPWARD = prove
 (`forall cL sL uL vL aL cK sK uK vK aK nx ny.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\ linside cK sK uK vK aK (&0) (&1 / &2) /\
     ABT_upper cL sL uL vL aL nx ny <= ABT_lower cK sK uK vK aK nx ny
     ==> &0 < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&0`; `&2 / &5`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `&0`; `&1 / &2`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
