(* ========================================================================= *)
(* Port of Compact/Geometry/CentralRightCornerSupport.lean                   *)
(* (namespace N12Compact.CentralRightCornerSupport).                         *)
(* A right wall's lower support is bounded by its actual upper corner        *)
(* exclusion.  Lean `lower R c s` is ABT_lower cR sR uR vR aR c s; the       *)
(* square R is the 5-tuple cR sR uR vR aR.  right_wall is CWE_RIGHT_WALL,    *)
(* lower_in_bands is C977NCO_LOWER_IN_BANDS, CornerWallLowerSupportMargin.F  *)
(* is cwlsm_f, pullY is the p2_base map (c,s,u,v,a) -> (c,--s,u-4s,4c-v-a,a).*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallLowerSupportMargin.ml";;

(* p * (l - r) = 0 from |- l = r *)
let CRCS_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let CRCS_LE_CANCEL = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: upper_u_margin (private) *)
let CRCS_UPPER_U_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 <= &1 - c * ((&1 - d) + d * t + (&43 / &500) * t pow 2) +
              s * (t - t pow 2 + (&43 / &500) * d * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d - t`; SQ_NONNEG `t:real`]
   [`&0 <= d * t`; `d * t <= &1 / &2`; `&0 <= (d - t) * (d + t)`; `t pow 2 <= &1 / &2`;
    `&0 <= (&1 - d) + d * t + (&43 / &500) * t pow 2`;
    `(&1 - d) + d * t + (&43 / &500) * t pow 2 <= &843 / &1000`;
    `&0 <= t * (&1 - t)`; `&0 <= t - t pow 2 + (&43 / &500) * d * t`;
    `&0 <= (&1 - c) * ((&1 - d) + d * t + (&43 / &500) * t pow 2)`;
    `&0 <= s * (t - t pow 2 + (&43 / &500) * d * t)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: band_bound (private) *)
let CRCS_BAND_BOUND = prove
 (`forall c s d t a u v. c977cc_normal c s /\ c977cc_normal d t /\ &0 < t /\ &1 <= a /\
     d * (u + a) - t * v <= &4 /\ v <= &2 * d - (&1543 / &500) * t /\
     (u + a <= &3 * (d + t) \/ v + a <= &3 * (d - t))
     ==> (c * d + s * t) * u + (s * d - c * t) * v - a * max (c * t - s * d) (&0) <=
         &2 * (c + s) + &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWLSM_MARGIN) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CRCS_UPPER_U_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= c * d`; `&0 <= s * t`; `&0 <= c * d + s * t`] THEN
  SUBGOAL_THEN `&0 <= max (c * t - s * d) (&0)` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * cwlsm_f c s d t = d * (&1 - &2 * c - s) + s * (&1 - t) +
                d * ((c * d + s * t) + max (c * t - s * d) (&0))` ASSUME_TAC THENL
   [REWRITE_TAC[CWLSM_F_DEF] THEN UNDISCH_TAC `~(d = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [ASM_CASES_TAC `&0 <= s * d - c * t` THENL
     [SUBGOAL_THEN `max (c * t - s * d) (&0) = &0` SUBST1_TAC THENL
       [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= (c * d + s * t) * (&3 * (d + t) - (u + a))`;
        `&0 <= (s * d - c * t) * (&2 * d - (&1543 / &500) * t - v)`;
        `&0 <= (a - &1) * (c * d + s * t)`] THEN
      NLIN_TAC ~deg2:false [CRCS_EQ_HINT `&3 * c + &2 * s` (ASSUME `d pow 2 + t pow 2 = &1`)];
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      SUBGOAL_THEN `max (c * t - s * d) (&0) = c * t - s * d` ASSUME_TAC THENL
       [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= s * (&1 - t) / d` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
      SUBGOAL_THEN
       `t * (&2 * (c + s) + &1 - ((c * d + s * t) * u + (s * d - c * t) * v +
                                  a * (s * d - c * t))) =
        s * (&3 * (d + t) - (u + a)) - (s * d - c * t) * (&4 - d * (u + a) + t * v) +
        (a - &1) * t * ((c * d + s * t) - (s * d - c * t)) + t * cwlsm_f c s d t +
        s * (&1 - t) / d` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[CWLSM_F_DEF] THEN
        MAP_EVERY UNDISCH_TAC [`~(d = &0)`; `d pow 2 + t pow 2 = &1`] THEN
        CONV_TAC REAL_FIELD; ALL_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= s * (&3 * (d + t) - (u + a))`;
        `&0 <= --(s * d - c * t) * (&4 - (d * (u + a) - t * v))`;
        `&0 <= t * ((c * d + s * t) - (s * d - c * t))`;
        `&0 <= (a - &1) * (t * ((c * d + s * t) - (s * d - c * t)))`;
        `&0 <= t * cwlsm_f c s d t`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CRCS_LE_CANCEL THEN EXISTS_TAC `t:real` THEN
      ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []];
    NLIN_FACTS_TAC []
     [`&0 <= (c * d + s * t) * (&4 - (d * (u + a) - t * v))`;
      `&0 <= s * (&3 * (d - t) - (v + a))`;
      `&0 <= s + d * ((c * d + s * t) + max (c * t - s * d) (&0))`;
      `&0 <= (a - &1) * (s + d * ((c * d + s * t) + max (c * t - s * d) (&0)))`;
      `&0 <= d * cwlsm_f c s d t`] THEN
    MATCH_MP_TAC CRCS_LE_CANCEL THEN EXISTS_TAC `d:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [CRCS_EQ_HINT `s * v` (ASSUME `d pow 2 + t pow 2 = &1`)]]);;

(* Lean: lower_support *)
let CRCS_LOWER_SUPPORT = prove
 (`forall cR sR uR vR aR c s.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal c s /\ c977cc_normal cR sR /\ &1 <= aR /\
     lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&3) (&3)
     ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] CWE_RIGHT_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `linside cR sR uR vR aR (&1543 / &500) (&2)` THEN
  UNDISCH_TAC `~linside cR sR uR vR aR (&3) (&3)` THEN
  REWRITE_TAC[linside] THEN REPEAT DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(c * cR + s * sR) = c * cR + s * sR` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN NLIN_TAC []; ALL_TAC] THEN
  ASM_CASES_TAC `sR = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    NLIN_FACTS_TAC [] [`&1 <= cR`] THEN
    SUBGOAL_THEN `cR = &1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID;
                REAL_NEG_0; REAL_ADD_LID] THEN
    SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`uR <= &3`; `vR <= &2`; `&0 <= c * (&3 - uR)`; `&0 <= s * (&2 - vR)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sR` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `cR:real`]
   [`&0 <= cR * (&1 + cR) - sR`; `&0 <= sR * (cR * (&1 + cR) - sR)`] THEN
  SUBGOAL_THEN `(&1 + cR) * (cR + cR * sR - &1) = sR * (cR * (&1 + cR) - sR)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `cR pow 2 + sR pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= cR + cR * sR` ASSUME_TAC THENL
   [MATCH_MP_TAC CRCS_LE_CANCEL THEN EXISTS_TAC `&1 + cR` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
  SUBGOAL_THEN `uR < &3 * (cR + sR)` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LT]) THEN
    NLIN_FACTS_TAC []
     [`&0 <= cR * (uR - &3 * (cR + sR))`; `&0 <= cR * (aR - &1)`;
      `vR < --sR * &1543 / &500 + cR * &2`;
      `sR * vR < sR * (--sR * &1543 / &500 + cR * &2)`] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `sR:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `vR < &3 * (cR - sR)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uR + aR <= &3 * (cR + sR) \/ vR + aR <= &3 * (cR - sR)` ASSUME_TAC THENL
   [ASM_CASES_TAC `uR + aR <= &3 * (cR + sR)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(uR < cR * &3 + sR * &3 /\ cR * &3 + sR * &3 < uR + aR /\
                   vR < --sR * &3 + cR * &3 /\ --sR * &3 + cR * &3 < vR + aR)` THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `cR:real`; `sR:real`; `aR:real`; `uR:real`; `vR:real`]
    CRCS_BAND_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= b ==> y <= b`) THEN
  REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`;
               REAL_ARITH `c * sR - s * cR <= &0 ==> &0 <= --c * sR + s * cR`;
               REAL_ARITH `~(c * sR - s * cR <= &0) ==> --c * sR + s * cR <= &0`] THEN
  REAL_ARITH_TAC);;

let CRCS_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: negative_lower_support *)
let CRCS_NEGATIVE_LOWER_SUPPORT = prove
 (`forall cR sR uR vR aR c s t.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal c s /\ c977cc_normal cR t /\ sR = --t /\ &1 <= aR /\
     lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2)
     ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`--sR`; `cR:real`; `vR:real`; `--uR - aR`; `aR:real`] CWE_RIGHT_WALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `lcont cR sR uR vR aR` THEN REWRITE_TAC[lcont; CRCS_TURN_INSIDE];
    DISCH_TAC] THEN
  UNDISCH_TAC `linside cR sR uR vR aR (&1543 / &500) (&2)` THEN
  REWRITE_TAC[linside] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `sR:real`)) THEN
  C977CSB_NORMAL_TAC THEN REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
  SUBGOAL_THEN `~(cR = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cR * (c - s)`; `&0 <= s * (cR - t)`; `&0 <= c * cR - s * t`;
    `&0 <= c * t + s * cR`] THEN
  SUBGOAL_THEN `abs(c * cR + s * --t) = c * cR - s * t /\
                abs(--c * --t + s * cR) = c * t + s * cR` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= t * (&1 + cR - &2 * t)`; `&0 <= (&1 + cR) * (&2 * cR + t - &2)`;
    `&2 <= &2 * cR + t`; `t <= &457 / &500`; `&0 <= t * (&457 / &500 - t)`] THEN
  ABBREV_TAC `Q = t * (cR + t - &457 / &500) / cR` THEN
  SUBGOAL_THEN `cR * Q = t * (cR + t - &457 / &500)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN UNDISCH_TAC `~(cR = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `Q <= t` ASSUME_TAC THENL
   [MATCH_MP_TAC CRCS_LE_CANCEL THEN EXISTS_TAC `cR:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - cR`; SQ_NONNEG `s - t`]
   [`&0 <= c * (cR - (&2 - cR - t))`; `&0 <= s * (t - Q)`; `c * cR + s * t <= &1`;
    `&0 <= &1 - (&2 - cR - t) * c - Q * s`;
    `&0 <= (c * cR - s * t) * (&4 - (cR * (uR + aR) - --t * (vR + aR)))`;
    `&0 <= s * ((&1543 / &500) * t + &2 * cR - vR)`;
    `&0 <= (c * cR - s * t) * (cR + t)`;
    `&0 <= (aR - &1) * ((c * cR - s * t) * (cR + t))`;
    `&0 <= cR * (&1 - (&2 - cR - t) * c - Q * s)`] THEN
  MATCH_MP_TAC CRCS_LE_CANCEL THEN EXISTS_TAC `cR:real` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false
   [CRCS_EQ_HINT `s * vR` (ASSUME `cR pow 2 + t pow 2 = &1`);
    CRCS_EQ_HINT `s:real` (ASSUME `cR * Q = t * (cR + t - &457 / &500)`)]);;

(* Lean: canonical_lower_support *)
let CRCS_CANONICAL_LOWER_SUPPORT = prove
 (`forall cR sR uR vR aR c s.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal c s /\ abs sR <= cR /\ &1 <= aR /\
     lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&3) (&3)
     ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= sR` THENL
   [MATCH_MP_TAC CRCS_LOWER_SUPPORT THEN ASM_REWRITE_TAC[c977cc_normal] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_POW_2]];
    MATCH_MP_TAC CRCS_NEGATIVE_LOWER_SUPPORT THEN EXISTS_TAC `--sR` THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_NEG_NEG] THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REAL_ARITH_TAC]);;

(* Lean: lower_pullY *)
let CRCS_LOWER_PULLY = prove
 (`forall cR sR uR vR aR c s. cR * cR + sR * sR = &1
     ==> ABT_lower cR (--sR) (uR - &4 * sR) (&4 * cR - vR - aR) aR c (--s) =
         ABT_lower cR sR uR vR aR c s - &4 * s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `c * cR + --s * --sR = c * cR + s * sR`;
              REAL_ARITH `abs(--c * --sR + --s * cR) = abs(--c * sR + s * cR)`] THEN
  UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING);;

(* Lean: signed_direction_support *)
let CRCS_SIGNED_DIRECTION_SUPPORT = prove
 (`forall cR sR uR vR aR c s.
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     abs s <= c /\ c pow 2 + s pow 2 = &1 /\ abs sR <= cR /\ &1 <= aR /\
     lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&3) (&3) /\ ~linside cR sR uR vR aR (&3) (&1)
     ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [MATCH_MP_TAC CRCS_CANONICAL_LOWER_SUPPORT THEN ASM_REWRITE_TAC[c977cc_normal] THEN
    ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`cR:real`; `--sR`; `uR - &4 * sR`; `&4 * cR - vR - aR`; `aR:real`;
                  `c:real`; `--s`] CRCS_CANONICAL_LOWER_SUPPORT) THEN
    ASM_SIMP_TAC[CRCS_LOWER_PULLY; LINSIDE_PULLY; LCONT_PULLY] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[c977cc_normal; REAL_ABS_NEG] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
      UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* Lean: forward_impossible *)
let CRCS_FORWARD_IMPOSSIBLE = prove
 (`forall cB sB uB (vB:real) aB cR sR uR vR aR.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     c977cc_normal cB sB /\ c977cc_normal cR sR /\ &1 < aB /\ &1 <= aR /\
     lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&3) (&3) /\
     &2 * (cB + sB) <= uB /\ uB + aB <= ABT_lower cR sR uR vR aR cB sB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `cB:real`; `sB:real`]
    CRCS_LOWER_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
