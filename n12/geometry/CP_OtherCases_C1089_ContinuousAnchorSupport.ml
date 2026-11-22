(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ContinuousAnchorSupport.lean  *)
(* (namespace N12Compact.Completion.OtherCases.C1089.ContinuousAnchorSupport)*)
(* lower / upper: ABT_lower / ABT_upper; formulas: C1092WS_FORMULAS;        *)
(* PhysicalWallSupport.own_lt / lower_le: C1092MPWS_OWN_LT / _LOWER_LE;     *)
(* ShortWallPenalty.penalty: C1092SWP_PENALTY; OuterArmScalars.endpoint:    *)
(* C1092MOAS_ENDPOINT; CenterCrosspointSupport.negative_axes:               *)
(* C1092CCSP_NEGATIVE_AXES; ContinuousAnchorScalars: C1089CAS_*;            *)
(* exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME; the frame              *)
(* turnFrame (turnFrame (turnFrame V)) of V = (c,s,u,v,a) is                *)
(* (s, --c, --v - a, u, a) (C1089CAP_TURN3).                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousAnchorScalars.ml";;
needs "n12/geometry/CP_C1092_MMMP_PhysicalWallSupport.ml";;
needs "n12/geometry/CP_C1092_MMMP_CenterCrosspointSupport.ml";;
needs "n12/geometry/CP_C1092_ShortWallPenalty.ml";;
needs "n12/geometry/CP_C1092_MMMP_OuterArmScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

let C1089CAP_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [FIRST [MATCH_MP_TAC REAL_LT_LMUL; MATCH_MP_TAC REAL_LE_LMUL;
            MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC]) tms;;

let C1089CAP_USE th = MP_TAC th THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN TRY ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: fixed (private) *)
let C1089CAP_FIXED = prove
 (`forall cC sC uC vC aC cW sW uW vW aW c s h b.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC = c /\ sC = --s /\ cW = h /\ sW = --b /\
     c977cc_normal c s /\ &0 < s /\ &0 <= h /\ &0 <= b /\
     &1 < aC /\ aC = aW /\ &0 <= vC /\ vC < (&13 / &50) * s /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\ linside cC sC uC vC aC (&1) (&2 / &5) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\ linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\ &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) v o concl)))
   [`cC:real = c`; `sC:real = --s`; `cW:real = h`; `sW:real = --b`; `aC:real = aW`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  SUBGOAL_THEN `h pow 2 + b pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `h * h + --b * --b = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1089CAP_USE (SPECL [`c:real`; `--s`; `uC:real`; `vC:real`; `aW:real`;
              `h:real`; `--b`; `uW:real`; `vW:real`; `aW:real`; `&2 / &5`]
         C1092CCSP_NEGATIVE_AXES) THEN
  C1089CAP_USE (SPECL [`h:real`; `--b`; `uW:real`; `vW:real`; `aW:real`] C1092MPWS_OWN_LT) THEN
  C1089CAP_USE (SPECL [`h:real`; `--b`; `uW:real`; `vW:real`; `aW:real`; `c:real`; `--s`]
         C1092MPWS_LOWER_LE) THEN
  C1089CAP_USE (SPECL [`c:real`; `--s`; `uC:real`; `vC:real`; `aW:real`; `h:real`; `--b`]
         C1092WS_FORMULAS) THEN
  C1089CAP_USE (SPECL [`c:real`; `s:real`] C1092MOAS_ENDPOINT) THEN
  C1089CAP_USE (SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1092SWP_PENALTY) THEN
  (* alpha = c h + s b > 0 *)
  SUBGOAL_THEN `&0 < h + b` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC []; ALL_TAC] THEN
  C1089CAP_PROD_TAC [`&0 < s * (h + b)`; `&0 <= (c - s) * h`] THEN
  SUBGOAL_THEN `&0 < c * h + s * b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(c * h + --s * --b) = c * h + s * b /\
                abs(--c * --b + --s * h) = abs(s * h - c * b) /\
                abs(c * b - s * h) = abs(s * h - c * b)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* ownNormal *)
  SUBGOAL_THEN `ABT_lower h (--b) uW vW aW c (--s) < c - (&2 / &5) * s` ASSUME_TAC THENL
   [UNDISCH_TAC `ABT_lower h (--b) uW vW aW c (--s) <=
       &2 * c - aW * (c * (h - --b) + abs (c * h + --s * --b) +
                      abs (--c * --b + --s * h)) / &2` THEN
    UNDISCH_TAC `&1 + c pow 2 + c * s <= &2 * c * h + c * b + s * b + abs (c * b - s * h)` THEN
    UNDISCH_TAC `&0 <= ((&1 - c) pow 2 + s * (c - &4 / &5)) / &2` THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`abs(s * h - c * b)`,`D:real`) THEN
    SPEC_TAC(`ABT_lower h (--b) uW vW aW c (--s)`,`L:real`) THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN REPEAT DISCH_TAC THEN
    C1089CAP_PROD_TAC [`&0 <= c * c`; `&0 <= c * s`] THEN
    SUBGOAL_THEN `&0 < (aW - &1) * (c * (h + b) + (c * h + s * b) + D)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c - (&2 / &5) * s < uC + aW` ASSUME_TAC THENL
   [UNDISCH_TAC `linside c (--s) uC vC aW (&1) (&2 / &5)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `ABT_upper c (--s) uC vC aW h (--b) <= uW` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `h * c + --b * --s = c * h + s * b /\ --h * --s + --b * c = s * h - c * b`
    (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> max x (&0) = x`] THEN DISCH_TAC THEN
  C1089CAP_PROD_TAC [`(c * h + s * b) * (c - (&2 / &5) * s) < (c * h + s * b) * (uC + aW)`] THEN
  ASM_CASES_TAC `&0 <= s * h - c * b` THENL
   [C1089CAP_USE(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1089CAS_FIRST) THEN
    C1089CAP_PROD_TAC [`(s * h - c * b) * &1 <= (s * h - c * b) * (vC + aW)`] THEN
    UNDISCH_TAC `(c * h + s * b) * uC + (s * h - c * b) * vC + aW * (c * h + s * b) +
                 aW * max (s * h - c * b) (&0) <= uW` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`] THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    C1089CAP_USE(SPECL [`c:real`; `s:real`; `h:real`; `b:real`] C1089CAS_SECOND) THEN
    C1089CAP_PROD_TAC [`&0 <= --(s * h - c * b) * ((&13 / &50) * s - vC)`] THEN
    UNDISCH_TAC `(c * h + s * b) * uC + (s * h - c * b) * vC + aW * (c * h + s * b) +
                 aW * max (s * h - c * b) (&0) <= uW` THEN
    ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> max x (&0) = &0`] THEN
    SUBGOAL_THEN `h * (c * c + s * s) = h * &1` MP_TAC THENL
     [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
      SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC]);;

(* the triple turnFrame *)
let C1089CAP_TURN3 = prove
 (`forall c s u v a x y. linside s (--c) (--v - a) u a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1089CAP_TURN3_LCY = prove
 (`forall c s u v a. lcy s (--c) (--v - a) u a = lcy c s u v a`,
  REWRITE_TAC[lcy] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let C1089CAP_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cC (--sC) /\ sC < &0 /\ &1 < aC /\ aC = aW /\ &0 <= vC /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\ linside cC sC uC vC aC (&1) (&2 / &5) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\ linside cW sW uW vW aW (&1) (&13 / &50) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\ &0 <= lcy cW sW uW vW aW /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`cV:real`; `sV:real`; `uV:real`; `vV:real`; `aV:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aV:real = aW`)) THEN
  SUBGOAL_THEN `vC < &13 / &50 * --sC` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aW (&13 / &50) (&0)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aW:real`;
                `sV:real`; `--cV`; `--vV - aW`; `uV:real`; `aW:real`;
                `cC:real`; `--sC`; `sV:real`; `cV:real`] C1089CAP_FIXED) THEN
  REWRITE_TAC[ldisj; C1089CAP_TURN3; C1089CAP_TURN3_LCY; REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC);;
