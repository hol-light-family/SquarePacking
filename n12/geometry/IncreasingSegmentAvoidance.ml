(* ========================================================================= *)
(* Port of Compact/Geometry/IncreasingSegmentAvoidance.lean (Jatloe N12).     *)
(* An increasing foreign segment avoiding a square's interior: either it     *)
(* lies above the upper V face, or its lower-U crossing is above that face.  *)
(* S12.inside_segment is CES_INSIDE_SEGMENT (CentralEscapeSegment.ml).       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

let ISA_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* Lean: dichotomy *)
let ISA_DICHOTOMY = prove
 (`forall cA sA uA vA aA cW sW uW vW aW x0 y0 x1 y1.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     linside cW sW uW vW aW x0 y0 /\ linside cW sW uW vW aW x1 y1 /\
     &0 < cA * (x1 - x0) + sA * (y1 - y0) /\
     &0 < --sA * (x1 - x0) + cA * (y1 - y0) /\
     uA < cA * x1 + sA * y1 /\ cA * x1 + sA * y1 < uA + aA /\
     vA < --sA * x0 + cA * y0 /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> vA + aA <= --sA * x0 + cA * y0 \/
         (cA * (x1 - x0) + sA * (y1 - y0)) * (vA + aA) <=
           (--sA * (x1 - x0) + cA * (y1 - y0)) * uA -
           ((--sA * (x1 - x0) + cA * (y1 - y0)) * (cA * x0 + sA * y0) -
            (cA * (x1 - x0) + sA * (y1 - y0)) * (--sA * x0 + cA * y0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = cA * (x1 - x0) + sA * (y1 - y0)` THEN
  ABBREV_TAC `e = --sA * (x1 - x0) + cA * (y1 - y0)` THEN
  ABBREV_TAC `U = cA * x0 + sA * y0` THEN
  ABBREV_TAC `V = --sA * x0 + cA * y0` THEN
  SUBGOAL_THEN `cA * x1 + sA * y1 = U + d` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "d"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `vA + aA <= V` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `al = (uA - U) / d` THEN
  ABBREV_TAC `be = (vA + aA - V) / e` THEN
  SUBGOAL_THEN `al * d = uA - U /\ be * e = vA + aA - V` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["al"; "be"] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d * e /\ (al * d) * e = (uA - U) * e /\
                (be * e) * d = (vA + aA - V) * d` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `al < be /\ al < &1 /\ &0 < be` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  ABBREV_TAC `t = (max (&0) al + min (&1) be) / &2` THEN
  SUBGOAL_THEN `&0 < t /\ t < &1 /\ al < t /\ t < be` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `uA - U < t * d /\ t * e < vA + aA - V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - t) * d /\ &0 < t * e` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `x0:real`; `y0:real`; `x1:real`; `y1:real`; `t:real`]
    CES_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `ldisj cA sA uA vA aA cW sW uW vW aW` THEN
  REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`(&1 - t) * x0 + t * x1`; `(&1 - t) * y0 + t * y1`]) THEN
  ASM_REWRITE_TAC[linside] THEN
  SUBGOAL_THEN
   `cA * ((&1 - t) * x0 + t * x1) + sA * ((&1 - t) * y0 + t * y1) = U + t * d /\
    --sA * ((&1 - t) * x0 + t * x1) + cA * ((&1 - t) * y0 + t * y1) = V + t * e`
   (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["U"; "V"; "d"; "e"] THEN CONJ_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: left_wall *)
let ISA_LEFT_WALL = prove
 (`forall cA sA uA vA aA cW sW uW vW aW.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aA /\ &0 < cA /\ &0 <= sA /\ sA <= cA /\
     uA + aA <= &2 * (cA + sA) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     linside cW sW uW vW aW (&1) (&113 / &50) /\
     ldisj cA sA uA vA aA cW sW uW vW aW
     ==> vA + aA <= &2 * cA - (&457 / &500) * sA \/
         &1641 / &25000 <=
           ((&13 / &50) * cA - (&43 / &500) * sA) * uA -
           ((&43 / &500) * cA + (&13 / &50) * sA) * (vA + aA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cA <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `sA:real`; SQ_NONNEG `cA - &1`]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `&457 / &500`; `&2`; `&1`; `&113 / &50`] ISA_DICHOTOMY) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  ASM_REWRITE_TAC[linside] THEN
  ANTS_TAC THENL [ISA_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL [DISJ1_TAC THEN ASM_REAL_ARITH_TAC; DISJ2_TAC] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `cA * cA + sA * sA = &1` THEN
  REAL_ARITH_TAC);;
