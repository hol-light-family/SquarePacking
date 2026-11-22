(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MixedWideWall.lean                        *)
(* (namespace N12Compact.C1092MixedWideWall).                                *)
(* square_support_bound: C1092MPWS_SQUARE_SUPPORT_BOUND;                     *)
(* center_coordinates: LCENTRE_COORDS; short_projections:                    *)
(* WFP_SHORT_PROJECTIONS; centerX/centerY: lcx/lcy.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977ChainBridge.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/CentralWallEscape.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/CP_C1092_MMMP_PhysicalWallSupport.ml";;

let C1092MWW_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092MWW_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MWW_LIN_TAC;;

let C1092MWW_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092MWW_MISS_TAC x y; ALL_TAC];;

let C1092MWW_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C1092MWW_LIN_TAC; ALL_TAC]) tms;;

let C1092MWW_SP dx dy =
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

let C1092MWW_PREP_TAC =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lcy c s u v a = s * (u + a / &2) + c * (v + a / &2)` ASSUME_TAC THENL
   [REWRITE_TAC[lcy]; ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th);;

(* Lean: positive_impossible (private) *)
let C1092MWW_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\ &0 < c /\ &0 <= s /\ s <= c /\
     (forall x y. linside c s u v a x y ==> x <= &2) /\ lcy c s u v a <= &0 /\
     linside c s u v a (&543 / &500) (&0) /\
     linside c s u v a (&1) (--(&39 / &100)) /\
     linside c s u v a (&1) (&2 / &5) /\
     ~linside c s u v a (&1) (--(&2 / &5)) /\
     ~linside c s u v a (&7 / &20) (&7 / &20)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1`; `&0`; `&2`]
    C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LID; tss_support_radius] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`;
               REAL_ARITH `&0 <= s ==> abs(-- &1 * s) = s`] THEN
  DISCH_TAC THEN
  C1092MWW_PREP_TAC THEN
  C1092MWW_SP `--(&13 / &20)` `&3 / &4` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  SUBGOAL_THEN `c - (&2 / &5) * s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MWW_FACT_TAC `--s - (&2 / &5) * c <= v` `&1` `--(&2 / &5)` THEN
    SUBGOAL_THEN `(&7 / &20) * (c + s) <= u` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MWW_FACT_TAC `v + a <= --(&7 / &20) * s + (&7 / &20) * c`
        `&7 / &20` `&7 / &20` THEN
      C1092MWW_LIN_TAC; ALL_TAC] THEN
    C1092MWW_PROD_TAC [`&0 <= s * (u - (&7 / &20) * (c + s))`;
                       `&0 <= c * (v - (--s - (&2 / &5) * c))`;
                       `&0 < (a - &1) * (c + s)`;
                       `&0 <= c * (&1 - c)`; `&0 <= s * (&1 - c)`] THEN
    NLIN_TAC [SQ_NONNEG `s - &3 / &10`]; ALL_TAC] THEN
  C1092MWW_PROD_TAC [`&0 <= s * (u - (c - (&2 / &5) * s))`;
                     `&0 < c * ((v + a) - (--s * &1 + c * &2 / &5))`] THEN
  SUBGOAL_THEN `(c - s) * ((&2 / &5) * (c + s) - a / &2) < lcy c s u v a` ASSUME_TAC THENL
   [C1092MWW_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c - s` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT; REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(c - c) * ((&2 / &5) * (c + c) - a / &2) < lcy c c u v a` THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 / &5) * (c + s) < a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MWW_PROD_TAC [`&0 <= (c - s) * ((&2 / &5) * (c + s) - a / &2)`] THEN
    C1092MWW_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 / &5 < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MWW_PROD_TAC [`&0 <= (&4 / &5 - c) * (&4 / &5 + c)`] THEN
    SUBGOAL_THEN `&3 / &5 <= s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
    C1092MWW_PROD_TAC [`&0 <= (&1 / &5 - (c - s)) * (&1 / &5 + (c - s))`] THEN
    SUBGOAL_THEN `&7 / &5 <= c + s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
    C1092MWW_LIN_TAC; ALL_TAC] THEN
  C1092MWW_PROD_TAC [`&0 <= c * (&2 - a * (c + s) / &2 - lcx c s u v a)`;
                     `&0 <= s * --lcy c s u v a`] THEN
  SUBGOAL_THEN `a * (&1 + c * c + c * s) <= &2 * c + (&4 / &5) * s` ASSUME_TAC THENL
   [C1092MWW_LIN_TAC; ALL_TAC] THEN
  C1092MWW_PROD_TAC [`&0 <= c * s`; `&0 <= c * c`] THEN
  C1092MWW_PROD_TAC [`&0 < (a - &1) * (&1 + c * c + c * s)`;
                     `&0 <= s * (c - &4 / &5)`] THEN
  NLIN_TAC [SQ_NONNEG `&1 - c`]);;

(* Lean: canonical_profile *)
let C1092MWW_CANONICAL_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\ &0 < c /\ abs s <= c /\
     (forall x y. linside c s u v a x y ==> x <= &2) /\ lcy c s u v a <= &0 /\
     linside c s u v a (&543 / &500) (&0) /\
     linside c s u v a (&1) (--(&39 / &100)) /\
     linside c s u v a (&1) (&2 / &5) /\
     ~linside c s u v a (&1) (--(&2 / &5)) /\
     ~linside c s u v a (&7 / &20) (&7 / &20)
     ==> s < &0 /\ --s < c /\ &5 / &4 < c - s /\
         (&7 / &20) * (c + s) <= u /\ --s - (&2 / &5) * c <= v /\
         u < c + (&2 / &5) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
      C1092MWW_POSITIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s <= c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MWW_PREP_TAC THEN
  C1092MWW_SP `&13 / &20` `--(&3 / &4)` THEN
  C1092MWW_FACT_TAC `(&7 / &20) * (c + s) <= u` `&7 / &20` `&7 / &20` THEN
  C1092MWW_FACT_TAC `--s - (&2 / &5) * c <= v` `&1` `--(&2 / &5)` THEN
  C1092MWW_PROD_TAC [`&0 < --s * ((c * &1 + s * &2 / &5) - u)`;
                     `&0 <= c * (v - (--s - (&2 / &5) * c))`] THEN
  SUBGOAL_THEN `(c + s) * (a / &2 - (&2 / &5) * (c - s)) < lcy c s u v a` ASSUME_TAC THENL
   [C1092MWW_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c + s` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `(c + s) * (a / &2 - (&2 / &5) * (c - s)) < lcy c s u v a` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&5 / &4 < c - s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092MWW_PROD_TAC [`&0 <= (c + s) * (a / &2 - (&2 / &5) * (c - s))`] THEN
    C1092MWW_LIN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C1092MWW_LIN_TAC);;
