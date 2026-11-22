(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/RightInwardProfile.lean              *)
(* (namespace N12Compact.C1092MMMPRightInwardProfile).                       *)
(* canonical_frame: CLF_CANONICAL_FRAME; Normal: c977cc_normal.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MRIP_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092MRIP_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MRIP_LIN_TAC;;

let C1092MRIP_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092MRIP_MISS_TAC x y; ALL_TAC];;

let C1092MRIP_UNFOLD_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `c977cc_normal x y`) (concl th) then
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG;
                                    REAL_MUL_RNEG; REAL_NEG_NEG] th)
    else NO_TAC)) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th);;

(* Lean: Data (structure) *)
let c1092mrip_data = new_definition
 `c1092mrip_data (c:real) s u v (a:real) <=>
    (&7 / &20) * (c + s) <= u /\ --s - (&13 / &50) * c <= v /\
    &9 * c < &35 * --s /\ &37 * --s < &13 * c /\
    &47 / &50 < c /\ &6 / &25 < --s /\ --s < &1 / &3`;;

(* Lean: positive_impossible (private) *)
let C1092MRIP_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c s /\ &1 < a /\
     linside c s u v a (&13 / &50) (&0) /\
     linside c s u v a (&543 / &500) (&0) /\
     linside c s u v a (&1) (&2 / &5) /\
     ~linside c s u v a (&1) (--(&13 / &50)) /\
     ~linside c s u v a (&7 / &20) (&7 / &20)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MRIP_UNFOLD_TAC THEN
  C1092MRIP_FACT_TAC `--s - (&13 / &50) * c <= v` `&1` `--(&13 / &50)` THEN
  C1092MRIP_FACT_TAC `v + a <= (&7 / &20) * (c - s)` `&7 / &20` `&7 / &20` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&13 / &20) * c - (&61 / &100) * s`;
                  SQ_NONNEG `(&61 / &100) * c + (&13 / &20) * s - &1`]
   [`(&61 / &100) * c + (&13 / &20) * s < &1`] THEN
  C1092MRIP_LIN_TAC);;

(* Lean: negative_data *)
let C1092MRIP_NEGATIVE_DATA = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c (--s) /\ &1 < a /\
     linside c s u v a (&13 / &50) (&0) /\
     linside c s u v a (&543 / &500) (&0) /\
     linside c s u v a (&1) (&2 / &5) /\
     ~linside c s u v a (&1) (--(&13 / &50)) /\
     ~linside c s u v a (&7 / &20) (&7 / &20)
     ==> c1092mrip_data c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MRIP_UNFOLD_TAC THEN
  C1092MRIP_FACT_TAC `(&7 / &20) * (c + s) <= u` `&7 / &20` `&7 / &20` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&61 / &100) * c - (&13 / &20) * --s`;
                  SQ_NONNEG `(&13 / &20) * c + (&61 / &100) * --s - &1`]
   [`(&13 / &20) * c + (&61 / &100) * --s < &1`] THEN
  C1092MRIP_FACT_TAC `--s - (&13 / &50) * c <= v` `&1` `--(&13 / &50)` THEN
  SUBGOAL_THEN `&9 * c < &35 * --s /\ &37 * --s < &13 * c` STRIP_ASSUME_TAC THENL
   [C1092MRIP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&13 * c - &37 * --s) * (&13 * c + &37 * --s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&47 / &50 < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&47 / &50 - c) * (&47 / &50 + c)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `--s < &1 / &3` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (--s - &1 / &3) * (--s + &1 / &3)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC []; ALL_TAC] THEN
  REWRITE_TAC[c1092mrip_data] THEN C1092MRIP_LIN_TAC);;

(* Lean: exists_negative *)
let C1092MRIP_EXISTS_NEGATIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&13 / &50) (&0) /\
     linside c s u v a (&543 / &500) (&0) /\
     linside c s u v a (&1) (&2 / &5) /\
     ~linside c s u v a (&1) (--(&13 / &50)) /\
     ~linside c s u v a (&7 / &20) (&7 / &20)
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           c977cc_normal c' (--s') /\ c1092mrip_data c' s' u' v' a'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `s' <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a:real`]
      C1092MRIP_POSITIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal c' (--s')` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1092MRIP_NEGATIVE_DATA THEN ASM_REWRITE_TAC[]);;
