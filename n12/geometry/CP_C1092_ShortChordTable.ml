(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShortChordTable.lean                      *)
(* (namespace N12Compact.C1092ShortChordTable).                              *)
(* Normal (C977CornerCubic) is c977cc_normal; normal_bounds is               *)
(* C977CC_NORMAL_BOUNDS.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092SCT_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092SCT_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092SCT_LIN_TAC;;

let C1092SCT_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092SCT_MISS_TAC x y; ALL_TAC];;

let C1092SCT_UNFOLD_TAC =
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th
                           else REWRITE_RULE[c977cc_normal; linside] th);;

(* Lean: PositiveFaces (definition) *)
let c1092sct_positive_faces = new_definition
 `c1092sct_positive_faces (b:real) t p q a <=>
    --b <= p /\ p + a <= t - (&39 / &100) * b /\ (&39 / &100) * t <= q /\
    q + a <= b + t`;;

(* Lean: NegativeFaces (definition) *)
let c1092sct_negative_faces = new_definition
 `c1092sct_negative_faces (b:real) t p q a <=>
    --b - t <= p /\ p + a <= --(&39 / &100) * b /\ --t <= q /\
    q + a <= b - (&39 / &100) * t`;;

(* Lean: steep *)
let C1092SCT_STEEP = prove
 (`forall b t a. c977cc_normal b t /\ &1 < a /\ a <= t + (&61 / &100) * b
           ==> &9 / &20 < t /\ b < &9 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&1 - b`] [`b <= &1 - t * t / &2`] THEN
  SUBGOAL_THEN `&9 / &20 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&9 / &20 - t) * (&1 - (&61 / &200) * (t + &9 / &20))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (t - &9 / &20) * (t + &9 / &20) /\
                &0 <= (b - &9 / &10) * (b + &9 / &10)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: positive *)
let C1092SCT_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c s /\
     linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     linside c s u v a (--(&1)) (&13 / &50) /\
     linside c s u v a (--(&1)) (&2 / &5) /\
     ~linside c s u v a (--(&1)) (&0) /\
     ~linside c s u v a (--(&1)) (&1) /\
     ~linside c s u v a (--(&39 / &100)) (&0) /\
     ~linside c s u v a (--(&39 / &100)) (&1)
     ==> c1092sct_positive_faces c s u v a /\ &9 / &20 < s /\ c < &9 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  SUBGOAL_THEN `c1092sct_positive_faces c s u v a` ASSUME_TAC THENL
   [C1092SCT_UNFOLD_TAC THEN
    C1092SCT_FACT_TAC `(&39 / &100) * s <= v` `--(&39 / &100)` `&0` THEN
    C1092SCT_FACT_TAC `u + a <= s - (&39 / &100) * c` `--(&39 / &100)` `&1` THEN
    C1092SCT_FACT_TAC `v + a <= c + s` `--(&1)` `&1` THEN
    C1092SCT_FACT_TAC `--c <= u` `--(&1)` `&0` THEN
    REWRITE_TAC[c1092sct_positive_faces] THEN C1092SCT_LIN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092SCT_STEEP THEN
  EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092sct_positive_faces c s u v a` THEN
  REWRITE_TAC[c1092sct_positive_faces] THEN REAL_ARITH_TAC);;

(* Lean: negative *)
let C1092SCT_NEGATIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c (--s) /\
     linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     linside c s u v a (--(&1)) (&13 / &50) /\
     linside c s u v a (--(&1)) (&2 / &5) /\
     ~linside c s u v a (--(&1)) (&0) /\
     ~linside c s u v a (--(&1)) (&1) /\
     ~linside c s u v a (--(&39 / &100)) (&0) /\
     ~linside c s u v a (--(&39 / &100)) (&1)
     ==> c1092sct_negative_faces c (--s) u v a /\ &9 / &20 < --s /\ c < &9 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  SUBGOAL_THEN `c1092sct_negative_faces c (--s) u v a` ASSUME_TAC THENL
   [C1092SCT_UNFOLD_TAC THEN
    C1092SCT_FACT_TAC `s <= v` `--(&1)` `&0` THEN
    SUBGOAL_THEN `u + a <= --(&39 / &100) * c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `v < (&39 / &100) * s` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
        C1092SCT_MISS_TAC `--(&39 / &100)` `&1`; ALL_TAC] THEN
      C1092SCT_MISS_TAC `--(&39 / &100)` `&0`; ALL_TAC] THEN
    C1092SCT_FACT_TAC `v + a <= c + (&39 / &100) * s` `--(&39 / &100)` `&1` THEN
    C1092SCT_FACT_TAC `--c + s <= u` `--(&1)` `&1` THEN
    REWRITE_TAC[c1092sct_negative_faces] THEN C1092SCT_LIN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092SCT_STEEP THEN
  EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092sct_negative_faces c (--s) u v a` THEN
  REWRITE_TAC[c1092sct_negative_faces] THEN REAL_ARITH_TAC);;
