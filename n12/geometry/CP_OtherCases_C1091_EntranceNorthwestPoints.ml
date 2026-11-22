(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/EntranceNorthwestPoints.lean  *)
(* (namespace N12Compact.Completion.OtherCases.C1091.EntranceNorthwest      *)
(* Points).  EntranceMergedShallow.Input: c1091ems_input; profile:          *)
(* C1091EMS_PROFILE; Normal: c977cc_normal; canonical_frame:                *)
(* CLF_CANONICAL_FRAME; inside_translated_iff: C1091MMS_TRANSLATED.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1091_EntranceMergedShallow.ml";;

let C1091ENP_UNFOLD_TAC ts =
  MAP_EVERY UNDISCH_TAC ts THEN REWRITE_TAC[linside] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

let C1091ENP_NEG_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;;

(* Lean: merged_alternative *)
let C1091ENP_MERGED_ALTERNATIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1091ems_input c s u v a
     ==> linside c s u v a (&3 / &5) (&1) \/ linside c s u v a (&23 / &50) (&101 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`] C1091EMS_INPUT_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [ALL_TAC;
    SUBGOAL_THEN `false` CONTR_TAC THEN
    MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`]
      C1091EMS_NONPOSITIVE_IMPOSSIBLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `c977cc_normal c1 s1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`] C1091EMS_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1091ems_input] o
    check (fun th -> concl th = `c1091ems_input c1 s1 u1 v1 a`)) THEN
  C1091ENP_UNFOLD_TAC [`linside c1 s1 u1 v1 a (--(&43 / &500)) (&0)`;
                       `linside c1 s1 u1 v1 a (&13 / &20) (&13 / &20)`] THEN
  REWRITE_TAC[linside] THEN
  ASM_CASES_TAC `&7 * s1 <= c1` THENL
   [DISJ1_TAC THEN RASM_ARITH_TAC; DISJ2_TAC THEN RASM_ARITH_TAC]);;

(* Lean: merged_alternative_original *)
let C1091ENP_MERGED_ALTERNATIVE_ORIGINAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&457 / &500) (&1) /\ linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&1) (&1) /\ ~linside c s u v a (&457 / &500) (&2)
     ==> linside c s u v a (&8 / &5) (&2) \/ linside c s u v a (&73 / &50) (&201 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &1 + s * &1)`; `v - (--s * &1 + c * &1)`;
                `a:real`] C1091ENP_MERGED_ALTERNATIVE) THEN
  ASM_REWRITE_TAC[c1091ems_input; C1091MMS_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

(* Lean: positive_low (private) *)
let C1091ENP_POSITIVE_LOW = prove
 (`forall c s u v a. &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&73 / &50) (&201 / &100)
     ==> linside c s u v a (&8 / &5) (&2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: negative_low (private) *)
let C1091ENP_NEGATIVE_LOW = prove
 (`forall c s u v a t. c * c + s * s = &1 /\ &0 < a /\ s = --t /\
     &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&73 / &50) (&201 / &100) /\
     ~linside c s u v a (&8 / &5) (&3) /\ ~linside c s u v a (&2) (&2)
     ==> linside c s u v a (&8 / &5) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C977CC_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C1091ENP_UNFOLD_TAC [`linside c (--t) u v a (&33 / &20) (&47 / &20)`;
                       `linside c (--t) u v a (&87 / &50) (&2)`;
                       `linside c (--t) u v a (&2) (&113 / &50)`;
                       `linside c (--t) u v a (&73 / &50) (&201 / &100)`] THEN
  SUBGOAL_THEN `u + a <= &2 * c - &2 * t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1091ENP_NEG_TAC `~linside c (--t) u v a (&2) (&2)`; ALL_TAC] THEN
  SUBGOAL_THEN `u < (&8 / &5) * c - &3 * t` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&8 / &5) * t + &3 * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1091ENP_NEG_TAC `~linside c (--t) u v a (&8 / &5) (&3)`; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: northwest_low *)
let C1091ENP_NORTHWEST_LOW = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&73 / &50) (&201 / &100) /\
     ~linside c s u v a (&8 / &5) (&3) /\ ~linside c s u v a (&2) (&2)
     ==> linside c s u v a (&8 / &5) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && can (find_term ((=) `linside`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC C1091ENP_POSITIVE_LOW THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C1091ENP_NEGATIVE_LOW THEN EXISTS_TAC `--s1` THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;
