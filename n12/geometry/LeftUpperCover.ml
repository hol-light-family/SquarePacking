(* ========================================================================= *)
(* Port of Compact/Geometry/LeftUpperCover.lean (N12Compact.LeftUpperCover). *)
(* A wall square with the original left-side anchors contains (7/5,5/2) or   *)
(* (1,283/100).                                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareAForced.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/FourSquareLongitudinal.ml";;

(* Unfold the square predicates in all (real) assumptions and the goal and   *)
(* close by linear arithmetic.  Assumptions with quantifiers are dropped.    *)
let LUC_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (find_term (fun t -> try fst(dest_const t) = "lcont" with _ -> false))
           (concl th) || is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside; lclosed; REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;;

(* Lean: low_of_lower_U *)
let LUC_LOW_OF_LOWER_U = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < c /\ abs s <= c /\ &1 < a /\
      lclosed c s u v a (&457 / &500) (&2) /\
      lclosed c s u v a (&1) (&12 / &5) /\
      ~linside c s u v a (&33 / &20) (&33 / &20) /\
      c * (&19 / &25) + s * (&187 / &100) <= u
      ==> linside c s u v a (&7 / &5) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FSAF_SP_TAC `&89 / &100` `--(&11 / &50)` THEN
  FSAF_SP_TAC `&16 / &25` `&63 / &100` THEN
  FSAF_SP_TAC `--(&1 / &4)` `&17 / &20` THEN
  LUC_LIN_TAC);;

(* Lean: high_upper_U (private) *)
let LUC_HIGH_UPPER_U = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < c /\ abs s <= c /\ &1 < a /\
      lcont c s u v a /\
      lclosed c s u v a (&457 / &500) (&2) /\
      --s * (&19 / &25) + c * (&187 / &100) <= v
      ==> c + s * (&283 / &100) < u + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    FSBL_LEFT_UPPER_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--c <= s /\ s <= c` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
   [`s * s <= c * c`; `c <= &1`; `&7 / &10 <= c`] THEN
  GEN_REWRITE_TAC I [GSYM(MATCH_MP REAL_LT_RMUL_EQ (ASSUME `&0 < c`))] THEN
  ASM_CASES_TAC `&0 <= s` THENL
   [FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `&0 <= s`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REAL_LE_RMUL_EQ (ASSUME `&0 < c`))] THEN
    SUBGOAL_THEN `(a * (&1 + s / c) + (&187 / &100) * s - (&19 / &25) * s pow 2 / c) * c =
                  a * (c + s) + (&187 / &100) * s * c - (&19 / &25) * s pow 2`
      SUBST1_TAC THENL
     [UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `s:real`] FSL_POSITIVE_SLOPE_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
    SUBGOAL_THEN `&0 <= (c + s - c pow 2 - (&24 / &25) * c * s - (&19 / &25) * s pow 2) *
                         (&1 + c)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(c + s - c pow 2 - (&24 / &25) * c * s - (&19 / &25) * s pow 2) *
                    (&1 + c) =
                    s * ((&1 - (&19 / &25) * s) * (&1 + c) + s * c -
                         (&24 / &25) * c * (&1 + c))` SUBST1_TAC THENL
       [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= c + s - c pow 2 - (&24 / &25) * c * s - (&19 / &25) * s pow 2`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `&1 + c` THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 < (a - &1) * (c + s)`] THEN
    REWRITE_TAC[REAL_POW_2] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    NLIN_TAC ~deg2:false [];
    SUBGOAL_THEN `s <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `s <= &0`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REAL_LE_RMUL_EQ (ASSUME `&0 < c`))] THEN
    SUBGOAL_THEN `(a - (&457 / &500) * s pow 2 / c + &2 * s) * c =
                  a * c - (&457 / &500) * s pow 2 + &2 * s * c`
      SUBST1_TAC THENL
     [UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    NLIN_FACTS_TAC [SQ_NONNEG `&1 - c`]
     [`--s <= &1`; `s * s / &2 <= &1 - c`; `&0 <= (c - &7 / &10) * (&1 - c)`;
      `&0 <= (c - &7 / &10) * --s`; `&0 <= --s * (&1 + s)`;
      `&0 <= c * (&1 - c) - (&457 / &500) * s * s - (&83 / &100) * c * s`;
      `&0 < (a - &1) * c`] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: high_of_not_low *)
let LUC_HIGH_OF_NOT_LOW = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < c /\ abs s <= c /\ &1 < a /\
      lcont c s u v a /\
      lclosed c s u v a (&457 / &500) (&2) /\
      lclosed c s u v a (&1) (&12 / &5) /\
      ~linside c s u v a (&19 / &25) (&187 / &100) /\
      ~linside c s u v a (&33 / &20) (&33 / &20) /\
      ~linside c s u v a (&7 / &5) (&5 / &2)
      ==> linside c s u v a (&1) (&283 / &100) /\
          --s * (&19 / &25) + c * (&187 / &100) <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `u < c * (&19 / &25) + s * (&187 / &100)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&7 / &5) (&5 / &2)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LUC_LOW_OF_LOWER_U THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `--s * (&19 / &25) + c * (&187 / &100) <= v` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&19 / &25) (&187 / &100)` THEN
    UNDISCH_TAC `lclosed c s u v a (&457 / &500) (&2)` THEN
    UNDISCH_TAC `lclosed c s u v a (&1) (&12 / &5)` THEN
    UNDISCH_TAC `abs s <= c` THEN UNDISCH_TAC `&0 < c` THEN
    UNDISCH_TAC `u < c * (&19 / &25) + s * (&187 / &100)` THEN
    REWRITE_TAC[linside; lclosed; REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LUC_HIGH_UPPER_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FSAF_SP_TAC `&16 / &25` `&63 / &100` THEN
  FSAF_SP_TAC `&2 / &5` `--(&33 / &100)` THEN
  FSAF_SP_TAC `&6 / &25` `&24 / &25` THEN
  UNDISCH_THEN `~linside c s u v a (&19 / &25) (&187 / &100)` (K ALL_TAC) THEN
  UNDISCH_THEN `~linside c s u v a (&33 / &20) (&33 / &20)` (K ALL_TAC) THEN
  LUC_LIN_TAC);;

(* Lean: cover *)
let LUC_COVER = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      lcont c s u v a /\
      lclosed c s u v a (&457 / &500) (&2) /\
      lclosed c s u v a (&1) (&12 / &5) /\
      ~linside c s u v a (&19 / &25) (&187 / &100) /\
      ~linside c s u v a (&33 / &20) (&33 / &20)
      ==> linside c s u v a (&7 / &5) (&5 / &2) \/
          linside c s u v a (&1) (&283 / &100)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `linside c s u v a (&7 / &5) (&5 / &2)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  SUBGOAL_THEN `lcont c1 s1 u1 v1 a` ASSUME_TAC THENL
   [UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`]
    LUC_HIGH_OF_NOT_LOW) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;
