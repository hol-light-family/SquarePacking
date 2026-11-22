(* ========================================================================= *)
(* Port of Compact/Completion/C1092/InwardMissingProfile.lean                *)
(* (N12Compact.C1092InwardMissingProfile).  Exact physical faces of a        *)
(* negative inward square missing the center.                                *)
(* S12.short_projections is FSAF_SHORT_PROJECTIONS.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareAForced.ml";;

let C1092IMP_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092IMP_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC;;

let C1092IMP_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN REPEAT CONJ_TAC THEN C1092IMP_LIN_TAC;;

(* Lean: Profile (structure) *)
let C1092IMP_profile = new_definition
 `C1092IMP_profile (c:real) s u v a <=>
    s < &0 /\ &0 <= v /\ --(&7 / &20) * (c - s) <= u /\
    u + a <= c + (&2 / &5) * s /\ v + a <= c - (&2 / &5) * s /\
    linside c s u v a (&13 / &20) (&7 / &20) /\
    C1092WPS_half c (--s) < &2 / &5`;;

(* Lean: profile *)
let C1092IMP_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\
     ~linside c s u v a (&1) (&2 / &5) /\
     ~linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20)
     ==> C1092IMP_profile c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C1092IMP_profile] THEN
  SUBGOAL_THEN `linside c s u v a (&13 / &20) (&7 / &20) <=>
                u < c * &13 / &20 + s * &7 / &20 /\ c * &13 / &20 + s * &7 / &20 < u + a /\
                v < --s * &13 / &20 + c * &7 / &20 /\ --s * &13 / &20 + c * &7 / &20 < v + a`
    SUBST1_TAC THENL [REWRITE_TAC[linside]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  C1092IMP_SP_TAC `&7 / &10` `&7 / &10` THEN
  C1092IMP_SP_TAC `&3 / &5` `--(&3 / &5)` THEN
  C1092IMP_SP_TAC `&3 / &4` `&13 / &20` THEN
  C1092IMP_SP_TAC `&13 / &20` `&7 / &20` THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IMP_MISS_TAC [`c * &0 + s * &0`]; ALL_TAC] THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL [C1092IMP_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c + (&2 / &5) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IMP_MISS_TAC [`c * &1 + s * &2 / &5`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 / &5) * c + s < u + a` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `--(&7 / &20) * c + (&7 / &20) * s <= u` THENL
     [C1092IMP_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&7 / &20) * s + (&7 / &20) * c <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092IMP_MISS_TAC [`c * --(&7 / &20)`]; ALL_TAC] THEN
    C1092IMP_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c - (&2 / &5) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092IMP_MISS_TAC [`c * &2 / &5 + s * &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&7 / &20) * (c - s) <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&7 / &20) * s + (&7 / &20) * c <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092IMP_MISS_TAC [`c * --(&7 / &20)`]; ALL_TAC] THEN
    C1092IMP_LIN_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY C1092IMP_LIN_TAC THEN
  (* the half-angle bound *)
  REWRITE_TAC[C1092WPS_half] THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [C1092IMP_LIN_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `(&1 + c) * (c - (&2 / &5) * s - &1) =
                (--s) * ((&2 / &5) * (&1 + c) + s)` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`&1 + c`; `c - (&2 / &5) * s - &1`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092IMP_LIN_TAC; DISCH_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`--s`; `--((&2 / &5) * (&1 + c) + s)`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092IMP_LIN_TAC; DISCH_TAC] THEN
  C1092IMP_LIN_TAC);;
