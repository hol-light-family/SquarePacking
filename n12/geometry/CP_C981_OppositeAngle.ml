(* ========================================================================= *)
(* Port of Compact/Completion/C981/OppositeAngle.lean                         *)
(* (N12Compact.C981CompletionOppositeAngle).  The positive-central angle     *)
(* reduction used in the final C981 cycles.  Square C is c s u v a (with     *)
(* s = r), square A is cA sA uA vA aA.  upper / lower are ABT_upper /        *)
(* ABT_lower; Normal is c977cc_normal; OppositeOffset.bounds is              *)
(* C981OO_BOUNDS; OppositeSupport.large_bounds / floor_upper / wall_upper    *)
(* are C981OS_*; short_projections is WFP_SHORT_PROJECTIONS.  The coordinate *)
(* walls of left_support / bottom_support are obtained from                  *)
(* DerivedWalls (OCDW_VERTICAL_RIGHT, OCDW_CLOSED_AFFINE_BOUND) and          *)
(* WallProfile.vertex (OCWPVG_VERTEX).  Tag C981OPA_.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_OppositeOffset.ml";;
needs "n12/geometry/CP_C981_OppositeSupport.ml";;
needs "n12/geometry/CP_OtherCases_DerivedWalls.ml";;
needs "n12/geometry/ABTransverse.ml";;

let C981OPA_LIN_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C981OPA_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside; TAUT `(~p ==> false) <=> p`] THEN
  REPEAT CONJ_TAC THEN C981OPA_LIN_TAC;;

let C981OPA_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC]) tms;;

let C981OPA_SEG_TAC y =
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) y)) (concl th) then
    MP_TAC(SPEC y th) else NO_TAC);;

(* Lean: positive_axes (private) *)
let C981OPA_POSITIVE_AXES = prove
 (`forall c s u v a cA sA uA vA aA r.
     c * c + s * s = &1 /\ &0 < a /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     s = r /\ c977cc_normal c r /\ &0 < cA /\ &0 <= sA /\ a = aA /\
     linside c s u v a (&0) (&0) /\
     linside cA sA uA vA aA (&0) (&13 / &50) /\ linside cA sA uA vA aA (&13 / &50) (&0) /\
     ldisj c s u v a cA sA uA vA aA
     ==> u + a <= ABT_lower cA sA uA vA aA c r \/
         ABT_upper c s u v a cA sA <= uA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aA`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  ABT_OWN_TAC [`c:real`; `r:real`; `u:real`; `v:real`; `a:real`] THEN
  ABT_OWN_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `a:real`] THEN
  MP_TAC(SPECL [`c:real`; `r:real`; `u:real`; `v:real`; `a:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `a:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABT_ALL_SB_TAC
   [[`c:real`; `r:real`; `u:real`; `v:real`; `a:real`], (`&0`, `&0`);
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `a:real`], (`&0`, `&13 / &50`);
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `a:real`], (`&13 / &50`, `&0`)]
   [`c:real`, `r:real`; `--r:real`, `c:real`; `cA:real`, `sA:real`; `--sA:real`, `cA:real`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ABT_ARITH_TAC);;

(* Lean: lower_offset (private) *)
let C981OPA_LOWER_OFFSET = prove
 (`forall cA sA uA vA aA d r.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     &0 < cA /\ &0 <= sA /\ &0 < d /\ &0 <= r /\ d pow 2 + r pow 2 = &1 /\ &0 <= uA /\
     linside cA sA uA vA aA (&0) (&13 / &50) /\ linside cA sA uA vA aA (&13 / &50) (&0)
     ==> ABT_lower cA sA uA vA aA d r <= uA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cA sA uA vA aA (&0) (&13 / &50)`; `linside cA sA uA vA aA (&13 / &50) (&0)`] THEN
  C981OPA_PROD_TAC [`&0 < cA * d`; `&0 <= sA * r`] THEN
  SUBGOAL_THEN `(cA * d + sA * r) pow 2 + (sA * d - cA * r) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN UNDISCH_TAC `cA * cA + sA * sA = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `cA * d + sA * r <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `sA * d - cA * r` REAL_LE_POW_2) THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (cA * d + sA * r - &1) * (cA * d + sA * r + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C981OPA_PROD_TAC [`&0 <= (&1 - (cA * d + sA * r)) * uA`] THEN
  REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(d * cA + r * sA) = cA * d + sA * r` SUBST1_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sA * d - cA * r` THENL
   [SUBGOAL_THEN `abs(--d * sA + r * cA) = sA * d - cA * r` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    C981OPA_PROD_TAC [`&0 <= (sA * d - cA * r) * (vA + aA)`] THEN RASM_ARITH_TAC;
    SUBGOAL_THEN `abs(--d * sA + r * cA) = --(sA * d - cA * r)` SUBST1_TAC THENL
     [RASM_ARITH_TAC; ALL_TAC] THEN
    C981OPA_PROD_TAC [`&0 <= --(sA * d - cA * r) * --vA`] THEN RASM_ARITH_TAC]);;

(* Lean: left_support (private) *)
let C981OPA_LEFT_SUPPORT = prove
 (`forall c s u v a r.
     c * c + s * s = &1 /\ &0 < a /\ s = r /\ linside c s u v a (&0) (&0) /\
     (forall y. ~linside c s u v a (--(&1)) y)
     ==> --(&1) <= c * u - r * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `&0`; `&0`; `--(&1)`] OCDW_VERTICAL_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u:real`; `v + a`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1`; `&0`; `--(&1)`;
                `&0`; `&0`; `c * u - s * (v + a)`; `s * u + c * (v + a)`]
    OCDW_CLOSED_AFFINE_BOUND) THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = r`)) THEN
  DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: bottom_support (private) *)
let C981OPA_BOTTOM_SUPPORT = prove
 (`forall c s u v a r.
     c * c + s * s = &1 /\ &0 < a /\ s = r /\ linside c s u v a (&0) (&0) /\
     (forall x. ~linside c s u v a x (--(&1)))
     ==> --(&1) <= r * u + c * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`;
                `&0`; `&0`; `--(&1)`] OCDW_VERTICAL_RIGHT) THEN
  ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u:real`; `v:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&0`; `&1`; `--(&1)`;
                `&0`; `&0`; `c * u - s * v`; `s * u + c * v`]
    OCDW_CLOSED_AFFINE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_LID] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real`; `x:real`] o check (fun th ->
      is_forall(concl th) && is_imp(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = r`)) THEN
    REAL_ARITH_TAC]);;

let C981OPA_SEGPT_TAC y pt =
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) y)) (concl th) then
    MP_TAC(SPEC pt th) else NO_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[linside; TAUT `(~p ==> false) <=> p`] THEN
  REPEAT CONJ_TAC THEN C981OPA_LIN_TAC;;

(* Lean: bound *)
let C981OPA_BOUND = prove
 (`forall c s u v a cA sA uA vA aA r.
     c * c + s * s = &1 /\ &0 < a /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     s = r /\ c977cc_normal c r /\ &1 < a /\ a <= &1001 / &1000 /\ a = aA /\
     &0 < cA /\ &0 <= sA /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (--(&1 / &2)) (&0) /\
     linside c s u v a (&0) (--(&1 / &2)) /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     ~linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     (forall x. --(&4 / &5) <= x ==> x <= --(&13 / &50) ==> ~linside c s u v a x (--(&1))) /\
     (forall y. --(&14 / &25) <= y ==> y <= &0 ==> ~linside c s u v a (--(&1)) y) /\
     linside cA sA uA vA aA (&0) (&13 / &50) /\ linside cA sA uA vA aA (&13 / &50) (&0) /\
     linside cA sA uA vA aA (&7 / &20) (&7 / &20) /\
     ~linside cA sA uA vA aA (&0) (&0) /\ ~linside cA sA uA vA aA (&13 / &50) (&1) /\
     (forall y. &13 / &50 <= y ==> y <= &4 / &5 ==> ~linside cA sA uA vA aA (&1) y) /\
     ldisj c s u v a cA sA uA vA aA
     ==> r < &8 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `r:real`]
    C981OPA_POSITIVE_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] C981OO_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMP_CONJ] THEN C981OPA_LIN_TAC;
    STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c r`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c r`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `c:real`; `r:real`]
    C981OPA_LOWER_OFFSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C981OPA_LIN_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aA`)) THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c r u v a (&0) (&0)`; `linside c r u v a (--(&1 / &2)) (&0)`;
    `linside c r u v a (&0) (--(&1 / &2))`;
    `linside c r u v a (--(&7 / &20)) (--(&7 / &20))`] THEN
  MP_TAC(SPECL [`c:real`; `r:real`; `&7 / &10`; `&7 / &10`] WFP_SHORT_PROJECTIONS) THEN
  MP_TAC(SPECL [`c:real`; `r:real`; `&61 / &100`; `&13 / &20`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v + a <= (&7 / &20) * (c + r)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C981OPA_MISS_TAC `~linside c r u v a (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&7 / &20) * (c - r)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C981OPA_MISS_TAC `~linside c r u v a (&7 / &20) (--(&7 / &20))`; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `u < --(&13 / &50) * c - r` ASSUME_TAC THENL [C981OPA_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&13 / &50) * r - c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C981OPA_SEGPT_TAC `--(&4 / &5)` `--(&13 / &50)`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&4 / &5) * c - r <= u \/ (&4 / &5) * r - c <= v` ASSUME_TAC THENL
   [ASM_CASES_TAC `--(&4 / &5) * c - r <= u` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C981OPA_SEGPT_TAC `--(&4 / &5)` `--(&4 / &5)`; ALL_TAC] THEN
  (* the bottom wall *)
  SUBGOAL_THEN `--(&1) <= r * u + c * v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `&4 / &5`)) (concl th))) THENL
     [MATCH_MP_TAC C981OPA_BOTTOM_SUPPORT THEN
      MAP_EVERY EXISTS_TAC [`r:real`; `a:real`] THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      MP_TAC(ASSUME `linside c r u v a x (--(&1))`) THEN REWRITE_TAC[linside] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `--(&4 / &5) < x /\ x < --(&13 / &50)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
         [C981OPA_PROD_TAC [`&0 <= c * (--(&4 / &5) - x)`];
          C981OPA_PROD_TAC [`&0 <= r * (x - --(&13 / &50))`]] THEN
        C981OPA_LIN_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `--(&4 / &5)`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      SUBGOAL_THEN `a < r + (&4 / &5) * c` ASSUME_TAC THENL
       [ASM_CASES_TAC `&9 / &20 <= r` THENL [C981OPA_LIN_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&89 / &100 <= c` ASSUME_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          C981OPA_PROD_TAC [`&0 <= (&9 / &20 - r) * (&9 / &20 + r)`;
                            `&0 < (&89 / &100 - c) * (&89 / &100 + c)`] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C981OPA_LIN_TAC; ALL_TAC] THEN
        C981OPA_LIN_TAC; ALL_TAC] THEN
      C981OPA_PROD_TAC [`&0 < r * (u + a)`; `&0 <= c * (v - ((&4 / &5) * r - c))`;
                        `&0 < r * ((r + (&4 / &5) * c) - a)`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C981OPA_LIN_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--c - (&14 / &25) * r <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C981OPA_SEGPT_TAC `--(&14 / &25)` `--(&14 / &25)`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `r:real`] C981OS_LARGE_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the left wall *)
  SUBGOAL_THEN `--(&1) <= c * u - r * (v + a)` ASSUME_TAC THENL
   [SUBGOAL_THEN `u < --c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `uA:real`)) (concl th))) THENL
       [C981OPA_LIN_TAC;
        MP_TAC(SPECL [`c:real`; `r:real`; `u:real`; `v:real`; `a:real`; `r:real`;
                      `cA:real`; `sA:real`] C981OS_FLOOR_UPPER) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[REAL_POW_2] THEN C981OPA_LIN_TAC; DISCH_TAC] THEN
        C981OPA_LIN_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `v + a <= r` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C981OPA_SEGPT_TAC `--(&14 / &25)` `&0`; ALL_TAC] THEN
    MATCH_MP_TAC C981OPA_LEFT_SUPPORT THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    MP_TAC(ASSUME `linside c r u v a (--(&1)) y`) THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
    SUBGOAL_THEN `--(&14 / &25) < y /\ y < &0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
       [C981OPA_PROD_TAC [`&0 <= r * (--(&14 / &25) - y)`];
        C981OPA_PROD_TAC [`&0 <= c * y`]] THEN
      C981OPA_LIN_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `--(&14 / &25)`)) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `uA:real`)) (concl th))) THENL
   [MP_TAC(SPECL [`c:real`; `r:real`; `u:real`; `v:real`; `a:real`; `r:real`;
                  `c:real`; `r:real`] C981OS_WALL_UPPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C981OPA_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`c:real`; `r:real`; `u:real`; `v:real`; `a:real`] ABT_OWNU) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C981OPA_LIN_TAC;
    MP_TAC(SPECL [`c:real`; `r:real`; `u:real`; `v:real`; `a:real`; `r:real`;
                  `cA:real`; `sA:real`] C981OS_WALL_UPPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C981OPA_LIN_TAC; DISCH_TAC] THEN
    C981OPA_LIN_TAC]);;
