(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TwoFifthsEntranceFloor.lean         *)
(* (N12Compact.C1092MMMPTwoFifthsEntrance).  The actual bottom-bar floor in  *)
(* both right-near alternatives.  OutwardScalars.increasing_projection:      *)
(* CCOS_INCREASING_PROJECTION; WallProfile.vertex / strict_closed_segment:   *)
(* OCWPVG_VERTEX / OCWPVG_STRICT_CLOSED_SEGMENT; ClosedPointExclusion.       *)
(* outside_of_closed: OUTSIDE_OF_CLOSED.  Square E is (c s u v a), the       *)
(* foreign bar owner B is (cB sB uB vB aB); apart is ldisj.  Tag C1092MTFF_.  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceNortheast.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;

(* close a goal by contradiction with the negated linside assumptions in keep:
   all other negated linside / quantified assumptions are dropped *)
let C1092MTFF_KEEP_TAC keep =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let t = concl th in
    if is_forall t || is_imp t || (is_neg t && can (find_term ((=) `linside`)) t &&
       not (mem t keep)) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let C1092MTFF_STEP t keep =
  SUBGOAL_THEN t ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN C1092MTFF_KEEP_TAC keep; ALL_TAC];;

(* Lean: southeast_caps *)
let C1092MTFF_SOUTHEAST_CAPS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&0) (--(&13 / &50)) /\ linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\ ~linside c s u v a (&1) (--(&13 / &50))
     ==> v + a <= &0 /\ u + a <= c - (&13 / &50) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MTFF_STEP `v + a <= &0` [`~linside c s u v a (&0) (&0)`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&13 / &50`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092MTFF_STEP `u + a <= c - (&13 / &50) * s` [`~linside c s u v a (&1) (--(&13 / &50))`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: southeast_outer_cap *)
let C1092MTFF_SOUTHEAST_OUTER_CAP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ &0 < s /\ s <= c /\
     linside c s u v a (&0) (--(&13 / &50)) /\ linside c s u v a (&13 / &50) (&0) /\
     linside c s u v a (&1) (--(&2 / &5)) /\
     ~linside c s u v a (&47 / &100) (&3 / &25)
     ==> v + a <= (&3 / &25) * c - (&47 / &100) * s /\ s < &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MTFF_STEP `v + a <= (&3 / &25) * c - (&47 / &100) * s`
    [`~linside c s u v a (&47 / &100) (&3 / &25)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&7 * s < &4 * c` ASSUME_TAC THENL
   [UNDISCH_TAC `linside c s u v a (&13 / &50) (&0)` THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 < (&4 * c - &7 * s) * (&4 * c + &7 * s)`;
    `&0 <= (s - &1 / &2) * (s + &1 / &2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: vertex_above_bar (private) *)
let C1092MTFF_VERTEX_ABOVE_BAR = prove
 (`forall c s u v a cB sB uB vB aB X Y.
     c * c + s * s = &1 /\ &0 < a /\
     lclosed c s u v a X Y /\ linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     &0 <= X /\ X <= &2 / &5 /\
     (forall x. &0 <= x ==> x <= &2 / &5 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj c s u v a cB sB uB vB aB
     ==> --(&1) < Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ASM_CASES_TAC `Y = --(&1)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `X:real`; `--(&1)`]
      OUTSIDE_OF_CLOSED) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ldisj c s u v a cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y < --(&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(Y = --(&1))` THEN UNDISCH_TAC `Y <= --(&1)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = (--(&1) - Y) / (--(&7 / &20) - Y)` THEN
  SUBGOAL_THEN `&0 < --(&7 / &20) - Y` ASSUME_TAC THENL
   [UNDISCH_TAC `Y < --(&1)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * (--(&7 / &20) - Y) = --(&1) - Y` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    UNDISCH_TAC `&0 < --(&7 / &20) - Y` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV; ASM_SIMP_TAC[REAL_LT_LDIV_EQ]] THEN
    UNDISCH_TAC `Y < --(&1)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) * Y + t * --(&7 / &20) = --(&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `t * (--(&7 / &20) - Y) = --(&1) - Y` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `X:real`; `Y:real`;
                `&7 / &20`; `--(&7 / &20)`; `t:real`] OCWPVG_STRICT_CLOSED_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - t) * X + t * &7 / &20` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  ANTS_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `ldisj c s u v a cB sB uB vB aB` THEN
  REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`(&1 - t) * X + t * &7 / &20`; `--(&1)`]) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: southeast_floor *)
let C1092MTFF_SOUTHEAST_FLOOR = prove
 (`forall c s u v a cB sB uB vB aB.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\ s < &1 / &2 /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&0) (--(&13 / &50)) /\ linside c s u v a (&13 / &50) (&0) /\
     v + a <= &0 /\ u + a <= c - (&13 / &50) * s /\
     (forall x. &0 <= x ==> x <= &2 / &5 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj c s u v a cB sB uB vB aB
     ==> a * (c + s) - &1 < s * (u + a) + c * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  NLIN_FACTS_TAC []
   [`&0 < (&1 / &2 - s) * (&1 / &2 + s)`; `&4 / &5 < c`] THEN
  SUBGOAL_THEN `--s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `ldisj c s u v a cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `--(&1)`]) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`linside c s u v a (&0) (--(&13 / &50))`; `u < --s`; `v + a <= &0`;
        `&1 < a`; `c <= &1`; `&0 < c`; `&0 < s`] THEN
      REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (is_forall o concl)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u:real`; `v:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `linside c s u v a (&13 / &50) (&0) /\ linside c s u v a (&0) (--(&13 / &50))`
    MP_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[linside] THEN STRIP_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= c * (u - --s)`; `&0 <= s * (--a - v)`; `&0 < s * (a - c)`;
    `&0 < c * u - s * v`;
    `&0 <= c * ((c - (&13 / &50) * s) - (u + a))`;
    `&0 < s * (v + a + (&13 / &50) * s)`;
    `&0 < (a - &1) * (c - s)`;
    `c * u - s * v < &1 - (&37 / &50) * s pow 2 - (&13 / &50) * c * s + s - c`;
    `&0 <= (c - &4 / &5) * (&1 - c)`;
    `&1 - c <= (&5 / &9) * s pow 2`;
    `&0 <= (&1 + (&13 / &50) * s) * ((&5 / &9) * s pow 2 - (&1 - c))`;
    `&0 <= s pow 2 * (&1 / &2 - s)`;
    `c * u - s * v < &2 / &5`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `c * u - s * v`; `s * u + c * v`] C1092MTFF_VERTEX_ABOVE_BAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN RASM_ARITH_TAC;
    DISCH_TAC THEN RASM_ARITH_TAC]);;

(* Lean: southeast_outer_small *)
let C1092MTFF_SOUTHEAST_OUTER_SMALL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\
     u + a <= c - (&13 / &50) * s /\
     v + a <= (&3 / &25) * c - (&47 / &100) * s /\
     a * (c + s) - &1 < s * (u + a) + c * (v + a)
     ==> &3 * s < c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= s * ((c - (&13 / &50) * s) - (u + a))`;
    `&0 <= c * (((&3 / &25) * c - (&47 / &100) * s) - (v + a))`;
    `&0 < (a - &1) * (c + s)`;
    `c + s - &1 - (&53 / &100) * c * s - (&3 / &25) * c pow 2 + (&13 / &50) * s pow 2 < &0`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&7 / &25 <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`c < &21 / &25`; `&0 < (&7 / &25 - s) * (&7 / &25 + s)`;
      `&0 < (&21 / &25 - c) * (&21 / &25 + c)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (s - &7 / &25) * (s + &7 / &25)`] THEN
  SUBGOAL_THEN `c <= &24 / &25` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 < (c - &24 / &25) * (c + &24 / &25)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (s - &7 / &25) * (c + &24 / &25 - s - &7 / &25)`;
    `&0 <= (c + s - &31 / &25) * (c + &24 / &25)`;
    `&31 / &25 <= c + s`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s:real`] [`c + s <= &3 / &2`] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c + s - &31 / &25) * (&1 - (&53 / &200) * (c + s + &31 / &25))`] THEN
  SUBGOAL_THEN
   `c + s - &1 - (&53 / &100) * c * s - (&3 / &25) * c pow 2 + (&13 / &50) * s pow 2 =
    &916 / &125000 + (c + s - &31 / &25) * (&1 - (&53 / &200) * (c + s + &31 / &25)) +
      (&19 / &50) * (s pow 2 - (&7 / &25) pow 2)`
    ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;
