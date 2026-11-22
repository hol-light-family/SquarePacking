(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShortRows/CoreSqueeze.lean                 *)
(* (N12Compact.C981CompletionShortSqueeze).  A central four-diamond owner A  *)
(* and its actual southeast neighbour B.  ClosedInside is lclosed;           *)
(* short_projections is WFP_SHORT_PROJECTIONS.  alpha, beta, gamma of the    *)
(* Lean proofs are written out.                                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_ShortRows_CoreScalars.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C981SQ_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C981SQ_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC];
   ALL_TAC];;

(* Lean: corner (private) *)
let C981SQ_CORNER = prove
 (`forall c s u v a U V. c * c + s * s = &1 /\
     (u <= U /\ U <= u + a) /\ (v <= V /\ V <= v + a)
     ==> lclosed c s u v a (c * U - s * V) (s * U + c * V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lclosed] THEN
  SUBGOAL_THEN `c * (c * U - s * V) + s * (s * U + c * V) = U /\
                --s * (c * U - s * V) + c * (s * U + c * V) = V` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: project_upper (private) *)
let C981SQ_PROJECT_UPPER = prove
 (`forall c s u v a nx ny U V. c * c + s * s = &1 /\ &0 < a /\
     (u <= U /\ U <= u + a) /\ (v <= V /\ V <= v + a)
     ==> (nx * c + ny * s) * U + (--nx * s + ny * c) * V <= ABT_upper c s u v a nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c * U - s * V`; `s * U + c * V`; `nx:real`; `ny:real`] ABT_CLOSED_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C981SQ_CORNER THEN
                  ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* Lean: project_lower (private) *)
let C981SQ_PROJECT_LOWER = prove
 (`forall c s u v a nx ny U V. c * c + s * s = &1 /\ &0 < a /\
     (u <= U /\ U <= u + a) /\ (v <= V /\ V <= v + a)
     ==> ABT_lower c s u v a nx ny <= (nx * c + ny * s) * U + (--nx * s + ny * c) * V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `c * U - s * V`; `s * U + c * V`; `nx:real`; `ny:real`] ABT_CLOSED_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C981SQ_CORNER THEN
                  ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* Lean: core_faces *)
let C981SQ_CORE_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
     linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> c981sr_core c s /\
         (&33 / &20) * c + (&47 / &20) * s <= u /\
         (&33 / &20) * c - (&47 / &20) * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&7 / &10`; `&7 / &10`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  C981SR_NORMAL_TAC THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&87 / &50) (&2)` THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&2) (&87 / &50)` THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&47 / &20) (&47 / &20)` THEN
  SUBGOAL_THEN `(&33 / &20) * c - (&47 / &20) * s <= v` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&47 / &20) (&33 / &20)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&33 / &20) * c + (&47 / &20) * s <= u` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&33 / &20) (&47 / &20)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C981SR_CORE_BOUNDS THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: coefficient_positive (private) *)
let C981SQ_COEFFICIENT_POSITIVE = prove
 (`forall c s b t. c981sr_core c s /\ &0 < b /\ --b <= t ==> &0 < c * b + s * t`,
  REPEAT STRIP_TAC THEN C981SR_CORE_TAC THEN
  C981SQ_PROD `&0 <= s * (t + b)` THEN C981SQ_PROD `&0 < b * (c - s)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: corner_faces (private) *)
let C981SQ_CORNER_FACES = prove
 (`forall c s u v a. &0 < c /\ abs s <= c /\
     linside c s u v a (&47 / &20) (&33 / &20) /\ linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&3) (&1)
     ==> u + a <= &3 * c + s \/ c - &3 * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&3) (&87 / &50)` THEN
  UNDISCH_TAC `~linside c s u v a (&3) (&1)` THEN UNDISCH_TAC `abs s <= c` THEN
  REWRITE_TAC[linside; REAL_ABS_BOUNDS] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  RASM_ARITH_TAC);;

(* Lean: positive_corner_low (private) *)
let C981SQ_POSITIVE_CORNER_LOW = prove
 (`forall c s u v a. &0 <= s /\ linside c s u v a (&3) (&87 / &50) /\
     (u + a <= &3 * c + s \/ c - &3 * s <= v)
     ==> c - &3 * s <= v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: advanced_faces (private) *)
let C981SQ_ADVANCED_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < c /\ abs s <= c /\
     linside c s u v a (&47 / &20) (&33 / &20) /\ linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&14 / &5) (&1) /\
     s <= &0 /\ --s < (&10 / &37) * c /\ u + a <= &3 * c + s /\ &1 < a
     ==> c - (&14 / &5) * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&3) (&87 / &50)` THEN
  UNDISCH_TAC `~linside c s u v a (&14 / &5) (&1)` THEN UNDISCH_TAC `abs s <= c` THEN
  REWRITE_TAC[linside; REAL_ABS_BOUNDS] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  RASM_ARITH_TAC);;

(* Lean: positive_advanced_modes (private) *)
let C981SQ_POSITIVE_ADVANCED_MODES = prove
 (`forall c s u v a. &0 < c /\ &0 <= s /\
     linside c s u v a (&47 / &20) (&33 / &20) /\ linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&14 / &5) (&1)
     ==> (&14 / &5) * c + s <= u \/ c - (&14 / &5) * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
  C981SQ_UNFOLD_TAC `linside c s u v a (&3) (&87 / &50)` THEN
  UNDISCH_TAC `~linside c s u v a (&14 / &5) (&1)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* one separating-axis case of `axes` *)
let C981SQ_CASE_TAC nx ny swap radius points =
  let sep = SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                   `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aA:real`; nx; ny]
                  ABT_SEPARATED in
  let sb (sq,(x,y)) =
    let c,s,u,v = sq in
    MP_TAC(SPECL [c; s; u; v; `aA:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  MP_TAC sep THEN ANTS_TAC THENL
  [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
    else ALL_TAC) THEN
   MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY sb points THEN DISCH_THEN DISJ_CASES_TAC THEN RASM_ARITH_TAC;;

(* Lean: axes (private) *)
let C981SQ_AXES = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aA /\ aA = aB /\ c977cc_normal cA sA /\ &0 < cB /\ abs sB <= cB /\
     (&33 / &20) * cA + (&47 / &20) * sA <= uA /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> ABT_upper cB sB uB vB aB (--sA) cA <= vA \/
         (sB <= &0 /\ ABT_upper cA sA uA vA aA cB sB <= uB) \/
         vB + aB <= ABT_lower cA sA uA vA aA (--sB) cB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aB`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `&7 / &10`; `--(&7 / &10)`] WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  C981SR_NORMAL_TAC THEN
  UNDISCH_TAC `abs sB <= cB` THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aA:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aA:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aA:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let qA = (`cA:real`,`sA:real`,`uA:real`,`vA:real`)
  and qB = (`cB:real`,`sB:real`,`uB:real`,`vB:real`) in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [C981SQ_CASE_TAC `cA:real` `sA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cB:real`; `sB:real`; `aA:real`]
       ABT_PARALLEL_RADIUS)
     [qA,(`&2`,`&87 / &50`); qB,(`&47 / &20`,`&33 / &20`)];
   C981SQ_CASE_TAC `--sA:real` `cA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cB:real`; `sB:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)
     [qA,(`&47 / &20`,`&47 / &20`); qB,(`&47 / &20`,`&33 / &20`)];
   C981SQ_CASE_TAC `cB:real` `sB:real` true
     (SPECL [`cB:real`; `sB:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_PARALLEL_RADIUS)
     [qA,(`&47 / &20`,`&47 / &20`); qA,(`&2`,`&87 / &50`); qB,(`&47 / &20`,`&33 / &20`)];
   C981SQ_CASE_TAC `--sB:real` `cB:real` true
     (SPECL [`cB:real`; `sB:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)
     [qA,(`&47 / &20`,`&47 / &20`); qB,(`&47 / &20`,`&33 / &20`)]]);;

(* Lean: backward_impossible (private) *)
let C981SQ_BACKWARD_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aA /\ c981sr_core cA sA /\ &0 < cB /\ abs sB <= cB /\ sB <= &0 /\
     (&33 / &20) * cA + (&47 / &20) * sA <= uA /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     ABT_upper cA sA uA vA aA cB sB <= uB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `abs sB <= cB` THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] C981SR_BACKWARD_U) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] C981SQ_COEFFICIENT_POSITIVE) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `cB:real`; `sB:real`;
                `uA + aA`; `vA:real`] C981SQ_PROJECT_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C981SR_CORE_TAC THEN
  C981SQ_UNFOLD_TAC `linside cA sA uA vA aA (&2) (&87 / &50)` THEN
  C981SQ_UNFOLD_TAC `linside cB sB uB vB aB (&47 / &20) (&33 / &20)` THEN
  SUBGOAL_THEN `--cB * sA + sB * cA <= &0` ASSUME_TAC THENL
  [C981SQ_PROD `&0 <= cA * --sB` THEN C981SQ_PROD `&0 <= sA * cB` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981SQ_PROD `&0 <= (cB * cA + sB * sA) * ((uA + aA) - ((&33 / &20) * cA + (&47 / &20) * sA + &1))` THEN
  C981SQ_PROD `&0 <= --(--cB * sA + sB * cA) * (((&87 / &50) * cA - &2 * sA) - vA)` THEN
  SUBGOAL_THEN
   `(cB * cA + sB * sA) * ((&33 / &20) * cA + (&47 / &20) * sA + &1) +
    (--cB * sA + sB * cA) * ((&87 / &50) * cA - &2 * sA) -
    ((&47 / &20) * cB + (&33 / &20) * sB) =
    cB * (cA - &7 / &10 + (&7 / &20) * sA pow 2 + (&61 / &100) * cA * sA) +
    sB * (sA + &9 / &100 + (&61 / &100) * sA pow 2 - (&7 / &20) * cA * sA)` MP_TAC THENL
  [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: own_v_impossible (private) *)
let C981SQ_OWN_V_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aB /\ &1 < aA /\ c981sr_core cA sA /\ &0 < cB /\ abs sB <= cB /\
     (&33 / &20) * cA + (&47 / &20) * sA <= uA /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     ~linside cB sB uB vB aB (&3) (&1) /\
     ~linside cB sB uB vB aB (&14 / &5) (&1) /\
     vB + aB <= ABT_lower cA sA uA vA aA (--sB) cB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C981SQ_CORNER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `&2`; `&87 / &50`;
                `--sB:real`; `cB:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `cB <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `sB:real`; SQ_NONNEG `cB - &1`]; ALL_TAC] THEN
  C981SR_CORE_TAC THEN
  UNDISCH_TAC `abs sB <= cB` THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  C981SQ_UNFOLD_TAC `linside cA sA uA vA aA (&2) (&87 / &50)` THEN
  C981SQ_UNFOLD_TAC `linside cB sB uB vB aB (&3) (&87 / &50)` THEN
  ASM_CASES_TAC `&0 <= sB` THENL
  [SUBGOAL_THEN `cB - &3 * sB <= vB` ASSUME_TAC THENL
   [MATCH_MP_TAC C981SQ_POSITIVE_CORNER_LOW THEN
    MAP_EVERY EXISTS_TAC [`uB:real`; `aB:real`] THEN ASM_REWRITE_TAC[linside] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `&0 <= sA * cB - cA * sB` THENL
   [SUBGOAL_THEN `sB <= (&9 / &35) * cB` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C981SQ_PROD `&0 <= cB * ((&9 / &35) * cA - sA)` THEN
     C981SQ_PROD `&0 < cA * (sB - (&9 / &35) * cB)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] C981SR_POSITIVE_OWN_V) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[c981sr_core; c977cc_normal; REAL_POW_2] THEN
                    ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `--sB:real`; `cB:real`;
                  `uA + aA`; `vA:real`] C981SQ_PROJECT_LOWER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] C981SQ_COEFFICIENT_POSITIVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[c981sr_core] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    C981SQ_PROD `&0 <= --(sA * cB - cA * sB) * ((uA + aA) - ((&33 / &20) * cA + (&47 / &20) * sA + &1))` THEN
    C981SQ_PROD `&0 <= (cA * cB + sA * sB) * (((&87 / &50) * cA - &2 * sA) - vA)` THEN
    SUBGOAL_THEN
     `(sA * cB - cA * sB) * ((&33 / &20) * cA + (&47 / &20) * sA + &1) +
      (cA * cB + sA * sB) * ((&87 / &50) * cA - &2 * sA) - (cB - &3 * sB) =
      cB * (&37 / &50 + (&61 / &100) * sA pow 2 - (&7 / &20) * cA * sA + sA) +
      sB * (&27 / &20 - (&7 / &20) * sA pow 2 - (&61 / &100) * cA * sA - cA)` MP_TAC THENL
    [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC];
   MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] ABT_OWNV) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
   MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `&47 / &20`;
                 `&33 / &20`; `--sB:real`; `cB:real`] ABT_STRICT_BOUNDS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
   SUBGOAL_THEN `--sB < (&9 / &35) * cB` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
     can (find_term ((=) `uB:real`)) (concl th))) THENL
   [MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C981SQ_ADVANCED_FACES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_BOUNDS] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    RASM_ARITH_TAC;
    RASM_ARITH_TAC]]);;

(* Lean: a_v_impossible (private) *)
let C981SQ_A_V_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aB /\ c981sr_core cA sA /\ &0 < cB /\ abs sB <= cB /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     ~linside cB sB uB vB aB (&3) (&1) /\
     ~linside cB sB uB vB aB (&14 / &5) (&1) /\
     ABT_upper cB sB uB vB aB (--sA) cA <= vA
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C981SQ_CORNER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] C981SQ_COEFFICIENT_POSITIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `--sA:real`; `cA:real`;
                `uB:real`; `vB + aB`] C981SQ_PROJECT_UPPER) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `--sA:real`; `cA:real`;
                `uB + aB`; `vB + aB`] C981SQ_PROJECT_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `cB <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `sB:real`; SQ_NONNEG `cB - &1`]; ALL_TAC] THEN
  C981SR_CORE_TAC THEN
  UNDISCH_TAC `abs sB <= cB` THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  C981SQ_UNFOLD_TAC `linside cA sA uA vA aA (&2) (&87 / &50)` THEN
  C981SQ_UNFOLD_TAC `linside cB sB uB vB aB (&47 / &20) (&33 / &20)` THEN
  C981SQ_UNFOLD_TAC `linside cB sB uB vB aB (&3) (&87 / &50)` THEN
  SUBGOAL_THEN
   `cA * sB - sA * cB <= &0 /\ cB - (&14 / &5) * sB <= vB /\
    &0 < (cA * sB - sA * cB) * ((&47 / &20) * cB + (&33 / &20) * sB) +
         (cA * cB + sA * sB) * (cB - (&14 / &5) * sB + &1) - ((&87 / &50) * cA - &2 * sA)
    ==> false` ASSUME_TAC THENL
  [STRIP_TAC THEN
   C981SQ_PROD `&0 <= --(cA * sB - sA * cB) * (((&47 / &20) * cB + (&33 / &20) * sB) - uB)` THEN
   C981SQ_PROD `&0 <= (cA * cB + sA * sB) * ((vB + aB) - (cB - (&14 / &5) * sB + &1))` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sB` THENL
  [SUBGOAL_THEN `cB - &3 * sB <= vB` ASSUME_TAC THENL
   [MATCH_MP_TAC C981SQ_POSITIVE_CORNER_LOW THEN
    MAP_EVERY EXISTS_TAC [`uB:real`; `aB:real`] THEN ASM_REWRITE_TAC[linside] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c977cc_normal cB sB` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; ALL_TAC] THEN
   ASM_CASES_TAC `cA * sB - sA * cB <= &0` THENL
   [SUBGOAL_THEN `sB <= &13 / &50` ASSUME_TAC THENL
    [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C981SQ_PROD `&0 <= cB * ((&9 / &35) * cA - sA)` THEN
     C981SQ_PROD `&0 < cA * (sB - (&9 / &35) * cB)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] C981SR_POSITIVE_SMALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[c981sr_core] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    C981SQ_PROD `&0 <= --(cA * sB - sA * cB) * (((&47 / &20) * cB + (&33 / &20) * sB) - uB)` THEN
    C981SQ_PROD `&0 <= (cA * cB + sA * sB) * ((vB + aB) - (cB - &3 * sB + &1))` THEN
    SUBGOAL_THEN
     `(cA * sB - sA * cB) * ((&47 / &20) * cB + (&33 / &20) * sB) +
      (cA * cB + sA * sB) * (cB - &3 * sB + &1) - ((&87 / &50) * cA - &2 * sA) =
      cA * (cB - &37 / &50 + (&13 / &20) * sB pow 2 - (&13 / &20) * cB * sB) +
      sA * (--(&7 / &20) - (&13 / &20) * sB pow 2 - (&13 / &20) * cB * sB + sB)` MP_TAC THENL
    [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
      C981SQ_POSITIVE_ADVANCED_MODES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
    [MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] C981SR_POSITIVE_LOWER_U) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[c981sr_core] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
     C981SQ_PROD `&0 <= (cA * sB - sA * cB) * ((uB + aB) - ((&14 / &5) * cB + sB + &1))` THEN
     C981SQ_PROD `&0 <= (cA * cB + sA * sB) * ((vB + aB) - (cB - &3 * sB + &1))` THEN
     SUBGOAL_THEN
      `(cA * sB - sA * cB) * ((&14 / &5) * cB + sB + &1) +
       (cA * cB + sA * sB) * (cB - &3 * sB + &1) - ((&87 / &50) * cA - &2 * sA) =
       cA * (cB + sB - &37 / &50 - (&1 / &5) * cB * sB) +
       sA * (--(&4 / &5) - (&1 / &5) * sB pow 2 - cB + sB)` MP_TAC THENL
     [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     RASM_ARITH_TAC;
     MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `sB:real`] C981SR_POSITIVE_LOW) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[c981sr_core] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
     C981SQ_PROD `&0 <= (cA * sB - sA * cB) * ((uB + aB) - ((&47 / &20) * cB + (&33 / &20) * sB))` THEN
     C981SQ_PROD `&0 <= (cA * cB + sA * sB) * ((vB + aB) - (cB - (&14 / &5) * sB + &1))` THEN
     SUBGOAL_THEN
      `(cA * sB - sA * cB) * ((&47 / &20) * cB + (&33 / &20) * sB) +
       (cA * cB + sA * sB) * (cB - (&14 / &5) * sB + &1) - ((&87 / &50) * cA - &2 * sA) =
       cA * (cB - &37 / &50 + (&13 / &20) * sB pow 2 - (&9 / &20) * cB * sB) +
       sA * (--(&7 / &20) - (&9 / &20) * sB pow 2 - (&13 / &20) * cB * sB + sB)` MP_TAC THENL
     [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     RASM_ARITH_TAC]];
   SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `cA * sB - sA * cB <= &0` ASSUME_TAC THENL
   [C981SQ_PROD `&0 <= cA * --sB` THEN C981SQ_PROD `&0 <= sA * cB` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `cB - (&14 / &5) * sB <= vB ==> false` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `--sB:real`] C981SR_NEGATIVE_LOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(cA * sB - sA * cB) * ((&47 / &20) * cB + (&33 / &20) * sB) +
      (cA * cB + sA * sB) * (cB - (&14 / &5) * sB + &1) - ((&87 / &50) * cA - &2 * sA) =
      cA * (cB - &37 / &50 + (&13 / &20) * (--sB) pow 2 + (&9 / &20) * cB * --sB) +
      sA * (--(&7 / &20) - (&9 / &20) * (--sB) pow 2 + (&13 / &20) * cB * --sB - --sB)`
    MP_TAC THENL
    [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_conj(lhand(concl th))
      then MATCH_MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
     can (find_term ((=) `uB:real`)) (concl th))) THENL
   [ASM_CASES_TAC `(&10 / &37) * cB <= --sB` THENL
    [MP_TAC(SPECL [`cA:real`; `sA:real`; `cB:real`; `--sB:real`] C981SR_NEGATIVE_STEEP) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
     C981SQ_PROD `&0 <= --(cA * sB - sA * cB) * (((&47 / &20) * cB + (&33 / &20) * sB) - uB)` THEN
     C981SQ_PROD `&0 <= (cA * cB + sA * sB) * ((vB + aB) - ((&87 / &50) * cB - &3 * sB))` THEN
     SUBGOAL_THEN
      `(cA * sB - sA * cB) * ((&47 / &20) * cB + (&33 / &20) * sB) +
       (cA * cB + sA * sB) * ((&87 / &50) * cB - &3 * sB) - ((&87 / &50) * cA - &2 * sA) =
       cA * ((&13 / &20) * cB * --sB - (&9 / &100) * (--sB) pow 2) -
       sA * (&7 / &20 + (&13 / &20) * (--sB) pow 2 + (&9 / &100) * cB * --sB)` MP_TAC THENL
     [UNDISCH_TAC `cB * cB + sB * sB = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
     RASM_ARITH_TAC;
     FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
       concl th = `cB - (&14 / &5) * sB <= vB ==> false`)) THEN
     MATCH_MP_TAC C981SQ_ADVANCED_FACES THEN
     MAP_EVERY EXISTS_TAC [`uB:real`; `aB:real`] THEN
     ASM_REWRITE_TAC[REAL_ABS_BOUNDS] THEN ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_imp(concl th) &&
      concl th = `cB - (&14 / &5) * sB <= vB ==> false`)) THEN
    ASM_REAL_ARITH_TAC]]);;

(* Lean: impossible *)
let C981SQ_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aA /\ aA = aB /\ c977cc_normal cA sA /\ &0 < cB /\ abs sB <= cB /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     ~linside cB sB uB vB aB (&3) (&1) /\
     ~linside cB sB uB vB aB (&14 / &5) (&1) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] C981SQ_CORE_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C981SQ_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [MATCH_MP_TAC C981SQ_A_V_IMPOSSIBLE;
   MATCH_MP_TAC C981SQ_BACKWARD_IMPOSSIBLE;
   MATCH_MP_TAC C981SQ_OWN_V_IMPOSSIBLE] THEN
  MAP_EVERY EXISTS_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                        `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aB`)) THEN
  ASM_REWRITE_TAC[]);;
