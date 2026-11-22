(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/EightPointObstruction.lean          *)
(* (N12Compact.Completion.OtherCases.EightPointObstruction).  Two strict     *)
(* points and six separate weak exclusions are impossible for an            *)
(* arbitrarily oriented open square of side greater than one.  The          *)
(* structure Input is the predicate ocepo_input; square q is c s u v a,     *)
(* square r is cr sr ur vr ar.  canonical_frame is CLF_CANONICAL_FRAME,      *)
(* increasing_projection is CCOS_INCREASING_PROJECTION.  Tag OCEPO_.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: Input (structure) *)
let ocepo_input = new_definition
 `ocepo_input c s u v a <=>
    &1 < a /\
    linside c s u v a (&13 / &20) (&7 / &20) /\
    linside c s u v a (&0) (&13 / &50) /\
    ~linside c s u v a (&0) (&0) /\
    ~linside c s u v a (&1 / &2) (&0) /\
    ~linside c s u v a (&0) (&1) /\
    ~linside c s u v a (&27 / &100) (--(&1 / &25)) /\
    ~linside c s u v a (&11 / &25) (&1) /\
    ~linside c s u v a (&37 / &50) (&1)`;;

(* Lean: Input.reframe *)
let OCEPO_INPUT_REFRAME = prove
 (`forall c s u v a cr sr ur vr ar.
     ocepo_input c s u v a /\ ar = a /\
     (forall x y. linside cr sr ur vr ar x y <=> linside c s u v a x y)
     ==> ocepo_input cr sr ur vr ar`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocepo_input] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* Lean: projection (private) *)
let OCEPO_PROJECTION = prove
 (`forall c s p q R. c pow 2 + s pow 2 = &1 /\ &0 < R /\ p pow 2 + q pow 2 < R pow 2
     ==> p * c + q * s < R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p * c + q * s) pow 2 + (q * c - p * s) pow 2 = p pow 2 + q pow 2`
  ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (p * c + q * s - R) * (p * c + q * s + R)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `q * c - p * s` REAL_LE_POW_2) THEN
  UNDISCH_TAC `(p * c + q * s) pow 2 + (q * c - p * s) pow 2 = p pow 2 + q pow 2` THEN
  UNDISCH_TAC `p pow 2 + q pow 2 < R pow 2` THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let OCEPO_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let OCEPO_CONTRA_TAC tm =
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN OCEPO_MISS_TAC tm;;

let OCEPO_PROJ_TAC c s p q r =
  MP_TAC(SPECL [c; s; p; q; r] OCEPO_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC];;

let OCEPO_SHORT_TAC c s p q =
  MP_TAC(SPECL [c; s; p; q] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC];;

(* Lean: nonnegative_impossible *)
let OCEPO_NONNEGATIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     ocepo_input c s u v a /\ &0 < c /\ &0 <= s /\ s <= c ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocepo_input] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (&13 / &20) (&7 / &20)`;
    `linside c s u v a (&0) (&13 / &50)`] THEN
  SUBGOAL_THEN `--(&1 / &2) * s <= v` ASSUME_TAC THENL
   [OCEPO_CONTRA_TAC `~linside c s u v a (&1 / &2) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCEPO_MISS_TAC `~linside c s u v a (&0) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
   [OCEPO_CONTRA_TAC `~linside c s u v a (&0) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&37 / &50) * c + s` ASSUME_TAC THENL
   [OCEPO_CONTRA_TAC `~linside c s u v a (&37 / &50) (&1)`; ALL_TAC] THEN
  OCEPO_PROJ_TAC `c:real` `s:real` `&237 / &50` `&31 / &25` `&5` THEN
  SUBGOAL_THEN `--(&11 / &25) * s + c < v + a` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&11 / &25) * c + s` ASSUME_TAC THENL
   [OCEPO_CONTRA_TAC `~linside c s u v a (&11 / &25) (&1)`; ALL_TAC] THEN
  OCEPO_SHORT_TAC `c:real` `s:real` `&17 / &100` `&26 / &25` THEN
  SUBGOAL_THEN `u < (&27 / &100) * c - (&1 / &25) * s` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&27 / &100) * s - (&1 / &25) * c <= v` ASSUME_TAC THENL
   [OCEPO_CONTRA_TAC `~linside c s u v a (&27 / &100) (--(&1 / &25))`; ALL_TAC] THEN
  OCEPO_PROJ_TAC `c:real` `s:real` `&37 / &25` `&127 / &100` `&2` THEN
  RASM_ARITH_TAC);;

(* Lean: nonpositive_impossible *)
let OCEPO_NONPOSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     ocepo_input c s u v a /\ s = --t /\ &0 < c /\ &0 <= t /\ t <= c ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocepo_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + --t * --t = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c (--t) u v a (&13 / &20) (&7 / &20)`;
    `linside c (--t) u v a (&0) (&13 / &50)`] THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL
   [OCEPO_CONTRA_TAC `~linside c (--t) u v a (&0) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `--t <= u` ASSUME_TAC THENL
   [OCEPO_CONTRA_TAC `~linside c (--t) u v a (&0) (&1)`; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c / &2 \/ t / &2 <= v` ASSUME_TAC THENL
   [OCEPO_MISS_TAC `~linside c (--t) u v a (&1 / &2) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `(&11 / &25) * c - t <= u \/ v + a <= c + (&11 / &25) * t` ASSUME_TAC THENL
   [OCEPO_MISS_TAC `~linside c (--t) u v a (&11 / &25) (&1)`; ALL_TAC] THEN
  OCEPO_SHORT_TAC `c:real` `t:real` `&3 / &50` `&1` THEN
  OCEPO_SHORT_TAC `c:real` `t:real` `&27 / &100` `&26 / &25` THEN
  SUBGOAL_THEN `u + a <= c / &2 /\ v + a <= c + (&11 / &25) * t` STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&27 / &100) * c + (&1 / &25) * t < u + a` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&27 / &100) * t - (&1 / &25) * c <= v` ASSUME_TAC THENL
   [OCEPO_CONTRA_TAC `~linside c (--t) u v a (&27 / &100) (--(&1 / &25))`; ALL_TAC] THEN
  OCEPO_PROJ_TAC `c:real` `t:real` `&77 / &50` `&117 / &100` `&2` THEN
  RASM_ARITH_TAC);;

(* Lean: impossible *)
let OCEPO_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ ocepo_input c s u v a ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cr:real` (X_CHOOSE_THEN `sr:real` (X_CHOOSE_THEN `ur:real`
    (X_CHOOSE_THEN `vr:real` (X_CHOOSE_THEN `ar:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] OCEPO_INPUT_REFRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= sr` THENL
   [MATCH_MP_TAC OCEPO_NONNEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC OCEPO_NONPOSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`; `--sr`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;
