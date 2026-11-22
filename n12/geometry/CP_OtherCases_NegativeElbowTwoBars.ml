(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/NegativeElbowTwoBars.lean           *)
(* (N12Compact.Completion.OtherCases.NegativeElbowTwoBars).  A negative      *)
(* inward elbow cannot avoid the bottom and right bars while omitting its    *)
(* centre.  q.s = -t is written s = --t.                                     *)
(* CanonicalScalars.bounds: CCCS_BOUNDS; BottomBarSupport.negative:          *)
(* CCBBS_NEGATIVE; S12.short_projections: FSAF_SHORT_PROJECTIONS;            *)
(* DerivedWalls.vertical_right / closed_affine_bound: OCDW_VERTICAL_RIGHT /  *)
(* OCDW_CLOSED_AFFINE_BOUND; WallProfile.vertex: OCWPVG_VERTEX;              *)
(* pullX: LINSIDE_PULLX.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareAForced.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_OtherCases_BottomBarSupport.ml";;
needs "n12/geometry/CP_OtherCases_DerivedWalls.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let CCNETB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let CCNETB_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let CCNETB_SEG_TAC x =
  FIRST_ASSUM(MP_TAC o SPEC x o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `--(&1)`)) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let CCNETB_RIGHT_TAC y =
  FIRST_ASSUM(MP_TAC o SPEC y o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `linside c (--t) u v a (&1)`)) (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: impossible *)
let CCNETB_IMPOSSIBLE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&0) (--(&13 / &50)) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\
     (forall x. &13 / &50 <= x /\ x <= &4 / &5 ==> ~linside c s u v a x (--(&1))) /\
     (forall y. --(&13 / &50) <= y /\ y <= &0 ==> ~linside c s u v a (&1) y)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c (--t) u v a (&7 / &20) (--(&7 / &20))`;
    `linside c (--t) u v a (&0) (--(&13 / &50))`;
    `linside c (--t) u v a (&13 / &50) (&0)`] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c (--t) u v a (&0) (&0)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= t` ASSUME_TAC THENL [CCNETB_RIGHT_TAC `&0`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `t:real`] CCBBS_NEGATIVE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)] THEN
  SUBGOAL_THEN `t - c * &13 / &50 < v + a` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(SPECL [`c:real`; `--t`; `&37 / &50`; `--(&1 / &5)`] FSAF_SHORT_PROJECTIONS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    STRIP_TAC THEN RASM_ARITH_TAC;
    CCNETB_PROD_TAC `t:real` `u:real` THEN
    CCNETB_PROD_TAC `c:real` `(t - c * &13 / &50) - (v + a)` THEN
    CCNETB_PRODLT_TAC `a - &1` `c + t` THEN
    CCNETB_PROD_TAC `c:real` `c - t` THEN
    CCNETB_PROD_TAC `c:real` `t:real` THEN
    NLIN_TAC ~deg2:false []];
   ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c + t * &13 / &50` ASSUME_TAC THENL
  [CCNETB_RIGHT_TAC `--(&13 / &50)`; ALL_TAC] THEN
  SUBGOAL_THEN `forall y. ~linside c (--t) u v a (&1) y` ASSUME_TAC THENL
  [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
   FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside]) THEN
   SUBGOAL_THEN `--(&13 / &50) < y /\ y < &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `linside c (--t) u v a (&1)`)) (concl th) &&
     is_imp(snd(dest_forall(concl th))))) THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  (* the right wall, through the reflected square *)
  MP_TAC(SPECL [`--c`; `--t`; `u - &4 * c`; `--v - a - &4 * --t`; `a:real`;
                `&73 / &20`; `--(&7 / &20)`; `&3`] OCDW_VERTICAL_RIGHT) THEN
  PURE_REWRITE_TAC[LINSIDE_PULLX; REAL_ARITH `&4 - &73 / &20 = &7 / &20`;
                   REAL_ARITH `&4 - &3 = &1`] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_TAC] THEN
  SUBGOAL_THEN `forall x y. linside c (--t) u v a x y ==> --(&1) <= --(&1) * x + &0 * y`
    ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`&4 - x`; `y:real`] o check (fun th ->
     is_forall(concl th) && can (find_term ((=) `&3`)) (concl th))) THEN
   ASM_REWRITE_TAC[REAL_ARITH `&4 - (&4 - x) = x`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `u + a:real`; `v + a:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `--(&1)`; `&0`; `--(&1)`;
                `&7 / &20`; `--(&7 / &20)`;
                `c * (u + a) - --t * (v + a)`; `--t * (u + a) + c * (v + a)`]
    OCDW_CLOSED_AFFINE_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `c * (u + a) + t * (v + a) <= &1` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [CCNETB_PRODLT_TAC `t:real` `t:real` THEN
   CCNETB_PRODLT_TAC `t * t` `(&4 / &5) * (&1 + c) - (&1 - t)` THEN
   SUBGOAL_THEN `(&1 + c) * (c + t - &1 - c * t + (&4 / &5) * t pow 2) =
                 t pow 2 * ((&4 / &5) * (&1 + c) - (&1 - t))` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < c + t - &1 - c * t + (&4 / &5) * t pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    CCNETB_PROD_TAC `&1 + c` `--(c + t - &1 - c * t + (&4 / &5) * t pow 2)` THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   CCNETB_PROD_TAC `c:real` `u:real` THEN
   CCNETB_PROD_TAC `t:real` `v - ((&4 / &5) * t - c)` THEN
   CCNETB_PRODLT_TAC `a - &1` `c + t` THEN
   NLIN_TAC ~deg2:false [];
   CCNETB_PROD_TAC `c:real` `&1 - (c * (u + a) + t * (v + a))` THEN
   CCNETB_PROD_TAC `t:real` `--t * (u + a) + c * v + &1` THEN
   SUBGOAL_THEN `c * (&1 - (c * (u + a) + t * (v + a))) + t * (--t * (u + a) + c * v + &1) =
                 c + t - a * c * t - (u + a)` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   CCNETB_PROD_TAC `&1 - c` `&1 - t` THEN
   CCNETB_PROD_TAC `c:real` `t:real` THEN
   CCNETB_PRODLT_TAC `a - &1` `&1 + c * t` THEN
   NLIN_TAC ~deg2:false []]);;
