(* ========================================================================= *)
(* Port of Compact/Geometry/CentralWallLongitudinal.lean (Jatloe).            *)
(* Continuous scalar margin for separation on the neighbouring wall's        *)
(* longitudinal axis.                                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallEscape.ml";;

(* Lean: X, Y, margin (definitions) *)
let cwl_x = new_definition
 `cwl_x (c:real) s = &2 + (&7 / &20) * s pow 2 + (&7 / &20) * c * s`;;
let cwl_y = new_definition
 `cwl_y (c:real) s = &33 / &20 + (&7 / &20) * s pow 2 - (&7 / &20) * c * s`;;
let cwl_margin = new_definition
 `cwl_margin (c:real) s q w =
    w + (c - s) + q * (c + s) + cwl_x c s - &4 + q * (cwl_y c s - &2) -
    (&457 / &500) * q pow 2`;;

let CWL_NONNEG_OF_MUL = prove
 (`forall x y. &0 < y /\ &0 <= y * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&0`; `x:real`; `y:real`] REAL_LE_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

(* Lean: normal_bounds (private) *)
let CWL_NORMAL_BOUNDS = prove
 (`forall c s. &12 / &13 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> c <= &1 /\ s <= &2 / &5 /\ &1 - (&13 / &25) * s pow 2 <= c`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (c - &12 / &13) * (c + &12 / &13) /\
                &0 <= (&1 - c) * (c - &12 / &13)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [NLIN_TAC []; ASM_REAL_ARITH_TAC]);;

(* Lean: tangent (private) *)
let CWL_TANGENT = prove
 (`forall c s q w. &0 <= c /\ &0 <= s /\ &0 <= q /\ &0 <= w /\
             c pow 2 + s pow 2 = &1 /\ w pow 2 = &1 + q pow 2
             ==> c + s * q <= w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w pow 2 - (c + s * q) pow 2 = (s - c * q) pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
   UNDISCH_TAC `w pow 2 = &1 + q pow 2` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(c + s * q) pow 2 <= w pow 2 /\ &0 <= c + s * q` MP_TAC THENL
  [CONJ_TAC THENL
   [MP_TAC(SPEC `s - c * q:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_SIMP_TAC[REAL_LE_MUL]]; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= w` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SPEC_TAC(`c + s * q:real`,`A:real`) THEN SPEC_TAC(`w:real`,`B:real`) THEN
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: small_margin (private) *)
let CWL_SMALL_MARGIN = prove
 (`forall c s p q w. &12 / &13 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
               &0 <= p /\ c * p = s /\ p <= q /\ q <= &1 / &2 /\
               &0 <= w /\ w pow 2 = &1 + q pow 2
               ==> &0 <= cwl_margin c s q w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CWL_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `q:real`; `w:real`] CWL_TANGENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ABBREV_TAC `kk = -- &2 + (&7 / &20) * s pow 2 + (&7 / &20) * c * s + &2 * c - s` THEN
  ABBREV_TAC `ll = --(&7 / &20) + (&7 / &20) * s pow 2 - (&7 / &20) * c * s +
                   c + &2 * s` THEN
  SUBGOAL_THEN `(&1 + c) * (kk + ll * p - (&457 / &500) * p pow 2) =
                p pow 2 * ((&543 / &500) * c - &457 / &500)` ASSUME_TAC THENL
  [EXPAND_TAC "kk" THEN EXPAND_TAC "ll" THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `c * p = s`)) THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= kk + ll * p - (&457 / &500) * p pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC CWL_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + c` THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p <= (&13 / &12) * s` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= p * (c - &12 / &13)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * p = s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ll - (&457 / &500) * (q + p)` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= s * (&1 - c)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPEC `s:real` REAL_LE_POW_2) THEN
   EXPAND_TAC "ll" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (q - p) * (ll - (&457 / &500) * (q + p))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= kk + ll * q - (&457 / &500) * q pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `&0 <= (q - p) * (ll - (&457 / &500) * (q + p))` THEN
   UNDISCH_TAC `&0 <= kk + ll * p - (&457 / &500) * p pow 2` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[cwl_margin; cwl_x; cwl_y] THEN
  UNDISCH_TAC `&0 <= kk + ll * q - (&457 / &500) * q pow 2` THEN
  UNDISCH_TAC `c + s * q <= w` THEN
  EXPAND_TAC "kk" THEN EXPAND_TAC "ll" THEN REAL_ARITH_TAC);;

(* Lean: large_margin (private) *)
let CWL_LARGE_MARGIN = prove
 (`forall c s q w. &12 / &13 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
             &1 / &2 <= q /\ q <= &23 / &20 /\
             &0 <= w /\ w pow 2 = &1 + q pow 2
             ==> &0 <= cwl_margin c s q w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CWL_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `q:real`; `w:real`] CWL_TANGENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
                  ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= s * (c - &12 / &13) /\ &0 <= s * (&1 - c) /\
                &0 <= s * (&2 / &5 - s)` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `kk = --(&6 / &5) + (&7 / &20) * s pow 2 + (&7 / &20) * c * s + c - s` THEN
  ABBREV_TAC `ll = &1 / &4 + (&7 / &20) * s pow 2 - (&7 / &20) * c * s + c + s` THEN
  SUBGOAL_THEN `&1 / &50 <= kk + ll * (&1 / &2) - (&457 / &500) * (&1 / &2) pow 2 /\
                &9 / &1000 <= kk + ll * (&23 / &20) -
                               (&457 / &500) * (&23 / &20) pow 2`
  STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "kk" THEN EXPAND_TAC "ll" THEN
   REWRITE_TAC[REAL_POW_2] THEN
   UNDISCH_TAC `&1 - (&13 / &25) * s pow 2 <= c` THEN REWRITE_TAC[REAL_POW_2] THEN
   DISCH_TAC THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= kk + ll * q - (&457 / &500) * q pow 2` ASSUME_TAC THENL
  [SUBGOAL_THEN
    `&0 <= (&23 / &20 - q) *
           ((kk + ll * (&1 / &2) - (&457 / &500) * (&1 / &2) pow 2) - &9 / &1000) /\
     &0 <= (q - &1 / &2) *
           ((kk + ll * (&23 / &20) - (&457 / &500) * (&23 / &20) pow 2) - &9 / &1000) /\
     &0 <= (q - &1 / &2) * (&23 / &20 - q)` MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[cwl_margin; cwl_x; cwl_y] THEN
  UNDISCH_TAC `&0 <= kk + ll * q - (&457 / &500) * q pow 2` THEN
  UNDISCH_TAC `&4 / &5 + &3 / &5 * q <= w` THEN
  EXPAND_TAC "kk" THEN EXPAND_TAC "ll" THEN REAL_ARITH_TAC);;

(* Lean: wall_axis_margin *)
let CWL_WALL_AXIS_MARGIN = prove
 (`forall c s p q w. &12 / &13 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
               &0 <= p /\ c * p = s /\ p <= q /\ q <= &23 / &20 /\
               &0 <= w /\ w pow 2 = &1 + q pow 2
               ==> &0 <= cwl_margin c s q w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `q <= &1 / &2` THENL
  [MATCH_MP_TAC CWL_SMALL_MARGIN THEN EXISTS_TAC `p:real` THEN ASM_REWRITE_TAC[];
   MATCH_MP_TAC CWL_LARGE_MARGIN THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
