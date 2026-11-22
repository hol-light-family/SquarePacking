(* ========================================================================= *)
(* Port of Compact/Geometry/CentralWallEscape.lean (Jatloe, N12-jatloe).      *)
(* A centre-escaping elbow crosses the neighbouring wall line at its         *)
(* half-angle point; the marker and the container wall force the half-angle  *)
(* below 1/5.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* Lean: right_wall *)
let CWE_RIGHT_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ lcont c s u v a
     ==> c * (u + a) - s * v <= &4`,
  REWRITE_TAC[lcont] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &4 - c * (u + a) + s * v ==> c * (u + a) - s * v <= &4`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + a - e) - s * (v + e)`;
                                `s * (u + a - e) + c * (v + e)`]) THEN
  ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
  [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: crossing_point *)
let CWE_CROSSING_POINT = prove
 (`forall c s u v a z.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= (&16 / &25) * c /\
     &0 <= z /\ (&1 + c) * z = s /\ s * z = &1 - c /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&5 / &2) (&3) /\
     ~linside c s u v a (&2) (&2)
     ==> linside c s u v a (&3) (&2 + z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= c + s` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `c / &2 + s <= &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= c * ((&16 / &25) * c - s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   NLIN_FACTS_TAC [SQ_NONNEG `c:real`] [`(c / &2 + s) * (c / &2 + s) <= &1`] THEN
   NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z * (c + &2 * s - &1)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `c * &2 + s * &2 <= u` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s * (&5 / &2) + c * &3` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: lower_face *)
let CWE_LOWER_FACE = prove
 (`forall c s u v a z.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ &0 <= s /\ &0 <= z /\ z < &2 / &5 /\
     linside c s u v a (&1543 / &500) (&2) /\
     linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&3) (&2 + z)
     ==> c * &3 + s * (&2 + z) <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s * (&2 / &5 - z) /\ &0 <= c * z /\ &0 < c * (&2 / &5 - z)`
  MP_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* Lean: wall_inequalities *)
let CWE_WALL_INEQUALITIES = prove
 (`forall c s u v a z.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ lcont c s u v a /\
     linside c s u v a (&1543 / &500) (&2) /\
     c * &3 + s * (&2 + z) <= u
     ==> s * z < (&43 / &500) * c /\
         c * s * z < &1 - c - (&43 / &500) * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CWE_RIGHT_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `linside c s u v a (&1543 / &500) (&2)` THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c * (c * &3 + s * (&2 + z)) <= c * u /\
                s * v <= s * (--s * &1543 / &500 + c * &2) /\
                &0 < c * (a - &1)` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: half_angle_lt *)
let CWE_HALF_ANGLE_LT = prove
 (`forall r t z. &0 < r /\ &0 <= t /\ r pow 2 + t pow 2 = &1 /\ &0 <= z /\
           t * z < (&43 / &500) * r /\
           r * t * z < &1 - r - (&43 / &500) * t pow 2
           ==> z < &1 / &5`,
  REWRITE_TAC[REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `t < (&43 / &100) * r` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= t * (z - &1 / &5)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&9 / &10 < r` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 < ((&43 / &100) * r - t) * ((&43 / &100) * r + t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_NOT_LE] THEN REPEAT DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= (r + &9 / &10) * (&9 / &10 - r)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   UNDISCH_TAC `r * t * z < &1 - r - (&43 / &500) * t * t` THEN
   UNDISCH_TAC `r * r + t * t = &1` THEN
   FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
   DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - r <= (&10 / &19) * t * t` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 - r) * (r - &9 / &10)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * t * z < (&4183 / &9500) * t * t` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * z < (&4183 / &9500) * t` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(r * z) * z <= ((&4183 / &9500) * t) * z` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r * (z * z) < r * (&179869 / &4750000)` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z * z < &179869 / &4750000` ASSUME_TAC THENL
  [MP_TAC(SPECL [`z * z:real`; `&179869 / &4750000`; `r:real`] REAL_LT_LMUL_EQ) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  NLIN_TAC []);;

(* Lean: slope_of_half_angle *)
let CWE_SLOPE_OF_HALF_ANGLE = prove
 (`forall c s z. &0 < c /\ &0 <= z /\ (&1 + c) * z = s /\ s * z = &1 - c /\
           z < &1 / &5
           ==> &12 * s < &5 * c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&1 + c) * z * z = &1 - c` ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + c) * z = s` THEN UNDISCH_TAC `s * z = &1 - c` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + c) * ((&1 / &5 - z) * (&25 + &5 * z))` MP_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `(&1 + c) * z = s` THEN REAL_ARITH_TAC);;

(* Lean: shallow_slope_lt *)
let CWE_SHALLOW_SLOPE_LT = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ &1 < aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= (&16 / &25) * cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&5 / &2) (&3) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> &12 * sA < &5 * cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `cA <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `sA:real`]; ALL_TAC] THEN
  ABBREV_TAC `z = sA / (&1 + cA)` THEN
  SUBGOAL_THEN `(&1 + cA) * z = sA /\ sA * z = &1 - cA` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "z" THEN UNDISCH_TAC `&0 < cA` THEN
   UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z` ASSUME_TAC THENL
  [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z < &2 / &5` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `z:real`]
    CWE_CROSSING_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
    CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lcont cW sW uW vW aW` ASSUME_TAC THENL
  [UNDISCH_TAC `lcont cR sR uR vR aR` THEN ASM_REWRITE_TAC[lcont]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cW sW uW vW aW (&3) (&2 + z)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aR` THEN
   REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `z:real`]
    CWE_LOWER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `z:real`]
    CWE_WALL_INEQUALITIES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `z:real`] CWE_HALF_ANGLE_LT) THEN
  REWRITE_TAC[REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_POW_2]; DISCH_TAC] THEN
  MATCH_MP_TAC CWE_SLOPE_OF_HALF_ANGLE THEN EXISTS_TAC `z:real` THEN
  ASM_REWRITE_TAC[]);;
