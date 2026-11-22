(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974WallReach.lean             *)
(* (N12Compact.Completion.OtherCases.C983.C974WallReach).  Section 3 of      *)
(* C974-THREE-SQUARE-ENDING.  Square W is c s u v a; the structure Data is   *)
(* the predicate oc983wr_data.  The half-angle tangent s / (1 + c) is        *)
(* handled through C1092WPS_half / C1092WPS_QUARTER_DATA.  Tag OC983WR_.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974CornerScalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_CornerProfile.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: Data (structure) *)
let oc983wr_data = new_definition
 `oc983wr_data c s u v a <=>
    &1 < a /\ &0 < c /\ &0 < s /\ s <= c /\ &3 * s < &2 * c /\
    linside c s u v a (&0) (&0) /\
    linside c s u v a (&4 / &5) (&0) /\
    u + a <= c /\
    v + a <= c / &2 /\
    --(s / (&1 + c)) * (&1 - s) < u`;;

(* Lean: frame_bounds *)
let OC983WR_FRAME_BOUNDS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ oc983wr_data c s u v a
     ==> &4 / &5 < c /\ c <= &1 /\ &0 < s / (&1 + c) /\ s / (&1 + c) < &1 / &3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oc983wr_data] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&2 * c - &3 * s) * (&2 * c + &3 * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&4 / &5 < c` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < c ==> &0 < &1 + c`] THEN
  ASM_REAL_ARITH_TAC);;

let OC983WR_CANCEL = prove
 (`forall k x y. &0 < k /\ k * x = k * y ==> x = y`,
  MESON_TAC[REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ]);;

let OC983WR_POS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

(* Lean: reach *)
let OC983WR_REACH = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ oc983wr_data c s u v a
     ==> exists beta. &0 < beta /\ linside c s u v a (&1) (--beta) /\
                s / (&1 + c) - &1 / &2 < --beta /\ s < &1 / &2 /\
                a - s / &2 < u + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OC983WR_FRAME_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN UNDISCH_TAC `oc983wr_data c s u v a` THEN
    REWRITE_TAC[oc983wr_data] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `oc983wr_data c s u v a` THEN REWRITE_TAC[oc983wr_data] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if can (find_term ((=) `s / (&1 + c)`)) (concl th)
                                 then MP_TAC th else NO_TAC)) THEN
  REWRITE_TAC[GSYM C1092WPS_half] THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ASSUME `linside c s u v a (&0) (&0)`) THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + z pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s * z = &1 - c` ASSUME_TAC THENL
   [MATCH_MP_TAC OC983WR_CANCEL THEN EXISTS_TAC `&1 + z pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - c < z * (&1 - s)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s < &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= z * (&2 * s - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `(&1 + z pow 2) / &2 - &2 * z` THEN
  SUBGOAL_THEN `&0 < (&1 + z pow 2) / &2 - &2 * z` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < (&1 + z pow 2) * (&1 - &2 * s)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c - s * ((&1 + z pow 2) / &2 - &2 * z) = &1 - z * (&1 - s)` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN UNDISCH_TAC `s * z = &1 - c` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < z * (&1 - z / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s + c * (&1 / &2 + ((&1 + z pow 2) / &2 - &2 * z)) < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < &1 - x ==> x < &1`) THEN
    MATCH_MP_TAC OC983WR_POS_CANCEL THEN EXISTS_TAC `&2 * (&1 + z pow 2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * (&1 + z pow 2)) *
        (&1 - (s + c * (&1 / &2 + ((&1 + z pow 2) / &2 - &2 * z)))) =
        z pow 2 * (&3 - z) * (&1 - z)` SUBST1_TAC THENL
     [UNDISCH_TAC `(&1 + z pow 2) * c = &1 - z pow 2` THEN
      UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < z * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ((&1 + z pow 2) / &2 - &2 * z) * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z * (&1 - s) < s / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < s / &2 - k ==> k < s / &2`) THEN
    MATCH_MP_TAC OC983WR_POS_CANCEL THEN EXISTS_TAC `&1 + z pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&1 + z pow 2) * (s / &2 - z * (&1 - s)) = z pow 2 * (&2 - z)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(&1 + z pow 2) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;
