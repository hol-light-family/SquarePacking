(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalFloor.lean                *)
(* (N12Compact.C1092MPPMInwardFinal).  OPPOSED-MISSING-INWARD section 1.     *)
(* The structure MissingProfile is the predicate c1092miff_missing_profile;  *)
(* square C is cC sC uC vC aC (c s u v a in single-square statements),      *)
(* square B is cB sB uB vB aB.  Normal is c977cc_normal; WallProfile.vertex  *)
(* / strict_closed_segment are OCWPVG_VERTEX / OCWPVG_STRICT_CLOSED_SEGMENT; *)
(* ClosedPointExclusion.outside_of_closed is OUTSIDE_OF_CLOSED.              *)
(* Tag C1092MIFF_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalScalars.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

(* Lean: MissingProfile (structure) *)
let c1092miff_missing_profile = new_definition
 `c1092miff_missing_profile c s u v a <=>
    &1 < a /\ c977cc_normal c (--s) /\ s < &0 /\ &17 / &20 < c /\ --s < &13 / &25 /\
    linside c s u v a (--(&7) / &20) (--(&7) / &20) /\
    linside c s u v a (&0) (--(&13) / &50) /\
    linside c s u v a (--(&13) / &50) (&0) /\
    linside c s u v a (--(&1)) (--(&2) / &5) /\
    --c - (&13 / &50) * s <= u /\
    --c + (&2 / &5) * s <= v /\
    v + a <= &0 /\
    ((--c + (&13 / &50) * s <= v /\ a <= c - (&13 / &50) * s) \/
     u + a <= --(&13 / &50) * c - s)`;;

let C1092MIFF_PROD_TAC = C1092MIFS_PROD_TAC;;

(* Lean: above_bar (private) *)
let C1092MIFF_ABOVE_BAR = prove
 (`forall cC sC uC vC aC cB sB uB vB aB X Y.
     cC * cC + sC * sC = &1 /\ &0 < aC /\
     lclosed cC sC uC vC aC X Y /\ linside cC sC uC vC aC (&0) (--(&13) / &50) /\
     --(&14) / &25 <= X /\ X <= &0 /\
     (forall x. --(&14) / &25 <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> --(&1) < Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ASM_CASES_TAC `Y = --(&1)` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~linside cB sB uB vB aB X (--(&1))` MP_TAC THENL
     [MATCH_MP_TAC OUTSIDE_OF_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ldisj cC sC uC vC aC cB sB uB vB aB` THEN
      REWRITE_TAC[ldisj] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `X:real` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y < --(&1)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < --(&13) / &50 - Y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(--(&1) - Y) / (--(&13) / &50 - Y) * (--(&13) / &50 - Y) = --(&1) - Y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (--(&1) - Y) / (--(&13) / &50 - Y) /\
                (--(&1) - Y) / (--(&13) / &50 - Y) < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `t = (--(&1) - Y) / (--(&13) / &50 - Y)` THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `X:real`; `Y:real`; `&0`; `--(&13) / &50`; `t:real`]
    OCWPVG_STRICT_CLOSED_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 - t) * Y + t * --(&13) / &50 = --(&1)` SUBST1_TAC THENL
   [UNDISCH_TAC `t * (--(&13) / &50 - Y) = --(&1) - Y` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  C1092MIFF_PROD_TAC [`&0 <= (&1 - t) * (X + &14 / &25)`; `&0 <= (&1 - t) * --X`] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - t) * X + t * &0` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  ANTS_TAC THENL [NLIN_TAC []; DISCH_TAC] THEN
  UNDISCH_TAC `ldisj cC sC uC vC aC cB sB uB vB aB` THEN
  REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]);;

(* Lean: missing_floor *)
let C1092MIFF_MISSING_FLOOR = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\
     c1092miff_missing_profile cC sC uC vC aC /\
     (forall x. --(&14) / &25 <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> cC - &1 - sC * (&1 - cC - (&13 / &50) * sC) < cC * (vC + aC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092miff_missing_profile cC sC uC vC aC`) THEN
  REWRITE_TAC[c1092miff_missing_profile; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  MP_TAC(ASSUME `linside cC sC uC vC aC (--(&1)) (--(&2) / &5)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `uC + aC`; `vC:real`] OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C1092MIFF_PROD_TAC
   [`&0 <= cC * (uC - (--cC - (&13 / &50) * sC))`;
    `&0 <= --sC * (vC - (--cC + (&2 / &5) * sC))`;
    `&0 < cC * (aC - &1)`] THEN
  MP_TAC(SPEC `cC + sC` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN `--cC * sC <= &1 / &2` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&14) / &25 < cC * (uC + aC) - sC * vC` ASSUME_TAC THENL
   [MP_TAC(SPEC `sC:real` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `cC * (uC + aC) - sC * vC < &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
      C1092MIFF_PROD_TAC
       [`&0 < cC * (aC - cC - (&2 / &5) * sC - (uC + aC))`;
        `&0 <= --sC * (--aC - vC)`;
        `&0 <= (cC + sC) * (cC - (&13 / &50) * sC - aC)`;
        `&0 < cC * --sC`] THEN
      MP_TAC(SPEC `sC:real` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
      NLIN_TAC ~deg2:false [];
      C1092MIFF_PROD_TAC
       [`&0 <= cC * (--(&13 / &50) * cC - sC - (uC + aC))`;
        `&0 <= --sC * (--aC - vC)`;
        `&0 < --sC * (aC - cC)`] THEN
      MP_TAC(SPEC `cC:real` REAL_LE_POW_2) THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
      NLIN_TAC ~deg2:false []];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cC * (uC + aC) - sC * vC`; `sC * (uC + aC) + cC * vC`]
    C1092MIFF_ABOVE_BAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C1092MIFF_PROD_TAC
   [`&0 <= --sC * (uC - (--cC - (&13 / &50) * sC))`;
    `&0 < (cC - sC) * (aC - &1)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: floor_coarse *)
let C1092MIFF_FLOOR_COARSE = prove
 (`forall c s H. c977cc_normal c s /\ &17 / &20 < c /\ s < &13 / &25 /\
     c - &1 + s * (&1 - c + (&13 / &50) * s) < c * H
     ==> --(&1) / &25 < H`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  SUBGOAL_THEN `(&1 + c) * (c - &1 + s * (&1 - c + (&13 / &50) * s)) =
                s pow 2 * ((&13 / &50) * (&1 + c) - &1 + s)` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MIFF_PROD_TAC [`&0 < (c - &17 / &20) * (c + &37 / &20)`] THEN
  SUBGOAL_THEN `&629 / &10000 < (&1 / &25) * c * (&1 + c)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + c) * ((c - &1 + s * (&1 - c + (&13 / &50) * s)) + c / &25)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `s <= &1 / &3` THENL
     [C1092MIFF_PROD_TAC
       [`&0 <= (&1 / &3 - s) * (&1 / &3 + s)`;
        `&0 <= s pow 2 * ((&13 / &50) * (&1 + c) - &1 + s + &519 / &1000)`] THEN
      RASM_ARITH_TAC;
      C1092MIFF_PROD_TAC
       [`&0 <= (&13 / &25 - s) * (&13 / &25 + s)`;
        `&0 <= s pow 2 * ((&13 / &50) * (&1 + c) - &1 + s + &557 / &3000)`] THEN
      RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c - &1 + s * (&1 - c + (&13 / &50) * s)) + c / &25` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < (&1 + c) * ((c - &1 + s * (&1 - c + (&13 / &50) * s)) + c / &25)` THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_ARITH `&0 <= c ==> &0 < &1 + c`;
                 REAL_ARITH `&7 / &10 <= c ==> &0 <= c`]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MIFF_PROD_TAC [`&0 <= c * --(H + &1 / &25)`] THEN
  RASM_ARITH_TAC);;

(* Lean: missing_near_center *)
let C1092MIFF_MISSING_NEAR_CENTER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c1092miff_missing_profile c s u v a /\
     c - &1 - s * (&1 - c - (&13 / &50) * s) < c * (v + a)
     ==> --(&1 / &25) < v + a /\ linside c s u v a (--(&1) / &25) (--(&1) / &25)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092miff_missing_profile; IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s`; `v + a`] C1092MIFF_FLOOR_COARSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c - &1 - s * (&1 - c - (&13 / &50) * s) < c * (v + a)` THEN
    REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  MP_TAC(ASSUME `linside c s u v a (--(&1)) (--(&2) / &5)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;
