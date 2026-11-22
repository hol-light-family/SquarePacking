(* ========================================================================= *)
(* Port of Compact/Geometry/MergedRightWallSector.lean                       *)
(* (N12Compact.MergedRightWallSector).  Complete positive-angle sector for   *)
(* the merged right central pair and its actual right wall.                  *)
(* Lean `upper A nx ny` / `lower R nx ny` are ABT_upper / ABT_lower.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CentralWallPairSupport.ml";;
needs "n12/geometry/MergedWallLongitudinalMargin.ml";;

(* Lean: faces *)
let MRWS_FACES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= &16 / &25 * c /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&47 / &20) (&47 / &20) /\
      ~linside c s u v a (&2) (&2) /\
      ~linside c s u v a (&3) (&87 / &50)
      ==> &2 * c + &2 * s <= u /\ &87 / &50 * c - &3 * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  SUBGOAL_THEN `&2 * c + &2 * s <= u` ASSUME_TAC THENL
   [UNDISCH_THEN `~linside c s u v a (&3) (&87 / &50)` (K ALL_TAC) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `~linside c s u v a (&2) (&2)` (K ALL_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: crossing *)
let MRWS_CROSSING = prove
 (`forall c s u v a z.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= &16 / &25 * c /\
      linside c s u v a (&47 / &20) (&33 / &20) /\
      linside c s u v a (&47 / &20) (&47 / &20) /\
      &2 * c + &2 * s <= u /\
      &0 <= z /\ (&1 + c) * z = s /\ s * z = &1 - c
      ==> linside c s u v a (&3) (&2 + z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th)))) THEN
  SUBGOAL_THEN `&1 / &2 <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= (&16 / &25 * c - s) * (&16 / &25 * c + s)`;
      `&0 < (&1 / &2 - c) * (&1 / &2 + c)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= z * (&2 * c - &1)`; `s / &3 <= c * z`; `c * z <= s`; `&0 <= s * z`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: axes (private) *)
let MRWS_AXES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR z.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\
     &0 < cA /\ &0 <= sA /\ sA <= &16 / &25 * cA /\ &0 < cR /\ &0 <= sR /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     &87 / &50 * cA - &3 * sA <= vA /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     &0 <= z /\ z < &2 / &5 /\
     linside cA sA uA vA aA (&3) (&2 + z) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> uA + aA <= ABT_lower cR sR uR vR aR cA sA \/
         ABT_upper cA sA uA vA aA cR sR <= uR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  SUBGOAL_THEN `cA <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `sA:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cR * z /\ &0 < cR * (&2 / &5 - z)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWPA_UNFOLD_TAC `linside cA sA uA vA aA (&47 / &20) (&33 / &20)` THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aA (&1543 / &500) (&2)` THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aA (&3) (&12 / &5)` THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    ABT_OWNU) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    ABT_OWNV) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    ABT_OWNU) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ASM_REWRITE_TAC[C977CB_faceSep] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [CWPA_CASE_TAC `cA:real` `sA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cR:real`; `sR:real`; `aA:real`]
       ABT_PARALLEL_RADIUS)
     (SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
             `&1543 / &500`; `&2`; `cA:real`; `sA:real`] ABT_STRICT_BOUNDS);
   CWPA_CASE_TAC `--sA:real` `cA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cR:real`; `sR:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)
     (SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`;
             `&3`; `&12 / &5`; `--sA:real`; `cA:real`] ABT_STRICT_BOUNDS);
   CWPA_CASE_TAC `cR:real` `sR:real` true
     (SPECL [`cR:real`; `sR:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_PARALLEL_RADIUS)
     (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
             `&47 / &20`; `&33 / &20`; `cR:real`; `sR:real`] ABT_STRICT_BOUNDS);
   CWPA_CASE_TAC `--sR:real` `cR:real` true
     (SPECL [`cR:real`; `sR:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)
     (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
             `&3`; `&2 + z`; `--sR:real`; `cR:real`] ABT_STRICT_BOUNDS)]);;

(* Lean: wall_axis (private) *)
let MRWS_WALL_AXIS = prove
 (`forall cA sA uA vA aA cR sR uR vR aR z.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ &0 < cR /\ &0 <= sR /\
     &0 <= cA * sR - sA * cR /\
     &2 * cA + &2 * sA <= uA /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     &0 <= z /\ z <= &1 / &5 /\ (&1 + cA) * z = sA /\ sA * z = &1 - cA /\
     cR * sR * z < &1 - cR - &43 / &500 * sR pow 2 /\
     ABT_upper cA sA uA vA aA cR sR <= uR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  SUBGOAL_THEN `&0 < cA * cR + sA * sR` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`&0 < cA * cR`; `&0 <= sA * sR`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    CWPS_SUPPORT_FORMULAS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cR:real`; `sR:real`; `z:real`] MWLM_MARGINS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CWE_RIGHT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  CWPA_UNFOLD_TAC `linside cA sA uA vA aA (&47 / &20) (&47 / &20)` THEN
  CWPA_UNFOLD_TAC `linside cR sR uR vR aA (&1543 / &500) (&2)` THEN
  NLIN_FACTS_TAC []
   [`(cA * cR + sA * sR) * (&2 * cA + &2 * sA) <= (cA * cR + sA * sR) * uA`;
    `(cA * sR - sA * cR) * (--sA * &47 / &20 + cA * &47 / &20) <= (cA * sR - sA * cR) * (vA + aA)`;
    `&0 < (aA - &1) * (cA * cR + sA * sR)`] THEN
  SUBGOAL_THEN `(cA * cR + sA * sR) * (&2 * cA + &2 * sA + &1) + (cA * sR - sA * cR) * (&47 / &20 * cA - &47 / &20 * sA) =
                (&2 * (cR + sR) + (cA * cR + sA * sR) + &7 / &20 * (cA - sA) * (cA * sR - sA * cR))` ASSUME_TAC THENL
   [UNDISCH_TAC `cA * cA + sA * sA = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * (cR + sR) + (cA * cR + sA * sR) + &7 / &20 * (cA - sA) * (cA * sR - sA * cR)) < uR` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`cR * (&2 * (cR + sR) + (cA * cR + sA * sR) + &7 / &20 * (cA - sA) * (cA * sR - sA * cR)) < cR * uR`;
    `sR * vR <= sR * (--sR * &1543 / &500 + cR * &2)`;
    `&0 < (aA - &1) * cR`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: point *)
let MRWS_POINT = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= &16 / &25 * cA /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&87 / &50) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] MRWS_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + cA` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `z = sA / (&1 + cA)` THEN
  SUBGOAL_THEN `(&1 + cA) * z = sA` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sA * z = &1 - cA` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `&1 + cA` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(&1 + cA) * z = sA` THEN UNDISCH_TAC `cA * cA + sA * sA = &1` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `z < &2 / &5` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [SQ_NONNEG `sA:real`] [`cA <= &1`; `&0 <= cA * (z - &2 / &5)`] THEN
    NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `z:real`]
    MRWS_CROSSING) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
    CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; PURE_REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aR`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  SUBGOAL_THEN
   `lcont cW sW uW vW aA /\
    linside cW sW uW vW aA (&1543 / &500) (&2) /\
    linside cW sW uW vW aA (&3) (&12 / &5) /\
    (forall x y. ~(linside cA sA uA vA aA x y /\ linside cW sW uW vW aA x y))`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[lcont]) THEN
    REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[lcont] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    CWE_LOWER_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    CWE_WALL_INEQUALITIES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `z:real`] CWE_HALF_ANGLE_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `z:real`] CWE_SLOPE_OF_HALF_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`] CWPA_COSINE_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`; `z:real`]
    CWPA_WALL_ANGLE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= cA * sW - sA * cW` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    MRWS_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ldisj] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
      CWPS_CENTRAL_AXIS_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
      MRWS_WALL_AXIS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;
