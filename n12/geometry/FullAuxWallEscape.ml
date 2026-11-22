(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallEscape.lean                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/DoubleAuxWallCenter.ml";;

(* Lean: narrow_faces_of_missing *)
let FAWE_NARROW_FACES_OF_MISSING = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ~linside cA sA uA vA aA (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> &0 < sA /\ &4 * sA < cA /\
         &2 * cA + &2 * sA <= uA /\ uA < &2 * cA + (&113 / &50) * sA /\
         &3 * cA - (&5 / &2) * sA < vA + aA /\
         vA + aA <= &3 * cA - (&12 / &5) * sA /\
         linside cA sA uA vA aA (&5 / &2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&3) (&12 / &5)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aA` THEN REWRITE_TAC[ldisj] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&4 * sA < cA` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(&16 / &25) * cA <= sA` THENL
     [DAWCE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CES_SHALLOW_CENTER) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `z = sA / (&1 + cA)` THEN
    SUBGOAL_THEN `&0 <= z /\ (&1 + cA) * z = sA` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `sA * z = &1 - cA` ASSUME_TAC THENL
     [SUBGOAL_THEN `(&1 + cA) * (sA * z) = (&1 + cA) * (&1 - cA)` MP_TAC THENL
       [UNDISCH_TAC `(&1 + cA) * z = sA` THEN UNDISCH_TAC `cA * cA + sA * sA = &1` THEN
        CONV_TAC REAL_RING; ALL_TAC] THEN
      REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DAWCE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `z:real`]
      DAWCE_MODERATE_CROSSING) THEN
    DAWCE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`; `z:real`]
      CWC_CENTER_OF_CROSSING) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DAWCE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CWPA_CENTRAL_LOWER_FACES) THEN
  FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  ASM_CASES_TAC `linside cA sA uA vA aA (&5 / &2) (&3)` THENL
   [ALL_TAC;
    DAWCE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CWC_SHALLOW) THEN
    ASM_MESON_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cA sA uA vA aA (&2) (&113 / &50)`; `linside cA sA uA vA aA (&113 / &50) (&2)`;
    `linside cA sA uA vA aA (&47 / &20) (&47 / &20)`; `linside cA sA uA vA aA (&5 / &2) (&3)`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `sA:real`] [`cA <= &1`] THEN
  SUBGOAL_THEN `vA + aA <= --sA * (&12 / &5) + cA * &3` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside cA sA uA vA aA (&12 / &5) (&3)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: narrow_faces *)
let FAWE_NARROW_FACES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> &0 < sA /\ &4 * sA < cA /\
         &2 * cA + &2 * sA <= uA /\ uA < &2 * cA + (&113 / &50) * sA /\
         &3 * cA - (&5 / &2) * sA < vA + aA /\
         vA + aA <= &3 * cA - (&12 / &5) * sA /\
         linside cA sA uA vA aA (&5 / &2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FAWE_NARROW_FACES_OF_MISSING THEN
  MAP_EVERY EXISTS_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ldisj cA sA uA vA aA cT sT uT vT aT` THEN REWRITE_TAC[ldisj] THEN
  ASM_MESON_TAC[]);;
