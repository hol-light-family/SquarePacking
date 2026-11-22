(* ========================================================================= *)
(* Port of Compact/Geometry/DoubleAuxWallCenter.lean                         *)
(*                                                                           *)
(* pullSwap q = (s, c, u, --v - a, a); container_pullSwap is LCONT_PULLSW.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/DoubleAuxWallCoupling.ml";;
needs "n12/geometry/CentralWallCenter.ml";;

(* apply a lemma instance: prove its antecedent from the assumptions, then
   add its conclusion as an assumption *)
let DAWCE_STEP th (asl,w as g) =
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN
     REWRITE_TAC[lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_MESON_TAC[]) in
  ASSUME_TAC (MP th ath) g;;

(* Lean: moderate_crossing *)
let DAWCE_MODERATE_CROSSING = prove
 (`forall c s u v a z.
     c * c + s * s = &1 /\ &1 < a /\
     &0 < c /\ &0 <= s /\ s <= c /\ c <= &4 * s /\
     &0 <= z /\ (&1 + c) * z = s /\ s * z = &1 - c /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     ~linside c s u v a (&12 / &5) (&3) /\
     ~linside c s u v a (&2) (&2)
     ==> linside c s u v a (&3) (&2 + z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&2) (&113 / &50)`; `linside c s u v a (&113 / &50) (&2)`;
    `linside c s u v a (&47 / &20) (&47 / &20)`] THEN
  SUBGOAL_THEN `c * &2 + s * &2 <= u` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&2) (&2)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s:real`; SQ_NONNEG `(&7 / &10) * (c + s) - &1`]
    [`(&7 / &10) * (c + s) <= &1`] THEN
  SUBGOAL_THEN `v + a <= --s * (&12 / &5) + c * &3` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c s u v a (&12 / &5) (&3)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `(&2 / &5) * c + s - &3 / &5`]
    [`&0 <= (&4 * s - c) * (&4 * s + &6 * c)`; `&3 / &5 <= (&2 / &5) * c + s`] THEN
  NLIN_FACTS_TAC []
    [`&0 <= z * ((&2 / &5) * c + s - &3 / &5)`; `(&3 / &5) * s <= z * (c + s)`;
     `&0 <= s * z`; `c * z <= s`] THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: shallow_point *)
let DAWCE_SHALLOW_POINT = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ aA = aR /\ aA = aT /\
     lcont cR sR uR vR aR /\ lcont cT sT uT vT aT /\
     &0 < cA /\ &0 <= sA /\ sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&8 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aT` o concl)) THEN
  ASM_CASES_TAC `linside cA sA uA vA aA (&2) (&2)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&3) (&12 / &5) /\
                ~linside cA sA uA vA aA (&12 / &5) (&3)` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&4 * sA <= cA` THENL
   [DAWCE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
      CWPA_CENTRAL_LOWER_FACES) THEN
    FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    DAWCE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aA:real`] DAWC_MISSING_STRONG) THEN
    DAWCE_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                      `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CWC_SHALLOW) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
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
  ASM_MESON_TAC[]);;

(* Lean: point *)
let DAWCE_POINT = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ aA = aR /\ aA = aT /\
     lcont cR sR uR vR aR /\ lcont cT sT uT vT aT /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cR sR uR vR aR (&3) (&87 / &50) /\
     ~linside cR sR uR vR aR (&3) (&8 / &5) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aR` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aT` o concl)) THEN
  (* tStrong *)
  DAWCE_STEP(REWRITE_RULE[lcont; LINSIDE_PULLSW]
    (SPECL [`sT:real`; `cT:real`; `uT:real`; `--vT - aA:real`; `aA:real`] CWC_RIGHT_HIGH)) THEN
  (* the positive frame of A *)
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aa:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aa:real = aA` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj; lcont]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `sa <= ca` THENL
   [DAWCE_STEP(SPECL [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aA:real`;
                      `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CWC_SHALLOW) THEN
    ASM_REWRITE_TAC[];
    DAWCE_STEP(REWRITE_RULE[ldisj; lcont; LINSIDE_PULLSW]
      (SPECL [`sa:real`; `ca:real`; `ua:real`; `--va - aA:real`; `aA:real`;
              `sT:real`; `cT:real`; `uT:real`; `--vT - aA:real`; `aA:real`;
              `sR:real`; `cR:real`; `uR:real`; `--vR - aA:real`; `aA:real`] DAWCE_SHALLOW_POINT)) THEN
    ASM_REWRITE_TAC[]]);;
