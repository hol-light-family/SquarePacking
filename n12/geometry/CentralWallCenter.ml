(* ========================================================================= *)
(* Port of Compact/Geometry/CentralWallCenter.lean (Jatloe, N12-jatloe).      *)
(* An elbow between two actual neighbouring wall squares contains the       *)
(* container centre.                                                         *)
(* S12.TransformFacts: container_pullX / inside_pullX / container_pullSwap / *)
(* inside_pullSwap are LCONT_PULLX, LINSIDE_PULLX, LCONT_PULLSW,             *)
(* LINSIDE_PULLSW of p2_base.ml; inside_segment is CES_INSIDE_SEGMENT.       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralWallPairSupport.ml";;
needs "n12/geometry/CentralOuterReach.ml";;
needs "n12/geometry/WallLowerReach.ml";;

(* Lean: center_of_crossing *)
let CWC_CENTER_OF_CROSSING = prove
 (`forall cA sA uA vA aA cR sR uR vR aR z.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= (&16 / &25) * cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     ~linside cA sA uA vA aA (&12 / &5) (&3) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     &0 <= z /\ (&1 + cA) * z = sA /\ sA * z = &1 - cA /\
     linside cA sA uA vA aA (&3) (&2 + z)
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `cA <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `sA:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `z < &2 / &5` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cW:real` (X_CHOOSE_THEN `sW:real` (X_CHOOSE_THEN
    `uW:real` (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `aW:real`
    STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aA`)) THEN
  SUBGOAL_THEN `lcont cW sW uW vW aA /\
                linside cW sW uW vW aA (&1543 / &500) (&2) /\
                linside cW sW uW vW aA (&3) (&12 / &5) /\
                ldisj cA sA uA vA aA cW sW uW vW aA`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[lcont; ldisj] THEN
   UNDISCH_TAC `lcont cR sR uR vR aA` THEN
   UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aA` THEN
   REWRITE_TAC[lcont; ldisj] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cW sW uW vW aA (&3) (&2 + z)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cA sA uA vA aA cW sW uW vW aA` THEN REWRITE_TAC[ldisj] THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    CWE_LOWER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    CWE_WALL_INEQUALITIES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `z:real`] CWE_HALF_ANGLE_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `z:real`] CWE_SLOPE_OF_HALF_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CWPA_CENTRAL_LOWER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    COR_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `&12 / &13 <= cA` ASSUME_TAC THENL
  [MATCH_MP_TAC CWPA_COSINE_BOUND THEN EXISTS_TAC `sA:real` THEN
   ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `cW:real`; `sW:real`; `z:real`]
    CWPA_WALL_ANGLE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN
    UNDISCH_TAC `cW * sW * z < &1 - cW - &43 / &500 * sW pow 2` THEN
    REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`; `z:real`]
    CWPA_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
  [MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                 `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
     CWPS_CENTRAL_AXIS_IMPOSSIBLE);
   MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                 `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
     CWPS_WALL_AXIS_IMPOSSIBLE)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]));;

(* Lean: shallow *)
let CWC_SHALLOW = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ lcont cR sR uR vR aR /\
     &0 < cA /\ &0 <= sA /\ sA <= cA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     ~linside cA sA uA vA aA (&12 / &5) (&3) /\
     ~linside cA sA uA vA aA (&5 / &2) (&3) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  ASM_CASES_TAC `(&16 / &25) * cA <= sA` THENL
  [UNDISCH_TAC `~linside cA sA uA vA aA (&2) (&2)` THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC CES_SHALLOW_CENTER THEN
   MAP_EVERY EXISTS_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `exists z. (&1 + cA) * z = sA /\ sA * z = &1 - cA /\ &0 <= z`
  STRIP_ASSUME_TAC THENL
  [EXISTS_TAC `sA / (&1 + cA)` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < cA` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < cA` THEN UNDISCH_TAC `cA * cA + sA * sA = &1` THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `z:real`]
    CWE_CROSSING_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  UNDISCH_TAC `~linside cA sA uA vA aA (&2) (&2)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CWC_CENTER_OF_CROSSING THEN
  MAP_EVERY EXISTS_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                        `z:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: right_high *)
let CWC_RIGHT_HIGH = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&1543 / &500) (&2) /\
     linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&113 / &50) (&2)
     ==> linside c s u v a (&3) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--c:real`; `s:real`; `u - &4 * c:real`; `--v - a - &4 * s:real`;
                `a:real`] WLR_POINT) THEN
  ASM_SIMP_TAC[LINSIDE_PULLX; LCONT_PULLX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `&3`; `&12 / &5`; `&3`; `&64 / &25`; `&5 / &8`] CES_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: point *)
let CWC_POINT = prove
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
     ~linside cR sR uR vR aR (&3) (&87 / &50) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aT`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] CWC_RIGHT_HIGH) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aA` THEN REWRITE_TAC[ldisj] THEN
   ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`sT:real`; `cT:real`; `uT:real`; `--vT - aA:real`; `aA:real`]
    CWC_RIGHT_HIGH) THEN
  ASM_SIMP_TAC[LINSIDE_PULLSW; LCONT_PULLSW] THEN ANTS_TAC THENL
  [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `ldisj cA sA uA vA aA cT sT uT vT aA` THEN REWRITE_TAC[ldisj] THEN
   ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = aA`)) THEN
  SUBGOAL_THEN
   `linside c' s' u' v' aA (&2) (&113 / &50) /\
    linside c' s' u' v' aA (&113 / &50) (&2) /\
    linside c' s' u' v' aA (&47 / &20) (&47 / &20) /\
    ~linside c' s' u' v' aA (&47 / &20) (&33 / &20) /\
    ~linside c' s' u' v' aA (&33 / &20) (&47 / &20) /\
    ~linside c' s' u' v' aA (&3) (&12 / &5) /\
    ~linside c' s' u' v' aA (&12 / &5) (&3) /\
    ~linside c' s' u' v' aA (&3) (&5 / &2) /\
    ~linside c' s' u' v' aA (&5 / &2) (&3) /\
    ldisj c' s' u' v' aA cR sR uR vR aA /\
    ldisj c' s' u' v' aA cT sT uT vT aA`
  STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[ldisj] THEN
   UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aA` THEN
   UNDISCH_TAC `ldisj cA sA uA vA aA cT sT uT vT aA` THEN
   REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) then REWRITE_TAC[GSYM th]
     else NO_TAC) THEN
  ASM_CASES_TAC `s' <= c'` THENL
  [MATCH_MP_TAC CWC_SHALLOW THEN
   MAP_EVERY EXISTS_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] THEN
   ASM_REWRITE_TAC[];
   MP_TAC(SPECL [`s':real`; `c':real`; `u':real`; `--v' - aA:real`; `aA:real`;
                 `sT:real`; `cT:real`; `uT:real`; `--vT - aA:real`; `aA:real`]
     CWC_SHALLOW) THEN
   ASM_SIMP_TAC[LINSIDE_PULLSW; LCONT_PULLSW] THEN
   UNDISCH_TAC `ldisj c' s' u' v' aA cT sT uT vT aA` THEN
   REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]]);;
