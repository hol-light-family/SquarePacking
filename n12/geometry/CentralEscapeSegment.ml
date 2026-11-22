(* ========================================================================= *)
(* Port of Compact/Geometry/CentralEscapeSegment.lean (Jatloe, N12-jatloe).   *)
(* A genuine neighbouring wall segment excludes the middle-angle escape of   *)
(* an elbow square from the container centre.                                *)
(* Also ports S12.inside_segment (source/S12/Convex.lean); short_projections *)
(* is WFP_SHORT_PROJECTIONS; pullSwap is LINSIDE_PULLSW (p2_base).           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: S12.inside_segment (source/S12/Convex.lean) *)
let CES_INSIDE_SEGMENT = prove
 (`forall c s u v a x y x' y' t.
     linside c s u v a x y /\ linside c s u v a x' y' /\ &0 <= t /\ t <= &1
     ==> linside c s u v a ((&1 - t) * x + t * x') ((&1 - t) * y + t * y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c * ((&1 - t) * x + t * x') + s * ((&1 - t) * y + t * y') =
      (&1 - t) * (c * x + s * y) + t * (c * x' + s * y') /\
    --s * ((&1 - t) * x + t * x') + c * ((&1 - t) * y + t * y') =
      (&1 - t) * (--s * x + c * y) + t * (--s * x' + c * y')`
  (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC REAL_CONVEX_BOUND_LT ORELSE MATCH_MP_TAC REAL_CONVEX_BOUND_GT) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: shallow_center *)
let CES_SHALLOW_CENTER = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ &0 < cA /\ &0 <= sA /\ sA <= cA /\ (&16 / &25) * cA <= sA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&12 / &5) (&3) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `&1543 / &500`; `&2`; `&3`; `&12 / &5`; `&23 / &40`]
    CES_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `&12731 / &20000`; `--(&77 / &100)`]
    WFP_SHORT_PROJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&7 / &10) * (cA + sA) <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `cA - sA:real`; SQ_NONNEG `(&7 / &10) * (cA + sA) - &1`];
   ALL_TAC] THEN
  SUBGOAL_THEN `(&20731 / &20000) * cA + (&23 / &100) * sA <= &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (sA - &16 / &25 * cA) * (sA + &13 / &100 * cA) /\
                 &0 <= cA * sA` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   NLIN_FACTS_TAC [SQ_NONNEG `cA:real`]
    [`((&20731 / &20000) * cA + (&23 / &100) * sA) *
      ((&20731 / &20000) * cA + (&23 / &100) * sA) <= &1`] THEN
   NLIN_TAC []; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) ||
     (try fst(dest_const(fst(strip_comb(concl th)))) = "ldisj" with _ -> false))) THEN
  REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`&60731 / &20000`; `&223 / &100`]) THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* Lean: angle_alternatives *)
let CES_ANGLE_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cR sR uR vR aR cT sT uT vT aT.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aA /\ &0 < cA /\ &0 <= sA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&3) (&12 / &5) /\
     ~linside cA sA uA vA aA (&12 / &5) (&3) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cA sA uA vA aA cT sT uT vT aT /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> sA < (&16 / &25) * cA \/ cA < (&16 / &25) * sA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `sA <= cA` THENL
  [DISJ1_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                 `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
     CES_SHALLOW_CENTER) THEN
   ASM_REWRITE_TAC[];
   DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`sA:real`; `cA:real`; `uA:real`; `--vA - aA:real`; `aA:real`;
                 `sT:real`; `cT:real`; `uT:real`; `--vT - aT:real`; `aT:real`]
     CES_SHALLOW_CENTER) THEN
   ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN
   UNDISCH_TAC `ldisj cA sA uA vA aA cT sT uT vT aT` THEN
   REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC]);;
