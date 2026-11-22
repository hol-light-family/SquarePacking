(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightCornerReachAxes.lean                   *)
(* (N12Compact.UpperRightCornerReachAxes).  Under the negated corner reach   *)
(* the NE corner E and the top square T have three directed SAT axes.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: lower_face *)
let URCRA_LOWER_FACE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ &0 <= s /\ s <= c /\ &1 < a /\
     linside c s u v a (&3) (&3) /\
     linside c s u v a (&16 / &5) (&3) /\
     ~linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&7 / &2) (&3)
     ==> (&12 / &5) * c - &3 * s <= v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `(&3 / &5) * c - (&1 / &2) * s`]
   [`((&1 / &2) * c + (&3 / &5) * s) * ((&1 / &2) * c + (&3 / &5) * s) <= &61 / &100`] THEN
  NLIN_FACTS_TAC [] [`(&1 / &2) * c + (&3 / &5) * s < &1`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 * c + (&12 / &5) * s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term ((=) `s * &12 / &5`)) (concl th))) THEN
    REWRITE_TAC[] THEN ABT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&7 / &2) * c + &3 * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term ((=) `c * &7 / &2`)) (concl th))) THEN
    REWRITE_TAC[] THEN ABT_ARITH_TAC;
    ALL_TAC] THEN
  ABT_ARITH_TAC);;

(* Lean: not_corner_transverse *)
let URCRA_NOT_CORNER_TRANSVERSE = prove
 (`forall cE sE uE vE aE cT sT uT vT aT.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     &0 < cE /\ &0 <= sE /\ &1 < aE /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     (&12 / &5) * cE - &3 * sE <= vE /\
     (ABT_upper cE sE uE vE aE (--sE) cE <= ABT_lower cT sT uT vT aT (--sE) cE \/
      ABT_upper cT sT uT vT aT (--sE) cE <= ABT_lower cE sE uE vE aE (--sE) cE)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `cE - sE`]
   [`(cE + sE) * (cE + sE) <= &2`; `(&3 / &5) * (cE + sE) < &1`] THEN
  let sE = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
  and sT = [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`] in
  ABT_ALL_SB_TAC [sE,(`&3`,`&3`); sT,(`&2`,`&1543 / &500`); sT,(`&12 / &5`,`&3`)]
    [`--sE`,`cE:real`] THEN
  ABT_OWN_TAC sE THEN ABT_ARITH_TAC);;

(* Lean: alternatives *)
let URCRA_ALTERNATIVES = prove
 (`forall cE sE uE vE aE cT sT uT vT aT.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     &0 < cE /\ &0 <= sE /\ sE <= cE /\
     &0 < cT /\ &0 <= sT /\ sT <= cT /\
     aE = aT /\ &1 < aE /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     ~linside cE sE uE vE aE (&3) (&12 / &5) /\
     ~linside cE sE uE vE aE (&7 / &2) (&3) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ldisj cE sE uE vE aE cT sT uT vT aT
     ==> ABT_upper cT sT uT vT aT cE sE <= uE \/
         uT + aT <= ABT_lower cE sE uE vE aE cT sT \/
         ABT_upper cE sE uE vE aE (--sT) cT <= vT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URCRA_LOWER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `cE - sE`]
   [`(cE + sE) * (cE + sE) <= &2`; `(&3 / &5) * (cE + sE) < &1`] THEN
  ABT_PAIR_TAC "E" "T"
    ["E",(`&3`,`&3`); "T",(`&2`,`&1543 / &500`); "T",(`&12 / &5`,`&3`)]);;
