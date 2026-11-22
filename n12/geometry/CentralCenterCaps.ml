(* ========================================================================= *)
(* Port of Compact/Geometry/CentralCenterCaps.lean                           *)
(* (N12Compact.CentralCenterCaps).  Central-marker exclusions bound both     *)
(* upper faces of a square owning the centre.                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: positive_caps *)
let CCC_POSITIVE_CAPS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ &0 <= s /\ s <= c /\ &1 < a /\
     linside c s u v a (&2) (&2) /\
     linside c s u v a (&3 / &2) (&2) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> u + a <= (&47 / &20) * c + (&33 / &20) * s /\
         v + a <= (&47 / &20) * c - (&33 / &20) * s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v + a <= (&47 / &20) * c - (&33 / &20) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term ((=) `s * &47 / &20`)) (concl th))) THEN
    REWRITE_TAC[] THEN ABT_ARITH_TAC;
    ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`] [`(c + s) * (c + s) <= &2`] THEN
  NLIN_FACTS_TAC [] [`(&7 / &10) * (c + s) < &1`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `v < (&33 / &20) * c - (&47 / &20) * s` THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
      can (find_term ((=) `s * &33 / &20`)) (concl th))) THEN
    REWRITE_TAC[] THEN ABT_ARITH_TAC;
    ABT_ARITH_TAC]);;

(* the diagonal reflection swapFrame of the Lean proof *)
let CCC_INSIDE_SWAP = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: signed_caps *)
let CCC_SIGNED_CAPS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ abs s <= c /\ &1 < a /\
     linside c s u v a (&2) (&2) /\
     linside c s u v a (&3 / &2) (&2) /\
     linside c s u v a (&2) (&3 / &2) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> u + a <= (&47 / &20) * c + (&33 / &20) * s /\
         v + a <= (&47 / &20) * c - (&33 / &20) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 <= s` THENL
   [MATCH_MP_TAC CCC_POSITIVE_CAPS THEN ASM_REWRITE_TAC[] THEN ABT_ARITH_TAC;
    MP_TAC(SPECL [`c:real`; `--s`; `v:real`; `u:real`; `a:real`] CCC_POSITIVE_CAPS) THEN
    ASM_REWRITE_TAC[CCC_INSIDE_SWAP] THEN
    ANTS_TAC THENL [ABT_ARITH_TAC; ABT_ARITH_TAC]]);;
