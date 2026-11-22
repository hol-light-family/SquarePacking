(* ========================================================================= *)
(* Port of Compact/Geometry/C849NegativeBL.lean (N12Compact.C849NegativeBL). *)
(* The negative-frame B triangle and the actual L square leave two oriented *)
(* separating faces.                                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C849NegativePoints.ml";;
needs "n12/geometry/ABTransverse.ml";;

let C849NBL_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC;;

let C849NBL_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[] THEN ABT_ARITH_TAC;;

(* Lean: left_inward_of_lower_U *)
let C849NBL_LEFT_INWARD_OF_LOWER_U = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ abs s <= c /\ &1 < a /\
     lclosed c s u v a (&457 / &500) (&2) /\
     lclosed c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     c * (&19 / &25) + s * (&187 / &100) <= u
     ==> linside c s u v a (&7 / &5) (&13 / &5)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside] THEN STRIP_TAC THEN
  C849NBL_SP_TAC `&89 / &100` `--(&11 / &50)` THEN
  C849NBL_SP_TAC `&16 / &25` `&73 / &100` THEN
  C849NBL_SP_TAC `--(&1 / &4)` `&19 / &20` THEN
  SUBGOAL_THEN `--s * (&33 / &20) + c * (&33 / &20) <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C849NBL_MISS_TAC [`c * &33 / &20`]; ALL_TAC] THEN
  ABT_ARITH_TAC);;

(* Lean: lower_V *)
let C849NBL_LOWER_V = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ abs s <= c /\ &1 < a /\
     lclosed c s u v a (&457 / &500) (&2) /\
     lclosed c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&19 / &25) (&187 / &100) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&7 / &5) (&13 / &5)
     ==> --s * (&19 / &25) + c * (&187 / &100) <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `u < c * (&19 / &25) + s * (&187 / &100)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&7 / &5) (&13 / &5)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC C849NBL_LEFT_INWARD_OF_LOWER_U THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside]) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C849NBL_MISS_TAC [`c * &19 / &25`]);;

(* Lean: inward_V_band *)
let C849NBL_INWARD_V_BAND = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ abs s <= c /\ &1 < a /\
     lclosed c s u v a (&457 / &500) (&2) /\
     --s * (&19 / &25) + c * (&187 / &100) <= v
     ==> v < --s * (&7 / &5) + c * (&13 / &5) /\
         --s * (&7 / &5) + c * (&13 / &5) < v + a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed] THEN STRIP_TAC THEN
  C849NBL_SP_TAC `&16 / &25` `&73 / &100` THEN ABT_ARITH_TAC);;

(* Lean: alternatives *)
let C849NBL_ALTERNATIVES = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cB /\ sB <= &0 /\ --sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     &1 < aB /\ aB = aL /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     ~linside cB sB uB vB aB (&2) (&5 / &2) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     ldisj cB sB uB vB aB cL sL uL vL aL
     ==> (--sL * (&19 / &25) + cL * (&187 / &100) <= vL) /\
         (ABT_upper cL sL uL vL aL (--sB) cB <= vB \/
          uL + aL <= ABT_lower cB sB uB vB aB cL sL)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C849NP_INWARD_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C849NP_UPPER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `--sL * (&19 / &25) + cL * (&187 / &100) <= vL` ASSUME_TAC THENL
   [MATCH_MP_TAC C849NBL_LOWER_V THEN EXISTS_TAC `uL:real` THEN EXISTS_TAC `aL:real` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ABT_ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `ldisj cB sB uB vB aB cL sL uL vL aL` THEN
      REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&7 / &5`; `&13 / &5`]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
    C849NBL_INWARD_V_BAND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ABT_ARITH_TAC; STRIP_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `sB:real`] [`cB <= &1`] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aB:real = aL`)) THEN
  let sB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
  and sL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] in
  let dirs = [`cB:real`,`sB:real`; `--sB`,`cB:real`; `cL:real`,`sL:real`; `--sL`,`cL:real`] in
  ABT_ALL_SB_TAC [sB,(`&33 / &20`,`&47 / &20`); sB,(`&7 / &5`,`&13 / &5`)] dirs THEN
  ABT_ALL_CB_TAC [sL,(`&457 / &500`,`&2`); sL,(`&1`,`&12 / &5`)] dirs THEN
  ABT_OWN_TAC sB THEN ABT_OWN_TAC sL THEN ABT_ARITH_TAC);;
