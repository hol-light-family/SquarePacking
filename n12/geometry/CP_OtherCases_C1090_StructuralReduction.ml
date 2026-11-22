(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/StructuralReduction.lean     *)
(* (namespace N12Compact.Completion.OtherCases.C1090.Structural; Lean header:*)
(* "All sources remain uncompiled").  Sections 7--8 of C1090-SIMPLIFIED-     *)
(* PROOF: the point table (c1090es_pointTable) forces S's G6 and E's F7 and  *)
(* hence Residual.Input (c1090ro_input); Early.Input (c1090eg_input) is      *)
(* impossible.  q : Fin 12 -> OpenSquare as in StructuralGeometry.ml (qc qs  *)
(* qu qv qa, unit normals as the hypothesis !i. i < 12 ==> qc i * qc i +     *)
(* qs i * qs i = &1).  Early.residual_input = C1090ER_RESIDUAL_INPUT,        *)
(* Early.point_table = C1090ES_POINT_TABLE, Residual.impossible =            *)
(* C1090RE_IMPOSSIBLE, h.apart = C1090EG_FOREIGN.  Tag C1090SR_.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1090_StructuralGeometry.ml";;
needs "n12/geometry/CP_OtherCases_C1090_EarlyResidual.ml";;

let C1090SR_TABLE_INPUT = prove
 (`forall qc qs qu qv qa. c1090es_pointTable qc qs qu qv qa ==> c1090eg_input qc qs qu qv qa`,
  SIMP_TAC[c1090es_pointTable]);;

let C1090SR_USE_TAC thl =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC (SPEC_ALL th)) thl THEN ASM_REWRITE_TAC[];;

(* Lean: southeast_g6 *)
let C1090SR_SOUTHEAST_G6 = prove
 (c1090sg_stmt [] (c1090sg_in 5 `&113 / &50` `&2`),
  C1090SR_USE_TAC [C1090SG_OUTWARD_MIXED_IMPOSSIBLE; C1090SG_OUTWARD_TOP_ONLY_IMPOSSIBLE;
                   C1090SG_NORTHEAST_F5_OR_F7] THEN
  CONV_TAC TAUT);;

(* Lean: northeast_f7 *)
let C1090SR_NORTHEAST_F7 = prove
 (c1090sg_stmt [] (c1090sg_in 6 `&12 / &5` `&3`),
  C1090SR_USE_TAC [C1090SG_NORTHEAST_ELBOW_IMPOSSIBLE; C1090SG_NORTHEAST_F5_OR_F7] THEN
  CONV_TAC TAUT);;

(* Lean: central_points *)
let C1090SR_CENTRAL_POINTS = prove
 (c1090sg_stmt [] (list_mk_conj [c1090sg_in 5 `&113 / &50` `&2`; c1090sg_in 6 `&12 / &5` `&3`;
                                 mk_neg (c1090sg_in 5 `&2` `&113 / &50`);
                                 mk_neg (c1090sg_in 6 `&113 / &50` `&2`)]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (c1090sg_in 5 `&113 / &50` `&2`) ASSUME_TAC THENL
   [MP_TAC (SPEC_ALL C1090SR_SOUTHEAST_G6) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC (SPEC_ALL C1090SR_NORTHEAST_F7) THEN
  MP_TAC (SPEC_ALL C1090SG_SOUTHEAST_F5_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1090EG_FOREIGN THEN EXISTS_TAC `5` THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[C1090SR_TABLE_INPUT]);;

(* Lean: residual_input *)
let C1090SR_RESIDUAL_INPUT = prove
 (c1090sg_stmt [] `c1090ro_input qc qs qu qv qa`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1090ER_RESIDUAL_INPUT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C1090SR_SOUTHEAST_G6; MATCH_MP_TAC C1090SR_NORTHEAST_F7] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: impossible_of_early_input *)
let C1090SR_IMPOSSIBLE_OF_EARLY_INPUT = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C1090RE_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1090SR_RESIDUAL_INPUT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C1090ES_POINT_TABLE THEN ASM_REWRITE_TAC[]);;
