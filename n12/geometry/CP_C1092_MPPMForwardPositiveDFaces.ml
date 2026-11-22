(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMForwardPositiveDFaces.lean            *)
(* (N12Compact.C1092MPPMForwardPositiveD).  Actual predecessor face exits in *)
(* C1092-POSITIVE-D-TRANSFER section 2.  Square C is c s u v a; the         *)
(* structure Predecessor is the predicate c1092fpdf_predecessor.  Tag        *)
(* C1092FPDF_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMForwardPositiveDScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: Predecessor (structure) *)
let c1092fpdf_predecessor = new_definition
 `c1092fpdf_predecessor c s u v a <=>
    linside c s u v a (&33 / &20) (&33 / &20) /\
    linside c s u v a (&1) (&87 / &50) /\
    linside c s u v a (&1) (&8 / &5) /\
    linside c s u v a (&87 / &50) (&2) /\
    ~linside c s u v a (&1) (&3 / &2) /\
    ~linside c s u v a (&33 / &20) (&47 / &20) /\
    ~linside c s u v a (&457 / &500) (&2) /\
    ~linside c s u v a (&1) (&113 / &50)`;;

let C1092FPDF_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: predecessor_faces *)
let C1092FPDF_PREDECESSOR_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\ c1092fpdf_predecessor c s u v a
     ==> c + (&3 / &2) * s <= u /\
         exists f. v + a <= f /\ c1092fpd_coefficients c s f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092fpdf_predecessor] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (&33 / &20) (&33 / &20)`;
    `linside c s u v a (&1) (&87 / &50)`;
    `linside c s u v a (&1) (&8 / &5)`;
    `linside c s u v a (&87 / &50) (&2)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `--s + (&3 / &2) * c <= v` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092FPDF_MISS_TAC `~linside c s u v a (&1) (&3 / &2)`; ALL_TAC] THEN
    SUBGOAL_THEN `&13 * s < &3 * c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `v + a <= --(&33 / &20) * s + (&47 / &20) * c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092FPDF_MISS_TAC `~linside c s u v a (&33 / &20) (&47 / &20)`; ALL_TAC] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&113 / &50) * c - s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092FPDF_MISS_TAC `~linside c s u v a (&1) (&113 / &50)`; ALL_TAC] THEN
  ASM_CASES_TAC `(&457 / &500) * c + &2 * s <= u` THENL
   [EXISTS_TAC `(&113 / &50) * c - s` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C1092FPD_REGIME_ONE THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    EXISTS_TAC `&2 * c - (&457 / &500) * s` THEN
    ASM_SIMP_TAC[C1092FPD_REGIME_TWO] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092FPDF_MISS_TAC `~linside c s u v a (&457 / &500) (&2)`]);;
