(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareAForced.lean (Jatloe N12).             *)
(* Direct forced point (2,5/2) for a positive shallow square A.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: S12.short_projections (source/S12/ShortCluster/Projections.lean) *)
let FSAF_SHORT_PROJECTIONS = prove
 (`forall c s dx dy. c * c + s * s = &1 /\ dx pow 2 + dy pow 2 <= &1
     ==> --(&1) <= c * dx + s * dy /\ c * dx + s * dy <= &1 /\
         --(&1) <= --s * dx + c * dy /\ --s * dx + c * dy <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c * dx + s * dy) pow 2 + (--s * dx + c * dy) pow 2 <= &1`
  MP_TAC THENL
   [SUBGOAL_THEN `(c * dx + s * dy) pow 2 + (--s * dx + c * dy) pow 2 =
                  (c * c + s * s) * (dx pow 2 + dy pow 2)` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ASM_REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  SPEC_TAC(`c * dx + s * dy`,`p:real`) THEN
  SPEC_TAC(`--s * dx + c * dy`,`q:real`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `p:real`; SQ_NONNEG `q:real`]);;

let FSAF_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  STRIP_TAC;;

(* Lean: row_point *)
let FSAF_ROW_POINT = prove
 (`forall c s u v a.
      lclosed c s u v a (&2) (&113 / &50) /\ linside c s u v a (&2) (&5 / &2)
      ==> linside c s u v a (&2) (&12 / &5)`,
  REWRITE_TAC[lclosed; linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_wide_point *)
let FSAF_POSITIVE_WIDE_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 < s /\ &20 * s <= &99 * c /\
      lclosed c s u v a (&2) (&113 / &50) /\
      lclosed c s u v a (&113 / &50) (&2) /\
      lclosed c s u v a (&47 / &20) (&47 / &20) /\
      ~linside c s u v a (&47 / &20) (&33 / &20) /\
      ~linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&3) (&12 / &5)
      ==> linside c s u v a (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FSAF_SP_TAC `-- &7 / &20` `&17 / &20` THEN
  FSAF_SP_TAC `&13 / &20` `&3 / &4` THEN
  FSAF_SP_TAC `&7 / &20` `&3 / &20` THEN
  SUBGOAL_THEN `s + c / &10 <= &1 /\ &7 / &10 * (c + s) <= &1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= c * (&99 * c - &20 * s)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - s:real`];
    ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[lclosed; linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_shallow_point *)
let FSAF_POSITIVE_SHALLOW_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 <= c /\ &0 < s /\ s <= c /\
      lclosed c s u v a (&2) (&113 / &50) /\
      lclosed c s u v a (&113 / &50) (&2) /\
      lclosed c s u v a (&47 / &20) (&47 / &20) /\
      ~linside c s u v a (&47 / &20) (&33 / &20) /\
      ~linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&3) (&12 / &5)
      ==> linside c s u v a (&2) (&5 / &2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FSAF_POSITIVE_WIDE_POINT THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: of_foreign_closed *)
let FSAF_OF_FOREIGN_CLOSED = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cR sR uR vR aR.
      cA * cA + sA * sA = &1 /\ &1 < aA /\
      cB * cB + sB * sB = &1 /\ &0 < aB /\
      cR * cR + sR * sR = &1 /\ &0 < aR /\
      &0 <= cA /\ &0 < sA /\ sA <= cA /\
      lclosed cA sA uA vA aA (&2) (&113 / &50) /\
      lclosed cA sA uA vA aA (&113 / &50) (&2) /\
      lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
      ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
      lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
      lclosed cR sR uR vR aR (&3) (&12 / &5) /\
      ldisj cA sA uA vA aA cB sB uB vB aB /\
      ldisj cA sA uA vA aA cR sR uR vR aR
      ==> linside cA sA uA vA aA (&2) (&5 / &2)`,
  REWRITE_TAC[ldisj] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FSAF_POSITIVE_SHALLOW_POINT THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC OUTSIDE_OF_CLOSED THENL
   [MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];
    MAP_EVERY EXISTS_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: axis_point *)
let FSAF_AXIS_POINT = prove
 (`forall c s u v a.
      &1 < a /\ c = &1 /\ s = &0 /\
      lclosed c s u v a (&2) (&113 / &50) /\
      lclosed c s u v a (&113 / &50) (&2) /\
      lclosed c s u v a (&47 / &20) (&47 / &20) /\
      ~linside c s u v a (&33 / &20) (&33 / &20) /\
      ~linside c s u v a (&47 / &20) (&33 / &20) /\
      ~linside c s u v a (&3) (&12 / &5)
      ==> linside c s u v a (&2) (&5 / &2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[lclosed; linside] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* Lean: wide_with_axis *)
let FSAF_WIDE_WITH_AXIS = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cR sR uR vR aR.
      cA * cA + sA * sA = &1 /\ &1 < aA /\
      cB * cB + sB * sB = &1 /\ &0 < aB /\
      cR * cR + sR * sR = &1 /\ &0 < aR /\
      &0 <= cA /\ &0 <= sA /\ &20 * sA <= &99 * cA /\
      lclosed cA sA uA vA aA (&2) (&113 / &50) /\
      lclosed cA sA uA vA aA (&113 / &50) (&2) /\
      lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
      ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
      ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
      lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
      lclosed cR sR uR vR aR (&3) (&12 / &5) /\
      ldisj cA sA uA vA aA cB sB uB vB aB /\
      ldisj cA sA uA vA aA cR sR uR vR aR
      ==> linside cA sA uA vA aA (&2) (&5 / &2)`,
  REWRITE_TAC[ldisj] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~linside cA sA uA vA aA (&3) (&12 / &5)` ASSUME_TAC THENL
   [MATCH_MP_TAC OUTSIDE_OF_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `sA = &0` THENL
   [MATCH_MP_TAC FSAF_AXIS_POINT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cA * cA + sA * sA = &1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN NLIN_TAC [];
    MATCH_MP_TAC FSAF_POSITIVE_WIDE_POINT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC OUTSIDE_OF_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* Lean: shallow_with_axis *)
let FSAF_SHALLOW_WITH_AXIS = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cR sR uR vR aR.
      cA * cA + sA * sA = &1 /\ &1 < aA /\
      cB * cB + sB * sB = &1 /\ &0 < aB /\
      cR * cR + sR * sR = &1 /\ &0 < aR /\
      &0 <= cA /\ &0 <= sA /\ sA <= cA /\
      lclosed cA sA uA vA aA (&2) (&113 / &50) /\
      lclosed cA sA uA vA aA (&113 / &50) (&2) /\
      lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
      ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
      ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
      lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
      lclosed cR sR uR vR aR (&3) (&12 / &5) /\
      ldisj cA sA uA vA aA cB sB uB vB aB /\
      ldisj cA sA uA vA aA cR sR uR vR aR
      ==> linside cA sA uA vA aA (&2) (&5 / &2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FSAF_WIDE_WITH_AXIS THEN
  MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
