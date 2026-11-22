(* ========================================================================= *)
(* Port of Compact/Geometry/C849NegativePoints.lean                          *)
(* (N12Compact.C849NegativePoints).  Consequences of the negative-frame B    *)
(* triangle.                                                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C849PositiveAbove.ml";;
needs "n12/geometry/FourSquareAForced.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: upper_face *)
let C849NP_UPPER_FACE = prove
 (`forall c s u v a.
     &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&2) (&1543 / &500) /\
     ~linside c s u v a (&2) (&5 / &2)
     ==> u + a <= &2 * c + (&5 / &2) * s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: inward_point *)
let C849NP_INWARD_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ s <= &0 /\ --s <= c /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&2) (&1543 / &500) /\
     ~linside c s u v a (&2) (&5 / &2)
     ==> linside c s u v a (&7 / &5) (&13 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C849NP_UPPER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&3 / &5`; `--(&1 / &10)`] FSAF_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN ABT_ARITH_TAC);;

(* Lean: right_faces *)
let C849NP_RIGHT_FACES = prove
 (`forall c s u v a.
     &0 < c /\ s <= &0 /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     lclosed c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&113 / &50) (&3)
     ==> u + a <= (&113 / &50) * c + &3 * s \/
         v + a <= --(&113 / &50) * s + &3 * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside; lclosed] THEN REAL_ARITH_TAC);;
