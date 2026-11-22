(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1091/ResidualInput.lean           *)
(* (namespace N12Compact.Completion.OtherCases.C1091.Residual).             *)
(* Literal residual point table of C1091 §2.                                 *)
(* q : Fin 12 -> OpenSquare is written as five coordinate functions          *)
(*   qc qs qu qv qa : num -> real,  q i = (qc i, qs i, qu i, qv i, qa i),    *)
(* with i ranging over i < 12.  (q i).Inside x y  is                         *)
(*   linside (qc i) (qs i) (qu i) (qv i) (qa i) x y.                         *)
(* For the packing, Lean  owners p  is  qc = \i. ooc c1 c2 a b l (EL i      *)
(* masks)  etc. (OriginalData).                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_MergedMarkerSeedWall.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: Input (structure) *)
let c1091ri_input = new_definition
 `c1091ri_input (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i. i < 12 ==> qa i <= &1001 / &1000) /\
    (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
    (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&1) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&3) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&457 / &500) (&1) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&3 / &2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&5 / &2) (&2) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&12 / &5) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&113 / &50) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&12 / &5) /\
    (forall x. &113 / &50 <= x /\ x <= &14 / &5
         ==> linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) x (&1)) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&1543 / &500) (&2) /\
    (forall y. &36 / &25 <= y /\ y <= &2
         ==> linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) y) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&12 / &5) (&3)`;;

(* Lean: Input.foreign *)
let C1091RI_FOREIGN = prove
 (`forall qc qs qu qv qa i j x y.
     c1091ri_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (qc j) (qs j) (qu j) (qv j) (qa j) x y
     ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REWRITE_TAC[c1091ri_input] THEN MESON_TAC[]);;

(* Lean: Input.southeast_cut *)
let C1091RI_SOUTHEAST_CUT = prove
 (`forall qc qs qu qv qa. c1091ri_input qc qs qu qv qa
     ==> linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&12 / &5) (&2)`,
  REWRITE_TAC[c1091ri_input] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&2`; `&5 / &2`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
