(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976/ResidualEnding.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C976).  The continuous C976   *)
(* ending on the literal actual-owner point table Data =                     *)
(* C976MergedLeft.ActualOwners.Data (c976mlao_data).  Conventions of         *)
(* CP_OtherCases_C976LeftTop_ActualOwners.ml: q : Fin 12 -> OpenSquare is    *)
(* qc qs qu qv qa : num -> real with the unit-normal hypothesis C976AO_UNIT; *)
(* auxiliary OpenSquares N, R, W are 5-tuples with explicit unit normal and  *)
(* positive side.  q.translated x y is                                       *)
(* (c, s, u - (c * x + s * y), v - (--s * x + c * y), a)                      *)
(* (C976AO_INSIDE_TRANSLATED); turnFrame (c, s, u, v, a) is                  *)
(* (--s, c, v, --u - a, a) (C976RE_TURN_INSIDE).  Used: C976NegativeTop      *)
(* .angle / Alternative (C976NTM_ANGLE, cc976f_alternative),                 *)
(* C976MergedLeft.ActualOwners (C976MLAO_ thms), C976LeftTop.ActualOwners   *)
(* (C976AO_ thms), ClosedFrames.canonical_frame (CLF_CANONICAL_FRAME),       *)
(* C981CompletionCornerAdvance.upper_wall (C981CA_UPPER_WALL).               *)
(* steep_negative_top is obtained from C976AO_STEEP_NEGATIVE_TOP applied to  *)
(* the family q with q 11 replaced by W (same inside set, same side).        *)
(* Tag C976RE_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_ActualOwners.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_Main.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;

(* Lean: S12.turnFrame_inside *)
let C976RE_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* a forward fact (hyps C976AO_UNIT, c976mlao_data [, c976ao_data]) as an assumption *)
let C976RE_FACT_TAC th = ASSUME_TAC (c976mlao_fix th);;
let c976re_field i x y =
  try c976mlao_field i x y with Failure _ -> c976mlao_fix (c976ao_field i x y);;

(* the wall of q 11 in the chart translated by (2, 3) *)
let c976re_wall () =
  let b = REWRITE_RULE[lcont] (c976ao_box 11) in
  let tm = c976ao_in 11 `&2 + x` `&3 + y` in
  GENL [`x:real`; `y:real`]
    (DISCH tm (c976ao_arith [UNDISCH (SPECL [`&2 + x`; `&3 + y`] b)] `y <= &1`));;

(* Lean: negative_alternative *)
let C976RE_NEGATIVE_ALTERNATIVE = prove
 (`forall qc qs qu qv qa cN sN uN vN aN.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c976mlao_data qc qs qu qv qa /\
     cN * cN + sN * sN = &1 /\ &0 < aN /\
     (forall x y. linside cN sN uN vN aN x y <=>
            linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2 + x) (&3 + y))
     ==> cc976f_alternative cN sN uN vN aN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cc976f_alternative] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_CASES_TAC `linside ((qc:num->real) 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)` THEN
  ASM_REWRITE_TAC[] THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MP_TAC(SPECL (c976ao_q 6 @ [`&113 / &50`; `&5 / &2`; `&2`; `&2 + x`]) OO_HORIZONTAL_SEGMENT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ACCEPT_TAC (c976re_field 6 `&113 / &50` `&2`);
        ACCEPT_TAC (c976re_field 6 `&5 / &2` `&2`);
        CONV_TAC REAL_RAT_REDUCE_CONV; RASM_ARITH_TAC; RASM_ARITH_TAC];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`&2 + x`; `&2`] (c976mlao_fix (c976ao_apart 7 6))) THEN
    ASM_REWRITE_TAC[];
    ACCEPT_TAC (c976mlao_fix (c976ao_apply ALL_CONV
      (SPECL (c976ao_q 7) OCTOLP_POINT_ORIGINAL)
      (let g = c976mlao_field and missing = ASSUME
         (mk_neg (c976ao_in 7 `&2` `&113 / &50`)) in
       [c976ao_unit 7; c976ao_pos 7; c976ao_side 7; g 7 `&47 / &20` `&47 / &20`;
        c976ao_field 7 `&113 / &50` `&3`; c976mlao_northeast_sharp missing; missing;
        c976ao_excl 7 11 (c976ao_top_origin ()); c976ao_excl 7 3 (g 3 `&3` `&3`);
        c976mlao_bar_excl ()])))]);;

(* the family q with q 11 replaced by a square of the same inside set and side *)
let C976RE_REPLACE = prove
 (`forall qc qs qu qv (qa:num->real) cW sW uW vW k.
     (forall x y. linside cW sW uW vW (qa k) x y <=> linside (qc k) (qs k) (qu k) (qv k) (qa k) x y)
     ==> forall i x y. linside (if i = k then cW else qc i) (if i = k then sW else qs i)
                         (if i = k then uW else qu i) (if i = k then vW else qv i) (qa i) x y <=>
                 linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* Lean: steep_negative_top *)
let C976RE_STEEP_NEGATIVE_TOP = prove
 (`forall qc qs qu qv qa cW sW uW vW aW.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c976mlao_data qc qs qu qv qa /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\ aW = qa 11 /\
     (forall x y. linside cW sW uW vW aW x y <=> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) x y) /\
     &0 < cW /\ sW <= &0
     ==> (&2 / &3) * cW < --sW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW = (qa:num->real) 11`)) THEN
  ASSUME_TAC (c976mlao_to_data ()) THEN
  MP_TAC(SPECL [`\i. if i = 11 then cW else (qc:num->real) i`;
                `\i. if i = 11 then sW else (qs:num->real) i`;
                `\i. if i = 11 then uW else (qu:num->real) i`;
                `\i. if i = 11 then vW else (qv:num->real) i`; `qa:num->real`]
    C976AO_STEEP_NEGATIVE_TOP) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
    MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                  `qa:num->real`; `cW:real`; `sW:real`; `uW:real`; `vW:real`; `11`]
      C976RE_REPLACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC (list_mk_comb(`c976ao_data`, C976AO_Q)) THEN
    REWRITE_TAC[c976ao_data; lcont] THEN ASM_REWRITE_TAC[]]);;

(* N = R.translated 2 3, T = W.translated 2 3, turnFrame T *)
let c976re_n =
  [`cR:real`; `sR:real`; `uR - (cR * &2 + sR * &3)`; `vR - (--sR * &2 + cR * &3)`; `(qa:num->real) 7`];;
let c976re_t =
  [`cW:real`; `sW:real`; `uW - (cW * &2 + sW * &3)`; `vW - (--sW * &2 + cW * &3)`; `(qa:num->real) 11`];;
let c976re_tt =
  [`--sW:real`; `cW:real`; `vW - (--sW * &2 + cW * &3)`; `--(uW - (cW * &2 + sW * &3)) - (qa:num->real) 11`;
   `(qa:num->real) 11`];;

let C976RE_ANGLE_SIDE_TAC =
  REWRITE_TAC[ldisj; C976RE_TURN_INSIDE; C976AO_INSIDE_TRANSLATED] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    ACCEPT_TAC (c976mlao_fix (c976ao_same 7 11));
    UNDISCH_TAC `cW * cW + sW * sW = &1` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `cR * cR + sR * sR = &1` THEN REAL_ARITH_TAC;
    RASM_ARITH_TAC];;

(* Lean: negative_northeast_impossible *)
let C976RE_NEGATIVE_NORTHEAST_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa cR sR uR vR aR.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c976mlao_data qc qs qu qv qa /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\ aR = qa 7 /\
     (forall x y. linside cR sR uR vR aR x y <=> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) x y) /\
     &0 < cR /\ sR < &0 /\ --sR <= cR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aR = (qa:num->real) 7`)) THEN
  C976RE_FACT_TAC (c976ao_side 7) THEN C976RE_FACT_TAC (c976ao_side 11) THEN
  C976RE_FACT_TAC (c976ao_pos 11) THEN C976RE_FACT_TAC (c976ao_unit 11) THEN
  C976RE_FACT_TAC (c976re_field 7 `&47 / &20` `&47 / &20`) THEN
  C976RE_FACT_TAC (c976re_field 7 `&113 / &50` `&3`) THEN
  C976RE_FACT_TAC (c976ao_excl 7 10 (c976mlao_right_high ())) THEN
  C976RE_FACT_TAC (c976ao_top_origin ()) THEN
  C976RE_FACT_TAC (c976ao_excl 11 8 (CONJUNCT2 (CONJUNCT2 (c976ao_left_points ())))) THEN
  C976RE_FACT_TAC (c976re_wall ()) THEN
  C976RE_FACT_TAC (c976ao_apart 7 11) THEN
  MP_TAC(SPECL (C976AO_Q @ c976re_n) C976RE_NEGATIVE_ALTERNATIVE) THEN
  ASM_REWRITE_TAC[C976AO_INSIDE_TRANSLATED] THEN DISCH_TAC THEN
  MP_TAC(SPECL (c976ao_q 11) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW = (qa:num->real) 11`)) THEN
  ASM_CASES_TAC `&0 <= sW` THENL
   [MP_TAC(SPECL (c976re_n @ c976re_t @ [`--sR:real`]) C976NTM_ANGLE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY C976RE_ANGLE_SIDE_TAC THEN
      MATCH_MP_TAC C981CA_UPPER_WALL THEN REPEAT CONJ_TAC THEN C976RE_ANGLE_SIDE_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `abs sW <= cW` THEN UNDISCH_TAC `&0 <= sW` THEN REAL_ARITH_TAC;
    MP_TAC(SPECL (c976re_n @ c976re_tt @ [`--sR:real`]) C976NTM_ANGLE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY C976RE_ANGLE_SIDE_TAC THEN
      MATCH_MP_TAC C981CA_UPPER_WALL THEN REPEAT CONJ_TAC THEN C976RE_ANGLE_SIDE_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL (C976AO_Q @ [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `(qa:num->real) 11`])
      C976RE_STEEP_NEGATIVE_TOP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC THEN RASM_ARITH_TAC]]);;

(* Lean: impossible *)
let C976RE_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c976mlao_data qc qs qu qv qa
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C976RE_FACT_TAC (c976ao_unit 7) THEN C976RE_FACT_TAC (c976ao_pos 7) THEN
  MP_TAC(SPECL (c976ao_q 7) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN = (qa:num->real) 7`)) THEN
  ASM_CASES_TAC `&0 <= sN` THENL
   [MATCH_MP_TAC C976MLAO_NONNEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC (C976AO_Q @ [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `(qa:num->real) 7`]);
    MATCH_MP_TAC C976RE_NEGATIVE_NORTHEAST_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC (C976AO_Q @ [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `(qa:num->real) 7`])] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs sN <= cN` THEN UNDISCH_TAC `&0 < cN` THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
