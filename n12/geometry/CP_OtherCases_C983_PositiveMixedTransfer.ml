(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/PositiveMixedTransfer.lean     *)
(* (namespace N12Compact.Completion.OtherCases.C983).                        *)
(* The positive mixed-neighbour point in C983-F4-FULL-8208-ENDING.           *)
(* OpenSquare N is c s u v a (see n12/geometry/p2_base.ml); W, T, E are cW.., cT.., cE..   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

let C983PMT_LIN_TAC =
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let C983PMT_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_mixed_transfer *)
let C983PMT_POSITIVE_MIXED_TRANSFER = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&0) (&13 / &50) /\
      linside c s u v a (&13 / &50) (&1) /\
      ~linside c s u v a (&0) (&0) /\
      ~linside c s u v a (&0) (&1) /\
      ~linside c s u v a (&13 / &50) (&0)
      ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`;
                  SQ_NONNEG `c:real`; SQ_NONNEG `s - &1`] [`c <= &1`; `s <= &1`] THEN
  SUBGOAL_THEN `v + a <= c` ASSUME_TAC THENL [C983PMT_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&13 / &50) * s <= v` ASSUME_TAC THENL [C983PMT_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c + (&13 / &50) * s /\ &0 < s` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s < &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 < (c - (&1 - (&13 / &50) * s)) * (c + (&1 - (&13 / &50) * s))`;
      `&0 <= s * ((&2669 / &2500) * s - &13 / &25)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `v < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL [C983PMT_LIN_TAC; ALL_TAC] THEN
  C983PMT_LIN_TAC);;

(* Lean: positive_mixed_original *)
let C983PMT_POSITIVE_MIXED_ORIGINAL = prove
 (`forall c s u v a cW sW uW vW aW cT sT uT vT aT cE sE uE vE aE.
      c * c + s * s = &1 /\ &0 < a /\
      cW * cW + sW * sW = &1 /\ &0 < aW /\
      cT * cT + sT * sT = &1 /\ &0 < aT /\
      cE * cE + sE * sE = &1 /\ &0 < aE /\
      &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&2) (&113 / &50) /\
      linside c s u v a (&113 / &50) (&3) /\
      linside cW sW uW vW aW (&2) (&2) /\
      linside cT sT uT vT aT (&2) (&3) /\
      linside cE sE uE vE aE (&113 / &50) (&2) /\
      ldisj c s u v a cW sW uW vW aW /\
      ldisj c s u v a cT sT uT vT aT /\
      ldisj c s u v a cE sE uE vE aE
      ==> linside c s u v a (&5 / &2) (&3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside c s u v a (&2) (&2) /\ ~linside c s u v a (&2) (&3) /\
                ~linside c s u v a (&113 / &50) (&2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`;
                `v - (--s * &2 + c * &2)`; `a:real`]
    C983PMT_POSITIVE_MIXED_TRANSFER) THEN
  REWRITE_TAC[C983PMT_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
