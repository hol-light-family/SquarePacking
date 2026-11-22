(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMMCancellation.lean                     *)
(* (namespace N12Compact.C1092MMMMCancellation).                             *)
(* The Lean variables B, T are written bw, tw (T is HOL's truth constant).   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMMPairScalars.ml";;

(* Lean: impossible *)
let C1092MMC_IMPOSSIBLE = prove
 (`forall a d r b t bw tw U V.
     c977cc_normal d r /\ c977cc_normal b t /\ c977cc_normal bw tw /\ &1 < a /\
     r < &7 / &50 /\ &99 / &100 < d /\ &9 / &20 < t /\ &9 / &20 < tw /\
     b < &9 / &10 /\ bw < &9 / &10 /\ U < &0 /\ V < &0 /\
     a * (&1 + b * r + t * d) <= b + t + (b * d - t * r) * V - (b * r + t * d) * U /\
     a * (&1 + tw * d - bw * r) <= bw + tw + (bw * d + tw * r) * U - (tw * d - bw * r) * V
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C1092MPS_SINE_BOUND) THEN
  MP_TAC(SPECL [`bw:real`; `tw:real`] C1092MPS_SINE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC
   [`&0 <= b * r`; `&0 < t * d`; `&0 < tw * (d - &99 / &100)`;
    `&0 <= r * (&9 / &10 - bw)`; `&0 < bw * (d - &99 / &100)`; `&0 <= tw * r`;
    `&0 <= (&5 / &7 - t) * (&1 - d)`; `&0 <= (&5 / &7 - tw) * (&1 - d)`;
    `&0 <= (b - t) * bw`; `&0 <= t * (bw - tw)`] THEN
  SUBGOAL_THEN `(b * r + t * d) pow 2 + (b * d - t * r) pow 2 = &1 /\
                (b * d - t * r) * (bw * d + tw * r) - (b * r + t * d) * (tw * d - bw * r) =
                b * bw - t * tw` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  ABBREV_TAC `ae = b * d - t * r` THEN
  ABBREV_TAC `aw = bw * d + tw * r` THEN
  ABBREV_TAC `ke = b * r + t * d` THEN
  ABBREV_TAC `kw = tw * d - bw * r` THEN
  SUBGOAL_THEN `&0 < ke /\ &0 <= kw /\ &693 / &1000 < aw` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ke"; "kw"; "aw"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ke <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `ae:real`; SQ_NONNEG `ke - &1`]; ALL_TAC] THEN
  ABBREV_TAC `DE = &1 + ke - b - t` THEN
  ABBREV_TAC `DW = &1 + kw - bw - tw` THEN
  SUBGOAL_THEN `&13 / &140 < DE /\ --(&29 / &875) < DW` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["DE"; "DW"; "ke"; "kw"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&29 / &875) < ke * DW` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= DW` THENL
     [C1092MPS_PROD_TAC [`&0 <= ke * DW`] THEN ASM_REAL_ARITH_TAC;
      C1092MPS_PROD_TAC [`&0 <= (&1 - ke) * --DW`] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  C1092MPS_PROD_TAC [`&0 < (aw - &693 / &1000) * DE`] THEN
  SUBGOAL_THEN `&4369 / &140000 < aw * DE + ke * DW` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MPS_PROD_TAC [`&0 < (a - &1) * (&1 + ke)`; `&0 < (a - &1) * (&1 + kw)`] THEN
  SUBGOAL_THEN `DE < ae * V - ke * U /\ DW < aw * U - kw * V` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["DE"; "DW"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MPS_PROD_TAC [`&0 < aw * ((ae * V - ke * U) - DE)`;
                     `&0 < ke * ((aw * U - kw * V) - DW)`;
                     `&0 <= (b * bw - t * tw) * --V`] THEN
  SUBGOAL_THEN `(ae * aw - ke * kw) * V = (b * bw - t * tw) * V` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
