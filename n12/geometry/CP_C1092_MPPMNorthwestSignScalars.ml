(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNorthwestSignScalars.lean             *)
(* (namespace N12Compact.C1092MPPMNorthwestSignScalars).                     *)
(* Normal is c977cc_normal.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMMPairScalars.ml";;

(* Lean: upper_span *)
let C1092MNWS_UPPER_SPAN = prove
 (`forall b t. c977cc_normal b t /\ (&1 + b) / &4 < t ==> b + t - &1 < (&3 / &4) * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 < t * (t - (&1 + b) / &4)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MPS_PROD_TAC [`&0 <= (&1 + b) * (b + t / &4 - &1)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: cap *)
let C1092MNWS_CAP = prove
 (`forall d r A H. c977cc_normal d r /\ r < &7 / &50 /\ &99 / &100 < d /\
     A <= (&7 / &20) * (d - r) /\ &1 - (&7 / &20) * (d + r) <= H /\ H < &41 / &50 /\
     &0 < A pow 2 + H pow 2 - &2 * (d - r) * A - &2 * (d + r) * H + &1
     ==> A < &1 / &10`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MPS_PROD_TAC
   [`&0 <= (A - &1 / &10) * (&2 * (d - r) - (A + &1 / &10))`;
    `&0 <= (H - (&1 - (&7 / &20) * (d + r))) *
           (&2 * (d + r) - (H + (&1 - (&7 / &20) * (d + r))))`;
    `&0 <= ((d + r) - &1) * (&27 / &10 - (&329 / &400) * ((d + r) + &1))`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: wall_sine *)
let C1092MNWS_WALL_SINE = prove
 (`forall b t. c977cc_normal b t /\ &5 / &4 < b + t ==> &9 / &32 < t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC [`&0 < (b + t - &5 / &4) * (b + t + &5 / &4)`;
                     `&0 <= t * (&1 - b)`] THEN
  NLIN_FACTS_TAC [] [`&9 / &16 < &2 * b * t`] THEN NLIN_TAC []);;

(* Lean: wall_margin *)
let C1092MNWS_WALL_MARGIN = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ r < &7 / &50 /\
             &99 / &100 < d /\ &5 / &4 < b + t
     ==> &0 < b * ((&9 / &10) * d + (&9 / &50) * r - &1) +
              t * (&2 / &5 - (&9 / &10) * r + (&9 / &50) * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C1092MNWS_WALL_SINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MPS_NORMAL_TAC THEN
  C1092MPS_PROD_TAC
   [`&0 < b * (((&9 / &10) * d + (&9 / &50) * r - &1) + &109 / &1000)`;
    `&0 <= &109 / &1000 * (&1 - b)`;
    `&0 < t * ((&2 / &5 - (&9 / &10) * r + (&9 / &50) * d) - &2261 / &5000)`] THEN
  ASM_REAL_ARITH_TAC);;
