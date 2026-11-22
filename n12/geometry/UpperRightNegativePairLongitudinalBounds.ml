(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightNegativePairLongitudinalBounds.lean    *)
(* (namespace N12Compact.UpperRightNegativePairLongitudinalBounds).          *)
(* Continuous longitudinal margins for the last northeast corner sector.     *)
(* Normal c s is c977cc_normal c s.  UpperRightNegativeTopBounds.arc is      *)
(* URNTB_ARC; UpperRightCornerLongitudinalBounds.disk_margin is              *)
(* URCLB_DISK_MARGIN.                                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightNegativeTopBounds.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* p * (l - r) = 0 from |- l = r *)
let URNPLB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let URNPLB_DISK tm a b =
  MP_TAC(SPECL [fst tm; snd tm; a; b] URCLB_DISK_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC];;

(* Lean: cosine_defect *)
let URNPLB_COSINE_DEFECT = prove
 (`forall c s. c977cc_normal c s ==> &1 - c <= (&3 / &5) * s pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= (&1 - c) * ((&3 / &5) * c - &2 / &5)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: forward_lower *)
let URNPLB_FORWARD_LOWER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 < &1 + e * (c + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * c * s) +
              f * (s - c + &13 / &20 - (&13 / &20) * s pow 2 - (&61 / &100) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URNTB_ARC) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  URNPLB_DISK (`e:real`,`f:real`) `&19 / &25` `&7 / &20` THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
   [`&0 <= c * s`;
    `--(&19 / &25) <= c + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * c * s`;
    `&0 <= s * (&1 - (&61 / &100) * c - (&13 / &20) * s)`;
    `--(&7 / &20) <= s - c + &13 / &20 - (&13 / &20) * s pow 2 - (&61 / &100) * c * s`;
    `&0 <= e * ((c + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * c * s) +
                 &19 / &25)`;
    `&0 <= f * ((s - c + &13 / &20 - (&13 / &20) * s pow 2 - (&61 / &100) * c * s) +
                 &7 / &20)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: forward_row *)
let URNPLB_FORWARD_ROW = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 < &1 + e * (c - &44 / &25 + (&33 / &50) * s pow 2) + f * (s - (&33 / &50) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&1 - c) * ((&33 / &50) * c - &17 / &50)`;
    `--(&19 / &25) <= c - &44 / &25 + (&33 / &50) * s pow 2`;
    `&0 <= s * (&1 - (&33 / &50) * c)`;
    `&0 <= e * ((c - &44 / &25 + (&33 / &50) * s pow 2) + &19 / &25)`;
    `&0 <= f * (s * (&1 - (&33 / &50) * c))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: forward_upper *)
let URNPLB_FORWARD_UPPER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ &0 <= e * s - f * c
     ==> &0 <= s + e * (&1 - c - (&44 / &25) * s + c * s) + f * (s pow 2 - s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `e:real`; `f:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&1 - e`; SQ_NONNEG `f - &25 / &69`]
   [`&0 <= (&1 - c) * (&1 - s)`; `&0 <= e * ((&1 - c) * (&1 - s))`;
    `&0 <= f * s`; `&0 <= (f * s) * (s - f)`;
    `e <= &1 - f pow 2 / &2`; `&0 <= &1 - (&19 / &25) * e - f + f pow 2`;
    `&0 <= s * (&1 - (&19 / &25) * e - f + f pow 2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: forward_reverse_upper *)
let URNPLB_FORWARD_REVERSE_UPPER = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ e * s - f * c <= &0
     ==> &0 <= s + e * (&1 - c - (&44 / &25) * s + c * s) + f * (s pow 2 - s) -
              s * (e * s - f * c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `c:real`; `s:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URNPLB_COSINE_DEFECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  URNPLB_DISK (`c:real`,`s:real`) `&22 / &25` `&3 / &10` THEN
  C977CSB_NORMAL_TAC THEN
  let A = `&1 - c + s * (c - s - &44 / &25)` and B = `s * (c + s - &1)` in
  let sub t = subst [A,`AA:real`; B,`BB:real`] t in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= s * (&44 / &25 - c + (&2 / &5) * s)`; `AA <= &0`; `&0 <= BB`;
    `&0 <= (c - e) * --AA`; `&0 <= (f - s) * BB`;
    `&0 <= s * (&2 - (&44 / &25) * c - (&3 / &5) * s)`]) THEN
  SUBGOAL_THEN (sub `&0 <= s + c * AA + s * BB`) ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [URNPLB_EQ_HINT `s - &1` (ASSUME `c pow 2 + s pow 2 = &1`)]; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: reverse_coefficients (private) *)
let URNPLB_REVERSE_COEFFICIENTS = prove
 (`forall e f. c977cc_normal e f
         ==> e - &44 / &25 + (&1 / &2) * f pow 2 - (&1 / &2) * e * f <= &0 /\
             &0 <= f + &1 / &2 - (&1 / &2) * f pow 2 - (&1 / &2) * e * f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= f * (e - f)`; `&0 <= f * (&1 - (e + f) / &2)`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: reverse_parallel *)
let URNPLB_REVERSE_PARALLEL = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ &0 <= e * s - f * c
     ==> &0 < &1 + c * (e - &44 / &25 + (&1 / &2) * f pow 2 - (&1 / &2) * e * f) +
              s * (f + &1 / &2 - (&1 / &2) * f pow 2 - (&1 / &2) * e * f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `e:real`; `f:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `e:real`; `f:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URNPLB_REVERSE_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (e - c) * --(e - &44 / &25 + (&1 / &2) * f pow 2 - (&1 / &2) * e * f)`;
    `&0 <= (s - f) * (f + &1 / &2 - (&1 / &2) * f pow 2 - (&1 / &2) * e * f)`] THEN
  NLIN_TAC ~deg2:false [URNPLB_EQ_HINT `&1 - f / &2` (ASSUME `e pow 2 + f pow 2 = &1`)]);;

(* Lean: reverse_parallel_top *)
let URNPLB_REVERSE_PARALLEL_TOP = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s /\ &0 <= e * s - f * c
     ==> &0 <= c - &1 + s * (&1 + c * (e - &44 / &25 + (&1 / &2) * f pow 2 -
                                       (&1 / &2) * e * f) +
                              s * (f + &1 / &2 - (&1 / &2) * f pow 2 - (&1 / &2) * e * f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `e:real`; `f:real`] C977CSB_SINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`e:real`; `f:real`] URNPLB_COSINE_DEFECT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] URNPLB_COSINE_DEFECT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  let co = `e - &44 / &25 + (&1 / &2) * f pow 2 - (&1 / &2) * e * f`
  and ot = `f + &1 / &2 - (&1 / &2) * f pow 2 - (&1 / &2) * e * f` in
  let sub t = subst [co,`CO:real`; ot,`OT:real`] t in
  NLIN_FACTS_TAC [SQ_NONNEG `&1 - c`; SQ_NONNEG `s:real`] (map sub
   [`&0 <= f * (&1 - e)`;
    `--(&19 / &25) - (&1 / &2) * f - (&1 / &10) * f pow 2 <= CO`;
    `&0 <= f * (&18 / &25 - (e + f) / &2)`;
    `&1 / &2 + (&7 / &25) * f <= OT`;
    `&0 <= c * (CO - (--(&19 / &25) - (&1 / &2) * f - (&1 / &10) * f pow 2))`;
    `&0 <= s * (OT - (&1 / &2 + (&7 / &25) * f))`;
    `&0 <= c / &2 - (&7 / &25) * s`;
    `&0 <= (s - f) * (c / &2 - (&7 / &25) * s)`;
    `&0 <= (s - f) * (f + s)`; `&0 <= c / &10 * ((s - f) * (f + s))`;
    `c <= &1 - s pow 2 / &2`; `&0 <= s * (&1 - c)`; `&0 <= s pow 2 * (&1 - c)`]) THEN
  SUBGOAL_THEN (sub `(&3 / &5) * s <= &1 + c * CO + s * OT`) ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [SQ_NONNEG `s - &15 / &28`;
      URNPLB_EQ_HINT `c / &10` (ASSUME `e pow 2 + f pow 2 = &1`);
      URNPLB_EQ_HINT `&1` (ASSUME `e pow 2 + f pow 2 = &1`);
      URNPLB_EQ_HINT `&1` (ASSUME `c pow 2 + s pow 2 = &1`)]; ALL_TAC] THEN
  NLIN_FACTS_TAC [] (map sub [`&0 <= s * ((&1 + c * CO + s * OT) - (&3 / &5) * s)`]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: reverse_row *)
let URNPLB_REVERSE_ROW = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 < &1 + c * (e - &63 / &50 - e pow 2 / &2) + s * f * (&1 - e / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (e - &7 / &10) * (&1 - e)`; `&91 / &200 <= e - e pow 2 / &2`;
    `&0 <= c * ((e - e pow 2 / &2) - &91 / &200)`;
    `&0 <= s * f`; `&0 <= (s * f) * (&1 - e / &2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: reverse_row_top *)
let URNPLB_REVERSE_ROW_TOP = prove
 (`forall e f c s. c977cc_normal e f /\ c977cc_normal c s
     ==> &0 <= c - &1 + s * (&1 + c * (e - &63 / &50 - e pow 2 / &2) + s * f * (&1 - e / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  URNPLB_DISK (`c:real`,`s:real`) `&161 / &200` `&59 / &100` THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (e - &7 / &10) * (&1 - e)`; `&91 / &200 <= e - e pow 2 / &2`;
    `&0 <= c * ((e - e pow 2 / &2) - &91 / &200)`;
    `&0 <= s * f`; `&0 <= (s * f) * (&1 - e / &2)`;
    `&1 - (&161 / &200) * c <= &1 + c * (e - &63 / &50 - e pow 2 / &2) + s * f * (&1 - e / &2)`;
    `&0 <= (&1 - c) * ((&59 / &100) * c - &41 / &100)`;
    `&1 - c <= (&59 / &100) * s pow 2`;
    `&0 <= s * ((&1 + c * (e - &63 / &50 - e pow 2 / &2) + s * f * (&1 - e / &2)) -
                (&1 - (&161 / &200) * c))`;
    `&0 <= s * (&1 - (&161 / &200) * c - (&59 / &100) * s)`] THEN
  NLIN_TAC ~deg2:false []);;
