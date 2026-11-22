(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointG01Models.  *)
(* lean (N12Compact.C1092MPPMMissingNegativeCrosspointSupport).  Fixed      *)
(* scalar models for the missing-negative G01 support.  Normal is           *)
(* c977cc_normal; Quarter is c1092mncs_quarter; half / normal_half /        *)
(* half_order C1092MCBH_*; QuadraticArc remainder / value / nonnegative     *)
(* c1092mpqa_* / C1092MPQA_NONNEGATIVE; middle_scalar_lower                 *)
(* C1092MNCG11_MIDDLE_SCALAR_LOWER.  The local lets w, H, D are written via *)
(* abbreviations.  Tag C1092MNG01M_.                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointG11.ml";;

let C1092MNG01M_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MNG01M_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092MNG01M_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092MNG01M_QUARTER_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mncs_quarter; c1092mcs_quarter] o
    check (fun th -> can (term_match [] `c1092mncs_quarter x y`) (concl th)));;

(* Lean: G01_low_remainder (private) *)
let C1092MNG01M_G01_LOW_REMAINDER = prove
 (`forall b z. &3 / &5 <= b /\ b <= &71 / &100 /\ &0 <= z /\ z <= &1 / &3
     ==> &0 <= c1092mpqa_remainder (&4 / &5) b (b - &1 / &100) (&0) z (&1 / &3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `c1092mpqa_remainder (&4 / &5) b (b - &1 / &100) (&0) z (&1 / &3) =
    &81 / &100 - b - (&79 / &100 + b) * (z pow 2 + (&1 / &3) pow 2 + z pow 2 * (&1 / &3) pow 2) +
    (&2 * b - &8 / &15) * z + (&2 / &3) * b` SUBST1_TAC THENL
  [REWRITE_TAC[c1092mpqa_remainder; c1092mpqa_X; c1092mpqa_Y; c1092mpqa_Z;
               c1092mpqa_sum3; c1092mpqa_pair3; c1092mpqa_triple3] THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092MNG01M_PROD `&0 <= (&1 / &3 - z) * (&1 / &3 + z)` THEN
  ABBREV_TAC `X = z pow 2 + (&1 / &3) pow 2 + z pow 2 * (&1 / &3) pow 2` THEN
  SUBGOAL_THEN `&0 <= X /\ X <= &19 / &81` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "X" THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
   REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  C1092MNG01M_PROD `&0 <= (&3 / &2 - (&79 / &100 + b)) * X` THEN
  C1092MNG01M_PROD `&0 <= z * (&2 * b - &8 / &15)` THEN
  C1092MNG01M_LP_TAC);;

(* Lean: G01_low_model *)
let C1092MNG01M_G01_LOW_MODEL = prove
 (`forall b h r. &3 / &5 <= b /\ b <= &71 / &100 /\ c1092mncs_quarter h r /\
           &4 / &5 <= h /\ r <= &3 / &5
     ==> &1 / &100 <= (&4 / &5) * h pow 2 + b * h * r + b -
                      (&3 / &5 + (&112 / &125) * b) * h - (&61 / &50) * b * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNG01M_QUARTER_TAC THEN
  SUBGOAL_THEN `c977cc_normal h r` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[c977cc_normal] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MCBH_NORMAL_HALF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`; `&4 / &5`; `&3 / &5`] C1092MCBH_HALF_ORDER) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
   ALL_TAC] THEN
  SUBGOAL_THEN `c1092mcbh_half (&4 / &5) (&3 / &5) = &1 / &3` SUBST1_TAC THENL
  [REWRITE_TAC[c1092mcbh_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  ABBREV_TAC `z = c1092mcbh_half h r` THEN
  MP_TAC(SPECL [`&4 / &5`; `b:real`; `b - &1 / &100`; `--(&3 / &5 + (&112 / &125) * b)`;
                `--(&61 / &50) * b`; `&0`; `z:real`; `&1 / &3`] C1092MPQA_NONNEGATIVE) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1092MNG01M_G01_LOW_REMAINDER THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[c1092mpqa_value; c1092sps_cosH; c1092sps_sinH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[c1092mpqa_value; c1092sps_cosH; c1092sps_sinH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092mpqa_value] THEN REAL_ARITH_TAC);;

(* Lean: G01_middle_model *)
let C1092MNG01M_G01_MIDDLE_MODEL = prove
 (`forall h r. c977cc_normal h r /\ &3 / &5 <= r
     ==> &1 / &100 <= &2 * h + r - &2 - (&112 / &125) * h * r + (&39 / &50) * r pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:real`; `r:real`] C1092MNCG11_MIDDLE_SCALAR_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal h r` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  C1092MNG01M_PROD `&0 <= h * ((&9 / &200) * h - (&41 / &1000) * r)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092MNG01M_LP_TAC);;

(* Lean: G01_high_model *)
let C1092MNG01M_G01_HIGH_MODEL = prove
 (`forall h r. c1092mncs_quarter h r /\ h <= r
     ==> &1 / &100 <= (&4 / &5) * h pow 2 + (&151 / &100) * h * r + (&71 / &100) * r pow 2 -
                      (&10211 / &6250) * h - (&1207 / &2500) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNG01M_QUARTER_TAC THEN
  MP_TAC C1092MNCG11_DIAGONAL_NORMAL THEN
  ABBREV_TAC `w = sqrt(&2) / &2` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * w * w = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `w pow 2 + w pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `w <= &177 / &250` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092MNG01M_PROD `&0 < (w - &177 / &250) * (w + &177 / &250)` THEN C1092MNG01M_LP_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `r <= &1` ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `h:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `(h + r) * (h + r) + (r - h) * (r - h) = &2` ASSUME_TAC THENL
  [UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `H = h + r` THEN ABBREV_TAC `D = r - h` THEN
  SUBGOAL_THEN `&0 <= H /\ &0 <= D /\ D <= &1` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["H"; "D"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `H <= &2 * w` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092MNG01M_PROD `&0 < (H - &2 * w) * (H + &2 * w)` THEN
   C1092MNG01M_PROD `&0 <= D * D` THEN C1092MNG01M_LP_TAC; ALL_TAC] THEN
  C1092MNG01M_PROD `&0 <= (&2 * w - H) * (&20 / &7 - (&2 * w + H))` THEN
  SUBGOAL_THEN `(&7 / &20) * D * D <= &2 * w - H` ASSUME_TAC THENL
  [C1092MNG01M_LP_TAC; ALL_TAC] THEN
  C1092MNG01M_PROD `&0 <= D * (&14387 / &25000 - (&9 / &200) * H - (&192301 / &500000) * D)` THEN
  SUBGOAL_THEN
   `(&4 / &5) * h pow 2 + (&151 / &100) * h * r + (&71 / &100) * r pow 2 -
    (&10211 / &6250) * h - (&1207 / &2500) * r - (&151 / &100 - (&26457 / &12500) * w) =
    (&26457 / &25000) * (&2 * w - H) - (&151 / &200) * D * D +
    D * (&14387 / &25000 - (&9 / &200) * H)` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["H"; "D"] THEN
   UNDISCH_TAC `h pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092MNG01M_LP_TAC);;
