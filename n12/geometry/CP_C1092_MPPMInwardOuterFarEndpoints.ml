(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardOuterFarEndpoints.lean         *)
(* (namespace N12Compact.C1092MPPMInwardOuterFar).  The two exact rational   *)
(* quartic endpoint estimates.  alpha / recipientGap / cap_coordinates /     *)
(* far_coordinates / recipient_order are c1092miof_* / C1092MIOF_* of        *)
(* CP_C1092_MPPMInwardOuterFarScalars.ml; Normal = c977cc_normal, half =     *)
(* C1092WPS_half.  Tag C1092MIOFE_.                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardOuterFarScalars.ml";;

let C1092MIOFE_LIN = NLIN_TAC ~deg2:false [];;

let C1092MIOFE_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MIOFE_LIN; ALL_TAC];;

let C1092MIOFE_POS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 < k * x ==> &0 < x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC);;

(* Lean: quartic_lower (private) *)
let C1092MIOFE_QUARTIC_LOWER = prove
 (`forall a0 a1 a2 a3 a4 x v.
     &0 <= a2 /\ &0 <= a3 /\ &0 <= a4 /\ &0 <= x /\ x <= v /\
     &0 <= a1 - &2 * a2 * v - &3 * a3 * v pow 2
     ==> a0 - a1 * v + a2 * v pow 2 + a3 * v pow 3 - a4 * v pow 4 <=
         a0 - a1 * x + a2 * x pow 2 + a3 * x pow 3 - a4 * x pow 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= v` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092MIOFE_PROD `&0 <= (v - x) * (&2 * v + x)` THEN
  C1092MIOFE_PROD `&0 <= a2 * (&2 * v - (x + v))` THEN
  SUBGOAL_THEN `&0 <= a3 * (&3 * v pow 2 - (x pow 2 + x * v + v pow 2))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= x pow 3 + x pow 2 * v + x * v pow 2 + v pow 3` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092MIOFE_PROD `&0 <= a4 * (x pow 3 + x pow 2 * v + x * v pow 2 + v pow 3)` THEN
  SUBGOAL_THEN `&0 <= a1 - a2 * (x + v) - a3 * (x pow 2 + x * v + v pow 2) +
                      a4 * (x pow 3 + x pow 2 * v + x * v pow 2 + v pow 3)` ASSUME_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (v - x) * (a1 - a2 * (x + v) - a3 * (x pow 2 + x * v + v pow 2) +
                      a4 * (x pow 3 + x pow 2 * v + x * v pow 2 + v pow 3))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: coordinate_form (private) *)
let C1092MIOFE_COORDINATE_FORM = prove
 (`forall c s. c977cc_normal c s
     ==> c = (&1 - C1092WPS_half c s pow 2) / (&1 + C1092WPS_half c s pow 2) /\
         s = (&2 * C1092WPS_half c s) / (&1 + C1092WPS_half c s pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

(* Lean: missing_endpoint *)
let C1092MIOFE_MISSING_ENDPOINT = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &279 / &1000
     ==> &0 < c1092miof_recipientGap (&0) c s (&275 / &373) (&252 / &373)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  MP_TAC(SPECL [`&2450`; `&10175`; `&12602`; `&7875`; `&23900`; `x:real`; `&279 / &1000`]
    C1092MIOFE_QUARTIC_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC C1092MIOFE_POS_CANCEL THEN
  EXISTS_TAC `&9325 * (&1 + x pow 2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&9325 * (&1 + x pow 2) pow 2) *
                c1092miof_recipientGap (&0) c s (&275 / &373) (&252 / &373) =
                &2450 - &10175 * x + &12602 * x pow 2 + &7875 * x pow 3 - &23900 * x pow 4`
   SUBST1_TAC THENL
   [REWRITE_TAC[c1092miof_recipientGap; c1092miof_alpha] THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: centered_endpoint *)
let C1092MIOFE_CENTERED_ENDPOINT = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &21 / &100
     ==> &0 < c1092miof_recipientGap (&17 / &125) c s (&275 / &373) (&252 / &373)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFS_HALF_TAC `c:real` `s:real` `x:real` THEN
  MP_TAC(SPECL [`&7966`; `&41525`; `&63010`; `&48725`; `&115216`; `x:real`; `&21 / &100`]
    C1092MIOFE_QUARTIC_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV REAL_RAT_REDUCE_CONV)) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC C1092MIOFE_POS_CANCEL THEN
  EXISTS_TAC `&46625 * (&1 + x pow 2) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&46625 * (&1 + x pow 2) pow 2) *
                c1092miof_recipientGap (&17 / &125) c s (&275 / &373) (&252 / &373) =
                &7966 - &41525 * x + &63010 * x pow 2 + &48725 * x pow 3 - &115216 * x pow 4`
   SUBST1_TAC THENL
   [REWRITE_TAC[c1092miof_recipientGap; c1092miof_alpha] THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: recipient_expand (private) *)
let C1092MIOFE_RECIPIENT_EXPAND = prove
 (`forall eta c s d t. c1092miof_recipientGap eta c s d t =
     &1 - (&1 - c * c1092miof_alpha c s + (&1 - eta) * s) * d -
     (&1 - s * c1092miof_alpha c s - (&1 - eta) * c) * t`,
  REWRITE_TAC[c1092miof_recipientGap] THEN REAL_ARITH_TAC);;

(* common proof of the two recipient bounds *)
let C1092MIOFE_RECIPIENT_TAC m eta endpoint closeb smallb aub ab bb =
  let eta1 = mk_binop `(-):real->real->real` `&1` eta in
  let mul = mk_binop `( * ):real->real->real` in
  let atm = list_mk_binop `(+):real->real->real`
              [mk_binop `(-):real->real->real` `&1` `c * c1092miof_alpha c s`; mul eta1 `s:real`] in
  let btm = mk_binop `(-):real->real->real`
              (mk_binop `(-):real->real->real` `&1` `s * c1092miof_alpha c s`) (mul eta1 `c:real`) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; m] C1092MIOF_CAP_COORDINATES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C1092MIOF_FAR_COORDINATES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] endpoint) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c s`)) THEN
  SUBGOAL_THEN closeb ASSUME_TAC THENL [C1092MIOFE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN smallb ASSUME_TAC THENL [C1092MIOFE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092miof_alpha c s` ASSUME_TAC THENL
   [REWRITE_TAC[c1092miof_alpha] THEN C1092MIOFE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN aub ASSUME_TAC THENL
   [REWRITE_TAC[c1092miof_alpha] THEN C1092MIOFE_LIN; ALL_TAC] THEN
  C1092MIOFE_PROD `&0 <= c1092miof_alpha c s * (&1 - c)` THEN
  C1092MIOFE_PROD `&0 <= s * c1092miof_alpha c s` THEN
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` ab atm) ASSUME_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092MIOFE_LIN; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` btm bb) ASSUME_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN C1092MIOFE_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; atm; btm] C1092MIOF_RECIPIENT_ORDER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN C1092MIOFE_LIN;
    DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092MIOFE_RECIPIENT_EXPAND]) THEN
  REWRITE_TAC[C1092MIOFE_RECIPIENT_EXPAND] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    let c = concl th in not (is_forall c) && not (can (find_term ((=) `c977cc_normal`)) c) &&
                        not (can (find_term ((=) `C1092WPS_half`)) c))) THEN
  REAL_ARITH_TAC;;

(* Lean: missing_recipient_positive *)
let C1092MIOFE_MISSING_RECIPIENT_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
     C1092WPS_half c s <= &279 / &1000 /\ &7 / &18 < C1092WPS_half d t
     ==> &0 < c1092miof_recipientGap (&0) c s d t`,
  C1092MIOFE_RECIPIENT_TAC `&279 / &1000` `&0` C1092MIOFE_MISSING_ENDPOINT
    `&17 / &20 < c` `s < &13 / &25` `c1092miof_alpha c s < &29 / &100`
    `&71 / &100` `&3 / &20`);;

(* Lean: centered_recipient_positive *)
let C1092MIOFE_CENTERED_RECIPIENT_POSITIVE = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
     C1092WPS_half c s <= &21 / &100 /\ &7 / &18 < C1092WPS_half d t
     ==> &0 < c1092miof_recipientGap (&17 / &125) c s d t`,
  C1092MIOFE_RECIPIENT_TAC `&21 / &100` `&17 / &125` C1092MIOFE_CENTERED_ENDPOINT
    `&91 / &100 < c` `s < &41 / &100` `c1092miof_alpha c s < &1 / &5`
    `&4 / &5` `&107 / &500`);;
