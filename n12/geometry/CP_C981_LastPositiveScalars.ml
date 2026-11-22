(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastPositiveScalars.lean                   *)
(* (N12Compact.C981CompletionLastPositiveScalars).  Continuous scalar       *)
(* margins for a central square whose positive sine is below .32.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_LastScalars.ml";;

let C981LPS_PROD = C981LS_PROD;;

(* Lean: small_bounds *)
let C981LPS_SMALL_BOUNDS = prove
 (`forall d r. c977cc_normal d r /\ r < &8 / &25
     ==> &947 / &1000 < d /\ d + r < &127 / &100`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C981LS_NORMALS_TAC THEN
  C981LPS_PROD `&0 < (&8 / &25 - r) * (&8 / &25 + r)` THEN
  SUBGOAL_THEN `&947 / &1000 < d` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C981LPS_PROD `&0 <= (&947 / &1000 - d) * (&947 / &1000 + d)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C981LPS_PROD `&0 <= (d - (&127 / &100 - r)) * (d + (&127 / &100 - r))` THEN
  C981LPS_PROD `&0 <= (&8 / &25 - r) * (&127 / &50 - &2 * (r + &8 / &25))` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: neighbor_bounds *)
let C981LPS_NEIGHBOR_BOUNDS = prove
 (`forall b t. c977cc_normal b t /\ &1 / &2 <= t
     ==> b <= &867 / &1000 /\ &683 / &500 <= b + t /\
         &53 / &500 <= b + t - &1 - (&3 / &5) * b * t /\
         b - t - &1 / &4 + (&3 / &5) * t pow 2 <= &267 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C981LS_NORMALS_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  C981LPS_PROD `&0 <= (t - &1 / &2) * (t + &1 / &2)` THEN
  C981LPS_PROD `&0 <= (b - &867 / &1000) * (b - &867 / &1000)` THEN
  SUBGOAL_THEN `b <= &867 / &1000` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&683 / &500 <= b + t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C981LPS_PROD `&0 <= (&683 / &500 - t - b) * (&683 / &500 - t + b)` THEN
   C981LPS_PROD `&0 <= (t - &1 / &2) * (&433 / &500 - t)` THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981LPS_PROD `&0 <= (b + t - &683 / &500) * (&1 - (&3 / &10) * (b + t + &683 / &500))` THEN
  C981LPS_PROD `&0 <= (t - &1 / &2) * (&1 - (&3 / &5) * (t + &1 / &2))` THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: first_impossible *)
let C981LPS_FIRST_IMPOSSIBLE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ r < &8 / &25 /\ &1 / &2 <= t /\
     &1 < b * (&1 + r - (&13 / &50) * r pow 2 - (&31 / &50) * d * r) +
          t * (&1 - d + (&13 / &50) * d * r - (&31 / &50) * r pow 2)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C981LPS_SMALL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C981LS_NORMALS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C981LPS_PROD `&0 <= r * (&1 - d)` THEN
  C981LPS_PROD `&0 <= (&1 - d) * (&3 * d - &2)` THEN
  C981LPS_PROD `&0 <= r * (&8 / &25 - r)` THEN
  C981LPS_PROD `&0 <= r * r` THEN
  C981LPS_PROD `&0 <= r * (d - &947 / &1000)` THEN
  C981LPS_PROD `&0 <= (&8 / &25 - r) * (&20643 / &50000 - (&13 / &50) * (r + &8 / &25))` THEN
  MP_TAC(SPECL [`b:real`; `t:real`;
     `&1 + r - (&13 / &50) * r * r - (&31 / &50) * d * r`;
     `&1 - d + (&13 / &50) * d * r - (&31 / &50) * r * r`] C981LS_HALF_ENDPOINT_REFINED) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: second_impossible *)
let C981LPS_SECOND_IMPOSSIBLE = prove
 (`forall d r b t. c977cc_normal d r /\ c977cc_normal b t /\ r < &8 / &25 /\ &1 / &2 <= t /\
     &1 < b * (&1 + r - (&22 / &25) * r / (d + r)) +
          t * (&13 / &50 + (&1 - d) - (&22 / &25) * r / (d + r))
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C981LPS_SMALL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C981LS_NORMALS_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&0 < d + r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&22 / &25) * r / (d + r) = ((&22 / &25) / (d + r)) * r` ASSUME_TAC THENL
  [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&69 / &100 < (&22 / &25) / (d + r) /\ (&22 / &25) / (d + r) <= &22 / &25`
  STRIP_ASSUME_TAC THENL
  [ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = `(&22 / &25) * r / (d + r) = ((&22 / &25) / (d + r)) * r`
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  ABBREV_TAC `q = (&22 / &25) / (d + r)` THEN
  C981LPS_PROD `&0 <= (&1 - d) * ((&257 / &500) * (&1 + d) - &1)` THEN
  C981LPS_PROD `&0 <= r * (q - &69 / &100)` THEN
  C981LPS_PROD `&0 <= r * (&22 / &25 - q)` THEN
  C981LPS_PROD `&0 <= r * (&8 / &25 - r)` THEN
  C981LPS_PROD `&0 <= r * r` THEN
  MP_TAC(SPECL [`b:real`; `t:real`; `&1 + r - q * r`; `&13 / &50 + (&1 - d) - q * r`]
    C981LS_HALF_ENDPOINT) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
