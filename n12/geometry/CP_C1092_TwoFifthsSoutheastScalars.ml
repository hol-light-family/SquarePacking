(* ========================================================================= *)
(* Port of Compact/Completion/C1092/TwoFifthsSoutheastScalars.lean           *)
(* (N12Compact.C1092TwoFifths.Scalars).  Exact southeast scalar estimates.   *)
(* half is C1092WPS_half; Normal is c977cc_normal.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsData.ml";;
needs "n12/geometry/CP_C1092_MMMP_PositiveInwardHalfangle.ml";;

(* nlinarith only [facts]: NLIN_TAC on the listed assumptions only *)
let C1092TFSS_ONLY tms hints (asl,w as g) =
  let ths = map (fun t -> try snd(find (fun (_,th) -> aconv (concl th) t) asl)
                          with Failure _ -> failwith ("C1092TFSS_ONLY: " ^ string_of_term t)) tms in
  (POP_ASSUM_LIST(K ALL_TAC) THEN MAP_EVERY ASSUME_TAC ths THEN NLIN_TAC hints) g;;

let C1092TFSS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: SouthBounds (structure) *)
let C1092TFSS_southBounds = new_definition
 `C1092TFSS_southBounds (c:real) s z <=>
    &47 / &50 < c /\ c <= &1 /\ &0 < s /\ s < &8 / &25 /\
    &0 < z /\ z < &1 / &6 /\ z * (&1 + c) = s /\ s * z = &1 - c /\
    z * (&1 - s) < &113 / &1000 /\
    &5 * z * (c + s) < &2 * ((&13 / &50) + s * (&1 - z))`;;

(* Lean: south_bounds *)
let C1092TFSS_SOUTH_BOUNDS = prove
 (`forall c s. &0 < c /\ &0 < s /\ &3 * s < c /\ c pow 2 + s pow 2 = &1
         ==> C1092TFSS_southBounds c s (C1092WPS_half c s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C1092WPS_half c s` MP_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MPIH_HALF_IDENTITIES) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[C1092TFSS_southBounds] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092TFSS_PROD `&0 < (c - &3 * s) * (c + &3 * s)` THEN
  SUBGOAL_THEN `&47 / &50 < c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092TFSS_PROD `&0 <= (&47 / &50 - c) * (&47 / &50 + c)` THEN
    C1092TFSS_ONLY [`&0 < (c - &3 * s) * (c + &3 * s)`; `c * c + s * s = &1`;
                    `&0 <= (&47 / &50 - c) * (&47 / &50 + c)`] [];
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [C1092TFSS_ONLY [`c * c + s * s = &1`] [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `s < &8 / &25` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092TFSS_PROD `&0 <= (s - &8 / &25) * (s + &8 / &25)` THEN
    C1092TFSS_ONLY [`&0 < (c - &3 * s) * (c + &3 * s)`; `c * c + s * s = &1`;
                    `&0 <= (s - &8 / &25) * (s + &8 / &25)`] [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z < &1 / &6` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092TFSS_PROD `&0 <= (z - &1 / &6) * (&1 + c)` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z * (&1 - s) < &113 / &1000` ASSUME_TAC THENL
   [C1092TFSS_PROD `&0 <= (&8 / &25 - s) * (&1 - &8 / &25 - s)` THEN
    SUBGOAL_THEN `(&1 + c) * (z * (&1 - s)) = s * (&1 - s)` ASSUME_TAC THENL
     [UNDISCH_TAC `z * (&1 + c) = s` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 + c) * (&113 / &1000 - z * (&1 - s))` MP_TAC THENL
     [C1092TFSS_ONLY [`(&1 + c) * (z * (&1 - s)) = s * (&1 - s)`;
                      `&0 <= (&8 / &25 - s) * (&1 - &8 / &25 - s)`; `&47 / &50 < c`] [];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092TFSS_PROD `&0 <= (&1 + c) * (z * (&1 - s) - &113 / &1000)` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1 - s * s / &2` ASSUME_TAC THENL
   [C1092TFSS_ONLY [`c * c + s * s = &1`] [SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  C1092TFSS_PROD `&0 <= (&3 * s) * ((&1 - s * s / &2) - c)` THEN
  SUBGOAL_THEN `s * s <= (&8 / &25) * (&8 / &25)` ASSUME_TAC THENL
   [C1092TFSS_PROD `&0 <= (&8 / &25 - s) * (&8 / &25 + s)` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + &7 * (s + &8 / &25) -
                (&3 / &2) * (s * s + (&8 / &25) * s + (&8 / &25) * (&8 / &25))` ASSUME_TAC
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092TFSS_PROD `&0 <= (&8 / &25 - s) * (&1 + &7 * (s + &8 / &25) -
                (&3 / &2) * (s * s + (&8 / &25) * s + (&8 / &25) * (&8 / &25)))` THEN
  SUBGOAL_THEN `&0 < (&13 / &25) * (&1 + c) + &2 * s - &3 * c * s - &7 * s * s` ASSUME_TAC
  THENL
   [C1092TFSS_ONLY [`&0 <= (&8 / &25 - s) * (&1 + &7 * (s + &8 / &25) -
                (&3 / &2) * (s * s + (&8 / &25) * s + (&8 / &25) * (&8 / &25)))`;
                    `&0 <= (&3 * s) * ((&1 - s * s / &2) - c)`; `&47 / &50 < c`] [];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + c) * (&2 * ((&13 / &50) + s * (&1 - z)) - &5 * z * (c + s)) =
                (&13 / &25) * (&1 + c) + &2 * s - &3 * c * s - &7 * s * s` ASSUME_TAC THENL
   [UNDISCH_TAC `z * (&1 + c) = s` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&5 * z * (c + s) < &2 * ((&13 / &50) + s * (&1 - z))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092TFSS_PROD `&0 <= (&1 + c) * (&5 * z * (c + s) - &2 * ((&13 / &50) + s * (&1 - z)))` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: right_large *)
let C1092TFSS_RIGHT_LARGE = prove
 (`forall d r. c977cc_normal d r /\ (&2 / &5) * d <= r
         ==> &10 / &29 <= d * r /\ &4 / &29 <= r pow 2 /\ r pow 2 <= &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  C1092TFSS_PROD `&0 <= (&5 * r - &2 * d) * (&5 * d - &2 * r)` THEN
  C1092TFSS_PROD `&0 <= (&5 * r - &2 * d) * (&5 * r + &2 * d)` THEN
  C1092TFSS_PROD `&0 <= (d - r) * (d + r)` THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: negative_loss *)
let C1092TFSS_NEGATIVE_LOSS = prove
 (`forall c s z d r. C1092TFSS_southBounds c s z /\ c977cc_normal d r /\ (&2 / &5) * d <= r
     ==> &113 / &1000 < (&33 / &50) * c * d * r +
                        s * ((&13 / &50) * d pow 2 - (&2 / &5) * r pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092TFSS_RIGHT_LARGE) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092TFSS_southBounds]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (c - &47 / &50) * (d * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&7 / &100) <= (&13 / &50) * d * d - (&2 / &5) * r * r` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092TFSS_PROD `&0 <= s * (((&13 / &50) * d * d - (&2 / &5) * r * r) + &7 / &100)` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_loss *)
let C1092TFSS_POSITIVE_LOSS = prove
 (`forall c s z d r. C1092TFSS_southBounds c s z /\ c977cc_normal d r /\ (&2 / &5) * d <= r
     ==> &113 / &1000 < (&33 / &50) * c * d * r -
                        s * ((&2 / &5) * d pow 2 - (&13 / &50) * r pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092TFSS_RIGHT_LARGE) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092TFSS_southBounds]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (c - &47 / &50) * (d * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 / &5) * d * d - (&13 / &50) * r * r <= &224 / &725` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092TFSS_PROD `&0 <= s * (&224 / &725 - ((&2 / &5) * d * d - (&13 / &50) * r * r))` THEN
  ASM_REAL_ARITH_TAC);;
