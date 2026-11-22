(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastRightScalars.lean                      *)
(* (N12Compact.C981CompletionLastRightScalars).  Scalar comparisons for the  *)
(* actual right-wall exclusion in the final C981 cycles.  The local half is  *)
(* c981lrs_half; the structure Minor is c981lrs_minor; Normal is             *)
(* c977cc_normal; quarter_lt is C981HA_QUARTER_LT; cross_order is            *)
(* C981OS_CROSS_ORDER; LastWallPolynomials first/second/third are            *)
(* C981LWP_*.  Purely scalar.  Tag C981LRS_.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_OppositeSupport.ml";;
needs "n12/geometry/CP_C981_LastWallPolynomials.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C981LRS_LIN = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C981LRS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN FIRST [MATCH_ACCEPT_TAC REAL_LE_SQUARE; MATCH_ACCEPT_TAC REAL_LE_POW_2;
                          NLIN_TAC ~deg2:false []; NLIN_TAC [SQ_NONNEG `z:real`]];
     ALL_TAC]) tms;;

let C981LRS_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

(* Lean: half (definition) *)
let c981lrs_half = new_definition `c981lrs_half (c:real) s = s / (&1 + c)`;;

(* Lean: half_data *)
let C981LRS_HALF_DATA = prove
 (`forall c s. &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> &0 <= c981lrs_half c s /\ c981lrs_half c s <= &1 /\
         c981lrs_half c s * (&1 + c) = s /\
         c981lrs_half c s * s + c = &1 /\
         (&1 + c981lrs_half c s pow 2) * c = &1 - c981lrs_half c s pow 2 /\
         (&1 + c981lrs_half c s pow 2) * s = &2 * c981lrs_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REWRITE_TAC[C1092WPS_half; GSYM c981lrs_half] THEN
  SPEC_TAC(`c981lrs_half c s`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 + c) * (z * s + c) = (&1 + c) * &1` MP_TAC THENL
   [UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL; REAL_ARITH `&0 < c ==> ~(&1 + c = &0)`]);;

(* Lean: Minor (structure) *)
let c981lrs_minor = new_definition
 `c981lrs_minor b t <=>
    &43 / &50 < b /\ b < &883 / &1000 /\ &47 / &100 < t /\ t <= &1 / &2 /\
    &1 / &4 < c981lrs_half b t /\ c981lrs_half b t <= &27 / &100 /\
    &1 / &10 <= b + t - &1 - (&3 / &5) * b * t`;;

let C981LRS_HALF_TAC c s z =
  MP_TAC(SPECL [c; s] C981LRS_HALF_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if free_in (list_mk_comb(`c981lrs_half`,[c;s])) (concl th) then MP_TAC th else NO_TAC)) THEN
  SPEC_TAC(list_mk_comb(`c981lrs_half`,[c;s]), z) THEN GEN_TAC THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC);;

(* Lean: minor *)
let C981LRS_MINOR = prove
 (`forall b t. c977cc_normal b t /\ &1 < t + (&3 / &5) * b /\ t <= &1 / &2
         ==> c981lrs_minor b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C981HA_QUARTER_LT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c981ha_half; GSYM c981lrs_half] THEN DISCH_TAC THEN
  REWRITE_TAC[c981lrs_minor] THEN
  C981LRS_HALF_TAC `b:real` `t:real` `h:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `&8 / &17 < t` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN
    C981LRS_PROD_TAC [`&0 < (h - &1 / &4) * (&1 + b)`] THEN
    SUBGOAL_THEN `b < &15 / &17` ASSUME_TAC THENL [C981LRS_LIN; ALL_TAC] THEN
    C981LRS_PROD_TAC [`&0 < (&15 / &17 - b) * (&15 / &17 + b)`;
                      `&0 <= (&8 / &17 - t) * (&8 / &17 + t)`] THEN C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 < (t - &8 / &17) * (t + &8 / &17)`] THEN
  SUBGOAL_THEN `b < &883 / &1000` ASSUME_TAC THENL
   [MP_TAC(SPEC `b - &883 / &1000` REAL_LE_SQUARE) THEN DISCH_TAC THEN C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= (&1 / &2 - t) * (&1 / &2 + t)`] THEN
  SUBGOAL_THEN `&43 / &50 < b` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN C981LRS_PROD_TAC [`&0 <= (&43 / &50 - b) * (&43 / &50 + b)`] THEN
    C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= h * (b - &43 / &50)`] THEN
  SUBGOAL_THEN `&23 / &17 < b + t` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN
    C981LRS_PROD_TAC [`&0 <= (&23 / &17 - t - b) * (&23 / &17 - t + b)`;
                      `&0 < (t - &8 / &17) * (&15 / &17 - t)`] THEN C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC
   [`&0 <= (b + t - &23 / &17) * (&1 - (&3 / &10) * (b + t + &23 / &17))`] THEN
  C981LRS_LIN);;

(* Lean: half_order (private) *)
let C981LRS_HALF_ORDER = prove
 (`forall c s b t. c pow 2 + s pow 2 = &1 /\ &0 < c /\ &0 <= s /\ c977cc_normal b t /\
     b * s - t * c <= &0
     ==> c981lrs_half c s <= c981lrs_half b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  MP_TAC(SPECL [`b:real`; `t:real`; `c:real`; `s:real`] C981OS_CROSS_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C981LRS_HALF_TAC `c:real` `s:real` `z:real` THEN
  C981LRS_HALF_TAC `b:real` `t:real` `h:real` THEN
  C981LRS_PROD_TAC [`&0 <= z * (c - b)`] THEN
  C981LRS_CONTRA THEN
  C981LRS_PROD_TAC [`&0 < (z - h) * (&1 + b)`] THEN C981LRS_LIN);;

let C981LRS_MINOR_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c981lrs_minor] o
    check (can (term_match [] `c981lrs_minor x y`) o concl));;

let C981LRS_NORMAL_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (can (term_match [] `c977cc_normal x y`) o concl));;

(* Lean: bu_negative *)
let C981LRS_BU_NEGATIVE = prove
 (`forall c s b t. c pow 2 + s pow 2 = &1 /\ &0 < c /\ &0 < s /\ c977cc_normal b t /\
     c981lrs_minor b t /\ b * s - t * c <= &0 /\
     &0 < &2 * (b * c + t * s) - b * c + (&7 / &5) * b * s - s - (b * c + t * s) * (c + s)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `b:real`; `t:real`] C981LRS_HALF_ORDER) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  C981LRS_MINOR_TAC THEN C981LRS_NORMAL_TAC THEN
  SUBGOAL_THEN `c981lrs_half c s <= &27 / &100` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981LRS_HALF_TAC `c:real` `s:real` `z:real` THEN
  MP_TAC(SPEC `z:real` C981LWP_FIRST) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2; REAL_ARITH `z pow 3 = z * z * z`]) THEN
  C981LRS_PROD_TAC [`&0 <= (z * z) * (&12 / &5 - z)`] THEN
  SUBGOAL_THEN `&0 <= &2 / &5 + z + (&12 / &5) * z * z - z * z * z /\
                &0 <= &1 - &2 * z + &3 * z * z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [C981LRS_LIN; MP_TAC(SPEC `z - &1 / &3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  C981LRS_PROD_TAC
   [`&0 <= (&2 / &5 + z + (&12 / &5) * z * z - z * z * z) * (&883 / &1000 - b)`;
    `&0 <= (&1 - &2 * z + &3 * z * z) * (&1 / &2 - t)`] THEN
  SUBGOAL_THEN `b * (&2 / &5 + z + (&12 / &5) * z * z - z * z * z) +
                t * (&1 - &2 * z + &3 * z * z) - &1 - z * z < &0` ASSUME_TAC THENL
   [C981LRS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + z * z) * (&2 * (b * c + t * s) - b * c + (&7 / &5) * b * s - s -
                 (b * c + t * s) * (c + s)) =
                s * (b * (&2 / &5 + z + (&12 / &5) * z * z - z * z * z) +
                     t * (&1 - &2 * z + &3 * z * z) - &1 - z * z)` ASSUME_TAC THENL
   [UNDISCH_TAC `z * s + c = &1` THEN UNDISCH_TAC `(&1 + z * z) * c = &1 - z * z` THEN
    UNDISCH_TAC `(&1 + z * z) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 < (&1 + z * z) * (&2 * (b * c + t * s) - b * c + (&7 / &5) * b * s - s -
                 (b * c + t * s) * (c + s))`] THEN
  C981LRS_PROD_TAC [`&0 < s * --(b * (&2 / &5 + z + (&12 / &5) * z * z - z * z * z) +
                     t * (&1 - &2 * z + &3 * z * z) - &1 - z * z)`] THEN
  C981LRS_LIN);;

(* Lean: bu_positive *)
let C981LRS_BU_POSITIVE = prove
 (`forall c s b t. c pow 2 + s pow 2 = &1 /\ &0 < c /\ &0 < s /\ c977cc_normal b t /\
     c981lrs_minor b t /\ &0 <= b * s - t * c /\
     &0 < &2 * (b * c + t * s) - b * c + (&7 / &5) * b * s - s - (b * c + t * s) * (c + s) -
          s * (b * s - t * c)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981LRS_MINOR_TAC THEN C981LRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `b:real`; `t:real`] C981OS_CROSS_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C981LRS_HALF_TAC `c:real` `s:real` `z:real` THEN
  C981LRS_HALF_TAC `b:real` `t:real` `h:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C981LRS_PROD_TAC [`&0 <= h * (b - c)`] THEN
  SUBGOAL_THEN `h <= z` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN C981LRS_PROD_TAC [`&0 < (h - z) * (&1 + c)`] THEN C981LRS_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= z * (&1 - s)`] THEN
  C981LRS_PROD_TAC [`&0 <= c * (z + c - &1)`] THEN
  SUBGOAL_THEN `&3 / &20 <= &7 / &5 - s - c * (&1 - z) /\ &7 / &5 - s - c * (&1 - z) <= &2 / &5`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `s - &1 / &2` REAL_LE_SQUARE) THEN DISCH_TAC THEN C981LRS_LIN;
      C981LRS_LIN]; ALL_TAC] THEN
  SUBGOAL_THEN `b <= &117 / &100 - (&3 / &5) * t` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN
    C981LRS_PROD_TAC [`&0 < (b - (&117 / &100 - (&3 / &5) * t)) * (b + (&117 / &100 - (&3 / &5) * t))`;
      `&0 <= (&1 / &2 - t) * (&351 / &250 - (&34 / &25) * (t + &1 / &2))`] THEN
    C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC
   [`&0 <= ((&117 / &100 - (&3 / &5) * t) - b) * (&7 / &5 - s - c * (&1 - z))`;
    `&0 <= (&1 / &2 - t) * ((&2 - s) - (&3 / &5) * (&7 / &5 - s - c * (&1 - z)))`] THEN
  MP_TAC(SPEC `z:real` C981LWP_SECOND) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2; REAL_ARITH `z pow 3 = z * z * z`]) THEN
  SUBGOAL_THEN `(&1 + z * z) * ((&87 / &100) * (&7 / &5 - s - c * (&1 - z)) + (&2 - s) / &2 - &1) =
      &87 / &250 - (&187 / &100) * z + (&261 / &125) * z * z - (&87 / &100) * z * z * z`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z * z) * c = &1 - z * z` THEN
    UNDISCH_TAC `(&1 + z * z) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (b * c + t * s) - b * c + (&7 / &5) * b * s - s - (b * c + t * s) * (c + s) -
      s * (b * s - t * c) =
      s * (b * (&7 / &5 - s - c * (&1 - z)) + t * (&2 - s) - &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `z * s + c = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < b * (&7 / &5 - s - c * (&1 - z)) + t * (&2 - s) - &1` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN
    C981LRS_PROD_TAC [`&0 <= s * --(b * (&7 / &5 - s - c * (&1 - z)) + t * (&2 - s) - &1)`] THEN
    C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC
   [`&0 <= (&1 + z * z) * (((&87 / &100) * (&7 / &5 - s - c * (&1 - z)) + (&2 - s) / &2) -
                         (b * (&7 / &5 - s - c * (&1 - z)) + t * (&2 - s)))`;
    `&0 < (&1 + z * z) * (b * (&7 / &5 - s - c * (&1 - z)) + t * (&2 - s) - &1)`] THEN
  C981LRS_LIN);;

(* Lean: ru_negative *)
let C981LRS_RU_NEGATIVE = prove
 (`forall c s b t. c pow 2 + s pow 2 = &1 /\ &0 < c /\ &0 < s /\ c977cc_normal b t /\
     c981lrs_minor b t /\ b * s - t * c <= &0
     ==> &0 < s * ((b * c + t * s) * (&1 - b) + (b * s - t * c) * (b + t - &1)) +
              c pow 2 - (&2 / &5) * c * s + c + s - &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `b:real`; `t:real`] C981LRS_HALF_ORDER) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
  C981LRS_MINOR_TAC THEN C981LRS_NORMAL_TAC THEN
  C981LRS_HALF_TAC `c:real` `s:real` `z:real` THEN
  C981LRS_HALF_TAC `b:real` `t:real` `h:real` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C981LRS_PROD_TAC [`&0 <= (&1 - b) * t`] THEN
  SUBGOAL_THEN `--(&9 / &10) <= b + t - &7 / &5 - b * t /\ t - b - t * t <= &0`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [C981LRS_LIN; MP_TAC(SPEC `t:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN C981LRS_LIN];
    ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= (h - z) * h`; `&0 <= h * (&27 / &100 - h)`] THEN
  SUBGOAL_THEN `&0 <= &1 - z * h` ASSUME_TAC THENL [C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= (z * z) * (h * h)`] THEN
  SUBGOAL_THEN `&1 <= (&1 + z * z) * (&1 + h * h)` ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN MP_TAC(SPEC `h:real` REAL_LE_SQUARE) THEN
    REPEAT DISCH_TAC THEN C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= --(t - b - t * t) * (&1 - z * h)`;
                    `&0 <= ((b + t - &7 / &5 - b * t) + &9 / &10) * (h + z)`] THEN
  SUBGOAL_THEN `&0 <= (&1 + z * z) * (&1 + h * h) + &2 * (b + t - &7 / &5 - b * t) * (h + z) -
                &2 * (t - b - t * t) * (&1 - z * h)` ASSUME_TAC THENL
   [C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= (h - z) * ((&1 + z * z) * (&1 + h * h) +
     &2 * (b + t - &7 / &5 - b * t) * (h + z) - &2 * (t - b - t * t) * (&1 - z * h))`] THEN
  SUBGOAL_THEN `(&1 + z * z) * (&1 + h * h) *
      ((&1 - z + c * (b + t - &7 / &5 - b * t) + s * (t - b - t * t)) -
       (&1 - h + b * (b + t - &7 / &5 - b * t) + t * (t - b - t * t))) =
      (h - z) * ((&1 + z * z) * (&1 + h * h) + &2 * (b + t - &7 / &5 - b * t) * (h + z) -
                 &2 * (t - b - t * t) * (&1 - z * h))` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z * z) * c = &1 - z * z` THEN
    UNDISCH_TAC `(&1 + z * z) * s = &2 * z` THEN
    UNDISCH_TAC `(&1 + h * h) * b = &1 - h * h` THEN
    UNDISCH_TAC `(&1 + h * h) * t = &2 * h` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - h + b * (b + t - &7 / &5 - b * t) + t * (t - b - t * t) <=
                &1 - z + c * (b + t - &7 / &5 - b * t) + s * (t - b - t * t)` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN
    C981LRS_PROD_TAC [`&0 < ((&1 + z * z) * (&1 + h * h)) *
      ((&1 - h + b * (b + t - &7 / &5 - b * t) + t * (t - b - t * t)) -
       (&1 - z + c * (b + t - &7 / &5 - b * t) + s * (t - b - t * t)))`] THEN
    C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= (b - &43 / &50) * (&1 - (&7 / &5) * t)`;
                    `&0 <= (t - &47 / &100) * (&1 / &2 - t)`] THEN
  SUBGOAL_THEN `&1 + t * t + (&7 / &5) * b * t - b - &2 * t < &0` ASSUME_TAC THENL
   [C981LRS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `t * (&1 - h + b * (b + t - &7 / &5 - b * t) + t * (t - b - t * t)) =
                --(&1 + t * t + (&7 / &5) * b * t - b - &2 * t)` ASSUME_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN UNDISCH_TAC `h * t + b = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - h + b * (b + t - &7 / &5 - b * t) + t * (t - b - t * t)`
  ASSUME_TAC THENL
   [C981LRS_CONTRA THEN
    C981LRS_PROD_TAC [`&0 <= t * --(&1 - h + b * (b + t - &7 / &5 - b * t) + t * (t - b - t * t))`] THEN
    C981LRS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `s * ((b * c + t * s) * (&1 - b) + (b * s - t * c) * (b + t - &1)) +
      c * c - (&2 / &5) * c * s + c + s - &2 =
      s * (&1 - z + c * (b + t - &7 / &5 - b * t) + s * (t - b - t * t))` SUBST1_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
    UNDISCH_TAC `z * s + c = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN C981LRS_LIN);;

(* Lean: ru_positive *)
let C981LRS_RU_POSITIVE = prove
 (`forall c s b t. c pow 2 + s pow 2 = &1 /\ &0 < c /\ &0 < s /\ c977cc_normal b t /\
     c981lrs_minor b t
     ==> &0 < s * ((b * c + t * s) * (&1 - b) + (b * s - t * c) * (&1 + (&2 / &5) * t)) +
              c pow 2 - (&2 / &5) * c * s + c + s - &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981LRS_MINOR_TAC THEN C981LRS_NORMAL_TAC THEN
  C981LRS_HALF_TAC `c:real` `s:real` `z:real` THEN
  MP_TAC(SPEC `z:real` C981LWP_THIRD) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[real_gt] THEN DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2; REAL_ARITH `z pow 3 = z * z * z`]) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `&433 / &500 < b` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN
    C981LRS_PROD_TAC [`&0 <= (&433 / &500 - b) * (&433 / &500 + b)`;
                      `&0 <= (&1 / &2 - t) * (&1 / &2 + t)`] THEN C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= (&1 / &2 - t) * (&7 / &10 - (&3 / &5) * t)`] THEN
  SUBGOAL_THEN `&7 / &5 - b + t - (&3 / &5) * t * t <= &221 / &250` ASSUME_TAC THENL
   [C981LRS_LIN; ALL_TAC] THEN
  C981LRS_PROD_TAC [`&0 <= c * (&221 / &250 - (&7 / &5 - b + t - (&3 / &5) * t * t))`;
                    `&0 <= s * ((b + t - &1 - (&3 / &5) * b * t) - &1 / &10)`] THEN
  SUBGOAL_THEN `(&1 + z * z) * (&1 - z - (&221 / &250) * c + s / &10) =
                &29 / &250 - (&4 / &5) * z + (&471 / &250) * z * z - z * z * z` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + z * z) * c = &1 - z * z` THEN
    UNDISCH_TAC `(&1 + z * z) * s = &2 * z` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - z - (&221 / &250) * c + s / &10` ASSUME_TAC THENL
   [C981LRS_CONTRA THEN
    C981LRS_PROD_TAC [`&0 <= (&1 + z * z) * --(&1 - z - (&221 / &250) * c + s / &10)`] THEN
    C981LRS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `s * ((b * c + t * s) * (&1 - b) + (b * s - t * c) * (&1 + (&2 / &5) * t)) +
      c * c - (&2 / &5) * c * s + c + s - &2 =
      s * (&1 - z - c * (&7 / &5 - b + t - (&3 / &5) * t * t) +
           s * (b + t - &1 - (&3 / &5) * b * t))` SUBST1_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
    UNDISCH_TAC `z * s + c = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN C981LRS_LIN);;
