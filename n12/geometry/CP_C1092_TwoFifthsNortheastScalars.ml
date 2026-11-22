(* ========================================================================= *)
(* Port of Compact/Completion/C1092/TwoFifthsNortheastScalars.lean           *)
(* (N12Compact.C1092TwoFifths.Scalars).  Northeast half-angle interval and   *)
(* the two continuous physical-wall width comparisons.  Scalar.              *)
(* Normal is c977cc_normal.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsData.ml";;

(* nlinarith only [facts]: NLIN_TAC on the listed assumptions only *)
let C1092TFNS_ONLY tms hints (asl,w as g) =
  let ths = map (fun t -> try snd(find (fun (_,th) -> aconv (concl th) t) asl)
                          with Failure _ -> failwith ("C1092TFNS_ONLY: " ^ string_of_term t)) tms in
  (POP_ASSUM_LIST(K ALL_TAC) THEN MAP_EVERY ASSUME_TAC ths THEN NLIN_TAC hints) g;;

let C1092TFNS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC];;

(* Lean: NorthBounds (structure) *)
let C1092TFNS_northBounds = new_definition
 `C1092TFNS_northBounds (b:real) t <=>
    &4 / &5 <= b /\ b < &15 / &17 /\ &8 / &17 < t /\ t <= &3 / &5 /\
    &8 * b < &15 * t /\ &4 * t <= &3 * b /\
    &11 / &10 < b + t - (&3 / &5) * b * t /\
    --(&23 / &125) <= b - t - &3 / &5 + (&3 / &5) * t pow 2 /\
    t + b / &2 <= &1`;;

(* Lean: north_bounds *)
let C1092TFNS_NORTH_BOUNDS = prove
 (`forall b t. c977cc_normal b t /\ &0 < b /\ &0 < t /\ &1 + b < &4 * t /\ &3 * t <= &1 + b
         ==> C1092TFNS_northBounds b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  REWRITE_TAC[C1092TFNS_northBounds; REAL_POW_2] THEN
  C1092TFNS_PROD `&0 <= (&1 + b - &3 * t) * (&1 + b + &3 * t)` THEN
  SUBGOAL_THEN `&4 / &5 <= b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092TFNS_PROD `&0 < (&4 / &5 - b) * (&1 + b)` THEN
    C1092TFNS_ONLY [`&0 <= (&1 + b - &3 * t) * (&1 + b + &3 * t)`;
                    `&0 < (&4 / &5 - b) * (&1 + b)`; `b * b + t * t = &1`] [];
    ALL_TAC] THEN
  SUBGOAL_THEN `t <= &3 / &5` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092TFNS_PROD `&0 < (t - &3 / &5) * (t + &3 / &5)` THEN
    C1092TFNS_PROD `&0 <= (b - &4 / &5) * (b + &4 / &5)` THEN
    C1092TFNS_ONLY [`&0 < (t - &3 / &5) * (t + &3 / &5)`;
                    `&0 <= (b - &4 / &5) * (b + &4 / &5)`; `b * b + t * t = &1`] [];
    ALL_TAC] THEN
  C1092TFNS_PROD `&0 < (&4 * t - &1 - b) * (&4 * t + &1 + b)` THEN
  SUBGOAL_THEN `b < &15 / &17` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092TFNS_PROD `&0 <= (b - &15 / &17) * (b + &1)` THEN
    C1092TFNS_ONLY [`&0 < (&4 * t - &1 - b) * (&4 * t + &1 + b)`;
                    `&0 <= (b - &15 / &17) * (b + &1)`; `b * b + t * t = &1`] [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 / &17 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092TFNS_PROD `&0 <= (&8 / &17 - t) * (&8 / &17 + t)` THEN
    C1092TFNS_PROD `&0 < (&15 / &17 - b) * (&15 / &17 + b)` THEN
    C1092TFNS_ONLY [`&0 <= (&8 / &17 - t) * (&8 / &17 + t)`;
                    `&0 < (&15 / &17 - b) * (&15 / &17 + b)`; `b * b + t * t = &1`] [];
    ALL_TAC] THEN
  SUBGOAL_THEN `&23 / &17 < b + t` ASSUME_TAC THENL
   [C1092TFNS_PROD `&0 < (t - &8 / &17) * (b - t + &7 / &17)` THEN
    SUBGOAL_THEN `(b + t - &23 / &17) * (b + &15 / &17) =
                  (t - &8 / &17) * (b - t + &7 / &17)` ASSUME_TAC THENL
     [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092TFNS_PROD `&0 <= (&23 / &17 - (b + t)) * (b + &15 / &17)` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092TFNS_PROD `&0 < (b + t - &23 / &17) * (&1 - (&3 / &10) * (b + t + &23 / &17))` THEN
  SUBGOAL_THEN `&11 / &10 < b + t - (&3 / &5) * b * t` ASSUME_TAC THENL
   [C1092TFNS_ONLY [`&0 < (b + t - &23 / &17) * (&1 - (&3 / &10) * (b + t + &23 / &17))`;
                    `b * b + t * t = &1`] [];
    ALL_TAC] THEN
  C1092TFNS_PROD `&0 <= (&3 / &5 - t) * (&1 - (&3 / &5) * (t + &3 / &5))` THEN
  SUBGOAL_THEN `t + b / &2 <= &1` ASSUME_TAC THENL
   [C1092TFNS_PROD `&0 <= (&3 / &5 - t) * (b + &4 / &5 - (t + &3 / &5) / &2)` THEN
    SUBGOAL_THEN `(&1 - t - b / &2) * (b + &4 / &5) =
                  (&3 / &5 - t) * (b + &4 / &5 - (t + &3 / &5) / &2)` ASSUME_TAC THENL
     [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092TFNS_PROD `&0 < (t + b / &2 - &1) * (b + &4 / &5)` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  C1092TFNS_ONLY [`&0 <= (&3 / &5 - t) * (&1 - (&3 / &5) * (t + &3 / &5))`;
                  `&4 / &5 <= b`] []);;

(* Lean: small_right *)
let C1092TFNS_SMALL_RIGHT = prove
 (`forall d r. c977cc_normal d r /\ r <= (&2 / &5) * d
         ==> r <= &2 / &5 /\ r <= (&1 + d) / &5 /\ &0 <= d + r / &5 - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (can (term_match [] `c977cc_normal x y`) o concl)) THEN
  SUBGOAL_THEN `r <= &2 / &5 /\ r <= (&1 + d) / &5` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092TFNS_PROD `&0 <= r * ((&1 + d) / &5 - r)` THEN
  SUBGOAL_THEN `(&1 + d) * (d + r / &5 - &1) = r * ((&1 + d) / &5 - r)` ASSUME_TAC THENL
   [UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092TFNS_PROD `&0 < (&1 + d) * (&1 - (d + r / &5))` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_width *)
let C1092TFNS_NEGATIVE_WIDTH = prove
 (`forall b t d r. c977cc_normal b t /\ c977cc_normal d r /\ r <= (&2 / &5) * d
             ==> &2 * t + b <= (&2 * t + b) * d + b * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092TFNS_SMALL_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  C1092TFNS_PROD `&0 <= (&2 * t + b) * ((&1 + d) / &5 - r)` THEN
  C1092TFNS_PROD `&0 <= (&1 + d) * (b - (&2 * t + b) / &5)` THEN
  SUBGOAL_THEN `&0 <= b * (&1 + d) - (&2 * t + b) * r` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092TFNS_PROD `&0 <= r * (b * (&1 + d) - (&2 * t + b) * r)` THEN
  SUBGOAL_THEN `(&1 + d) * ((&2 * t + b) * d + b * r - (&2 * t + b)) =
                r * (b * (&1 + d) - (&2 * t + b) * r)` ASSUME_TAC THENL
   [UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092TFNS_PROD `&0 < (&1 + d) * ((&2 * t + b) - ((&2 * t + b) * d + b * r))` THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_width *)
let C1092TFNS_POSITIVE_WIDTH = prove
 (`forall b t d r. c977cc_normal b t /\ C1092TFNS_northBounds b t /\
             c977cc_normal d r /\ r <= (&2 / &5) * d
             ==> &0 <= &1 - b - &2 * t + ((&2 * t + b) * d + (&2 * t - b) * r) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] C1092TFNS_SMALL_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092TFNS_northBounds]) THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092TFNS_PROD `&0 <= (&1 - d / &2 + r / &2) * ((&3 / &4) * (b + &4 / &5) - (t + &3 / &5))` THEN
  C1092TFNS_PROD `&0 <= ((&2 - d - r) - (&3 / &4) * (&1 - d / &2 + r / &2)) * (b + &4 / &5)` THEN
  SUBGOAL_THEN `&0 <= (&2 - d - r) * (b + &4 / &5) - (&1 - d / &2 + r / &2) * (t + &3 / &5)`
    ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092TFNS_PROD `&0 <= (&3 / &5 - t) *
     ((&2 - d - r) * (b + &4 / &5) - (&1 - d / &2 + r / &2) * (t + &3 / &5))` THEN
  SUBGOAL_THEN
   `((&1 - b * (&1 - d / &2 + r / &2) - t * (&2 - d - r)) - (d + r / &5 - &1)) * (b + &4 / &5) =
    (&3 / &5 - t) *
     ((&2 - d - r) * (b + &4 / &5) - (&1 - d / &2 + r / &2) * (t + &3 / &5))` ASSUME_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - b * (&1 - d / &2 + r / &2) - t * (&2 - d - r)) - (d + r / &5 - &1)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092TFNS_PROD `&0 < (--((&1 - b * (&1 - d / &2 + r / &2) - t * (&2 - d - r)) -
                            (d + r / &5 - &1))) * (b + &4 / &5)` THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
