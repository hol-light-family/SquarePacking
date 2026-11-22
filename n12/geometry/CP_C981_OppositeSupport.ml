(* ========================================================================= *)
(* Port of Compact/Completion/C981/OppositeSupport.lean                       *)
(* (N12Compact.C981CompletionOppositeSupport).  Uniform positive-normal      *)
(* support comparisons for the opposite central angle argument.  C has       *)
(* sC = r with c977cc_normal cC r; upper is ABT_upper; the Lean lets alpha,  *)
(* beta, X, Y, H are written out.                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_LastPositivePair.ml";;

let C981OS_LIN = NLIN_TAC ~deg2:false [];;

let C981OS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C981OS_LIN; ALL_TAC];;

let C981OS_NPROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[REAL_ARITH `x * y = --x * --y`] THEN MATCH_MP_TAC REAL_LE_MUL THEN
   CONJ_TAC THEN C981OS_LIN; ALL_TAC];;

let C981OS_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C981OS_LIN; ALL_TAC];;

let C981OS_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C981OS_RING tm units = SUBGOAL_THEN tm ASSUME_TAC THENL
  [MAP_EVERY UNDISCH_TAC units THEN CONV_TAC REAL_RING; ALL_TAC];;

(* Lean: cross_order *)
let C981OS_CROSS_ORDER = prove
 (`forall c s d r. &0 < c /\ &0 <= s /\ &0 < d /\ &0 <= r /\
             c pow 2 + s pow 2 = &1 /\ d pow 2 + r pow 2 = &1 /\ &0 <= s * d - c * r
             ==> c <= d /\ r <= s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  C981OS_PROD `&0 <= s * d` THEN C981OS_PROD `&0 <= c * r` THEN
  C981OS_PROD `&0 <= (s * d - c * r) * (s * d + c * r)` THEN
  C981OS_RING `(s * d - c * r) * (s * d + c * r) = d * d - c * c`
    [`c * c + s * s = &1`; `d * d + r * r = &1`] THEN
  SUBGOAL_THEN `c <= d` ASSUME_TAC THENL
   [C981OS_CONTRA THEN C981OS_PROD `&0 < (c - d) * (c + d)` THEN C981OS_LIN; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C981OS_CONTRA THEN
  C981OS_PROD `&0 < (r - s) * (r + s)` THEN
  C981OS_PROD `&0 <= (d - c) * (c + d)` THEN C981OS_LIN);;

(* Lean: large_bounds *)
let C981OS_LARGE_BOUNDS = prove
 (`forall d r. c977cc_normal d r /\ &8 / &25 <= r
         ==> d < &237 / &250 /\ &1267 / &1000 < d + r /\ &32 / &625 <= &1 - d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C981OS_PROD `&0 <= (r - &8 / &25) * (r + &8 / &25)` THEN
  SUBGOAL_THEN `d < &237 / &250` ASSUME_TAC THENL
   [C981OS_CONTRA THEN C981OS_PROD `&0 <= (d - &237 / &250) * (d + &237 / &250)` THEN
    C981OS_LIN; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; C981OS_LIN] THEN
  C981OS_CONTRA THEN
  C981OS_FACT `r <= &1267 / &2000` THEN
  C981OS_PROD `&0 <= (&1267 / &1000 - r - d) * (&1267 / &1000 - r + d)` THEN
  C981OS_PROD `&0 <= (r - &8 / &25) * (&947 / &1000 - r)` THEN
  C981OS_LIN);;

(* Lean: upper_formula (private) *)
let C981OS_UPPER_FORMULA = prove
 (`forall cC sC uC vC aC r c s.
     sC = r /\ &0 <= c * cC + s * r
     ==> ABT_upper cC sC uC vC aC c s =
           (c * cC + s * r) * (uC + aC / &2) + (s * cC - c * r) * (vC + aC / &2) +
           (aC / &2) * (c * cC + s * r + abs(s * cC - c * r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `--c * r + s * cC = s * cC - c * r`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

let C981OS_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `r:real`] C981OS_LARGE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `&0 < cC` ASSUME_TAC THENL [C981OS_LIN; ALL_TAC] THEN
  C981OS_PROD `&0 < c * cC` THEN C981OS_PROD `&0 <= s * r` THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `r:real`; `c:real`; `s:real`]
    C981OS_UPPER_FORMULA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C981OS_LIN; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = r`));;

(* Lean: floor_upper *)
let C981OS_FLOOR_UPPER = prove
 (`forall cC sC uC vC aC r c s.
     cC * cC + sC * sC = &1 /\ &0 < aC /\
     sC = r /\ c977cc_normal cC r /\ &1 < aC /\ aC <= &1001 / &1000 /\
     &8 / &25 <= r /\ &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
     --cC <= uC /\ linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
     linside cC sC uC vC aC (&0) (--(&1 / &2))
     ==> aC - cC <= ABT_upper cC sC uC vC aC c s`,
  C981OS_SETUP_TAC THEN
  MP_TAC(ASSUME `linside cC r uC vC aC (--(&1 / &2)) (&0)`) THEN
  MP_TAC(ASSUME `linside cC r uC vC aC (&0) (--(&1 / &2))`) THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  C981OS_PROD `&0 <= (c * cC + s * r) * (uC + cC)` THEN
  ASM_CASES_TAC `&0 <= s * cC - c * r` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `cC:real`; `r:real`] C981OS_CROSS_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C981OS_LIN; STRIP_TAC] THEN
    SUBGOAL_THEN `abs(s * cC - c * r) = s * cC - c * r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]; ALL_TAC] THEN
    C981OS_PROD `&0 <= (s * cC - c * r) * (vC + aC - r / &2)` THEN
    C981OS_PROD `&0 <= (&1 - cC - &32 / &625) * (&1 - cC + &32 / &625)` THEN
    C981OS_PROD `&0 <= cC * (&1001 / &1000 - aC)` THEN
    C981OS_FACT `aC * cC - &1 + r * r / &2 <= &0` THEN
    C981OS_PROD `&0 <= r * (aC - cC / &2)` THEN
    C981OS_NPROD `&0 <= (c - cC) * (aC * cC - &1 + r * r / &2)` THEN
    C981OS_PROD `&0 <= (s - r) * (aC * r - cC * r / &2)` THEN
    C981OS_RING `(c * cC + s * r) * (aC - cC) + (s * cC - c * r) * (r / &2) =
                 c * (aC * cC - &1 + r * r / &2) + s * (aC * r - cC * r / &2)`
      [`cC * cC + r * r = &1`] THEN
    C981OS_RING `cC * (aC * cC - &1 + r * r / &2) + r * (aC * r - cC * r / &2) = aC - cC`
      [`cC * cC + r * r = &1`] THEN
    C981OS_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `r:real`; `c:real`; `s:real`] C981OS_CROSS_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C981OS_LIN; STRIP_TAC] THEN
  SUBGOAL_THEN `abs(s * cC - c * r) = --(s * cC - c * r)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> abs x = --x`) THEN C981OS_LIN; ALL_TAC] THEN
  C981OS_PROD `&0 <= --(s * cC - c * r) * (--cC / &2 - vC)` THEN
  C981OS_PROD `&0 <= cC * (aC - cC)` THEN C981OS_PROD `&0 <= cC * r` THEN
  C981OS_PROD `&0 <= (cC - r) * (aC - cC)` THEN
  C981OS_PROD `&0 <= cC * ((&3 / &2) * cC - aC)` THEN
  C981OS_FACT `&0 <= aC * cC - cC * cC + cC * r / &2` THEN
  C981OS_FACT `aC * r - r * cC - cC * cC / &2 <= &0` THEN
  C981OS_PROD `&0 <= (c - cC) * (aC * cC - cC * cC + cC * r / &2)` THEN
  C981OS_NPROD `&0 <= (s - r) * (aC * r - r * cC - cC * cC / &2)` THEN
  C981OS_RING `cC * (aC * cC - cC * cC + cC * r / &2) + r * (aC * r - r * cC - cC * cC / &2) =
               aC - cC` [`cC * cC + r * r = &1`] THEN
  C981OS_LIN);;

(* Lean: wall_upper *)
let C981OS_WALL_UPPER = prove
 (`forall cC sC uC vC aC r c s.
     cC * cC + sC * sC = &1 /\ &0 < aC /\
     sC = r /\ c977cc_normal cC r /\ &1 < aC /\ aC <= &1001 / &1000 /\
     &8 / &25 <= r /\ &0 < c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\
     --(&1) <= cC * uC - r * (vC + aC) /\ --(&1) <= r * uC + cC * vC
     ==> &17 / &500 < ABT_upper cC sC uC vC aC c s`,
  C981OS_SETUP_TAC THEN
  C981OS_PROD `&0 <= c * (cC * uC - r * (vC + aC) + &1)` THEN
  C981OS_PROD `&0 <= s * (r * uC + cC * vC + &1)` THEN
  C981OS_PROD `&0 <= cC * r` THEN
  C981OS_PROD `&0 < (aC - &1) * (&1 + cC * r)` THEN
  C981OS_PROD `&0 < ((cC + r) - &1 - &267 / &1000) * ((cC + r) - &1 + &267 / &1000)` THEN
  C981OS_FACT `&17 / &500 < aC * (&1 + cC * r) - (cC + r)` THEN
  ASM_CASES_TAC `&0 <= s * cC - c * r` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `cC:real`; `r:real`] C981OS_CROSS_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C981OS_LIN; STRIP_TAC] THEN
    SUBGOAL_THEN `abs(s * cC - c * r) = s * cC - c * r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`]; ALL_TAC] THEN
    C981OS_PROD `&0 <= cC * (&1001 / &1000 - aC)` THEN
    C981OS_FACT `aC * cC - &1 <= &0` THEN
    C981OS_PROD `&0 < (aC - &1) * (cC + r)` THEN
    C981OS_FACT `&0 <= aC * (cC + r) - &1` THEN
    C981OS_NPROD `&0 <= (c - cC) * (aC * cC - &1)` THEN
    C981OS_PROD `&0 <= (s - r) * (aC * (cC + r) - &1)` THEN
    C981OS_RING `cC * (aC * cC - &1) + r * (aC * (cC + r) - &1) = aC * (&1 + cC * r) - (cC + r)`
      [`cC * cC + r * r = &1`] THEN
    C981OS_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `r:real`; `c:real`; `s:real`] C981OS_CROSS_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C981OS_LIN; STRIP_TAC] THEN
  SUBGOAL_THEN `abs(s * cC - c * r) = --(s * cC - c * r)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &0 ==> abs x = --x`) THEN C981OS_LIN; ALL_TAC] THEN
  C981OS_PROD `&0 < (aC - &1) * (cC + r)` THEN
  C981OS_FACT `&0 <= aC * (cC + r) - &1` THEN
  C981OS_PROD `&0 <= r * (&1001 / &1000 - aC)` THEN
  C981OS_FACT `aC * r - &1 <= &0` THEN
  C981OS_PROD `&0 <= (c - cC) * (aC * (cC + r) - &1)` THEN
  C981OS_NPROD `&0 <= (s - r) * (aC * r - &1)` THEN
  C981OS_RING `cC * (aC * (cC + r) - &1) + r * (aC * r - &1) = aC * (&1 + cC * r) - (cC + r)`
    [`cC * cC + r * r = &1`] THEN
  C981OS_LIN);;
