(* ========================================================================= *)
(* Port of Compact/Cases/C868/LowerNegative.lean (Jatloe, N12-jatloe).        *)
(* The negative lower-left square has enough support in every nonnegative   *)
(* canonical direction.  Normal: c977cc_normal; upper / lower: ABT_upper /   *)
(* ABT_lower; strict_bounds: ABT_STRICT_BOUNDS; upper_in_bands:              *)
(* C977NCO_UPPER_IN_BANDS; C868CentralSupport.modes: C868CS_MODES;           *)
(* C868CentralSeparation.alternatives: C868CSEP_ALTERNATIVES.                *)
(* turnFrame^3 o pullSwap is the transpose (C868LN_TRANSPOSE).               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C868CentralSeparation.ml";;

(* products of factors, each factor proved by linear arithmetic *)
let rec C868LN_PROD_TAC g =
  ((MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C868LN_PROD_TAC) ORELSE
   (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C868LN_PROD_TAC) ORELSE
   NLIN_TAC ~deg2:false []) g;;

let C868LN_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C868LN_PROD_TAC; ALL_TAC];;

let C868LN_NORMAL_TAC =
  FIRST_X_ASSUM(fun th ->
    let th' = check (fun th -> fst(strip_comb(concl th)) = `c977cc_normal`) th in
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th') THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th'));;

(* turnFrame (turnFrame (turnFrame (pullSwap A))) has c, -s, loV, loU *)
let C868LN_TRANSPOSE = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: modes *)
let C868LN_MODES = prove
 (`forall cA sA uA vA aA.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal cA (--sA) /\ &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5)
     ==> (&8 / &5) * cA - sA <= vA \/
         ((&8 / &5) * cA + sA <= uA /\ &13 * --sA < cA) \/
         (cA + (&8 / &5) * sA <= uA /\ cA - (&8 / &5) * sA <= vA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `--sA`; `vA:real`; `uA:real`; `aA:real`] C868CS_MODES) THEN
  ASM_REWRITE_TAC[C868LN_TRANSPOSE] THEN
  C868LN_NORMAL_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

(* Lean: support_scalar (private) *)
let C868LN_SUPPORT_SCALAR = prove
 (`forall c s C t a u v.
     c977cc_normal c s /\ c977cc_normal C t /\ &1 < a /\
     t / &2 < u /\ --(&13 / &50) * t < v /\
     (a - t - (&2 / &5) * C <= v \/
      (a - (&2 / &5) * C + t <= u /\ &13 * t < C) \/
      (a - C + (&2 / &5) * t <= u /\ a - C - (&2 / &5) * t <= v))
     ==> &0 < (c * C - s * t) * u + (s * C + c * t) * v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REPEAT(DISCH_THEN(fun th -> ASSUME_TAC th THEN
    (if fst(strip_comb(concl th)) = `c977cc_normal` then C868LN_NORMAL_TAC
     else ALL_TAC))) THEN
  SUBGOAL_THEN `&0 <= c * C - s * t` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s * C + c * t` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c * C - s * t) + (s * C + c * t)` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THENL
  [SUBGOAL_THEN `t + (&2 / &5) * C <= &1` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < u /\ &0 < v` STRIP_ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `u <= v` THENL
   [C868LN_PROD `&0 < ((c * C - s * t) + (s * C + c * t)) * u` THEN
    C868LN_PROD `&0 <= (s * C + c * t) * (v - u)`;
    C868LN_PROD `&0 < ((c * C - s * t) + (s * C + c * t)) * v` THEN
    C868LN_PROD `&0 <= (c * C - s * t) * (u - v)`] THEN
   NLIN_TAC ~deg2:false [];
   SUBGOAL_THEN `t < &1 / &13` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   C868LN_PROD `&0 <= c * (C - &13 * t)` THEN
   C868LN_PROD `&0 <= t * (c - s)` THEN
   C868LN_PROD `&0 <= C * (c - s)` THEN
   C868LN_PROD `&0 <= c * (C - t)` THEN
   C868LN_PROD `&0 < c * C` THEN
   SUBGOAL_THEN `(&12 / &13) * (c * C) <= c * C - s * t /\
                 s * C + c * t <= &2 * (c * C)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < c * C - s * t /\ &3 / &5 < u /\ --(&1 / &50) < v`
     STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   C868LN_PROD `&0 < (c * C - s * t) * (u - &3 / &5)` THEN
   C868LN_PROD `&0 <= (s * C + c * t) * (v + &1 / &50)` THEN
   NLIN_TAC ~deg2:false [];
   SUBGOAL_THEN `&0 <= (&1 - C) * (C + t) + (&2 / &5) * t * (C - t)`
     ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
   C868LN_PROD `&0 <= (c - s) * ((&1 - C) * (C + t) + (&2 / &5) * t * (C - t))` THEN
   C868LN_PROD `&0 <= ((&2 * s) * (&1 - C)) * ((&3 / &5) * C - &2 / &5)` THEN
   SUBGOAL_THEN `s * (C * C + t * t) = s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (c * C - s * t) * (&1 - C + (&2 / &5) * t) +
                       (s * C + c * t) * (&1 - C - (&2 / &5) * t)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   C868LN_PROD `&0 <= (c * C - s * t) * (u - (a - C + (&2 / &5) * t))` THEN
   C868LN_PROD `&0 <= (s * C + c * t) * (v - (a - C - (&2 / &5) * t))` THEN
   C868LN_PROD `&0 < ((c * C - s * t) + (s * C + c * t)) * (a - &1)` THEN
   NLIN_TAC ~deg2:false []]);;

(* Lean: support *)
let C868LN_SUPPORT = prove
 (`forall cA sA uA vA aA c s.
     cA * cA + sA * sA = &1 /\ &0 < aA /\
     c977cc_normal c s /\ c977cc_normal cA (--sA) /\ &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5)
     ==> &2 * (c + s) < ABT_upper cA sA uA vA aA c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] C868LN_MODES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `cA:real`; `--sA`; `aA:real`;
                `uA + aA - &2 * cA - &2 * sA`; `vA + aA + &2 * sA - &2 * cA`]
    C868LN_SUPPORT_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
  [MP_TAC(ASSUME `linside cA sA uA vA aA (&2) (&3 / &2)`) THEN
   MP_TAC(ASSUME `linside cA sA uA vA aA (&87 / &50) (&2)`) THEN
   FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
   REWRITE_TAC[linside] THEN POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC;
   DISCH_TAC] THEN
  REPEAT C868LN_NORMAL_TAC THEN
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
  SUBGOAL_THEN `abs(c * cA + s * sA) = c * cA + s * sA /\
                abs(--c * sA + s * cA) = --c * sA + s * cA`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(c + s) * (cA * cA + sA * sA) = c + s` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: only_lower_normal *)
let C868LN_ONLY_LOWER_NORMAL = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cA (--sA) /\ c977cc_normal cH sH /\
     aA = aH /\ &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&2) (&2) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ldisj cA sA uA vA aA cH sH uH vH aH
     ==> vA + aA <= ABT_lower cH sH uH vH aH (--sA) cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aH`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aH:real`;
                `cH:real`; `sH:real`] C868LN_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aH:real`;
                `&2`; `&3 / &2`; `cA:real`; `sA:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aH:real`;
                `&3 / &2`; `&2`; `--sH`; `cH:real`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_POW_2] THEN
   UNDISCH_TAC `cH * cH + sH * sH = &1` THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aH:real`;
                `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`]
    C868CSEP_ALTERNATIVES) THEN
  REPEAT C868LN_NORMAL_TAC THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN
   (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC ORELSE NLIN_TAC ~deg2:false []); ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~a ==> a \/ b ==> b`) THEN DISCH_TAC THEN
  UNDISCH_TAC `linside cH sH uH vH aH (&2) (&2)` THEN REWRITE_TAC[linside] THEN
  STRIP_TAC THEN NLIN_TAC ~deg2:false []);;
