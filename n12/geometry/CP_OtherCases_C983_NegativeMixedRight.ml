(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeMixedRight.lean        *)
(* (N12Compact.Completion.OtherCases.C983.NegativeMixedRight).  The mixed   *)
(* branch with the southeast/right separator on the right transverse axis    *)
(* and the northeast/right separator on the northeast parallel axis.         *)
(* Conventions of NegativeRightOwned.ml: squares E, N, R are                 *)
(* cE sE uE vE aE, cN sN uN vN aN, cR sR uR vR aR (unit normals / positive   *)
(* sides explicit); RightTripleData.Input = ocrtd_input, RightProfile =      *)
(* ocrtd_rightprofile, NegativeTripleFaces.Data = ccntf_data, upper / lower  *)
(* = ABT_upper / ABT_lower.  The private residual is c983nmr_residual; the   *)
(* Lean abbreviation q = (1 - b) / a is introduced with a * q = 1 - b.       *)
(* Tag C983NMR_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeRightOwned.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeRightSeparation.ml";;

let C983NMR_LIN = NLIN_TAC ~deg2:false [];;

let C983NMR_MAX_POS = REAL_ARITH `forall x. &0 <= x ==> max x (&0) = x`;;
let C983NMR_MAX_NEG = REAL_ARITH `forall x. ~(&0 <= x) ==> max x (&0) = &0`;;

(* Lean: residual (private) *)
let c983nmr_residual = new_definition
 `c983nmr_residual (a:real) (b:real) (d:real) (r:real) (v:real) =
    a * (&1 - r) + r * v + (a + b - &2) * (a * d + b * r) + a * max (a * r - b * d) (&0)`;;

(* Lean: scalar_bounds (private) *)
let C983NMR_SCALAR_BOUNDS = prove
 (`forall a b d r. &0 < a /\ &0 <= b /\ &0 < d /\ &0 < r /\ a pow 2 + b pow 2 = &1 /\
     d pow 2 + r pow 2 = &1
     ==> &0 < a * d + b * r /\ a * d + b * r <= &1 /\ a <= &1 /\ b <= &1 /\ d <= &1 /\
         &1 <= a + b /\ a + b < &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983NRO_PROD `&0 < a * d` THEN C983NRO_PROD `&0 <= b * r` THEN
  C983NRO_RING `(a * d + b * r) pow 2 + (a * r - b * d) pow 2 = &1` THEN
  SUBGOAL_THEN `a * d + b * r <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC C983NRO_UNIT_LE THEN EXISTS_TAC `a * r - b * d` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a <= &1 /\ b <= &1 /\ d <= &1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC C983NRO_UNIT_LE THEN
    ASM_MESON_TAC[REAL_ADD_SYM]; ALL_TAC] THEN
  C983NRO_PROD `&0 <= a * b` THEN
  SUBGOAL_THEN `&1 <= a + b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NRO_PROD `&0 < (&1 - (a + b)) * (&1 + (a + b))` THEN C983NMR_LIN; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY C983NMR_LIN THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `a - &1:real`; SQ_NONNEG `b - &1:real`]);;

let C983NMR_BOUNDS_TAC =
  MP_TAC(SPECL [`a:real`; `b:real`; `d:real`; `r:real`] C983NMR_SCALAR_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

(* Lean: scalar_universal (private) *)
let C983NMR_SCALAR_UNIVERSAL = prove
 (`forall a b d r v. &0 < a /\ &0 <= b /\ &0 < d /\ &0 < r /\ a pow 2 + b pow 2 = &1 /\
     d pow 2 + r pow 2 = &1 /\ r < &3 / &4 /\ d + r / &7 < &1 /\
     &1 - (&1 - b) / a <= v /\ b - a / &7 <= v
     ==> &0 <= c983nmr_residual a b d r v`,
  REPEAT GEN_TAC THEN ABBREV_TAC `q = (&1 - b) / a` THEN STRIP_TAC THEN
  C983NMR_BOUNDS_TAC THEN
  SUBGOAL_THEN `a * q = &1 - b` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C983NRO_FACT `&0 < &2 - a - b` THEN C983NRO_FACT `&2 - a - b <= &1` THEN
  ASM_CASES_TAC `&4 / &5 <= b` THENL
   [SUBGOAL_THEN `a <= &3 / &5` ASSUME_TAC THENL
     [C983NRO_PROD `&0 <= (b - &4 / &5) * (b + &4 / &5)` THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NRO_PROD `&0 < (a - &3 / &5) * (a + &3 / &5)` THEN C983NMR_LIN; ALL_TAC] THEN
    C983NRO_PROD `&0 <= (&2 - a - b) * (&1 - d - r / &7)` THEN
    C983NRO_PROD `&0 <= (&1 - (&2 - a - b)) * (&1 - &4 / &3 * r)` THEN
    C983NRO_PROD `&0 <= a * ((&2 - a - b) * (&1 - d - r / &7) +
                             (&1 - (&2 - a - b)) * (&1 - &4 / &3 * r))` THEN
    C983NRO_PROD `&0 <= r * (&1 - b)` THEN
    C983NRO_PROD `&0 <= (r * (&1 - b)) * (&25 + &4 * b - &46 * a)` THEN
    C983NRO_PROD `&0 <= r * (v - (b - a / &7))` THEN
    SUBGOAL_THEN `&0 <= max (a * r - b * d) (&0)` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    C983NRO_PROD `&0 <= a * max (a * r - b * d) (&0)` THEN
    C983NRO_RING `a * (&1 - r) + r * (b - a / &7) + (a + b - &2) * (a * d + b * r) =
        a * ((&2 - a - b) * (&1 - d - r / &7) + (&1 - (&2 - a - b)) * (&1 - &4 / &3 * r)) +
        (r / &21) * (&1 - b) * (&25 + &4 * b - &46 * a)` THEN
    REWRITE_TAC[c983nmr_residual] THEN C983NMR_LIN;
    ALL_TAC] THEN
  C983NRO_PROD `&0 <= (&1 - b) * (&1 - a) pow 2` THEN
  C983NRO_RING `a * (&2 * a - &2 + b * (&2 - a - q)) = (&1 - b) * (&1 - a) pow 2` THEN
  SUBGOAL_THEN `&0 <= &2 * a - &2 + b * (&2 - a - q)` ASSUME_TAC THENL
   [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
    C983NMR_LIN; ALL_TAC] THEN
  C983NRO_PROD `&0 <= r * (v - (&1 - q))` THEN
  ASM_CASES_TAC `&0 <= a * r - b * d` THENL
   [C983NRO_RING `r * (a * d + b * r) - d * (a * r - b * d) = b` THEN
    C983NRO_PROD `&0 <= r * (&1 - (a * d + b * r))` THEN
    C983NRO_PROD `&0 <= d * (a * r - b * d)` THEN
    C983NRO_FACT `b <= r` THEN
    C983NRO_PROD `&0 <= b * (&1 - b)` THEN C983NRO_PROD `&0 <= a * (&1 - a)` THEN
    C983NRO_RING `a * (&2 - a - q) = b - (&1 - a) pow 2` THEN
    SUBGOAL_THEN `&0 <= &2 - a - q` ASSUME_TAC THENL
     [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
      C983NMR_LIN; ALL_TAC] THEN
    C983NRO_PROD `&0 <= (&2 - a) * (&1 - (a * d + b * r))` THEN
    C983NRO_PROD `&0 <= (r - b) * (&2 - a - q)` THEN
    ASM_SIMP_TAC[c983nmr_residual; C983NMR_MAX_POS] THEN
    C983NRO_RING `a * (&1 - r) + r * v + (a + b - &2) * (a * d + b * r) + a * (a * r - b * d) =
                  a + (a - &2) * (a * d + b * r) + r * (&1 + v - a)` THEN
    C983NMR_LIN;
    ALL_TAC] THEN
  C983NRO_RING `b * (a * d + b * r) + a * (a * r - b * d) = r` THEN
  C983NRO_PROD `&0 <= b * (&1 - (a * d + b * r))` THEN
  C983NRO_PROD `&0 <= a * --(a * r - b * d)` THEN
  C983NRO_FACT `r <= b` THEN
  C983NRO_PROD `&0 <= (&2 - a - b) * (&1 - (a * d + b * r))` THEN
  ASM_SIMP_TAC[c983nmr_residual; C983NMR_MAX_NEG] THEN
  ASM_CASES_TAC `&1 - q <= a` THENL
   [C983NRO_PROD `&0 <= (b - r) * (a - (&1 - q))` THEN C983NMR_LIN;
    SUBGOAL_THEN `&2 <= &2 * a + b` ASSUME_TAC THENL
     [C983NRO_PROD `&0 <= b * (&4 - &5 * b)` THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NRO_PROD `&0 < (&2 - (&2 * a + b)) * (&2 - b + &2 * a)` THEN C983NMR_LIN;
      ALL_TAC] THEN
    C983NRO_PROD `&0 <= r * (&1 - q - a)` THEN C983NMR_LIN]);;

(* Lean: scalar_shallow (private) *)
let C983NMR_SCALAR_SHALLOW = prove
 (`forall a b d r v. &0 < a /\ &0 <= b /\ &0 < d /\ &0 < r /\ a pow 2 + b pow 2 = &1 /\
     d pow 2 + r pow 2 = &1 /\ &29 / &100 < r /\ b <= &9 / &41 /\
     &1 + &4 / &5 * b - a <= v
     ==> &0 <= c983nmr_residual a b d r v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C983NMR_BOUNDS_TAC THEN
  SUBGOAL_THEN `&40 / &41 <= a` ASSUME_TAC THENL
   [C983NRO_PROD `&0 <= (&9 / &41 - b) * (&9 / &41 + b)` THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NRO_PROD `&0 < (&40 / &41 - a) * (&40 / &41 + a)` THEN C983NMR_LIN; ALL_TAC] THEN
  C983NRO_PROD `&0 <= a * (r - &29 / &100)` THEN
  C983NRO_PROD `&0 <= b * (&1 - d)` THEN
  C983NRO_FACT `&0 <= a * r - b * d` THEN
  C983NRO_PROD `&0 <= (&2 - a) * (&1 - (a * d + b * r))` THEN
  C983NRO_PROD `&0 <= (r - &29 / &100) * (&2 + &4 / &5 * b - &2 * a)` THEN
  C983NRO_PROD `&0 <= r * (v - (&1 + &4 / &5 * b - a))` THEN
  C983NRO_PROD `&0 <= (&1 - a) * (&14 / &25 * (&1 + a) - &1)` THEN
  C983NRO_FACT `&1 - a <= &14 / &25 * b pow 2` THEN
  C983NRO_PROD `&0 <= b * (&29 / &125 - &497 / &625 * b)` THEN
  C983NRO_FACT `&0 <= &2 * a - &2 + &29 / &100 * (&2 + &4 / &5 * b - &2 * a)` THEN
  ASM_SIMP_TAC[c983nmr_residual; C983NMR_MAX_POS] THEN
  C983NRO_RING `a * (&1 - r) + r * v + (a + b - &2) * (a * d + b * r) + a * (a * r - b * d) =
                a + (a - &2) * (a * d + b * r) + r * (&1 + v - a)` THEN
  C983NMR_LIN);;

(* the final step of wall_residual, with J = max B 0 written out as j *)
let C983NMR_WALL_TAIL j =
  let sub = subst [j, `j:real`] in
  let lexpr = sub `(cR * cN + --sR * --sN) * uR - (cR * --sN - --sR * cN) * vR - j * aR` in
  C983NRO_FACT `&1 - --sN < uN + aN` THEN
  C983NRO_FACT (mk_binop `(<=):real->real->bool` `uN + aN` lexpr) THEN
  C983NRO_FACT `cR * (uR + aR) + --sR * (vR + aR) <= &2` THEN
  C983NRO_PROD `&0 < cR * ((uN + aN) - (&1 - --sN))` THEN
  C983NRO_PROD (mk_binop `(<=):real->real->bool` `&0`
    (mk_binop `( * ):real->real->real` `cR:real` (mk_binop `(-):real->real->real` lexpr `uN + aN`))) THEN
  C983NRO_PROD `&0 <= (cR * cN + --sR * --sN) * (&2 - (cR * (uR + aR) + --sR * (vR + aR)))` THEN
  C983NRO_PROD `&0 <= (cR + --sR) * (cR * cN + --sR * --sN)` THEN
  C983NRO_PROD (sub `&0 <= cR * j`) THEN
  C983NRO_PROD (sub `&0 <= ((cR + --sR) * (cR * cN + --sR * --sN) + cR * j) * (aR - &1)`) THEN
  C983NRO_RING (mk_eq(mk_binop `(-):real->real->real`
      `(cR * cN + --sR * --sN) * (cR * (uR + aR) + --sR * (vR + aR))`
      (mk_binop `( * ):real->real->real` `cR:real` lexpr),
    sub `--sN * vR + ((cR + --sR) * (cR * cN + --sR * --sN) + cR * j) * aR`)) THEN
  C983NMR_LIN;;

(* Lean: wall_residual (private) *)
let C983NMR_WALL_RESIDUAL = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     ABT_upper cN sN uN vN aN cN sN <= ABT_lower cR sR uR vR aR cN sN
     ==> c983nmr_residual cR (--sR) cN (--sN) vR < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C983NRO_INPUT_TAC THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[octoqp_data] o
    check (fun th -> concl th = `octoqp_data cN sN uN vN aN`)) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "real_le" (concl th) &&
    lhand(concl th) = `ABT_upper cN sN uN vN aN cN sN`)) THEN
  ASM_REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN DISCH_TAC THEN
  C983NRO_PROD `&0 < cR * cN` THEN C983NRO_PROD `&0 <= --sR * --sN` THEN
  SUBGOAL_THEN `abs(cN * cR + sN * sR) = cR * cN + --sR * --sN` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x = y ==> abs x = y`) THEN
    CONJ_TAC THENL [C983NMR_LIN; REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= cR * --sN - --sR * cN` THENL
   [SUBGOAL_THEN `abs(--cN * sR + sN * cR) = cR * --sN - --sR * cN` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x = --y ==> abs x = y`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[c983nmr_residual; C983NMR_MAX_POS] THEN
    C983NMR_WALL_TAIL `cR * --sN - --sR * cN`;
    SUBGOAL_THEN `abs(--cN * sR + sN * cR) = --(cR * --sN - --sR * cN)` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --y /\ x = --y ==> abs x = --y`) THEN
      CONJ_TAC THENL [C983NMR_LIN; REAL_ARITH_TAC]; ALL_TAC] THEN
    ASM_SIMP_TAC[c983nmr_residual; C983NMR_MAX_NEG] THEN
    C983NMR_WALL_TAIL `&0`]);;

(* Lean: vertex_floor (private) *)
let C983NMR_VERTEX_FLOOR = prove
 (`forall cE sE uE vE aE t cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     ccntf_data cE sE uE vE aE t /\ ocrtd_rightprofile cR sR uR vR aR /\
     ABT_upper cE sE uE vE aE (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR
     ==> --sR - cR / &7 < vR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`]
    C983NRS_SOUTHEAST_VERTEX_COORDINATES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`]
    C983NCO_UPPER_VERTEX_Y_GT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cE * (uE + aE) + t * (vE + aE)`; `--t * (uE + aE) + cE * (vE + aE)`;
                `--sR:real`; `cR:real`] ABT_CLOSED_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocrtd_rightprofile] o
    check (fun th -> concl th = `ocrtd_rightprofile cR sR uR vR aR`)) THEN
  C983NRO_PROD `&0 <= --sR * ((cE * (uE + aE) + t * (vE + aE)) - &1)` THEN
  C983NRO_PROD `&0 < cR * ((--t * (uE + aE) + cE * (vE + aE)) - --(&1) / &7)` THEN
  C983NMR_LIN);;

let C983NMR_ANTS_TAC =
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE C983NMR_LIN); DISCH_TAC];;

(* Lean: impossible *)
let C983NMR_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     ABT_upper cN sN uN vN aN cN sN <= ABT_lower cR sR uR vR aR cN sN /\
     ABT_upper cE sE uE vE aE (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C983NMR_WALL_RESIDUAL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  C983NRO_INPUT_TAC THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[octoqp_data] o
    check (fun th -> concl th = `octoqp_data cN sN uN vN aN`)) THEN
  C983NRO_RING `cN pow 2 + (--sN) pow 2 = &1` THEN
  SUBGOAL_THEN `ocrtd_rightprofile cR sR uR vR aR` ASSUME_TAC THENL
   [REWRITE_TAC[ocrtd_rightprofile] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C983NMR_VERTEX_FLOOR) THEN
  C983NMR_ANTS_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] C983NCO_NORTH_SINE_GT) THEN
  C983NMR_ANTS_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] C983NCO_NORTH_PROJECTION_LT) THEN
  C983NMR_ANTS_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] OCTOQS_PROFILE_BOUNDS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE C983NMR_LIN); STRIP_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNV) THEN
  C983NMR_ANTS_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th) &&
    can (find_term ((=) `vE:real`)) (concl th))) THENL
   [ASM_CASES_TAC `--sR <= &9 / &41` THENL
     [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`;
                    `cR:real`; `--sR`] C983NRO_SOUTHEAST_FIRST_SHALLOW) THEN
      C983NMR_ANTS_TAC THEN
      MP_TAC(SPECL [`cR:real`; `--sR`; `cN:real`; `--sN`; `vR:real`] C983NMR_SCALAR_SHALLOW) THEN
      C983NMR_ANTS_TAC THEN C983NMR_LIN;
      MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`;
                    `cR:real`; `--sR`] C983NRO_SOUTHEAST_FIRST_STEEP) THEN
      C983NMR_ANTS_TAC THEN
      MP_TAC(SPECL [`cR:real`; `--sR`; `cN:real`; `--sN`; `vR:real`] C983NMR_SCALAR_UNIVERSAL) THEN
      C983NMR_ANTS_TAC THEN C983NMR_LIN];
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`;
                  `cR:real`; `--sR`] C983NRO_SOUTHEAST_SECOND_FLOOR) THEN
    C983NMR_ANTS_TAC THEN
    MP_TAC(SPECL [`cR:real`; `--sR`; `cN:real`; `--sN`; `vR:real`] C983NMR_SCALAR_UNIVERSAL) THEN
    C983NMR_ANTS_TAC THEN C983NMR_LIN]);;
