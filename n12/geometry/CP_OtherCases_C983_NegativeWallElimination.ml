(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeWallElimination.lean   *)
(* (Jatloe, N12-jatloe; namespace                                            *)
(*  N12Compact.Completion.OtherCases.C983.NegativeWallElimination).          *)
(* Both separators refer to one physical right square R = cR sR uR vR aR.    *)
(* Lean upper/lower are ABT_upper/ABT_lower; correction R and delta R are    *)
(* parametrized by R's normal (c, s).                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

let OC983NWE_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let OC983NWE_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: correction (definition) *)
let oc983nwe_correction = new_definition
 `oc983nwe_correction (c:real) (s:real) (x:real) (y:real) =
    min (x * c + y * s) (&0) + min (--x * s + y * c) (&0)`;;

(* Lean: delta (definition) *)
let oc983nwe_delta = new_definition
 `oc983nwe_delta (c:real) (s:real) (x:real) (y:real) (z:real) (w:real) =
    (x * w + y * z) * (c - s) - w * oc983nwe_correction c s x y -
    y * oc983nwe_correction c s z (--w)`;;

(* Lean: twice_min (private) *)
let OC983NWE_TWICE_MIN = prove
 (`forall a. &2 * min a (&0) = a - abs a`,
  GEN_TAC THEN REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: lower_formula *)
let OC983NWE_LOWER_FORMULA = prove
 (`forall c s u v a x y.
     ABT_lower c s u v a x y =
     (x * c + y * s) * u + (--x * s + y * c) * v + a * oc983nwe_correction c s x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C981SF_LOWER_IN_BANDS; oc983nwe_correction] THEN
  MP_TAC(SPEC `x * c + y * s` OC983NWE_TWICE_MIN) THEN
  MP_TAC(SPEC `--x * s + y * c` OC983NWE_TWICE_MIN) THEN
  SPEC_TAC(`min (x * c + y * s) (&0)`,`m1:real`) THEN
  SPEC_TAC(`min (--x * s + y * c) (&0)`,`m2:real`) THEN
  SPEC_TAC(`abs (x * c + y * s)`,`b1:real`) THEN
  SPEC_TAC(`abs (--x * s + y * c)`,`b2:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `b1 = (x * c + y * s) - &2 * m1 /\ b2 = (--x * s + y * c) - &2 * m2`
  (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: eliminate *)
let OC983NWE_ELIMINATE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR x y z w.
     &1 < aR /\ &0 < cR /\ sR <= &0 /\
     cR * (uR + aR) - sR * (vR + aR) <= &2 /\
     &0 <= x /\ &0 < y /\ &0 < z /\ &0 <= w /\
     ABT_upper cE sE uE vE aE x y <= ABT_lower cR sR uR vR aR x y /\
     ABT_upper cN sN uN vN aN z (--w) <= ABT_lower cR sR uR vR aR z (--w)
     ==> w * ABT_upper cE sE uE vE aE x y + y * ABT_upper cN sN uN vN aN z (--w) +
         aR * oc983nwe_delta cR sR x y z w <= &2 * (x * w + y * z) /\
         &0 < oc983nwe_delta cR sR x y z w /\
         w * ABT_upper cE sE uE vE aE x y + y * ABT_upper cN sN uN vN aN z (--w) +
         oc983nwe_delta cR sR x y z w - &2 * (x * w + y * z) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OC983NWE_PROD_TAC `x:real` `w:real` THEN OC983NWE_PRODLT_TAC `y:real` `z:real` THEN
  SUBGOAL_THEN `oc983nwe_correction cR sR x y <= &0 /\
                oc983nwe_correction cR sR z (--w) <= &0` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[oc983nwe_correction; real_min] THEN
   REPEAT COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  OC983NWE_PROD_TAC `w:real` `--oc983nwe_correction cR sR x y` THEN
  OC983NWE_PROD_TAC `y:real` `--oc983nwe_correction cR sR z (--w)` THEN
  OC983NWE_PRODLT_TAC `x * w + y * z` `cR - sR` THEN
  SUBGOAL_THEN `&0 < oc983nwe_delta cR sR x y z w` ASSUME_TAC THENL
  [REWRITE_TAC[oc983nwe_delta] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `w * ABT_lower cR sR uR vR aR x y + y * ABT_lower cR sR uR vR aR z (--w) +
    aR * oc983nwe_delta cR sR x y z w =
    (x * w + y * z) * (cR * (uR + aR) - sR * (vR + aR))` ASSUME_TAC THENL
  [REWRITE_TAC[OC983NWE_LOWER_FORMULA; oc983nwe_delta] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  OC983NWE_PROD_TAC `w:real`
    `ABT_lower cR sR uR vR aR x y - ABT_upper cE sE uE vE aE x y` THEN
  OC983NWE_PROD_TAC `y:real`
    `ABT_lower cR sR uR vR aR z (--w) - ABT_upper cN sN uN vN aN z (--w)` THEN
  OC983NWE_PROD_TAC `x * w + y * z` `&2 - (cR * (uR + aR) - sR * (vR + aR))` THEN
  OC983NWE_PRODLT_TAC `aR - &1` `oc983nwe_delta cR sR x y z w` THEN
  SUBGOAL_THEN
   `w * ABT_upper cE sE uE vE aE x y + y * ABT_upper cN sN uN vN aN z (--w) +
    aR * oc983nwe_delta cR sR x y z w <= &2 * (x * w + y * z)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []);;

(* Lean: universal_identity *)
let OC983NWE_UNIVERSAL_IDENTITY = prove
 (`forall a b u v ell. a pow 2 + b pow 2 = &1
     ==> a * (a * (u + ell) + b * (v + ell) - &2) =
         a pow 2 * (u + b - &1) + b * (a * v - a - b + &1) + a * (a + b) * (ell - &1) +
         (&1 - b) * (&1 - a) pow 2`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

(* Lean: universal_impossible *)
let OC983NWE_UNIVERSAL_IMPOSSIBLE = prove
 (`forall a b u v ell. &0 < a /\ &0 <= b /\ a pow 2 + b pow 2 = &1 /\ &1 < ell /\
     &1 - b < u /\ a + b - &1 < a * v /\ a * (u + ell) + b * (v + ell) <= &2
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `a:real`] [`b <= &1`] THEN
  SUBGOAL_THEN `&0 < a pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN RASM_ARITH_TAC; ALL_TAC] THEN
  OC983NWE_PRODLT_TAC `a pow 2` `u + b - &1` THEN
  OC983NWE_PROD_TAC `b:real` `a * v - a - b + &1` THEN
  OC983NWE_PRODLT_TAC `a:real` `a + b` THEN
  OC983NWE_PRODLT_TAC `a * (a + b)` `ell - &1` THEN
  OC983NWE_PROD_TAC `&1 - b` `(&1 - a) pow 2` THEN
  OC983NWE_PROD_TAC `a:real` `&2 - (a * (u + ell) + b * (v + ell))` THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `u:real`; `v:real`; `ell:real`]
    OC983NWE_UNIVERSAL_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: shallow_margin *)
let OC983NWE_SHALLOW_MARGIN = prove
 (`forall a b. &0 < a /\ &0 <= b /\ a pow 2 + b pow 2 = &1 /\ b <= &9 / &41
     ==> &2 + &34 / &8405 <=
         (&26 / &25) * a pow 2 + (&4 / &5) * b pow 2 - &2 * a * b + a + &2 * b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `b:real`] [`a <= &1`] THEN
  OC983NWE_PROD_TAC `&9 / &41 - b` `&9 / &41 + b` THEN
  NLIN_FACTS_TAC [] [`b pow 2 <= &81 / &1681`] THEN
  SUBGOAL_THEN `&40 / &41 <= a` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   OC983NWE_PRODLT_TAC `&40 / &41 - a` `&40 / &41 + a` THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  OC983NWE_PROD_TAC `&1 - a` `b:real` THEN
  SUBGOAL_THEN `(&1 - a) * (&1 - &2 * b) <= &1 / &41` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: shallow_impossible *)
let OC983NWE_SHALLOW_IMPOSSIBLE = prove
 (`forall a b u v ell. &0 < a /\ &0 <= b /\ a pow 2 + b pow 2 = &1 /\ &1 < ell /\
     b <= &9 / &41 /\ (&26 / &25) * a - b < u /\ &1 + (&4 / &5) * b - a < v /\
     a * (u + ell) + b * (v + ell) <= &2
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`] OC983NWE_SHALLOW_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  OC983NWE_PRODLT_TAC `a:real` `u - ((&26 / &25) * a - b)` THEN
  OC983NWE_PROD_TAC `b:real` `v - (&1 + (&4 / &5) * b - a)` THEN
  OC983NWE_PRODLT_TAC `a + b` `ell - &1` THEN
  NLIN_TAC ~deg2:false []);;
