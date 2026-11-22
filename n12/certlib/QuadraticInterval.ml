(* ========================================================================= *)
(* Port of source/S12/QuadraticInterval.lean (Jatloe, N12-jatloe).           *)
(* Degree-two Bernstein positivity on a closed interval.                     *)
(* Lean's rational fields (Quadratic : Q^3) are HOL reals; Lean's evalRat    *)
(* (over Q) and eval (over R) are both quad_eval.                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: structure Quadratic *)
let quadratic_INDUCT,quadratic_RECURSION =
  define_type "quadratic = Quadratic real real real";;

(* Lean: Quadratic.evalRat / Quadratic.eval *)
let quad_eval = define
 `quad_eval (Quadratic a b c) t = a * t pow 2 + b * t + c`;;

(* Lean: Quadratic.CheckOn *)
let quad_check_on = define
 `quad_check_on (Quadratic a b c) l h <=>
    l < h /\ &0 <= quad_eval (Quadratic a b c) l /\
    &0 <= quad_eval (Quadratic a b c) l + (h - l) * (&2 * a * l + b) / &2 /\
    &0 <= quad_eval (Quadratic a b c) h`;;

let QI_NONNEG_FACTOR = prove
 (`forall x d. &0 < d /\ &0 <= d * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:real`; `--x`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC);;

(* Lean: Quadratic.sound *)
let QI_QUADRATIC_SOUND = prove
 (`forall q l h t. quad_check_on q l h /\ l <= t /\ t <= h ==> &0 <= quad_eval q t`,
  MATCH_MP_TAC quadratic_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`A:real`; `B:real`; `C:real`; `l:real`; `h:real`; `t:real`] THEN
  REWRITE_TAC[quad_check_on; quad_eval] THEN STRIP_TAC THEN
  MATCH_MP_TAC QI_NONNEG_FACTOR THEN EXISTS_TAC `(h - l) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(h - l) pow 2 * (A * t pow 2 + B * t + C) =
    (A * l pow 2 + B * l + C) * (h - t) pow 2 +
    &2 * ((A * l pow 2 + B * l + C) + (h - l) * (&2 * A * l + B) / &2) * ((t - l) * (h - t)) +
    (A * h pow 2 + B * h + C) * (t - l) pow 2` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC);;
