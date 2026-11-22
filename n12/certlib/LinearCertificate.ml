(* ========================================================================= *)
(* Port of source/S12/LinearCertificate.lean (Jatloe, N12-jatloe).           *)
(* Representation (dimension-generic, as Lean's Affine n / LinearConstraint n):*)
(*   Affine n            -> affine = Affine (coeffs : real list) (constant)   *)
(*   LinearConstraint n  -> lincon = LinCon affine (strict : bool)            *)
(*   x : Fin n -> R      -> x : real list  (x i = EL i x)                     *)
(*   Affine.eval f x     -> aff_eval f x = ldot coeffs x + constant           *)
(* ldot multiplies coefficient and point entrywise, stopping at the shorter   *)
(* list; for data of the intended dimension n (n coefficients, n coordinates) *)
(* this is exactly Lean's sum over Fin n.  Affine.add pads with zeros.        *)
(* Lean's rational data are HOL reals (rational literals).                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* List.flatten (Lean's flatMap f l is lflat (MAP f l)) *)
let lflat = define
 `(lflat [] = []) /\ (lflat (CONS (h:A list) t) = APPEND h (lflat t))`;;

let MEM_LFLAT = prove
 (`forall x (ls:(A list)list). MEM x (lflat ls) <=> exists l. MEM l ls /\ MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[lflat; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

(* Lean: structure Affine *)
let affine_INDUCT,affine_RECURSION = define_type "affine = Affine (real list) real";;
(* Lean: structure LinearConstraint *)
let lincon_INDUCT,lincon_RECURSION = define_type "lincon = LinCon affine bool";;

let aff_coeff = define `aff_coeff (Affine cs k) = cs`;;
let aff_constant = define `aff_constant (Affine cs k) = k`;;
let lc_form = define `lc_form (LinCon f b) = f`;;
let lc_strict = define `lc_strict (LinCon f b) = b`;;

let ldot = define
 `(ldot [] xs = &0) /\
  (ldot (CONS c cs) [] = &0) /\
  (ldot (CONS c cs) (CONS x xs) = c * x + ldot cs xs)`;;

let ladd = define
 `(ladd [] ys = ys) /\
  (ladd (CONS x xs) [] = CONS x xs) /\
  (ladd (CONS x xs) (CONS y ys) = CONS (x + y) (ladd xs ys))`;;

(* Lean: Affine.eval *)
let aff_eval = define `aff_eval (Affine cs k) x = ldot cs x + k`;;

(* Lean: Affine.zero *)
let aff_zero = new_definition `aff_zero n = Affine (REPLICATE n (&0)) (&0)`;;
(* Lean: Affine.add *)
let aff_add = define `aff_add (Affine cs k) (Affine ds l) = Affine (ladd cs ds) (k + l)`;;
(* Lean: Affine.scale *)
let aff_scale = define `aff_scale a (Affine cs k) = Affine (MAP (\c. a * c) cs) (a * k)`;;

let LDOT_NIL_RIGHT = prove
 (`forall cs. ldot cs [] = &0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ldot]);;

let LDOT_REPLICATE_0 = prove
 (`forall n xs. ldot (REPLICATE n (&0)) xs = &0`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; ldot] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ldot] THEN REAL_ARITH_TAC);;

let LDOT_LADD = prove
 (`forall cs ds xs. ldot (ladd cs ds) xs = ldot cs xs + ldot ds xs`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ladd; ldot; REAL_ADD_LID] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ladd; ldot; REAL_ADD_RID] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ldot; LDOT_NIL_RIGHT] THEN REAL_ARITH_TAC);;

let LDOT_MAP_SCALE = prove
 (`forall a cs xs. ldot (MAP (\c. a * c) cs) xs = a * ldot cs xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; ldot; REAL_MUL_RZERO] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ldot; REAL_MUL_RZERO] THEN REAL_ARITH_TAC);;

(* Lean: Affine.eval_zero *)
let LC_AFF_EVAL_ZERO = prove
 (`forall n x. aff_eval (aff_zero n) x = &0`,
  REWRITE_TAC[aff_zero; aff_eval; LDOT_REPLICATE_0; REAL_ADD_LID]);;

(* Lean: Affine.eval_add *)
let LC_AFF_EVAL_ADD = prove
 (`forall f g p. aff_eval (aff_add f g) p = aff_eval f p + aff_eval g p`,
  MATCH_MP_TAC affine_INDUCT THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC affine_INDUCT THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[aff_add; aff_eval; LDOT_LADD] THEN REAL_ARITH_TAC);;

(* Lean: Affine.eval_scale *)
let LC_AFF_EVAL_SCALE = prove
 (`forall a f p. aff_eval (aff_scale a f) p = a * aff_eval f p`,
  GEN_TAC THEN MATCH_MP_TAC affine_INDUCT THEN
  REWRITE_TAC[aff_scale; aff_eval; LDOT_MAP_SCALE] THEN REAL_ARITH_TAC);;

(* Lean: LinearConstraint.Holds *)
let lc_holds = define
 `lc_holds (LinCon f b) x <=> if b then &0 < aff_eval f x else &0 <= aff_eval f x`;;

(* Lean: LinearConstraint.zero / add / scale *)
let lc_zero = new_definition `lc_zero n = LinCon (aff_zero n) false`;;
let lc_add = define
 `lc_add (LinCon f b) (LinCon g c) = LinCon (aff_add f g) (b \/ c)`;;
let lc_scale = define
 `lc_scale a (LinCon f b) = LinCon (aff_scale a f) (&0 < a /\ b)`;;

(* Lean: LinearConstraint.holds_add *)
let LC_HOLDS_ADD = prove
 (`forall r s p. lc_holds r p /\ lc_holds s p ==> lc_holds (lc_add r s) p`,
  MATCH_MP_TAC lincon_INDUCT THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC lincon_INDUCT THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lc_add; lc_holds; LC_AFF_EVAL_ADD] THEN
  MAP_EVERY BOOL_CASES_TAC [`a1:bool`; `a1':bool`] THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* Lean: LinearConstraint.holds_scale *)
let LC_HOLDS_SCALE = prove
 (`forall a r p. &0 <= a /\ lc_holds r p ==> lc_holds (lc_scale a r) p`,
  GEN_TAC THEN MATCH_MP_TAC lincon_INDUCT THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[lc_scale; lc_holds; LC_AFF_EVAL_SCALE] THEN
  ASM_CASES_TAC `a1:bool` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  TRY COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LT_MUL; REAL_LE_MUL] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]);;

(* Lean: linearCombination *)
let lin_comb = define
 `(lin_comb n [] = lc_zero n) /\
  (lin_comb n (CONS t terms) = lc_add (lc_scale (FST t) (SND t)) (lin_comb n terms))`;;

(* Lean: LinearCertificateCheck *)
let lcert_check = new_definition
 `lcert_check n inputs terms <=>
    (forall t. MEM t terms ==> &0 <= FST t /\ MEM (SND t) inputs) /\
    lc_strict (lin_comb n terms) = true /\
    lc_form (lin_comb n terms) = aff_zero n`;;

(* Lean: linearCombination_holds *)
let LC_LINEARCOMBINATION_HOLDS = prove
 (`forall n terms x. (forall t. MEM t terms ==> &0 <= FST t /\ lc_holds (SND t) x)
               ==> lc_holds (lin_comb n terms) x`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[lin_comb; MEM; lc_zero; lc_holds; LC_AFF_EVAL_ZERO; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LC_HOLDS_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC LC_HOLDS_SCALE THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

(* Lean: linear_certificate_sound *)
let LC_LINEAR_CERTIFICATE_SOUND = prove
 (`forall n inputs terms. lcert_check n inputs terms
     ==> ~(exists x. forall r. MEM r inputs ==> lc_holds r x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcert_check] THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `x:real list` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `terms:(real#lincon)list`; `x:real list`]
    LC_LINEARCOMBINATION_HOLDS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `lc_strict (lin_comb n terms)` THEN
  UNDISCH_TAC `lc_form (lin_comb n terms) = aff_zero n` THEN
  SPEC_TAC(`lin_comb n terms`,`r:lincon`) THEN MATCH_MP_TAC lincon_INDUCT THEN
  REWRITE_TAC[lc_strict; lc_form; lc_holds] THEN REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[LC_AFF_EVAL_ZERO; REAL_LT_REFL]);;
