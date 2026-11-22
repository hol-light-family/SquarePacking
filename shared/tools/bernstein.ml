(* ========================================================================= *)
(* Univariate polynomial bounds by Bernstein subdivision, and bounds on the  *)
(* first-quadrant unit arc  c, s >= 0, c^2 + s^2 = 1  through the rational   *)
(* parametrisation  c = 2t/(1+t^2), s = (1-t^2)/(1+t^2), 0 <= t <= 1.         *)
(* ========================================================================= *)

needs "shared/tools/nlin.ml";;

(* dense univariate polynomials over num: coefficient list, lowest first *)
let rec upadd p q = match p,q with
    [],q -> q | p,[] -> p | a::p',b::q' -> (a +/ b) :: upadd p' q';;
let upscale c p = map (fun a -> c */ a) p;;
let rec upmul p q = match p with
    [] -> [] | a::p' -> upadd (upscale a q) (num 0 :: upmul p' q);;
let rec uppow p n = if n = 0 then [num 1] else upmul p (uppow p (n-1));;
let rec binom n k = if k = 0 || k = n then num 1 else binom (n-1) (k-1) +/ binom (n-1) k;;
let upeval p x = List.fold_right (fun a acc -> a +/ x */ acc) p (num 0);;

(* compose p(u + (v-u) x) *)
let upcompose_affine p u v =
  List.fold_right (fun a acc -> upadd [a] (upmul [u; v -/ u] acc)) p [];;

(* Bernstein coefficients of p (degree <= n) on [u,v] *)
let bernstein_coeffs p n u v =
  let q = upcompose_affine p u v in
  let q = q @ List.init (max 0 (n + 1 - List.length q)) (fun _ -> num 0) in
  List.init (n+1) (fun i ->
    List.fold_left (+/) (num 0)
      (List.init (i+1) (fun k -> (binom i k // binom n k) */ List.nth q k)));;

(* split [a,b] until all Bernstein coefficients are >= 0 *)
let rec bern_intervals p n a b depth =
  if forall (fun c -> c >=/ num 0) (bernstein_coeffs p n a b) then [(a,b)]
  else if depth = 0 then failwith "bern_intervals: no certificate"
  else let m = (a +/ b) // num 2 in
       bern_intervals p n a m (depth-1) @ bern_intervals p n m b (depth-1);;

let REAL_POW_LE_SUB = prove
 (`forall x n. &0 <= x ==> &0 <= x pow n`, SIMP_TAC[REAL_POW_LE]);;

(* |- &0 <= (t - u) pow i * (v - t) pow j  under hypotheses u <= t, t <= v *)
let bern_basis t u v i j =
  let ut = ASSUME (mk_binop `(<=):real->real->bool` (term_of_rat u) t)
  and tv = ASSUME (mk_binop `(<=):real->real->bool` t (term_of_rat v)) in
  let p1 = MATCH_MP REAL_SUB_LE' ut and p2 = MATCH_MP REAL_SUB_LE' tv in
  let q1 = SPEC (mk_small_numeral i) (MATCH_MP REAL_POW_LE_SUB p1)
  and q2 = SPEC (mk_small_numeral j) (MATCH_MP REAL_POW_LE_SUB p2) in
  MATCH_MP REAL_LE_MUL' (CONJ q1 q2);;

(* prove  u <= t /\ t <= v ==> &0 <= p  for one interval *)
let bern_leaf t ptm n u v =
  let basis = List.init (n+1) (fun i -> bern_basis t u v i (n-i)) in
  let goal = mk_binop `(<=):real->real->bool` `&0` ptm in
  let nth = ASSUME (mk_neg goal) in
  let th = NLIN_REFUTE ~deg2:false (nth :: basis) in
  let th1 = CCONTR goal th in
  let hu = mk_binop `(<=):real->real->bool` (term_of_rat u) t
  and hv = mk_binop `(<=):real->real->bool` t (term_of_rat v) in
  DISCH (mk_conj(hu,hv)) (PROVE_HYP (CONJUNCT1 (ASSUME (mk_conj(hu,hv))))
                           (PROVE_HYP (CONJUNCT2 (ASSUME (mk_conj(hu,hv)))) th1));;

(* |- !t. a <= t /\ t <= b ==> &0 <= p(t) *)
let POLY_NONNEG_ON t ptm a b =
  nlin_atoms := [t];
  let pp = poly_of_term ptm in
  if length !nlin_atoms > 1 then failwith "POLY_NONNEG_ON: not univariate" else
  let deg = itlist (fun (m,_) d -> max d (match m with [] -> 0 | [_,k] -> k | _ -> 0)) pp 0 in
  let p = List.init (deg+1) (fun k ->
            try assoc (if k = 0 then [] else [0,k]) pp with Failure _ -> num 0) in
  let ivs = bern_intervals p deg a b 20 in
  let leaves = map (fun (u,v) -> bern_leaf t ptm deg u v) ivs in
  (* glue: a <= t <= b implies one of the intervals *)
  let at = term_of_rat a and bt = term_of_rat b in
  let hyp = mk_conj(mk_binop `(<=):real->real->bool` at t, mk_binop `(<=):real->real->bool` t bt) in
  let goal = mk_binop `(<=):real->real->bool` `&0` ptm in
  let ivdisj = list_mk_disj (map (fun th -> lhand(concl th)) leaves) in
  let cover = REAL_ARITH (mk_imp(hyp, ivdisj)) in
  let rec cases dth ls = match ls with
      [l] -> MP l dth
    | l::r -> let a,b = dest_disj (concl dth) in
              DISJ_CASES dth (MP l (ASSUME a)) (cases (ASSUME b) r)
    | [] -> failwith "POLY_NONNEG_ON" in
  let th = cases (UNDISCH cover) leaves in
  GEN t (DISCH hyp th);;

(* ------------------------------------------------------------------------- *)
(* The arc.                                                                  *)
(* ------------------------------------------------------------------------- *)

let ARC_PARAM = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c * c + s * s = &1
         ==> exists t. &0 <= t /\ t <= &1 /\ c * (&1 + t * t) = &2 * t /\
                 s * (&1 + t * t) = &1 - t * t`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `c / (&1 + s)` THEN
  SUBGOAL_THEN `&0 < &1 + s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `&0 < &1 + s` THEN
  CONV_TAC REAL_FIELD);;

(* |- !c s. &0 <= c /\ &0 <= s /\ c * c + s * s = &1 ==> &0 <= P(c,s) *)
let ARC_NONNEG ptm =
  let c = `c:real` and s = `s:real` and t = `t:real` in
  nlin_atoms := [c; s];
  let pp = poly_of_term ptm in
  if length !nlin_atoms > 2 then failwith "ARC_NONNEG: other atoms" else
  let deg_m m = itlist (fun (_,k) a -> a + k) m 0 in
  let k = itlist (fun (m,_) d -> max d (deg_m m)) pp 0 in
  let pw v m = try assoc v m with Failure _ -> 0 in
  (* Q(t) = sum coef (2t)^i (1-t^2)^j (1+t^2)^(k-i-j) *)
  let q = itlist (fun (m,a) acc ->
            let i = pw 0 m and j = pw 1 m in
            upadd (upscale a (upmul (uppow [num 0; num 2] i)
                    (upmul (uppow [num 1; num 0; num(-1)] j) (uppow [num 1; num 0; num 1] (k-i-j))))) acc)
           pp [] in
  let qtm = itlist (fun (i,a) acc -> mk_binop `(+):real->real->real`
                     (mk_binop `( * ):real->real->real` (term_of_rat a)
                        (mk_binop `(pow):real->num->real` t (mk_small_numeral i))) acc)
             (List.mapi (fun i a -> (i,a)) q) `&0` in
  let qth = POLY_NONNEG_ON t qtm (num 0) (num 1) in
  let dk = mk_binop `(pow):real->num->real` `&1 + t * t` (mk_small_numeral k) in
  let ident = REAL_RING (mk_imp(`c * (&1 + t * t) = &2 * t /\ s * (&1 + t * t) = &1 - t * t`,
                          mk_eq(mk_binop `( * ):real->real->real` ptm dk, qtm))) in
  prove(mk_forall(c, mk_forall(s, mk_imp(`&0 <= c /\ &0 <= s /\ c * c + s * s = &1`,
          mk_binop `(<=):real->real->bool` `&0` ptm))),
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP ARC_PARAM) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC t qth) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC ident THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC dk THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_POW_LT THEN
    MP_TAC(SPEC t REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;
