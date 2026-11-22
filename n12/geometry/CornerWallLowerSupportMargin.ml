(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallLowerSupportMargin.lean               *)
(* (namespace N12Compact.CornerWallLowerSupportMargin).                     *)
(* Lower-support margin for a right wall missing its upper corner.          *)
(* Normal c s is c977cc_normal c s (C977CornerCubic).  Divisions by the     *)
(* positive cosines are cleared by CWLSM_CLEAR_TAC.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWLSM_clear_poly dens k t =
  let mul = `( * ):real->real->real` in
  let rec repl tm = match tm with
      Comb(Comb(Const("real_div",_),x),v) when exists (fun (x,_) -> x = v) dens ->
        mk_binop mul (repl x) (assoc v dens)
    | Comb(f,x) -> mk_comb(repl f, repl x)
    | _ -> tm in
  let t2 = repl (mk_binop mul k t) in
  nlin_atoms := [];
  let p = poly_of_term t2 in
  let atoms = !nlin_atoms in
  let index_of tm =
    let rec go i l = match l with [] -> -1 | h::r -> if aconv h tm then i else go (i+1) r in
    go 0 atoms in
  let pairs = map (fun (v,iv) -> (index_of v, index_of iv)) dens in
  let cancel m =
    itlist (fun (vi,ii) m ->
      if vi < 0 || ii < 0 then m else
      let a = try assoc vi m with Failure _ -> 0
      and b = try assoc ii m with Failure _ -> 0 in
      let e = min a b in
      let m' = filter (fun (x,_) -> x <> vi && x <> ii) m in
      let m' = (if a - e > 0 then [vi, a - e] else []) @
               (if b - e > 0 then [ii, b - e] else []) @ m' in
      sort (fun (x,_) (y,_) -> x < y) m') pairs m in
  let p' = pnorm (map (fun (m,c) -> (cancel m, c)) p) in
  if exists (fun (m,_) -> exists (fun (_,ii) -> ii >= 0 && exists (fun (x,_) -> x = ii) m) pairs) p'
  then failwith "CWLSM_clear_poly: denominators remain" else
  let atom i = el i atoms in
  let mono (m,c) =
    let fs = map (fun (i,e) -> if e = 1 then atom i
                    else mk_binop `(pow):real->num->real` (atom i) (mk_small_numeral e)) m in
    let ct = term_of_rat c in
    if fs = [] then ct else
    let pr = end_itlist (fun a b -> mk_binop mul a b) fs in
    if c =/ num 1 then pr else mk_binop mul ct pr in
  if p' = [] then `&0` else
  end_itlist (fun a b -> mk_binop `(+):real->real->real` a b) (map mono p');;

(* prove |- ~(v1 = &0) /\ ... ==> k * t = P *)
let CWLSM_CLEAR_EQ dens k t =
  let p = CWLSM_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWLSM_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWLSM_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWLSM_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWLSM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWLSM_LT_BY_POS else CWLSM_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [NLIN_TAC [];
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWLSM_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWLSM_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWLSM_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWLSM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [NLIN_TAC []; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWLSM_SCALE_LT else CWLSM_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWLSM_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: F (def) *)
let CWLSM_F_DEF = new_definition
 `cwlsm_f (c:real) (s:real) (d:real) (t:real) =
    &1 - &2 * c - s + s * (&1 - t) / d + (c * d + s * t) + max (c * t - s * d) (&0)`;;

(* Lean: diagonal_minimum *)
let CWLSM_DIAGONAL_MINIMUM = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> (&1 - d) pow 2 + (&1 - d) * t * (&1 - t) / d <= cwlsm_f c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWLSM_F_DEF] THEN
  SUBGOAL_THEN `d * ((&1 - t) / d) = &1 - t /\ &0 <= (&1 - t) / d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `~(d = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_CASES_TAC `s <= t` THENL
   [MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 <= c * (t - s)`; `&0 <= s * (c - d)`; `&0 <= c * t - s * d`] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> max x (&0) = x`] THEN
    SUBGOAL_THEN `(&2 - d - t) * t <= (d - (&1 - d) * ((&1 - t) / d)) * d` ASSUME_TAC THENL
     [NLIN_TAC ~deg2:false [CWLSM_EQ_HINT `&1 - d` (ASSUME `d * ((&1 - t) / d) = &1 - t`)];
      ALL_TAC] THEN
    MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`; `&2 - d - t`;
                  `d - (&1 - d) * ((&1 - t) / d)`] C977CSB_LINEAR_ARC_MAX) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    NLIN_TAC ~deg2:false [CWLSM_EQ_HINT `s:real` (ASSUME `d * ((&1 - t) / d) = &1 - t`)];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    NLIN_FACTS_TAC [] [`&0 <= d * (s - t)`; `&0 <= t * (d - c)`; `c * t - s * d <= &0`] THEN
    ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> max x (&0) = &0`] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (&2 - d) * (d - c)`; `&0 <= (&1 - d) * ((&1 - t) / d)`;
      `&0 <= ((&1 - d) * ((&1 - t) / d)) * (s - t)`] THEN
    NLIN_TAC ~deg2:false [CWLSM_EQ_HINT `s:real` (ASSUME `d * ((&1 - t) / d) = &1 - t`)]]);;

(* Lean: margin *)
let CWLSM_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t ==> &0 <= cwlsm_f c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWLSM_DIAGONAL_MINIMUM) THEN
  ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - d) * t * (&1 - t) / d` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&1 - d` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;
