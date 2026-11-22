(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallNegativeMixedBounds.lean              *)
(* (namespace N12Compact.CornerWallNegativeMixedBounds).                    *)
(* Uniform continuous margins for the negative-L O-v / L-v selector.        *)
(* Normal c s is c977cc_normal c s (C977CornerCubic).  Divisions by the     *)
(* positive cosines are cleared by CWNMB_CLEAR_TAC.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/CornerWallCycleBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWNMB_clear_poly dens k t =
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
  then failwith "CWNMB_clear_poly: denominators remain" else
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
let CWNMB_CLEAR_EQ dens k t =
  let p = CWNMB_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWNMB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWNMB_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWNMB_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWNMB_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWNMB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWNMB_LT_BY_POS else CWNMB_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWNMB_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWNMB_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWNMB_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWNMB_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWNMB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWNMB_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWNMB_SCALE_LT else CWNMB_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWNMB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let CWNMB_FIELD_TAC = REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;;

(* Lean: baseline *)
let CWNMB_BASELINE = prove
 (`forall c s. c977cc_normal c s /\ s <= &51 / &100 /\ &43 / &50 <= c
         ==> &9 / &10 <= (cwcb_bottom c s + s) / c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`]
   [`&0 <= s * (&51 / &100 - s)`; `&0 <= &2499 / &10000 + (&49 / &100) * s - s pow 2`;
    `&0 <= (&51 / &100 - s) * (&2499 / &10000 + (&49 / &100) * s - s pow 2)`;
    `s pow 2 * (&1 - s) <= &13 / &100`;
    `&0 <= (c - &43 / &50) * (c + &43 / &50)`; `&0 <= (c - &43 / &50) * c pow 2`;
    `&0 <= (&1 / &10) * c pow 2 * (&1 + c) - s pow 2 * (&1 - s)`] THEN
  SUBGOAL_THEN `&0 <= (&1 + c) * ((&1 / &10) * c pow 2 - (&1 - c) * (&1 - s))`
    ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CWNMB_EQ_HINT `&1 - s` (ASSUME `c pow 2 + s pow 2 = &1`)];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= (&1 / &10) * c pow 2 - (&1 - c) * (&1 - s)`] THEN
  REWRITE_TAC[CWCB_BOTTOM_DEF] THEN
  CWNMB_CLEAR_TAC [`c:real`,`ic:real`] `c pow 2` THEN
  NLIN_TAC ~deg2:false [CWNMB_EQ_HINT `&1` (ASSUME `c pow 2 + s pow 2 = &1`)]);;

(* Lean: projection_bound (private) *)
let CWNMB_PROJECTION_BOUND = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
     t <= &51 / &100 /\ &43 / &50 <= c /\ &43 / &50 <= d
     ==> (cwcb_bottom c s + &2 * s) / c + t + (&1 - t) / d <= &72 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWCB_BOTTOM_DEF] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s - &1 / &2`; SQ_NONNEG `c:real`]
   [`&0 <= (c - &43 / &50) * (c + &43 / &50)`; `s * (&1 - s) <= &1 / &4`;
    `&0 <= d * c * ((&50 / &43) * c - &1)`;
    `&0 <= d * ((&625 / &1849) * c pow 2 - s * (&1 - s))`;
    `&0 <= t * (&1 - d)`; `&0 <= (&50 / &43) * d - (d * t + &1 - t)`;
    `&0 <= c pow 2 * ((&50 / &43) * d - (d * t + &1 - t))`; `&0 <= c pow 2 * d`] THEN
  CWNMB_CLEAR_TAC [`c:real`,`ic:real`; `d:real`,`id:real`] `c pow 2 * d` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: low_margin *)
let CWNMB_LOW_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ r <= t /\ t <= &51 / &100 /\ &43 / &50 <= d
     ==> &0 < &1 + (l / c) * cwcb_bottom c s + l * (s * l + c * r) / c +
              l / d - (r * d - l * t) - (l / d) * (t + (&72 / &25) * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CWNMB_BASELINE) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWNMB_PROJECTION_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(d = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s / c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= t + (&1 - t) / d` ASSUME_TAC THENL
   [CWNMB_CLEAR_TAC [`d:real`,`id:real`] `d:real` THEN
    NLIN_FACTS_TAC [] [`&0 <= (&1 - d) * (&1 - t)`] THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `(cwcb_bottom c s + s) / c = cwcb_bottom c s / c + s / c /\
                (cwcb_bottom c s + &2 * s) / c = cwcb_bottom c s / c + &2 * (s / c)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN CWNMB_FIELD_TAC; ALL_TAC] THEN
  ABBREV_TAC `alpha = cwcb_bottom c s / c + t + (&1 - t) / d - &72 / &25` THEN
  ABBREV_TAC `beta = s / c` THEN
  SUBGOAL_THEN
   `(&1 + (l / c) * cwcb_bottom c s + l * (s * l + c * r) / c +
     l / d - (r * d - l * t) - (l / d) * (t + (&72 / &25) * d)) - (&1 + alpha + beta) =
    (&1 - l) * (--alpha - beta * (&1 + l)) + r * (l - d)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["alpha"; "beta"] THEN
    MAP_EVERY UNDISCH_TAC [`~(c = &0)`; `~(d = &0)`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= --alpha - &2 * beta`; `&0 <= beta * (&1 - l)`;
    `&0 <= (&1 - l) * (--alpha - beta * (&1 + l))`; `&0 <= r * (l - d)`;
    `&1 / &50 <= &1 + alpha + beta`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: wall_coefficients (private) *)
let CWNMB_WALL_COEFFICIENTS = prove
 (`forall d t. c977cc_normal d t /\ t <= &51 / &100 /\ &43 / &50 <= d
     ==> &2 * t pow 2 + (&43 / &500) * d * t + (&72 / &25) * d pow 2 - d <= &19 / &10 /\
         (&457 / &500) * d pow 2 + t pow 2 + (&22 / &25) * d * t - t <= &457 / &500`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
   [`&0 <= (d - &43 / &50) * (&1 - d)`; `&1 - d <= (&27 / &50) * t pow 2`;
    `&0 <= t * (&1 - d)`; `&0 <= t * (&51 / &100 - t)`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false [SQ_NONNEG `t - &13 / &100`]);;

(* Lean: remaining_square (private) *)
let CWNMB_REMAINING_SQUARE = prove
 (`forall l r. c977cc_normal l r ==> &0 <= (&1 - l) * (&1 - (&3 / &5) * l) + r * (l - &457 / &500)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  ASM_CASES_TAC `&457 / &500 <= l` THENL
   [NLIN_FACTS_TAC [] [`&0 <= (&1 - l) * (&1 - (&3 / &5) * l)`; `&0 <= r * (l - &457 / &500)`]
    THEN NLIN_TAC ~deg2:false [];
    NLIN_FACTS_TAC [] [`r <= &5 / &7`; `&0 <= (&5 / &7 - r) * (&457 / &500 - l)`] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `l - &3 / &4`]]);;

(* Lean: high_margin *)
let CWNMB_HIGH_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= &51 / &100 /\ &43 / &50 <= d
     ==> &0 <= &1 + (l / c) * cwcb_bottom c s + l * (s * l + c * r) / c + (r * t + l * d) -
              (r * d - l * t) * ((&457 / &500) * d - &2 * t) -
              (r * t + l * d) * (t + (&72 / &25) * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CWNMB_BASELINE) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] CWNMB_WALL_COEFFICIENTS) THEN
  MP_TAC(SPECL [`l:real`; `r:real`] CWNMB_REMAINING_SQUARE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s / c <= &3 / &5` ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:real`; `&3 / &5`; `c:real`] REAL_LE_LDIV_EQ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(l / c) * cwcb_bottom c s + (s / c) * l pow 2 - ((&3 / &10) * l + (&3 / &5) * l pow 2) =
    l * ((cwcb_bottom c s + s) / c - &9 / &10) + l * (&1 - l) * (&3 / &5 - s / c) /\
    &1 + (l / c) * cwcb_bottom c s + l * (s * l + c * r) / c + (r * t + l * d) -
      (r * d - l * t) * ((&457 / &500) * d - &2 * t) - (r * t + l * d) * (t + (&72 / &25) * d) =
    &1 + (l / c) * cwcb_bottom c s + (s / c) * l pow 2 + l * r -
      l * (&2 * t pow 2 + (&43 / &500) * d * t + (&72 / &25) * d pow 2 - d) -
      r * ((&457 / &500) * d pow 2 + t pow 2 + (&22 / &25) * d * t - t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MAP_EVERY UNDISCH_TAC [`~(c = &0)`; `d pow 2 + t pow 2 = &1`] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= l * ((cwcb_bottom c s + s) / c - &9 / &10)`;
    `&0 <= l * (&1 - l)`; `&0 <= (l * (&1 - l)) * (&3 / &5 - s / c)`;
    `&0 <= l * (&19 / &10 - (&2 * t pow 2 + (&43 / &500) * d * t + (&72 / &25) * d pow 2 - d))`;
    `&0 <= r * (&457 / &500 - ((&457 / &500) * d pow 2 + t pow 2 + (&22 / &25) * d * t - t))`]
  THEN NLIN_TAC ~deg2:false []);;
