(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallCycleBounds.lean                      *)
(* (namespace N12Compact.CornerWallCycleBounds).                            *)
(* Exact endpoint inequalities for a genuine O/L/W support cycle.           *)
(* Normal c s is c977cc_normal c s (C977CornerCubic).  Divisions by the     *)
(* positive cosines are cleared by CWCB_CLEAR_TAC.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWCB_clear_poly dens k t =
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
  then failwith "CWCB_clear_poly: denominators remain" else
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
let CWCB_CLEAR_EQ dens k t =
  let p = CWCB_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWCB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWCB_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWCB_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWCB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWCB_LT_BY_POS else CWCB_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [NLIN_TAC [];
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWCB_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWCB_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWCB_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWCB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [NLIN_TAC []; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWCB_SCALE_LT else CWCB_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWCB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: bottom (def) *)
let CWCB_BOTTOM_DEF = new_definition
 `cwcb_bottom (c:real) (s:real) = &1 + s / c - &2 * s - s pow 2 / c`;;

(* Lean: bottom_mul (private) *)
let CWCB_BOTTOM_MUL = prove
 (`forall c s. &0 < c ==> c * cwcb_bottom c s = c + s - &2 * c * s - s pow 2`,
  REWRITE_TAC[CWCB_BOTTOM_DEF] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* Lean: arc_nonnegative *)
let CWCB_ARC_NONNEGATIVE = prove
 (`forall c s l r b p q. c977cc_normal c s /\ c977cc_normal l r /\ r <= s /\
     &0 <= p /\ &0 <= b + p /\ &0 <= b + p * c + q * s
     ==> &0 <= b + p * l + q * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  ASM_CASES_TAC `s = &0` THENL
   [SUBGOAL_THEN `r = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&1 <= l`] THEN
    SUBGOAL_THEN `l = &1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `l:real`; `r:real`; `&0`] C977CSB_ARC_CHORD) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= c * (s * l - s + r * (&1 - c))` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CWCB_EQ_HINT `r:real` (ASSUME `c pow 2 + s pow 2 = &1`)];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= s * l - s + r * (&1 - c)`;
    `&0 <= (s - r) * (b + p)`; `&0 <= r * (b + p * c + q * s)`;
    `&0 <= p * (s * l - s + r * (&1 - c))`;
    `&0 <= s * (b + p * l + q * r)`] THEN
  NLIN_TAC []);;

(* Lean: endpoint_zero *)
let CWCB_ENDPOINT_ZERO = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t
     ==> &0 <= (d / c) * cwcb_bottom c s + &1 + (t + d + d * s / c) - t - &3 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWCB_BOTTOM_DEF] THEN
  CWCB_CLEAR_TAC [`c:real`,`ic:real`] `c pow 2` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`]
   [`&0 <= (&1 - c) * (&1 - s)`; `&0 <= c pow 2 + (&1 - c) * (&1 - s)`;
    `&0 <= (c - d) * (c pow 2 + (&1 - c) * (&1 - s))`;
    `&0 <= c * (&1 - c)`; `&0 <= (c * (&1 - c)) * (c + s - &1)`] THEN
  NLIN_TAC ~deg2:false [CWCB_EQ_HINT `d:real` (ASSUME `c pow 2 + s pow 2 = &1`)]);;

(* Lean: endpoint_self *)
let CWCB_ENDPOINT_SELF = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t
     ==> &0 <= (d / c) * cwcb_bottom c s + &1 + (c * t + d * s + d / c) - t - &3 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWCB_BOTTOM_DEF] THEN
  CWCB_CLEAR_TAC [`c:real`,`ic:real`] `c pow 2` THEN
  let qc = `&2 * c + s * c pow 2 - &3 * c pow 2 - &2 * s * c + s * (&1 - s)` in
  let sub t = subst [qc, `QC:real`] t in
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`]
   (map sub
   [`&0 <= (&1 - c) * (&1 - s)`; `&0 <= c pow 2 + (&1 - c) * (&1 - s)`;
    `&0 <= (&1 - c) * (c pow 2 + (&1 - c) * (&1 - s))`]) THEN
  SUBGOAL_THEN (sub `QC <= --(c pow 3)`) ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CWCB_EQ_HINT `&1` (ASSUME `c pow 2 + s pow 2 = &1`)]; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`]
   (map sub
   [`&0 <= (c - d) * (--(c pow 3) - QC)`;
    `c pow 2 * (c * d + s * t) <= c pow 2`;
    `&0 <= (c + s - &1) * (t - s)`;
    `&0 <= c pow 2 * ((c + s - &1) * (t - s))`]) THEN
  SUBGOAL_THEN (sub `c pow 2 + c * QC + (c - &1) * s * c pow 2 <=
                     c pow 2 + d * QC + (c - &1) * t * c pow 2`) ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CWCB_EQ_HINT `c pow 2` (ASSUME `c pow 2 + s pow 2 = &1`)];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   (map sub
   [`&0 <= ((&1 - s) * (&1 - c)) * (&2 * c - &1)`]) THEN
  SUBGOAL_THEN (sub `&0 <= c + QC + c * (c - &1) * s`) ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CWCB_EQ_HINT `&1` (ASSUME `c pow 2 + s pow 2 = &1`)]; ALL_TAC] THEN
  NLIN_FACTS_TAC [] (map sub [`&0 <= c * (c + QC + c * (c - &1) * s)`]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: positive_coefficient *)
let CWCB_POSITIVE_COEFFICIENT = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ r <= s
     ==> &0 <= (d / c) * cwcb_bottom c s + &1 + (l * (t + d) + (d * s / c) * (l + r)) -
              t - &3 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWCB_ENDPOINT_ZERO) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWCB_ENDPOINT_SELF) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= d * s / c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(t + d + d * s / c) * c + (d * s / c) * s = c * t + d * s + d / c`
    ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c pow 2 + s pow 2 = &1`; `&7 / &10 <= c`] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `l:real`; `r:real`;
    `(d / c) * cwcb_bottom c s + &1 - t - &3 * d`; `t + d + d * s / c`; `d * s / c`]
    CWCB_ARC_NONNEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: negative_coefficient *)
let CWCB_NEGATIVE_COEFFICIENT = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ r <= t
     ==> &0 <= (d / c) * cwcb_bottom c s + &1 + (l * (t + d + d * s / c) + t * r) -
              t - &3 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWCB_ENDPOINT_ZERO) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWCB_ENDPOINT_SELF) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= d * s / c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `c * t + d * s + d / c <= (t + d + d * s / c) * d + t * t` ASSUME_TAC THENL
   [CWCB_CLEAR_TAC [`c:real`,`ic:real`] `c:real` THEN
    NLIN_FACTS_TAC [SQ_NONNEG `c - t`; SQ_NONNEG `s - d`]
     [`c * t + d * s <= &1`; `&0 <= (c - d) * (&1 - c * t - d * s)`] THEN
    NLIN_TAC ~deg2:false [CWCB_EQ_HINT `c:real` (ASSUME `d pow 2 + t pow 2 = &1`)];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`;
    `(d / c) * cwcb_bottom c s + &1 - t - &3 * d`; `t + d + d * s / c`; `t:real`]
    CWCB_ARC_NONNEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: cross_bound (private) *)
let CWCB_CROSS_BOUND = prove
 (`forall c s l r. c977cc_normal c s /\ c977cc_normal l r ==> r <= c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= (c - s) * (c + s)`; `&0 <= (l - r) * (l + r)`] THEN
  NLIN_TAC []);;

(* Lean: positive_large_coefficient *)
let CWCB_POSITIVE_LARGE_COEFFICIENT = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ s <= r
     ==> &0 <= (d / c) * cwcb_bottom c s + &1 + (l * (t + d) + d * r * (&1 + s / c)) -
              t - &3 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWCB_ENDPOINT_SELF) THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `l:real`; `r:real`] CWCB_CROSS_BOUND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c + s) * (l - r)`; `&0 <= (c - s) * (c - r)`;
    `&0 <= (c + s) * (c + l) - &2 * c * (r + s)`;
    `&0 <= (r - s) * ((c + s) * (c + l) - &2 * c * (r + s))`] THEN
  SUBGOAL_THEN `&0 <= (c + l) * ((c + s) * (r - s) - &2 * c * (c - l))` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CWCB_EQ_HINT `&2 * c` (ASSUME `l pow 2 + r pow 2 = &1`);
                          CWCB_EQ_HINT `&2 * c` (ASSUME `c pow 2 + s pow 2 = &1`)];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c + s) * (r - s) - &2 * c * (c - l)`;
    `&0 <= d * ((c + s) * (r - s) - &2 * c * (c - l))`;
    `&0 <= c * (d - t)`; `&0 <= (c * (d - t)) * (c - l)`] THEN
  SUBGOAL_THEN `c * t + d * s + d / c <= l * (t + d) + d * r * (&1 + s / c)` ASSUME_TAC THENL
   [CWCB_CLEAR_TAC [`c:real`,`ic:real`] `c:real` THEN
    NLIN_TAC ~deg2:false [CWCB_EQ_HINT `d:real` (ASSUME `c pow 2 + s pow 2 = &1`)];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: negative_large_coefficient *)
let CWCB_NEGATIVE_LARGE_COEFFICIENT = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= r
     ==> &0 <= (d / c) * cwcb_bottom c s + &1 + (d * l * (&1 + s / c) + r * (t + d)) -
              t - &3 * d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `d:real`; `t:real`]
    CWCB_NEGATIVE_COEFFICIENT) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `d:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= (r - t) * (d + l - r - t)`] THEN
  SUBGOAL_THEN `&0 <= (d + l) * (r - t - d + l)` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false [CWCB_EQ_HINT `&1` (ASSUME `l pow 2 + r pow 2 = &1`);
                          CWCB_EQ_HINT `&1` (ASSUME `d pow 2 + t pow 2 = &1`)];
    ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= r - t - d + l`; `&0 <= d * (c + s)`; `&0 <= (d * (c + s)) * (r - t - d + l)`;
    `&0 <= c * t - d * s`; `&0 <= (c * t - d * s) * (r - t)`] THEN
  SUBGOAL_THEN `d * (t + d + d * s / c) + t * t <= d * l * (&1 + s / c) + r * (t + d)`
    ASSUME_TAC THENL
   [CWCB_CLEAR_TAC [`c:real`,`ic:real`] `c:real` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
