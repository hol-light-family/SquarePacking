(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerLongitudinalBounds.lean          *)
(* (namespace N12Compact.CornerWallMarkerLongitudinalBounds).                *)
(* Continuous positive-L longitudinal margins.  X, Y are cwml_x, cwml_y      *)
(* (CornerWallMarkerLongitudinal); bottom is cwcb_bottom; Normal c s is      *)
(* c977cc_normal c s.                                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/CornerWallCycleBounds.ml";;
needs "n12/geometry/CornerWallMarkerLongitudinal.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMLB_clear_poly dens k t =
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
  then failwith "CWMLB_clear_poly: denominators remain" else
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
let CWMLB_CLEAR_EQ dens k t =
  let p = CWMLB_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMLB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMLB_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWMLB_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMLB_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMLB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMLB_LT_BY_POS else CWMLB_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWMLB_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMLB_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMLB_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMLB_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMLB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWMLB_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMLB_SCALE_LT else CWMLB_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMLB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: wall_bounds *)
let CWMLB_WALL_BOUNDS = prove
 (`forall d t. c977cc_normal d t /\ &4 / &5 <= d
         ==> cwml_y d t <= &17 / &20 /\ cwml_x d t + cwml_y d t - d <= &219 / &125`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWML_X_DEF; CWML_Y_DEF] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
   [`&0 <= t * (&1 - (&13 / &20) * d)`; `&0 <= (d - &4 / &5) * (&1 - d)`;
    `&0 <= d * t`] THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false [SQ_NONNEG `t:real`]);;

(* Lean: cubic_nonnegative (private) *)
let CWMLB_CUBIC_NONNEGATIVE = prove
 (`forall r. r <= &5 / &7 ==> &0 <= &3 / &20 - (&341 / &500) * r + (&41 / &40) * r pow 2 -
                               (&1 / &2) * r pow 3`,
  GEN_TAC THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `r - &3 / &5`]
   [`&0 <= (r - &3 / &5) pow 2 * (&3 / &8 - r / &2)`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `(&1 / &10) * (r - &3 / &5) + &1 / &125`]);;

(* Lean: bottom_bound (private) *)
let CWMLB_BOTTOM_BOUND = prove
 (`forall c s r t. c977cc_normal c s /\ &0 <= r /\ r <= &1 /\ s <= t /\ t <= &3 / &5
     ==> &1 - (&1 - r) * t - t pow 2 <= (cwcb_bottom c s + s * r) / c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWCB_BOTTOM_DEF] THEN
  NLIN_FACTS_TAC []
   [`&0 <= s * (&3 / &5 - s)`; `s pow 2 <= (&3 / &5) * s`; `&0 <= r * s`;
    `&0 <= &1 - (&1 - r) * s - s pow 2`;
    `&0 <= (s * (&1 - s)) * (&1 - c)`;
    `&0 <= c * (&1 - c)`; `&0 <= (c * (&1 - c)) * (&1 - (&1 - r) * s - s pow 2)`;
    `&0 <= (&1 - r) * (t - s)`; `&0 <= (t - s) * (t + s)`;
    `&1 - (&1 - r) * t - t pow 2 <= &1 - (&1 - r) * s - s pow 2`;
    `&0 <= c pow 2 * ((&1 - (&1 - r) * s - s pow 2) - (&1 - (&1 - r) * t - t pow 2))`] THEN
  CWMLB_CLEAR_TAC [`c:real`,`ic:real`] `c pow 2` THEN
  NLIN_TAC ~deg2:false [CWMLB_EQ_HINT `&1` (ASSUME `c pow 2 + s pow 2 = &1`)]);;

(* Lean: bottom_axis *)
let CWMLB_BOTTOM_AXIS = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= &3 / &5 /\ &4 / &5 <= d
     ==> &0 <= &1 + (r / c) * cwcb_bottom c s + (r / c) * (c * l + s * r) -
              l * cwml_y d t - r * cwml_x d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] CWMLB_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `r:real`; `t:real`] CWMLB_BOTTOM_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`r:real`] CWMLB_CUBIC_NONNEGATIVE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (r / c) * cwcb_bottom c s + (r / c) * (c * l + s * r) -
                l * cwml_y d t - r * cwml_x d t =
                &1 - l * cwml_y d t + l * r +
                r * ((cwcb_bottom c s + s * r) / c - cwml_x d t)` SUBST1_TAC THENL
   [UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d - &1`; SQ_NONNEG `l - &1`]
   [`&0 <= r * ((cwcb_bottom c s + s * r) / c - (&1 - (&1 - r) * t - t pow 2))`;
    `&0 <= (l - r) * (&17 / &20 - cwml_y d t)`;
    `&0 <= r * (&219 / &125 - (cwml_x d t + cwml_y d t - d))`;
    `d <= &1 - t pow 2 / &2`; `&0 <= r * ((&1 - t pow 2 / &2) - d)`;
    `&0 <= r * (&1 - r)`; `&0 <= (r * (&1 - r)) * (&3 / &5 - t)`;
    `&0 <= (&3 / &5 - t) * (&3 / &5 + t)`; `&0 <= r * ((&3 / &5) pow 2 - t pow 2)`;
    `l <= &1 - r pow 2 / &2`; `&0 <= (&17 / &20 - r) * ((&1 - r pow 2 / &2) - l)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: singleton_axis *)
let CWMLB_SINGLETON_AXIS = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ &4 / &5 <= d
     ==> &0 <= c * l + c * r + c * r * (c * l + s * r) + r pow 2 - r pow 2 * (&2 * c + s) -
              c * l * (l * cwml_y d t + r * cwml_x d t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] CWMLB_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (l + r - &1) * (&3 / &2 - (l + r))`; `&0 <= l + r - &1 - (&4 / &5) * l * r`;
    `&0 <= l * (l - r)`; `&0 <= (l * (l - r)) * (&1 - cwml_y d t)`;
    `&0 <= l * r`; `&0 <= (l * r) * (&9 / &5 - (cwml_x d t + cwml_y d t - d))`;
    `&0 <= l + r - l pow 2 * cwml_y d t + l * r * (d - cwml_x d t) - r pow 2`;
    `&0 <= (l * r) * (c - d)`;
    `&0 <= c * (l + r - l pow 2 * cwml_y d t + l * r * (d - cwml_x d t) - r pow 2)`;
    `&0 <= c * ((l * r) * (c - d))`;
    `&0 <= (&1 - s) * (&1 - c)`; `&0 <= r * r`; `&0 <= (r * r) * ((&1 - s) * (&1 - c))`] THEN
  NLIN_TAC ~deg2:false []);;
