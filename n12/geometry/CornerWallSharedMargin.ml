(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallSharedMargin.lean                     *)
(* (namespace N12Compact.CornerWallSharedMargin).                           *)
(* Strict margin for the shared singleton axis.                             *)
(* Normal c s is c977cc_normal c s (C977CornerCubic).  Divisions by the     *)
(* positive cosines are cleared by CWSM_CLEAR_TAC.                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWSM_clear_poly dens k t =
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
  then failwith "CWSM_clear_poly: denominators remain" else
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
let CWSM_CLEAR_EQ dens k t =
  let p = CWSM_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWSM_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWSM_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWSM_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWSM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWSM_LT_BY_POS else CWSM_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [NLIN_TAC [];
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWSM_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWSM_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWSM_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWSM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [NLIN_TAC []; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWSM_SCALE_LT else CWSM_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWSM_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: first (def) *)
let CWSM_FIRST_DEF = new_definition
 `cwsm_first (c:real) (d:real) (t:real) = c + t - &72 / &25 + (&1 - t) / d`;;

(* Lean: second (def) *)
let CWSM_SECOND_DEF = new_definition
 `cwsm_second (c:real) (s:real) (d:real) = s + d - &2 + (&1 - s) / c`;;

(* Lean: first_mul (private) *)
let CWSM_FIRST_MUL = prove
 (`forall c d t. &0 < d ==> d * cwsm_first c d t = c * d + d * t - (&72 / &25) * d + &1 - t`,
  REWRITE_TAC[CWSM_FIRST_DEF] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(d = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* Lean: second_mul (private) *)
let CWSM_SECOND_MUL = prove
 (`forall c s d. &0 < c ==> c * cwsm_second c s d = c * s + c * d - &2 * c + &1 - s`,
  REWRITE_TAC[CWSM_SECOND_DEF] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(c = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let CWSM_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `d:real`; `t:real`] CWSM_FIRST_MUL) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`] CWSM_SECOND_MUL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: bounds (private) *)
let CWSM_BOUNDS = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t /\
     t <= &3 / &5 /\ &4 / &5 <= d
     ==> --(&49 / &50) <= cwsm_first c d t /\ cwsm_first c d t <= &0 /\
         --(&1 / &5) <= cwsm_second c s d /\ cwsm_second c s d <= &0`,
  CWSM_SETUP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (d - &4 / &5) * (d - &1 / &2)`; `&0 <= (d - t) * (&3 / &5 - t)`;
    `&0 <= d * (c - d)`; `&0 <= d * (cwsm_first c d t + &49 / &50)`;
    `&0 <= (d - &4 / &5) * (&47 / &25 - t)`; `&0 <= d * (&1 - c)`;
    `d * cwsm_first c d t <= &0`;
    `&0 <= (&1 - s) * (&1 - c)`; `&0 <= c * (d - &4 / &5)`;
    `&0 <= c * (cwsm_second c s d + &1 / &5)`;
    `&0 <= (&1 - c) * (c + s - &1)`; `&0 <= c * (c - d)`;
    `c * cwsm_second c s d <= &0`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* Lean: norm_sq *)
let CWSM_NORM_SQ = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t /\
     t <= &3 / &5 /\ &4 / &5 <= d
     ==> (cwsm_first c d t) pow 2 + (cwsm_second c s d) pow 2 <= &249901 / &250000`,
  CWSM_SETUP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWSM_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s <= &1 / &10` THENL
   [NLIN_FACTS_TAC [] [`&0 <= s * (&1 / &10 - s)`] THEN
    SUBGOAL_THEN `&49 / &50 <= c` ASSUME_TAC THENL
     [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      NLIN_FACTS_TAC [] [`&0 <= (&49 / &50 - c) * (&49 / &50 + c)`] THEN
      NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    NLIN_FACTS_TAC []
     [`&0 <= (d - t) * (&1 - t)`; `&0 <= d * (c - &49 / &50)`;
      `&0 <= d * (cwsm_first c d t + &9 / &10)`; `&0 <= cwsm_first c d t + &9 / &10`;
      `&0 <= (cwsm_first c d t + &9 / &10) * (&9 / &10 - cwsm_first c d t)`;
      `&0 <= (cwsm_second c s d + &1 / &5) * (&1 / &5 - cwsm_second c s d)`] THEN
    NLIN_TAC ~deg2:false [];
    NLIN_FACTS_TAC [SQ_NONNEG `&1 - c`]
     [`&0 <= (s - &1 / &10) * (s + &1 / &10)`; `&1 / &200 <= &1 - c`;
      `&0 <= (&3 / &5 - s) * (&1 - c)`; `&1 / &500 <= (&1 - s) * (&1 - c)`;
      `&0 <= c * (d - &4 / &5)`;
      `&0 <= c * (cwsm_second c s d + &99 / &500)`;
      `&0 <= cwsm_second c s d + &99 / &500`;
      `&0 <= (cwsm_first c d t + &49 / &50) * (&49 / &50 - cwsm_first c d t)`;
      `&0 <= (cwsm_second c s d + &99 / &500) * (&99 / &500 - cwsm_second c s d)`] THEN
    NLIN_TAC ~deg2:false []]);;

(* Lean: shared_axis *)
let CWSM_SHARED_AXIS = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= &3 / &5 /\ &4 / &5 <= d
     ==> &0 < &1 + l * (c + t - &72 / &25 + (&1 - t) / d) +
              r * (s + d - &2 + (&1 - s) / c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM CWSM_FIRST_DEF; GSYM CWSM_SECOND_DEF] THEN
  UNDISCH_TAC `c977cc_normal l r` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWSM_NORM_SQ) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`cwsm_first c d t`,`A:real`) THEN SPEC_TAC(`cwsm_second c s d`,`B:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(l * A + r * B) pow 2 + (l * B - r * A) pow 2 = A pow 2 + B pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `l * B - r * A`] [`(l * A + r * B) pow 2 < &1`] THEN
  NLIN_TAC []);;
