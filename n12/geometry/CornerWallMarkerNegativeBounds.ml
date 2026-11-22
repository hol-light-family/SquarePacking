(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerNegativeBounds.lean             *)
(* (namespace N12Compact.CornerWallMarkerNegativeBounds).                   *)
(* Two continuous backward-negative-left margins.                           *)
(* Normal c s is c977cc_normal c s (C977CornerCubic).  Divisions by the     *)
(* positive cosines are cleared by CWMNB_CLEAR_TAC.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMNB_clear_poly dens k t =
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
  then failwith "CWMNB_clear_poly: denominators remain" else
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
let CWMNB_CLEAR_EQ dens k t =
  let p = CWMNB_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMNB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMNB_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMNB_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMNB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMNB_LT_BY_POS else CWMNB_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [NLIN_TAC [];
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMNB_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMNB_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMNB_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMNB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [NLIN_TAC []; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMNB_SCALE_LT else CWMNB_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMNB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: X (def) *)
let CWMNB_X_DEF = new_definition
 `cwmnb_x (c:real) (s:real) = s - &1 + (&1 - (&457 / &500) * s) / c`;;

(* Lean: x_lower *)
let CWMNB_X_LOWER = prove
 (`forall c s. c977cc_normal c s /\ c <= &457 / &500 /\ s <= &3 / &5
         ==> &9 / &100 <= cwmnb_x c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWMNB_X_DEF] THEN
  NLIN_FACTS_TAC [] [`&0 <= (&3 / &5 - s) * (&457 / &500 - c)`] THEN
  CWMNB_CLEAR_TAC [`c:real`,`ic:real`] `c:real` THEN NLIN_TAC ~deg2:false []);;

(* Lean: unit_sum (private) *)
let CWMNB_UNIT_SUM = prove
 (`forall l r. c977cc_normal l r ==> --(&43 / &500) <= l + r - &1 - l * r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `l - r`; SQ_NONNEG `l + r - &99 / &70`]
   [`l + r <= &99 / &70`; `&0 <= (&99 / &70 - (l + r)) * (l + r + &99 / &70 - &2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: left_margin *)
let CWMNB_LEFT_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= &3 / &5 /\ &4 / &5 <= d /\ c <= &457 / &500 /\ t <= r
     ==> &0 <= l + r - &1 + cwmnb_x c s * l pow 2 + (c + d - &2 - d pow 2) * l * r +
              ((&43 / &500) + t * (&1 - d)) * r pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`l:real`; `r:real`] CWMNB_UNIT_SUM) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CWMNB_X_LOWER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `l:real`]
   [`&0 <= l pow 2 * (cwmnb_x c s - &9 / &100)`; `&0 <= t * (r - t)`;
    `&0 <= (&1 - d) * (&1 + d - l)`; `&0 <= t * r - l * (&1 - d)`;
    `&0 <= r * (&1 - d)`; `&0 <= (r * (&1 - d)) * (t * r - l * (&1 - d))`;
    `&0 <= l * r`; `&0 <= (l * r) * (c - d)`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `l:real`]);;

(* Lean: wall_margin *)
let CWMNB_WALL_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= &3 / &5 /\ &4 / &5 <= d /\ c <= &457 / &500 /\ &3 / &5 <= r
     ==> &0 <= &1 - l + l * cwmnb_x c s +
              r * (c - &3 + (&1 - (&457 / &500) * t) / d + l + r * t / d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CWMNB_X_LOWER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `l - &4 / &5`; SQ_NONNEG `&1 - d`]
   [`r <= &5 / &7`; `&0 <= (r - &3 / &5) * (r + &3 / &5)`; `l <= &4 / &5`;
    `&0 <= l * (cwmnb_x c s - &9 / &100)`; `&0 <= r * (c - d)`;
    `t <= (&3 / &4) * d`;
    `&0 <= r * (&457 / &500 - r)`;
    `&0 <= (r * (&457 / &500 - r)) * ((&3 / &4) * d - t)`;
    `&0 <= (&4 / &5 - l) * (&91 / &100 - r)`;
    `&0 <= (r - &3 / &5) * ((&3 / &4) * r - &871 / &2000)`;
    `&0 <= (&1 - l) * (&1 - r) + l * cwmnb_x c s - (&3 / &4) * r * (&457 / &500 - r)`;
    `&0 <= d * ((&1 - l) * (&1 - r) + l * cwmnb_x c s - (&3 / &4) * r * (&457 / &500 - r))`;
    `&0 <= d * (r * (c - d))`; `&0 <= r * (&1 - d) pow 2`] THEN
  CWMNB_CLEAR_TAC [`d:real`,`id:real`] `d:real` THEN NLIN_TAC ~deg2:false []);;
