(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerSharedBounds.lean               *)
(* (namespace N12Compact.CornerWallMarkerSharedBounds).                     *)
(* Marker coefficient bounds for the common positive-L transverse axis.     *)
(* Normal c s is c977cc_normal c s (C977CornerCubic).  Divisions by the     *)
(* positive cosines are cleared by CWMSB_CLEAR_TAC.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMSB_clear_poly dens k t =
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
  then failwith "CWMSB_clear_poly: denominators remain" else
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
let CWMSB_CLEAR_EQ dens k t =
  let p = CWMSB_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMSB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMSB_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMSB_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMSB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMSB_LT_BY_POS else CWMSB_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [NLIN_TAC [];
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMSB_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMSB_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMSB_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMSB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [NLIN_TAC []; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMSB_SCALE_LT else CWMSB_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMSB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: first (def) *)
let CWMSB_FIRST_DEF = new_definition
 `cwmsb_first (c:real) (d:real) (t:real) = c + t - &3 + (&1 - (&457 / &500) * t) / d`;;

(* Lean: second (def) *)
let CWMSB_SECOND_DEF = new_definition
 `cwmsb_second (c:real) (s:real) (d:real) = s + d - &2 + (&1 - (&457 / &500) * s) / c`;;

(* Lean: first_coefficient *)
let CWMSB_FIRST_COEFFICIENT = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t /\
     t <= &3 / &5 /\ &4 / &5 <= d
     ==> --(c + d) / &2 <= cwmsb_first c d t + s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWMSB_FIRST_DEF] THEN
  NLIN_FACTS_TAC []
   [`&1 / &2 <= c`; `&0 <= (&1 - c) * (c - &1 / &2)`;
    `&0 <= (&3 / &5 - t) * (&1 - t)`] THEN
  SUBGOAL_THEN `d + &2 * t <= &2` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    NLIN_FACTS_TAC [] [`&0 < (d - (&2 - &2 * t)) * (d + (&2 - &2 * t))`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&1 - d) * (&2 - d - &2 * t)`;
    `&0 <= d * ((&1 - c) * (c - &1 / &2))`] THEN
  CWMSB_CLEAR_TAC [`d:real`,`id:real`] `&2 * d` THEN
  NLIN_TAC ~deg2:false [CWMSB_EQ_HINT `&2 * d` (ASSUME `c pow 2 + s pow 2 = &1`)]);;

(* Lean: second_coefficient *)
let CWMSB_SECOND_COEFFICIENT = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t /\
     t <= &3 / &5 /\ &4 / &5 <= d
     ==> --(s + t) / &2 <= cwmsb_second c s d - c * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWMSB_SECOND_DEF] THEN
  ASM_CASES_TAC `t <= &7 / &25` THENL
   [NLIN_FACTS_TAC []
     [`&0 <= c + d - &2 * (s + t)`; `&0 <= (t - s) * (c + d - &2 * (s + t))`] THEN
    SUBGOAL_THEN `&0 <= (c + d) * (d + t / &2 - (c + s / &2))` ASSUME_TAC THENL
     [NLIN_TAC ~deg2:false [CWMSB_EQ_HINT `&1 / &2` (ASSUME `d pow 2 + t pow 2 = &1`);
                            CWMSB_EQ_HINT `&1 / &2` (ASSUME `c pow 2 + s pow 2 = &1`)];
      ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `&1 - c`]
     [`&0 <= d + t / &2 - (c + s / &2)`; `&0 <= c * (d + t / &2 - (c + s / &2))`;
      `&0 <= (&1 - s) * (&1 - c) pow 2`] THEN
    CWMSB_CLEAR_TAC [`c:real`,`ic:real`] `c:real` THEN NLIN_TAC ~deg2:false [];
    NLIN_FACTS_TAC []
     [`&0 <= (t - &7 / &25) * (&3 / &5 - t)`] THEN
    SUBGOAL_THEN `&11 / &10 <= d + t / &2` ASSUME_TAC THENL
     [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      NLIN_FACTS_TAC [] [`&0 < (&11 / &10 - t / &2 - d) * (&11 / &10 - t / &2 + d)`] THEN
      NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `(&207 / &500) * c - (&9 / &10) * s`;
                    SQ_NONNEG `(&9 / &10) * c + (&207 / &500) * s - &1`]
     [`&0 <= (&1 - c) * (c - &1 / &2)`;
      `c pow 2 - (&3 / &2) * c + &457 / &500 <= &207 / &500`;
      `(&9 / &10) * c + (&207 / &500) * s < &1`;
      `&0 <= c * (d + t / &2 - &11 / &10)`;
      `&0 <= s * (&207 / &500 - (c pow 2 - (&3 / &2) * c + &457 / &500))`] THEN
    CWMSB_CLEAR_TAC [`c:real`,`ic:real`] `c:real` THEN NLIN_TAC ~deg2:false []]);;

(* Lean: margin *)
let CWMSB_MARGIN = prove
 (`forall c s d t l r extra.
     c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= &3 / &5 /\ &4 / &5 <= d /\
     &0 <= extra /\ s * l - c * r <= extra
     ==> &0 <= &1 + l * cwmsb_first c d t + r * cwmsb_second c s d + extra`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWMSB_FIRST_COEFFICIENT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWMSB_SECOND_COEFFICIENT) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `l:real`; `r:real`] C977CSB_DOT_LE_ONE) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= l * ((cwmsb_first c d t + s pow 2) - --(c + d) / &2)`;
    `&0 <= r * ((cwmsb_second c s d - c * s) - --(s + t) / &2)`;
    `&0 <= s * (extra - (s * l - c * r))`; `&0 <= (&1 - s) * extra`] THEN
  NLIN_TAC ~deg2:false []);;
