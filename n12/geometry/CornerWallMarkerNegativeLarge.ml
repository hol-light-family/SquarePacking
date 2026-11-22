(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerNegativeLarge.lean               *)
(* (namespace N12Compact.CornerWallMarkerNegativeLarge).                     *)
(* Genuine-marker support reductions for negative L after its backward U     *)
(* separator.  Squares are 5-tuples (L.s = -r, W.s = -t); Lean upper/lower   *)
(* are ABT_upper/ABT_lower; bottom_support/restrictions are the CWMNC_       *)
(* theorems; the scalar margins are CWMNB_LEFT_MARGIN / CWMNB_WALL_MARGIN.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallMarkerNegativeCorner.ml";;
needs "n12/geometry/CornerWallMarkerNegativeBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMNL_clear_poly dens k t =
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
  then failwith "CWMNL_clear_poly: denominators remain" else
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
let CWMNL_CLEAR_EQ dens k t =
  let p = CWMNL_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMNL_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMNL_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWMNL_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMNL_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMNL_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMNL_LT_BY_POS else CWMNL_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWMNL_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMNL_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMNL_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMNL_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMNL_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWMNL_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMNL_SCALE_LT else CWMNL_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMNL_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: X (def) *)
let CWMNL_X_DEF = new_definition
 `cwmnl_x (c:real) (s:real) = s - &1 + (&1 - (&457 / &500) * s) / c`;;

(* Lean: leftMargin (def) *)
let CWMNL_LEFTMARGIN_DEF = new_definition
 `cwmnl_leftmargin (c:real) (s:real) (d:real) (t:real) (l:real) (r:real) =
    l + r - &1 + l pow 2 * cwmnl_x c s + l * r * (c + d - &2 - d pow 2) +
    r pow 2 * (&43 / &500 + t * (&1 - d))`;;

(* Lean: wallMargin (def) *)
let CWMNL_WALLMARGIN_DEF = new_definition
 `cwmnl_wallmargin (c:real) (s:real) (d:real) (t:real) (l:real) (r:real) =
    &1 - l + l * cwmnl_x c s + r * (c - &3 + (&1 - (&457 / &500) * t) / d + l + r * t / d)`;;

(* Lean: wall_support *)
let CWMNL_WALL_SUPPORT = prove
 (`forall cW sW uW vW aW t l r.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cW t /\ c977cc_normal l r /\ sW = --t /\ t <= r /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     vW + aW <= (&457 / &500) * t + &3 * cW
     ==> ABT_lower cW sW uW vW aW r l <=
         (r * cW - l * t) * ((&457 / &500) * cW - &2 * t) +
         (r * t + l * cW) * ((&457 / &500) * t + &3 * cW - aW)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `cW:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= cW * (r - t)`; `&0 <= t * (cW - l)`; `&0 <= r * cW - l * t`;
    `&0 <= r * t + l * cW`] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `r:real`; `l:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  UNDISCH_TAC `linside cW sW uW vW aW (&457 / &500) (&2)` THEN
  ASM_SIMP_TAC[C977NCO_NEGATIVE_BANDS] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (r * cW - l * t) * ((cW * &457 / &500 - t * &2) - uW)`;
    `&0 <= (r * t + l * cW) * (((&457 / &500) * t + &3 * cW) - (vW + aW))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: left_axis_of_margin *)
let CWMNL_LEFT_AXIS_OF_MARGIN = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ c977cc_normal cW t /\
     sL = --r /\ sW = --t /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     t <= r /\ linside cW sW uW vW aW (&457 / &500) (&2) /\
     uL + aL <= ABT_lower cO sO uO vO aO cL (--r) /\
     vL + aL <= ABT_lower cW sW uW vW aW r cL /\
     &0 <= cwmnl_leftmargin cO sO cW t cL r
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cL:real`; `r:real`;
                `&2 * cO + (&457 / &500) * sO`] CWMNC_BOTTOM_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `r:real`] CWMNL_WALL_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  ASM_REWRITE_TAC[lcx; REAL_ABS_NEG] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `abs r = r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(cO = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWMNL_CLEAR_ASSUME_TAC [`cO:real`,`iO:real`] `cO:real`
    (REWRITE_RULE[CWMNL_LEFTMARGIN_DEF; CWMNL_X_DEF]
      (ASSUME `&0 <= cwmnl_leftmargin cO sO cW t cL r`)) THEN
  let H = `sO * cL + cO * r` and E = `r * cW - cL * t` and K = `r * t + cL * cW`
  and M = `(&457 / &500) * cW - &2 * t` and T = `(&457 / &500) * t + &3 * cW` in
  let qc = subst [H,`HH:real`; K,`KK:real`]
      `cO * (cL + r) + cL * (cO * HH + cL) + cO * r * KK`
  and rc = subst [E,`EE:real`; K,`KK:real`; M,`MM:real`; T,`TT:real`]
      `cL pow 2 * (&2 * cO + (&457 / &500) * sO) + cO * r * (EE * MM + KK * TT)` in
  let sub tm = subst [qc,`QC:real`; rc,`RC:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= cL * uL + r * vL`;
    `&0 <= cL * ((cL * (&2 * cO + (&457 / &500) * sO) -
                  aL * (cO * (sO * cL + cO * r) + cL)) - cO * ABT_lower cO sO uO vO aL cL (--r))`;
    `&0 <= cO * (ABT_lower cO sO uO vO aL cL (--r) - (uL + aL))`;
    `&0 <= cL * (cO * (ABT_lower cO sO uO vO aL cL (--r) - (uL + aL)))`;
    `&0 <= cO * (cL * uL + r * vL)`; `&0 <= cO * r`;
    `&0 <= (cO * r) * (((r * cW - cL * t) * ((&457 / &500) * cW - &2 * t) +
                       (r * t + cL * cW) * ((&457 / &500) * t + &3 * cW - aL)) -
                      ABT_lower cW sW uW vW aL r cL)`;
    `&0 <= (cO * r) * (ABT_lower cW sW uW vW aL r cL - (vL + aL))`;
    `aL * QC <= RC`;
    `&0 <= sO * cL + cO * r`; `&0 <= r * t + cL * cW`;
    `&0 < cO * (cL + r)`; `&0 <= cO * (sO * cL + cO * r) + cL`;
    `&0 <= cL * (cO * (sO * cL + cO * r) + cL)`; `&0 <= (cO * r) * (r * t + cL * cW)`;
    `&0 < QC`; `&0 < (aL - &1) * QC`]) THEN
  NLIN_TAC ~deg2:false
   [CWMNL_EQ_HINT `cO:real` (ASSUME `cL pow 2 + r pow 2 = &1`);
    CWMNL_EQ_HINT `cO * (&2 * cL * r + (&457 / &500) * r pow 2)`
      (ASSUME `cW pow 2 + t pow 2 = &1`)]);;

(* Lean: wall_axis_of_margin *)
let CWMNL_WALL_AXIS_OF_MARGIN = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW (uW:real) vW aW r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ c977cc_normal cW t /\
     sL = --r /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     t <= r /\
     uL + aL <= ABT_lower cO sO uO vO aO cL (--r) /\
     ABT_upper cL sL uL vL aL t cW <= vW /\
     &0 <= cwmnl_wallmargin cO sO cW t cL r
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`; `cL:real`; `r:real`;
                `&2 * cO + (&457 / &500) * sO`] CWMNC_BOTTOM_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `r:real`; `cW:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  ASM_REWRITE_TAC[lcx; REAL_ABS_NEG] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aL`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `abs r = r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cW * (r - t)`; `&0 <= t * (cW - cL)`; `t * cL - cW * r <= &0`;
    `&0 <= r * t + cL * cW`] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`;
                `t:real`; `cW:real`] C977NCO_UPPER_NEGATIVE_NONPOS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cL * uL + r * vL`; `&0 <= (r * t + cL * cW) * (cL * uL + r * vL)`] THEN
  SUBGOAL_THEN `&0 <= r * ABT_upper cL sL uL vL aL t cW + cW * uL - aL * r * (r * t + cL * cW)`
    ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false
     [CWMNL_EQ_HINT `--cW * uL` (ASSUME `cL pow 2 + r pow 2 = &1`);
      CWMNL_EQ_HINT `r:real` (ASSUME `ABT_upper cL sL uL vL aL t cW =
         (t * cL - cW * r) * uL + (t * r + cW * cL) * (vL + aL)`)]; ALL_TAC] THEN
  SUBGOAL_THEN `~(cO = &0) /\ ~(cW = &0) /\ &0 < cO * cW` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWMNL_CLEAR_ASSUME_TAC [`cO:real`,`iO:real`; `cW:real`,`iW:real`] `cO * cW`
    (REWRITE_RULE[CWMNL_WALLMARGIN_DEF; CWMNL_X_DEF]
      (ASSUME `&0 <= cwmnl_wallmargin cO sO cW t cL r`)) THEN
  let qc = `cW * (cO * (sO * cL + cO * r) + cL + cO) + cO * r * (r * t + cL * cW) + cO * r`
  and rc = `cW * cL * (&2 * cO + (&457 / &500) * sO) + cO * r * ((&457 / &500) * t + &3 * cW)` in
  let sub tm = subst [qc,`QC:real`; rc,`RC:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= cW * ((cL * (&2 * cO + (&457 / &500) * sO) -
                  aL * (cO * (sO * cL + cO * r) + cL)) - cO * ABT_lower cO sO uO vO aL cL (--r))`;
    `&0 <= cO * (ABT_lower cO sO uO vO aL cL (--r) - (uL + aL))`;
    `&0 <= cW * (cO * (ABT_lower cO sO uO vO aL cL (--r) - (uL + aL)))`;
    `&0 <= cO * (r * ABT_upper cL sL uL vL aL t cW + cW * uL - aL * r * (r * t + cL * cW))`;
    `&0 <= cO * r`;
    `&0 <= (cO * r) * (vW - ABT_upper cL sL uL vL aL t cW)`;
    `&0 <= (cO * r) * (((&457 / &500) * t + &3 * cW) - (vW + aL))`;
    `aL * QC <= RC`;
    `&0 <= sO * cL + cO * r`; `&0 < cO * (sO * cL + cO * r) + cL + cO`;
    `&0 < cW * (cO * (sO * cL + cO * r) + cL + cO)`;
    `&0 <= (cO * r) * (r * t + cL * cW)`;
    `&0 < QC`; `&0 < (aL - &1) * QC`]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: left_axis *)
let CWMNL_LEFT_AXIS = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW uW vW aW r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ c977cc_normal cW t /\
     sL = --r /\ sW = --t /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     sO <= t /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     linside cL sL uL vL aL (&1) (&1) /\ linside cW sW uW vW aW (&457 / &500) (&2) /\
     uL + aL <= ABT_lower cO sO uO vO aO cL (--r) /\
     vL + aL <= ABT_lower cW sW uW vW aW r cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `t:real`; `cO:real`; `sO:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`]
    CWMNC_RESTRICTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `r:real`]
    CWMNB_LEFT_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `r:real`; `t:real`]
    CWMNL_LEFT_AXIS_OF_MARGIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CWMNL_LEFTMARGIN_DEF; CWMNL_X_DEF] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           UNDISCH_TAC `&0 <= cL + r - &1 + cwmnb_x cO sO * cL pow 2 +
                 (cO + cW - &2 - cW pow 2) * cL * r +
                 ((&43 / &500) + t * (&1 - cW)) * r pow 2` THEN
           REWRITE_TAC[CWMNB_X_DEF] THEN REAL_ARITH_TAC];
    REWRITE_TAC[]]);;

(* Lean: wall_axis *)
let CWMNL_WALL_AXIS = prove
 (`forall cO sO uO vO aO cL sL uL vL aL cW sW (uW:real) vW aW r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ c977cc_normal cW t /\
     sL = --r /\ &1 < aL /\ aO = aL /\ aL = aW /\
     lcont cO sO uO vO aO /\ lcont cL sL uL vL aL /\
     uO + aO <= &2 * cO + (&457 / &500) * sO /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     sO <= t /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     linside cL sL uL vL aL (&1) (&1) /\
     uL + aL <= ABT_lower cO sO uO vO aO cL (--r) /\
     ABT_upper cL sL uL vL aL t cW <= vW
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `t:real`; `cO:real`; `sO:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`]
    CWMNC_RESTRICTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `r:real`]
    CWMNB_WALL_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `r:real`; `t:real`]
    CWMNL_WALL_AXIS_OF_MARGIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CWMNL_WALLMARGIN_DEF; CWMNL_X_DEF] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REAL_ARITH_TAC;
           UNDISCH_TAC `&0 <= &1 - cL + cL * cwmnb_x cO sO +
              r * (cO - &3 + (&1 - (&457 / &500) * t) / cW + cL + r * t / cW)` THEN
           REWRITE_TAC[CWMNB_X_DEF] THEN REAL_ARITH_TAC];
    REWRITE_TAC[]]);;
