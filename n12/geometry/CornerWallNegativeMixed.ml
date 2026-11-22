(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallNegativeMixed.lean                     *)
(* (namespace N12Compact.CornerWallNegativeMixed).                           *)
(* The negative singleton's O-v / L-v selector is excluded.  Squares are     *)
(* 5-tuples (L.s = -r, W.s = -t); Lean lower is ABT_lower; bottom is         *)
(* cwcb_bottom; the margins are CWNMB_LOW_MARGIN / CWNMB_HIGH_MARGIN;        *)
(* CornerWallNegativeShared.wall_support is CWNS_WALL_SUPPORT.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallCycleBounds.ml";;
needs "n12/geometry/CornerWallNegativeMixedBounds.ml";;
needs "n12/geometry/CornerWallNegativeShared.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWNMX_clear_poly dens k t =
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
  then failwith "CWNMX_clear_poly: denominators remain" else
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
let CWNMX_CLEAR_EQ dens k t =
  let p = CWNMX_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWNMX_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWNMX_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWNMX_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWNMX_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWNMX_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWNMX_LT_BY_POS else CWNMX_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWNMX_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWNMX_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWNMX_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWNMX_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWNMX_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWNMX_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWNMX_SCALE_LT else CWNMX_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWNMX_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: singleton_lower *)
let CWNMX_SINGLETON_LOWER = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL r.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ sL = --r /\
     lcont cL sL uL vL aL /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO
     ==> cL * (vO + aO) + aL * cL * (sO * cL + cO * r) <= cO * vL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                  ASM_REWRITE_TAC[lcx; REAL_ABS_NEG] THEN DISCH_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `abs r = r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= sO * cL + cO * r`; `&0 <= cO * (cL - r)`; `&0 <= r * (cO - sO)`;
    `&0 <= cO * cL - sO * r`] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`;
                `--sO`; `cO:real`] C977NCO_LOWER_NEGATIVE_NONPOS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cL * uL + r * vL`; `&0 <= (sO * cL + cO * r) * (cL * uL + r * vL)`;
    `&0 <= cL * (ABT_lower cL sL uL vL aL (--sO) cO - (vO + aO))`] THEN
  NLIN_TAC ~deg2:false
   [CWNMX_EQ_HINT `--cO * vL` (ASSUME `cL pow 2 + r pow 2 = &1`);
    CWNMX_EQ_HINT `cL:real` (ASSUME `ABT_lower cL sL uL vL aL (--sO) cO =
       (--sO * cL - cO * r) * (uL + aL) + (--sO * r + cO * cL) * vL`)]);;

(* Lean: marker_support *)
let CWNMX_MARKER_SUPPORT = prove
 (`forall cW sW uW vW aW t l r.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cW t /\ c977cc_normal l r /\ sW = --t /\ t <= r /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     vW + aW <= t + (&72 / &25) * cW
     ==> ABT_lower cW sW uW vW aW r l + aW * (r * t + l * cW) <=
         (r * cW - l * t) * ((&457 / &500) * cW - &2 * t) +
         (r * t + l * cW) * (t + (&72 / &25) * cW)`,
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
    `&0 <= (r * t + l * cW) * ((t + (&72 / &25) * cW) - (vW + aW))`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: sector *)
let CWNMX_SECTOR = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ c977cc_normal cW t /\
     sL = --r /\ sW = --t /\ &1 < aL /\ aL = aW /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     linside cW sW uW vW aW (&457 / &500) (&2) /\
     cwcb_bottom cO sO < vO + aO /\
     vW + aW <= t + (&72 / &25) * cW /\
     sO <= t /\ t <= &51 / &100 /\ &43 / &50 <= cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     vL + aL <= ABT_lower cW sW uW vW aW r cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`]
    CWNMX_SINGLETON_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `~(cO = &0) /\ ~(cW = &0) /\ &0 < cO * cW` STRIP_ASSUME_TAC THENL
   [C977CSB_NORMAL_TAC THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r <= t` THENL
   [MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                  `cL:real`; `r:real`] CWNS_WALL_SUPPORT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `r:real`]
      CWNMB_LOW_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`cW:real`; `t:real`; `cL:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
    C977CSB_NORMAL_TAC THEN
    CWNMX_CLEAR_ASSUME_TAC [`cO:real`,`iO:real`; `cW:real`,`iW:real`] `cO * cW`
      (ASSUME `&0 < &1 + (cL / cO) * cwcb_bottom cO sO + cL * (sO * cL + cO * r) / cO +
              cL / cW - (r * cW - cL * t) - (cL / cW) * (t + (&72 / &25) * cW)`) THEN
    (let qc = `cO * cW + cW * cL * (sO * cL + cO * r) + cO * (cL - cW * (r * cW - cL * t))` in
    let sub tm = subst [qc,`QC:real`] tm in
    NLIN_FACTS_TAC [] (map sub
     [`&0 <= cW * (ABT_lower cW sW uW vW aL r cL - (vL + aL))`;
      `&0 <= cW * (cO * vL - (cL * (vO + aO) + aL * cL * (sO * cL + cO * r)))`;
      `&0 <= cO * ((cL * (t + (&72 / &25) * cW) - aL * (cL - cW * (r * cW - cL * t))) -
                   cW * ABT_lower cW sW uW vW aL r cL)`;
      `&0 <= cO * (cW * (ABT_lower cW sW uW vW aL r cL - (vL + aL)))`;
      `cW * cL * (vO + aO) + aL * QC <= cO * cL * (t + (&72 / &25) * cW)`;
      `&0 <= cW * (t - r)`; `&0 <= t * (cL - cW)`; `&0 <= --(r * cW - cL * t)`;
      `&0 <= cL - cW * (r * cW - cL * t)`; `&0 <= cO * (cL - cW * (r * cW - cL * t))`;
      `&0 <= sO * cL + cO * r`; `&0 <= cW * cL`;
      `&0 <= (cW * cL) * (sO * cL + cO * r)`;
      `&0 < QC`; `&0 < (aL - &1) * QC`;
      `&0 < (cW * cL) * ((vO + aO) - cwcb_bottom cO sO)`]) THEN
    NLIN_TAC ~deg2:false []);
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                  `cL:real`; `r:real`] CWNMX_MARKER_SUPPORT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `r:real`]
      CWNMB_HIGH_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
    C977CSB_NORMAL_TAC THEN
    CWNMX_CLEAR_ASSUME_TAC [`cO:real`,`iO:real`] `cO:real`
      (ASSUME `&0 <= &1 + (cL / cO) * cwcb_bottom cO sO + cL * (sO * cL + cO * r) / cO +
              (r * t + cL * cW) - (r * cW - cL * t) * ((&457 / &500) * cW - &2 * t) -
              (r * t + cL * cW) * (t + (&72 / &25) * cW)`) THEN
    (let qc = `cL * (sO * cL + cO * r) + cO * (&1 + (r * t + cL * cW))` in
    let sub tm = subst [qc,`QC:real`] tm in
    NLIN_FACTS_TAC [] (map sub
     [`&0 <= cO * (((r * cW - cL * t) * ((&457 / &500) * cW - &2 * t) +
                    (r * t + cL * cW) * (t + (&72 / &25) * cW)) -
                   (ABT_lower cW sW uW vW aL r cL + aL * (r * t + cL * cW)))`;
      `&0 <= cO * (ABT_lower cW sW uW vW aL r cL - (vL + aL))`;
      `cL * (vO + aO) + aL * QC <=
       cO * ((r * cW - cL * t) * ((&457 / &500) * cW - &2 * t) +
             (r * t + cL * cW) * (t + (&72 / &25) * cW))`;
      `&0 <= sO * cL + cO * r`; `&0 <= cL * (sO * cL + cO * r)`;
      `&0 <= r * t + cL * cW`; `&0 < cO * (&1 + (r * t + cL * cW))`;
      `&0 < QC`; `&0 < (aL - &1) * QC`;
      `&0 < cL * ((vO + aO) - cwcb_bottom cO sO)`]) THEN
    NLIN_TAC ~deg2:false [])]);;
