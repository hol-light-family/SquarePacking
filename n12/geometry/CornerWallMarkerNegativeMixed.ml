(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerNegativeMixed.lean               *)
(* (namespace N12Compact.CornerWallMarkerNegativeMixed).                     *)
(* The genuine-marker negative-L O-v / L-v selector on the full canonical    *)
(* arc.  Squares are 5-tuples (L.s = -r, W.s = -t); Lean upper/lower are     *)
(* ABT_upper/ABT_lower; boundary, G are cwmmb_boundary, cwmmb_g; X, Y, H are *)
(* cwml_x, cwml_y, cwml_h; singleton_lower is CWNMX_SINGLETON_LOWER.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/CornerWallMarkerMixedBounds.ml";;
needs "n12/geometry/CornerWallNegativeMixed.ml";;
needs "n12/geometry/CornerWallMarkerLongitudinal.ml";;
needs "n12/geometry/CornerWallMarkerNegativeHighBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMNM_clear_poly dens k t =
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
  then failwith "CWMNM_clear_poly: denominators remain" else
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
let CWMNM_CLEAR_EQ dens k t =
  let p = CWMNM_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMNM_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMNM_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWMNM_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMNM_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMNM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMNM_LT_BY_POS else CWMNM_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWMNM_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMNM_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMNM_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMNM_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMNM_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWMNM_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMNM_SCALE_LT else CWMNM_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMNM_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: low_margin *)
let CWMNM_LOW_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ r <= t /\ t <= &3 / &5 /\ &4 / &5 <= d
     ==> &0 <= &1 + (l / c) * cwmmb_boundary c s + l * (s * l + c * r) / c + l / d -
              (r * d - l * t) - (l / d) * (t + &3 * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `l:real`; `r:real`]
    CWMMB_LINEAR_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(d = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  let H = `c * (&1 + l) * (l + &1 - &2 * d) - s * l * r` in
  let sub tm = subst [H,`HH:real`] tm in
  SUBGOAL_THEN (sub `&0 <= HH`) ASSUME_TAC THENL
   [ASM_CASES_TAC `r <= s` THENL
     [MP_TAC(SPECL [`c:real`; `s:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= c * (&1 + l)`; `&0 <= (c * (&1 + l)) * (c - d)`;
        `&0 <= s * l`; `&0 <= (s * l) * (s - r)`; `&0 <= c * l`;
        `&0 <= c * l + &2 * c - &1`; `&0 <= (l - c) * (c * l + &2 * c - &1)`] THEN
      NLIN_TAC ~deg2:false [CWMNM_EQ_HINT `--l` (ASSUME `c pow 2 + s pow 2 = &1`)];
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      MP_TAC(SPECL [`l:real`; `r:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      NLIN_FACTS_TAC []
       [`&0 <= c * (r - s)`; `&0 <= s * (c - l)`; `&0 <= c * r - s * l`;
        `&0 <= r * (c * r - s * l)`;
        `&0 <= c * (&1 + l)`; `&0 <= (c * (&1 + l)) * (l - d)`] THEN
      NLIN_TAC ~deg2:false [CWMNM_EQ_HINT `--c` (ASSUME `l pow 2 + r pow 2 = &1`)]];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [] (map sub [`&0 <= r * HH`]) THEN
  SUBGOAL_THEN `&0 <= (s / c) * l * (l - &1) + r * (l + &1 - &2 * d)` ASSUME_TAC THENL
   [CWMNM_CLEAR_TAC [`c:real`,`ic:real`] `c * (&1 + l)` THEN
    NLIN_TAC ~deg2:false [CWMNM_EQ_HINT `s * l` (ASSUME `l pow 2 + r pow 2 = &1`)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + (l / c) * cwmmb_boundary c s + l * (s * l + c * r) / c + l / d -
     (r * d - l * t) - (l / d) * (t + &3 * d)) -
    (&1 + l * (cwmmb_g c s + t + (&1 - t) / d - &3) - r * (&1 - d)) =
    (s / c) * l * (l - &1) + r * (l + &1 - &2 * d)` ASSUME_TAC THENL
   [REWRITE_TAC[CWMMB_G_DEF] THEN
    MAP_EVERY UNDISCH_TAC [`~(c = &0)`; `~(d = &0)`] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: wall_support *)
let CWMNM_WALL_SUPPORT = prove
 (`forall cW sW uW vW aW t l r H.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cW t /\ c977cc_normal l r /\ sW = --t /\ r <= t /\
     lcont cW sW uW vW aW /\ vW + aW <= H
     ==> cW * ABT_lower cW sW uW vW aW r l <=
         l * H - aW * (l - cW * (r * cW - l * t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `t:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= cW * (t - r)`; `&0 <= t * (l - cW)`; `r * cW - l * t <= &0`;
    `&0 <= r * t + l * cW`] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `r:real`; `l:real`] C977NCO_LOWER_NEGATIVE_NONPOS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[lcx; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `abs t = t` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; DISCH_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= cW * uW + t * vW`;
    `&0 <= --(r * cW - l * t) * (cW * uW + t * vW)`;
    `&0 <= l * (H - (vW + aW))`] THEN
  NLIN_TAC ~deg2:false [CWMNM_EQ_HINT `l * vW` (ASSUME `cW pow 2 + t pow 2 = &1`)]);;

(* Lean: low_sector *)
let CWMNM_LOW_SECTOR = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ c977cc_normal cW t /\
     sL = --r /\ sW = --t /\ &1 < aL /\ aL = aW /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     cwmmb_boundary cO sO < vO + aO /\
     vW + aW <= t + &3 * cW /\
     sO <= t /\ r <= t /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     vL + aL <= ABT_lower cW sW uW vW aW r cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`]
    CWNMX_SINGLETON_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `r:real`; `t + &3 * cW`] CWMNM_WALL_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `r:real`]
    CWMNM_LOW_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `t:real`; `cL:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(cO = &0) /\ ~(cW = &0) /\ &0 < cO * cW` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CWMNM_CLEAR_ASSUME_TAC [`cO:real`,`iO:real`; `cW:real`,`iW:real`] `cO * cW`
    (ASSUME `&0 <= &1 + (cL / cO) * cwmmb_boundary cO sO + cL * (sO * cL + cO * r) / cO +
              cL / cW - (r * cW - cL * t) - (cL / cW) * (t + &3 * cW)`) THEN
  let qc = `cO * cW + cW * cL * (sO * cL + cO * r) + cO * (cL - cW * (r * cW - cL * t))` in
  let sub tm = subst [qc,`QC:real`] tm in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= cW * (ABT_lower cW sW uW vW aL r cL - (vL + aL))`;
    `&0 <= cW * (cO * vL - (cL * (vO + aO) + aL * cL * (sO * cL + cO * r)))`;
    `&0 <= cO * ((cL * (t + &3 * cW) - aL * (cL - cW * (r * cW - cL * t))) -
                 cW * ABT_lower cW sW uW vW aL r cL)`;
    `&0 <= cO * (cW * (ABT_lower cW sW uW vW aL r cL - (vL + aL)))`;
    `cW * cL * (vO + aO) + aL * QC <= cO * cL * (t + &3 * cW)`;
    `&0 <= cW * (t - r)`; `&0 <= t * (cL - cW)`; `&0 <= --(r * cW - cL * t)`;
    `&0 <= cL - cW * (r * cW - cL * t)`; `&0 <= cO * (cL - cW * (r * cW - cL * t))`;
    `&0 <= sO * cL + cO * r`; `&0 <= cW * cL`;
    `&0 <= (cW * cL) * (sO * cL + cO * r)`;
    `&0 < QC`; `&0 < (aL - &1) * QC`;
    `&0 < (cW * cL) * ((vO + aO) - cwmmb_boundary cO sO)`]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: high_wall_support *)
let CWMNM_HIGH_WALL_SUPPORT = prove
 (`forall cW sW uW vW aW t l r.
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cW t /\ c977cc_normal l r /\ sW = --t /\ t <= r /\
     uW + aW <= (&33 / &20) * cW - (&47 / &20) * t /\
     vW + aW <= (&457 / &500) * t + &3 * cW
     ==> ABT_lower cW sW uW vW aW r l + (aW - &1) * cwml_h cW t r l <=
         r * cwml_y cW t + l * cwml_x cW t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `cW:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= cW * (r - t)`; `&0 <= t * (cW - l)`; `&0 <= r * cW - l * t`;
                     `&0 <= r * t + l * cW`] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `r:real`; `l:real`] C977NCO_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[CWML_X_DEF; CWML_Y_DEF; CWML_H_DEF] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (r * cW - l * t) * (((&33 / &20) * cW - (&47 / &20) * t) - (uW + aW))`;
    `&0 <= (r * t + l * cW) * (((&457 / &500) * t + &3 * cW) - (vW + aW))`] THEN
  NLIN_TAC ~deg2:false
   [CWMNM_EQ_HINT `(&33 / &20) * r + &3 * l` (ASSUME `cW pow 2 + t pow 2 = &1`)]);;

(* Lean: high_sector_of_margin *)
let CWMNM_HIGH_SECTOR_OF_MARGIN = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ c977cc_normal cW t /\
     sL = --r /\ sW = --t /\ &1 < aL /\ aL = aW /\
     lcont cL sL uL vL aL /\
     cwmmb_boundary cO sO < vO + aO /\
     uW + aW <= (&33 / &20) * cW - (&47 / &20) * t /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     t <= r /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     vL + aL <= ABT_lower cW sW uW vW aW r cL /\
     &0 <= &1 + (cL / cO) * cwmmb_boundary cO sO + (cL / cO) * (sO * cL + cO * r) -
           r * cwml_y cW t - cL * cwml_x cW t
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `r:real`]
    CWNMX_SINGLETON_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`;
                `cL:real`; `r:real`] CWMNM_HIGH_WALL_SUPPORT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aW`)) THEN
  MP_TAC(SPECL [`cL:real`; `r:real`; `cW:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(cO = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cwml_h cW t r cL` ASSUME_TAC THENL
   [REWRITE_TAC[CWML_H_DEF] THEN
    NLIN_FACTS_TAC [] [`&0 <= cW * (r - t)`; `&0 <= t * (cW - cL)`; `&0 <= r * t`;
                       `&0 <= cL * cW`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN
   `cO * (&1 + (cL / cO) * cwmmb_boundary cO sO + (cL / cO) * (sO * cL + cO * r) -
          r * cwml_y cW t - cL * cwml_x cW t) =
    cL * cwmmb_boundary cO sO + (cO + cL * (sO * cL + cO * r) + cO * cwml_h cW t r cL) -
    cO * (r * cwml_y cW t + cL * cwml_x cW t + cwml_h cW t r cL)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(cO = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= sO * cL + cO * r`; `&0 <= cL * (sO * cL + cO * r)`;
    `&0 <= cO * cwml_h cW t r cL`;
    `&0 < cO + cL * (sO * cL + cO * r) + cO * cwml_h cW t r cL`;
    `&0 <= cO * (ABT_lower cW sW uW vW aL r cL - (vL + aL))`;
    `&0 <= cO * ((r * cwml_y cW t + cL * cwml_x cW t) -
                 (ABT_lower cW sW uW vW aL r cL + (aL - &1) * cwml_h cW t r cL))`;
    `&0 <= cO * (&1 + (cL / cO) * cwmmb_boundary cO sO + (cL / cO) * (sO * cL + cO * r) -
           r * cwml_y cW t - cL * cwml_x cW t)`;
    `&0 < cL * ((vO + aO) - cwmmb_boundary cO sO)`;
    `&0 < (aL - &1) * (cO + cL * (sO * cL + cO * r) + cO * cwml_h cW t r cL)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: sector *)
let CWMNM_SECTOR = prove
 (`forall cO sO (uO:real) vO aO cL sL uL vL aL cW sW uW vW aW r t.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\
     c977cc_normal cO sO /\ c977cc_normal cL r /\ c977cc_normal cW t /\
     sL = --r /\ sW = --t /\ &1 < aL /\ aL = aW /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     cwmmb_boundary cO sO < vO + aO /\
     uW + aW <= (&33 / &20) * cW - (&47 / &20) * t /\
     vW + aW <= (&457 / &500) * t + &3 * cW /\
     sO <= t /\ t <= &3 / &5 /\ &4 / &5 <= cW /\
     vO + aO <= ABT_lower cL sL uL vL aL (--sO) cO /\
     vL + aL <= ABT_lower cW sW uW vW aW r cL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `r <= t` THENL
   [MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `r:real`; `t:real`]
      CWMNM_LOW_SECTOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC;
                    REWRITE_TAC[]];
    MP_TAC(SPECL [`cO:real`; `sO:real`; `cW:real`; `t:real`; `cL:real`; `r:real`]
      CWMNHB_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `r:real`; `t:real`]
      CWMNM_HIGH_SECTOR_OF_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]]);;
