(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerOtherMixedBounds.lean           *)
(* (namespace N12Compact.CornerWallMarkerOtherMixedBounds).                 *)
(* The other positive-left transverse selector with the genuine upper marker.*)
(* Normal c s is c977cc_normal c s (C977CornerCubic).  Divisions by the     *)
(* positive cosines are cleared by CWMOMB_CLEAR_TAC.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/CornerWallMarkerSharedBounds.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing variable denominators: k * t = P with P a polynomial, for terms  *)
(* t whose divisions are by the variables in dens (each paired with a fresh  *)
(* name for its inverse).  P is computed outside the kernel and the equation *)
(* is proved by REAL_FIELD.                                                  *)
(* ------------------------------------------------------------------------- *)

let CWMOMB_clear_poly dens k t =
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
  then failwith "CWMOMB_clear_poly: denominators remain" else
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
let CWMOMB_CLEAR_EQ dens k t =
  let p = CWMOMB_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMOMB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMOMB_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWMOMB_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMOMB_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMOMB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMOMB_LT_BY_POS else CWMOMB_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWMOMB_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMOMB_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMOMB_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMOMB_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMOMB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWMOMB_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMOMB_SCALE_LT else CWMOMB_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMOMB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

(* Lean: coefficient (private) *)
let CWMOMB_COEFFICIENT = prove
 (`forall c s. c977cc_normal c s /\ &4 / &5 <= c /\ s <= &3 / &5
         ==> --(&1 / &10) * s pow 2 <= c + s - &2 + (&1 - (&457 / &500) * s) / c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  CWMOMB_CLEAR_TAC [`c:real`,`ic:real`] `c:real` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`&0 <= c * s pow 2`] THEN
  ASM_CASES_TAC `&457 / &500 <= c` THENL
   [NLIN_FACTS_TAC [] [`&0 <= s * (c - &457 / &500)`] THEN
    NLIN_TAC ~deg2:false [SQ_NONNEG `&1 - c`];
    NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
     [`&0 <= (&3 / &5 - s) * (&457 / &500 - c)`;
      `&0 <= --(&1 / &10) * c pow 2 + (&23 / &25) * c - &141 / &250`;
      `&0 <= (c - &4 / &5) * (--(&1 / &10) * c pow 2 + (&23 / &25) * c - &141 / &250)`] THEN
    NLIN_TAC ~deg2:false [CWMOMB_EQ_HINT `(&1 / &10) * c` (ASSUME `c pow 2 + s pow 2 = &1`)]]);;

(* Lean: quartic_disk (private) *)
let CWMOMB_QUARTIC_DISK = prove
 (`forall l r d t. c977cc_normal l r /\ c977cc_normal d t
     ==> &0 <= l + d * (&1 + l pow 2 - &3 * l) + t * (l pow 2 - l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&1 - l`]
   [`(&1 - l) pow 2 <= &9 / &100`;
    `&0 <= (&1 - l) pow 2 * (&1 - &2 * (&1 - l) pow 2)`] THEN
  SUBGOAL_THEN `(&1 + l pow 2 - &3 * l) pow 2 + (l pow 2 - l) pow 2 <= l pow 2` MP_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SPEC_TAC(`&1 + l pow 2 - &3 * l`,`A:real`) THEN SPEC_TAC(`l pow 2 - l`,`B:real`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(d * A + t * B) pow 2 + (d * B - t * A) pow 2 = A pow 2 + B pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d * B - t * A`] [`(d * A + t * B) pow 2 <= l pow 2`] THEN
  NLIN_TAC []);;

(* Lean: margin *)
let CWMOMB_MARGIN = prove
 (`forall c s d t l r extra.
     c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= &3 / &5 /\ &4 / &5 <= d /\
     &0 <= extra /\ s * l - c * r <= extra
     ==> &0 <= &1 + d * c + t * l + d * r + d / l +
              (d * r / l) * (s - &2 + (&1 - (&457 / &500) * s) / c) -
              (&457 / &500) * t - &3 * d + (d / l) * extra`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(d = &0) /\ ~(l = &0) /\ &0 < l` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r <= t` THENL
   [MP_TAC(SPECL [`d:real`; `t:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `l:real`; `r:real`; `extra:real`]
      CWMSB_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `&1 + d * c + t * l + d * r + d / l +
      (d * r / l) * (s - &2 + (&1 - (&457 / &500) * s) / c) -
      (&457 / &500) * t - &3 * d + (d / l) * extra =
      (d / l) * (&1 + l * cwmsb_first c d t + r * cwmsb_second c s d + extra) +
      ((t * l + d * r) * (l - d)) / l` SUBST1_TAC THENL
     [REWRITE_TAC[CWMSB_FIRST_DEF; CWMSB_SECOND_DEF] THEN
      MAP_EVERY UNDISCH_TAC [`~(c = &0)`; `~(d = &0)`; `~(l = &0)`] THEN
      CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC];
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(SPECL [`l:real`; `r:real`; `d:real`; `t:real`] C977CSB_COSINE_ORDER) THEN
    MP_TAC(SPECL [`l:real`; `r:real`; `d:real`; `t:real`] CWMOMB_QUARTIC_DISK) THEN
    MP_TAC(SPECL [`c:real`; `s:real`] CWMOMB_COEFFICIENT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    DISCH_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    CWMOMB_CLEAR_ASSUME_TAC [`c:real`,`ic:real`] `c:real`
      (ASSUME `--(&1 / &10) * s pow 2 <= c + s - &2 + (&1 - (&457 / &500) * s) / c`) THEN
    CWMOMB_CLEAR_TAC [`l:real`,`il:real`; `c:real`,`ic:real`] `l * c` THEN
    let cb = `c * s - &2 * c + &1 - (&457 / &500) * s` in
    let sub t = subst [cb,`CB:real`] t in
    NLIN_FACTS_TAC []
     [`&0 <= d * extra`; `&0 <= c * (d * extra)`;
      `&0 <= c * (l + d * (&1 + l pow 2 - &3 * l) + t * (l pow 2 - l))`] THEN
    ASM_CASES_TAC (sub `c * l + CB <= &0`) THENL
     [NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
       (map sub
       [`&0 <= d * (l - r)`; `&0 <= (d * (l - r)) * --(c * l + CB)`;
        `&0 <= d * l`;
        `&0 <= s * (&3 / &5 - s)`; `&0 <= (&1 - d) * s pow 2`;
        `&0 <= (&43 / &500) * t - (&1 / &10) * d * s pow 2`;
        `&0 <= c * l`; `&0 <= (c * l) * ((&43 / &500) * t - (&1 / &10) * d * s pow 2)`]) THEN
      NLIN_FACTS_TAC [] [`&0 <= d * l * (c pow 2 + c * s - &2 * c + &1 - (&457 / &500) * s +
                                          (&1 / &10) * c * s pow 2)`] THEN
      NLIN_TAC ~deg2:false [];
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
      NLIN_FACTS_TAC []
       (map sub
       [`&0 <= d * r`; `&0 <= (d * r) * (c * l + CB)`;
        `&0 <= d * l`; `l <= c`; `&0 <= c * (d * l)`; `&0 <= (c * (d * l)) * (c - l)`;
        `&0 <= t * l`; `&0 <= c * (t * l)`]) THEN
      NLIN_TAC ~deg2:false []]]);;
