(* ========================================================================= *)
(* Port of Compact/Geometry/CornerWallMarkerMixedBounds.lean                *)
(* (namespace N12Compact.CornerWallMarkerMixedBounds).                      *)
(* Genuine-marker scalar for O-v / L-v when positive L tilts no farther than O.*)
(* Normal c s is c977cc_normal c s (C977CornerCubic).  Divisions by the     *)
(* positive cosines are cleared by CWMMB_CLEAR_TAC.                         *)
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

let CWMMB_clear_poly dens k t =
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
  then failwith "CWMMB_clear_poly: denominators remain" else
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
let CWMMB_CLEAR_EQ dens k t =
  let p = CWMMB_clear_poly dens k t in
  let nz = map (fun (v,_) -> mk_neg(mk_eq(v,`&0`))) dens in
  let gl = mk_imp(list_mk_conj nz, mk_eq(mk_binop `( * ):real->real->real` k t, p)) in
  REAL_FIELD gl;;

let CWMMB_LE_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 <= k * (y - x) ==> x <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;
let CWMMB_LT_BY_POS = prove
 (`forall k x y. &0 < k /\ &0 < k * (y - x) ==> x < y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* positivity of a product of positive factors and powers *)
let CWMMB_POS_TAC =
  (REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN TRY(MATCH_MP_TAC REAL_POW_LT) THEN
   RASM_ARITH_TAC) ORELSE NLIN_TAC [];;

(* goal a <= b (or a < b): reduce to &0 <= P (or &0 < P), P = k * (b - a)  *)
(* cleared; the nonzero-denominator and positivity side goals use RASM.    *)
let CWMMB_CLEAR_TAC dens k (asl,w as g) =
  let lt = is_comb w && is_comb(rator w) && fst(dest_const(rator(rator w))) = "real_lt" in
  let a = lhand w and b = rand w in
  let th = CWMMB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (MATCH_MP_TAC (if lt then CWMMB_LT_BY_POS else CWMMB_LE_BY_POS) THEN EXISTS_TAC k THEN
   CONJ_TAC THENL
    [CWMMB_POS_TAC;
     MP_TAC th THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
       DISCH_THEN SUBST1_TAC]]) g;;

(* from |- a <= b (or a < b) and |- &0 < k: |- &0 <= P, P = k * (b - a) cleared *)
let CWMMB_SCALE_LE = prove
 (`forall k x y. &0 < k /\ x <= y ==> &0 <= k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;
let CWMMB_SCALE_LT = prove
 (`forall k x y. &0 < k /\ x < y ==> &0 < k * (y - x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC);;

let CWMMB_CLEAR_ASSUME_TAC dens k th (asl,w as g) =
  let c = concl th in
  let lt = fst(dest_const(rator(rator c))) = "real_lt" in
  let a = lhand c and b = rand c in
  let eq = CWMMB_CLEAR_EQ dens k (mk_binop `(-):real->real->real` b a) in
  (SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` k) ASSUME_TAC THENL
    [CWMMB_POS_TAC; ALL_TAC] THEN
   MP_TAC eq THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(fun eqth ->
     let kth = ASSUME (mk_binop `(<):real->real->bool` `&0` k) in
     let th1 = MATCH_MP (if lt then CWMMB_SCALE_LT else CWMMB_SCALE_LE) (CONJ kth th) in
     ASSUME_TAC (REWRITE_RULE[eqth] th1))) g;;

(* p * (l - r) = 0 from |- l = r *)
let CWMMB_EQ_HINT p th =
  let r = rand(concl th) in
  let th1 = AP_TERM (mk_comb(`( * ):real->real->real`,p))
                    (AP_THM (AP_TERM `(-):real->real->real` th) r) in
  TRANS th1 (REWRITE_CONV[REAL_SUB_REFL; REAL_MUL_RZERO] (rand(concl th1)));;

let CWMMB_POS_CANCEL = prove
 (`forall k p. &0 < k /\ &0 <= k * p ==> &0 <= p`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: boundary (def) *)
let CWMMB_BOUNDARY_DEF = new_definition
 `cwmmb_boundary (c:real) (s:real) = &1 + s / c - &2 * s - (&457 / &500) * s pow 2 / c`;;

(* Lean: G (def) *)
let CWMMB_G_DEF = new_definition
 `cwmmb_g (c:real) (s:real) = (cwmmb_boundary c s + s) / c`;;

(* Lean: g_order *)
let CWMMB_G_ORDER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t /\
     t <= &3 / &5 /\ &4 / &5 <= d ==> cwmmb_g d t <= cwmmb_g c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  ASM_CASES_TAC `t = &0` THENL
   [SUBGOAL_THEN `s = &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [] [`&1 <= c`; `&1 <= d`] THEN
    SUBGOAL_THEN `c = &1 /\ d = &1` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ &0 < s + t` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CWMMB_G_DEF; CWMMB_BOUNDARY_DEF] THEN
  CWMMB_CLEAR_TAC [`c:real`,`ic:real`; `d:real`,`id:real`] `c pow 2 * d pow 2` THEN
  let R = `(&1 - d) + d * s pow 2 + s * t` in
  let B = `(c + d) * ((&457 / &500) * (s + t) - RR) - c * d * (&1 - s) * (s + t)` in
  let SG = `c * d * (&1 - s) * (s + t) + (c + d) * RR` in
  let sub t = subst [R,`RR:real`] (subst [B,`BB:real`; SG,`SS:real`] t) in
  NLIN_FACTS_TAC [SQ_NONNEG `d:real`]
   [`&0 <= (&1 - s) * (s + t)`; `c * d * (&1 + d) <= d * (c + d)`;
    `&0 <= ((&1 - s) * (s + t)) * (d * (c + d) - c * d * (&1 + d))`] THEN
  SUBGOAL_THEN (sub `d * (&1 - s) * (s + t) + (&1 + d) * RR =
                     (s + t) * (d + s) + t pow 2 * (&1 - s pow 2)`) ASSUME_TAC THENL
   [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
   (map sub
   [`&0 <= &1 - t pow 2`; `&0 <= (&1 - t pow 2) * (t - s)`;
    `&0 <= ((&1 - t pow 2) * (t - s)) * (t + &2 * s)`;
    `(s + t) * s + t pow 2 * (&1 - s pow 2) <= (s + t) * ((&3 * t - t pow 3) / &2)`;
    `&0 <= t * (&3 / &5 - t)`; `&0 <= &66 / &25 - (&3 / &5) * t - t pow 2`;
    `&0 <= (&3 / &5 - t) * (&66 / &25 - (&3 / &5) * t - t pow 2)`;
    `(&3 * t - t pow 3) / &2 <= &99 / &125`;
    `(s + t) * ((&3 * t - t pow 3) / &2) <= (s + t) * (&99 / &125)`;
    `&0 <= (s + t) * (&1 - d)`;
    `(s + t) * (d + s) + t pow 2 * (&1 - s pow 2) <= (&9 / &10) * (&1 + d) * (s + t)`;
    `(c + d) * ((s + t) * (d + s) + t pow 2 * (&1 - s pow 2)) <=
     (c + d) * ((&9 / &10) * (&1 + d) * (s + t))`]) THEN
  SUBGOAL_THEN (sub `(&1 + d) * SS <= (&9 / &10) * (&1 + d) * (s + t) * (c + d)`)
    ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false
     [CWMMB_EQ_HINT `c + d` (ASSUME (sub `d * (&1 - s) * (s + t) + (&1 + d) * RR =
                     (s + t) * (d + s) + t pow 2 * (&1 - s pow 2)`))]; ALL_TAC] THEN
  SUBGOAL_THEN (sub `SS <= (&9 / &10) * (s + t) * (c + d)`) ASSUME_TAC THENL
   [MATCH_MP_TAC CWMMB_LE_BY_POS THEN EXISTS_TAC `&1 + d` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
  NLIN_FACTS_TAC [] (map sub [`&0 <= (s + t) * (c + d)`; `&0 <= BB`; `&0 <= (t - s) * BB`]) THEN
  (fun (asl,w as g) ->
     let p = rand w in
     (MATCH_MP_TAC CWMMB_POS_CANCEL THEN EXISTS_TAC `c + d` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_binop `( * ):real->real->real` `c + d` p, sub `(t - s) * BB`))
        SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`c pow 2 + s pow 2 = &1`; `d pow 2 + t pow 2 = &1`] THEN
        CONV_TAC REAL_RING;
        ASM_REWRITE_TAC[]]) g));;

(* Lean: g_upper *)
let CWMMB_G_UPPER = prove
 (`forall c s. c977cc_normal c s /\ s <= &3 / &5 ==> cwmmb_g c s <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  REWRITE_TAC[CWMMB_G_DEF; CWMMB_BOUNDARY_DEF] THEN
  NLIN_FACTS_TAC [] [`&0 <= (&1 - c) * (&1 - s - (&43 / &500) * (&1 + c))`] THEN
  CWMMB_CLEAR_TAC [`c:real`,`ic:real`] `c pow 2` THEN
  NLIN_TAC ~deg2:false [CWMMB_EQ_HINT `&1` (ASSUME `c pow 2 + s pow 2 = &1`)]);;

(* Lean: endpoint_gain *)
let CWMMB_ENDPOINT_GAIN = prove
 (`forall d t. c977cc_normal d t /\ t <= &3 / &5 /\ &4 / &5 <= d
         ==> &2 + (&4 / &7) * (&1 - d) pow 2 <= cwmmb_g d t + t + (&1 - t) / d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  let z = `&1 - d` in
  let sub t = subst [z,`zz:real`] t in
  NLIN_FACTS_TAC [] (map sub
   [`&0 <= zz`; `zz <= &1 / &5`; `&0 <= zz * (&10 * d - &8)`]) THEN
  SUBGOAL_THEN (sub `&3 * zz <= t`) ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    NLIN_FACTS_TAC [] (map sub [`&0 < (&3 * zz - t) * (&3 * zz + t)`]) THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG z] (map sub
   [`&0 <= &543 / &500 + &4 / &7 - (&3 + &2 * (&4 / &7)) * (&1 / &5 + zz) +
          (&4 / &7) * ((&1 / &5) pow 2 + (&1 / &5) * zz + zz pow 2)`;
    `&0 <= (&1 / &5 - zz) * (&543 / &500 + &4 / &7 - (&3 + &2 * (&4 / &7)) * (&1 / &5 + zz) +
          (&4 / &7) * ((&1 / &5) pow 2 + (&1 / &5) * zz + zz pow 2))`;
    `(&543 / &500 + &4 / &7) * zz - (&3 + &2 * (&4 / &7)) * zz pow 2 + (&4 / &7) * zz pow 3
       <= &43 / &250`;
    `&0 <= zz * (t - &3 * zz)`;
    `&0 <= &43 / &250 - zz * (&543 / &500 - t + (&4 / &7) * d pow 2)`;
    `&0 <= zz * (&43 / &250 - zz * (&543 / &500 - t + (&4 / &7) * d pow 2))`]) THEN
  REWRITE_TAC[CWMMB_G_DEF; CWMMB_BOUNDARY_DEF] THEN
  CWMMB_CLEAR_TAC [`d:real`,`id:real`] `d pow 2` THEN
  NLIN_TAC ~deg2:false [CWMMB_EQ_HINT `&1` (ASSUME `d pow 2 + t pow 2 = &1`)]);;

(* Lean: norm *)
let CWMMB_NORM = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ s <= t /\
     t <= &3 / &5 /\ &4 / &5 <= d
     ==> (cwmmb_g c s + t + (&1 - t) / d - &3) pow 2 + (&1 - d) pow 2 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWMMB_G_ORDER) THEN
  MP_TAC(SPECL [`d:real`; `t:real`] CWMMB_ENDPOINT_GAIN) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CWMMB_G_UPPER) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `(&1 - t) / d <= &5 / &4` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1 - t`; `&5 / &4`; `d:real`] REAL_LE_LDIV_EQ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) + (&4 / &7) * (&1 - d) pow 2 <= cwmmb_g c s + t + (&1 - t) / d - &3 /\
                cwmmb_g c s + t + (&1 - t) / d - &3 <= &0 /\
                (&1 - d) pow 2 <= &1 / &25` MP_TAC THENL
   [REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    NLIN_TAC [SQ_NONNEG `&1 - d`]; ALL_TAC] THEN
  SPEC_TAC(`cwmmb_g c s + t + (&1 - t) / d - &3`,`P:real`) THEN
  SPEC_TAC(`&1 - d`,`z:real`) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `z:real`]
   [`&0 <= (P - (--(&1) + (&4 / &7) * z pow 2)) * (&1 - (&4 / &7) * z pow 2 - P)`;
    `&0 <= z pow 2 * (&2 * (&4 / &7) - &1 - (&4 / &7) pow 2 * z pow 2)`] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: linear_margin *)
let CWMMB_LINEAR_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ t <= &3 / &5 /\ &4 / &5 <= d
     ==> &0 <= &1 + l * (cwmmb_g c s + t + (&1 - t) / d - &3) - r * (&1 - d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CWMMB_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c977cc_normal l r` THEN REWRITE_TAC[c977cc_normal] THEN STRIP_TAC THEN
  SPEC_TAC(`cwmmb_g c s + t + (&1 - t) / d - &3`,`P:real`) THEN
  SPEC_TAC(`&1 - d`,`z:real`) THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(l * P - r * z) pow 2 + (r * P + l * z) pow 2 = P pow 2 + z pow 2`
    ASSUME_TAC THENL
   [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `r * P + l * z`] [`(l * P - r * z) pow 2 <= &1`] THEN
  NLIN_TAC []);;

(* Lean: low_margin *)
let CWMMB_LOW_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ r <= s /\ t <= &3 / &5 /\ &4 / &5 <= d
     ==> &0 <= &1 + (l / c) * cwmmb_boundary c s + (s * l - c * r) * (l + r) / c +
              r * d + l * t + l / d - &3 * l - l * t / d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `l:real`; `r:real`]
    CWMMB_LINEAR_MARGIN) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `l:real`; `r:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(d = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= c * (s - r)`; `&0 <= s * (l - c)`; `&0 <= s * l - c * r`] THEN
  SUBGOAL_THEN `&0 <= ((s * l - c * r) / c) * (l + r - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + (l / c) * cwmmb_boundary c s + (s * l - c * r) * (l + r) / c +
     r * d + l * t + l / d - &3 * l - l * t / d) -
    (&1 + l * (cwmmb_g c s + t + (&1 - t) / d - &3) - r * (&1 - d)) =
    ((s * l - c * r) / c) * (l + r - &1)` ASSUME_TAC THENL
   [REWRITE_TAC[CWMMB_G_DEF] THEN
    MAP_EVERY UNDISCH_TAC [`~(c = &0)`; `~(d = &0)`] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: high_margin *)
let CWMMB_HIGH_MARGIN = prove
 (`forall c s d t l r. c977cc_normal c s /\ c977cc_normal d t /\ c977cc_normal l r /\
     s <= t /\ s <= r /\ t <= &3 / &5 /\ &4 / &5 <= d
     ==> &0 <= (cwmmb_boundary c s - (c * r - s * l) * ((&457 / &500) * l + r)) /
              (c * l + s * r) +
              &1 + r * d + l * t + l / d - &3 * l - l * t / d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `l:real`; `r:real`]
    CWMMB_LINEAR_MARGIN) THEN
  MP_TAC(SPECL [`d:real`; `t:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN C977CSB_NORMAL_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < c * l`; `&0 <= s * r`; `&0 < c * l + s * r`;
                     `&0 < c * (c * l + s * r)`] THEN
  SUBGOAL_THEN `~(c = &0) /\ ~(d = &0) /\ ~(c * l + s * r = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] [`&0 <= c * (r - s)`; `&0 <= s * (c - l)`; `&0 <= c * r - s * l`] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&1 - c) * (&10 * c - &8)`] THEN
  SUBGOAL_THEN `&3 * (&1 - c) <= s` ASSUME_TAC THENL
   [REFUTE_THEN (ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
    NLIN_FACTS_TAC [] [`&0 < (&3 * (&1 - c) - s) * (&3 * (&1 - c) + s)`] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&2 * s - &1`]
   [`&0 <= (&1 - s) * (s - &3 * (&1 - c))`; `(&1 - c) * (&1 - s) <= &1 / &12`] THEN
  SUBGOAL_THEN `c * cwmmb_boundary c s = c + s - &2 * c * s - (&457 / &500) * s pow 2`
    ASSUME_TAC THENL
   [REWRITE_TAC[CWMMB_BOUNDARY_DEF] THEN UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `v = c - s - cwmmb_boundary c s` THEN
  SUBGOAL_THEN `v <= (&43 / &500) * c` ASSUME_TAC THENL
   [MATCH_MP_TAC CWMMB_LE_BY_POS THEN EXISTS_TAC `c:real` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; EXPAND_TAC "v" THEN NLIN_TAC ~deg2:false
       [CWMMB_EQ_HINT `&1` (ASSUME `c pow 2 + s pow 2 = &1`)]]; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (l - r) * ((&43 / &500) * c)`; `&0 <= r * ((&43 / &500) * c - v)`;
    `&0 <= (&43 / &500) * c * l - r * v`;
    `&0 <= (c * r - s * l) * ((&43 / &500) * c * l - r * v)`] THEN
  SUBGOAL_THEN
   `c * (c * l + s * r) *
    (((cwmmb_boundary c s - (c * r - s * l) * ((&457 / &500) * l + r)) / (c * l + s * r) +
      &1 + r * d + l * t + l / d - &3 * l - l * t / d) -
     (&1 + l * (cwmmb_g c s + t + (&1 - t) / d - &3) - r * (&1 - d))) =
    (c - l * (c * l + s * r)) * cwmmb_boundary c s +
    (c * r - s * l) * ((c * l + s * r) - c * ((&457 / &500) * l + r))` ASSUME_TAC THENL
   [REWRITE_TAC[CWMMB_G_DEF] THEN
    MAP_EVERY UNDISCH_TAC [`~(c = &0)`; `~(d = &0)`; `~(c * l + s * r = &0)`] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  NLIN_FACTS_TAC []
   [`&0 <= (c * (c * l + s * r)) *
           (&1 + l * (cwmmb_g c s + t + (&1 - t) / d - &3) - r * (&1 - d))`] THEN
  MATCH_MP_TAC CWMMB_POS_CANCEL THEN EXISTS_TAC `c * (c * l + s * r)` THEN
  ASM_REWRITE_TAC[] THEN
  NLIN_TAC ~deg2:false
   [CWMMB_EQ_HINT `cwmmb_boundary c s * c` (ASSUME `l pow 2 + r pow 2 = &1`);
    CWMMB_EQ_HINT `(c * r - s * l) * r` (ASSUME `c - s - cwmmb_boundary c s = v`)]);;
