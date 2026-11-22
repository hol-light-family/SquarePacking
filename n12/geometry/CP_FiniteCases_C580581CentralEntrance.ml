(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C580581CentralEntrance.lean        *)
(* (N12Compact.FiniteCases.C580581CentralEntrance).  The two actual central  *)
(* owners: southeast near point, merged inward F5 point, northeast top       *)
(* points and the merged center.  Statements indexed by v : Fin 2 are OCaml  *)
(* arrays of the two theorems (family v = C580E_FAM.(v), bottomMask v =      *)
(* C580E_BOTTOM.(v)).  Private seed_point = oo_seed, foreign = oo_excl,      *)
(* aux_inside = oo_aux_point; C580581Entrance.inside v p hf i = conjunct i   *)
(* of C580E_INSIDE.(v); compulsory = FC580P_COMPULSORY.  SouthwestPoint.point*)
(* / MergedNearPoint.points_original on pullX (owner p m) are CCSWP_POINT /  *)
(* CCMNP_POINTS_ORIGINAL at the LINSIDE_PULLX tuple; MergedLeftCenter.point  *)
(* = FCMLC_POINT.  Tag FC580CE_.                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C580581Points.ml";;
needs "n12/geometry/CP_CommonCases_SouthwestPoint.ml";;
needs "n12/geometry/CP_CommonCases_MergedNearPoint.ml";;
needs "n12/geometry/CP_FiniteCases_MergedLeftCenter.ml";;

let FC580CE_VARS = FC580P_VARS;;

let fc580ce_hyp v = c580e_hyp v;;
let fc580ce_np v = CONJUNCT1 (ASSUME (fc580ce_hyp v));;
let fc580ce_gen v th = GENL FC580CE_VARS (DISCH (fc580ce_hyp v) th);;
let fc580ce_inst v uth = MP (SPECL FC580CE_VARS uth) (ASSUME (fc580ce_hyp v));;

let fc580ce_tuple m =
  map (fun f -> list_mk_comb(f, FC580CE_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let fc580ce_own m x y = list_mk_comb(`linside`, fc580ce_tuple m @ [x; y]);;
let fc580ce_stmt v body = list_mk_forall(FC580CE_VARS, mk_imp(fc580ce_hyp v, body));;

(* Lean: seed_point (private) *)
let fc580ce_seed v m p = fc580ce_inst v (oo_inst C580E_FAM.(v) (oo_seed m p));;
(* compulsory: [sw; low; se; bottom; left; south; right; top; north] *)
let fc580ce_comp v i = el i (CONJUNCTS (fc580ce_inst v FC580P_COMPULSORY.(v)));;
(* Lean: aux_inside (private) *)
let fc580ce_auxpt m j mem = EQ_MP (SYM (SPECL (FC580CE_VARS @ [mk_small_numeral m]) (oo_aux_point j))) mem;;
(* C580581Entrance.inside v p hf i, coordinates evaluated *)
let fc580ce_claim v i =
  CONV_RULE (REWRITE_CONV[AUXPTS_EXPL.(1)] THENC ONCE_DEPTH_CONV EL_CONV THENC REWRITE_CONV[VECTOR_2])
    (el i (CONJUNCTS (fc580ce_inst v C580E_INSIDE.(v))));;
(* Lean: foreign (private) *)
let fc580ce_excl v m n thn = fc580ce_inst v (oo_excl C580E_FAM.(v) m n (fc580ce_gen v thn));;
let fc580ce_apart v m n = fc580ce_inst v (oo_apart C580E_FAM.(v) m n);;

let fc580ce_num tm = EQT_ELIM (REAL_RAT_REDUCE_CONV tm);;
let fc580ce_vseg m x y0 y1 y lo hi =
  MP (SPECL (fc580ce_tuple m @ [x; y0; y1; y]) OO_VERTICAL_SEGMENT)
     (end_itlist CONJ [lo; hi; fc580ce_num (mk_binop `(<):real->real->bool` y0 y1);
                       fc580ce_num (mk_binop `(<=):real->real->bool` y0 y);
                       fc580ce_num (mk_binop `(<=):real->real->bool` y y1)]);;
let fc580ce_hseg m x0 x1 y x lo hi =
  MP (SPECL (fc580ce_tuple m @ [x0; x1; y; x]) OO_HORIZONTAL_SEGMENT)
     (end_itlist CONJ [lo; hi; fc580ce_num (mk_binop `(<):real->real->bool` x0 x1);
                       fc580ce_num (mk_binop `(<=):real->real->bool` x0 x);
                       fc580ce_num (mk_binop `(<=):real->real->bool` x x1)]);;

(* discharge the antecedent of a geometry lemma from the given facts, the owner unit
   normal / side and literal arithmetic *)
let fc580ce_discharge v ms th ths =
  let np = fc580ce_np v in
  let units = map (fun m -> MP (SPECL (FC580CE_VARS @ [mk_small_numeral m]) OO_UNIT) np) ms in
  let boxes = map (fun m -> MP (SPECL (FC580CE_VARS @ [mk_small_numeral m]) OO_BOX) np) ms in
  let side = MP (SPECL FC580CE_VARS OO_SIDE) np in
  let ant = lhand (concl th) in
  let close = FIRST [FIRST (map ACCEPT_TAC (ths @ boxes)); REFL_TAC;
                     MAP_EVERY MP_TAC units THEN REAL_ARITH_TAC;
                     MP_TAC side THEN REAL_ARITH_TAC] in
  MP th (TAC_PROOF(([], ant), REPEAT CONJ_TAC THEN close));;

(* a lemma about q applied to pullX (owner m): x -> 4 - x *)
let fc580ce_pullx v m lemma ths =
  let (c, s, u, w, a) = match fc580ce_tuple m with [c; s; u; w; a] -> (c, s, u, w, a) | _ -> failwith "tuple" in
  let c' = mk_comb(`(--):real->real`, c) in
  let u' = mk_binop `(-):real->real->real` u (mk_binop `( * ):real->real->real` `&4` c) in
  let w' = mk_binop `(-):real->real->real`
             (mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, w)) a)
             (mk_binop `( * ):real->real->real` `&4` s) in
  let th = SPECL [c'; s; u'; w'; a] lemma in
  let th = CONV_RULE (REWRITE_CONV[LINSIDE_PULLX] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) th in
  fc580ce_discharge v [m] th ths;;

let fc580ce_prove v body th =
  prove(fc580ce_stmt v body, REPEAT GEN_TAC THEN DISCH_TAC THEN ACCEPT_TAC th);;

(* Lean: southeast_near *)
let FC580CE_SOUTHEAST_NEAR = Array.init 2 (fun v ->
  let bm = C580E_BOTTOM.(v) in
  let mark = fc580ce_seed v 512 (`&47 / &20`, `&33 / &20`) in
  let inward = fc580ce_auxpt 512 4 (fc580ce_comp v 5) in
  let elbow = fc580ce_claim v 6 in
  let cornerLo = fc580ce_seed v 8 (`&3`, `&28 / &25`) in
  let cornerHi = fc580ce_seed v 8 (`&3`, `&87 / &50`) in
  let cornerMid = fc580ce_vseg 8 `&3` `&28 / &25` `&87 / &50` `&33 / &20` cornerLo cornerHi in
  let bottomHi = fc580ce_auxpt bm 6 (fc580ce_comp v 3) in
  let bottomLo = fc580ce_claim v 4 in
  let bottomMid = fc580ce_hseg bm `&113 / &50` `&12 / &5` `&1` `&47 / &20` bottomLo bottomHi in
  let near = fc580ce_pullx v 512 CCSWP_POINT
    [mark; inward; elbow; fc580ce_excl v 512 8 cornerMid; fc580ce_excl v 512 bm bottomLo;
     fc580ce_excl v 512 bm bottomMid; fc580ce_excl v 512 8 cornerHi] in
  fc580ce_prove v (fc580ce_own 512 `&41 / &20` `&39 / &20`) near);;

(* Lean: merged_inward *)
let FC580CE_MERGED_INWARD = Array.init 2 (fun v ->
  let goal = fc580ce_own 2304 `&2` `&113 / &50` in
  let markSW = fc580ce_seed v 2304 (`&33 / &20`, `&33 / &20`) in
  let markNW = fc580ce_seed v 2304 (`&33 / &20`, `&47 / &20`) in
  let inwardSE = fc580ce_auxpt 512 4 (fc580ce_comp v 5) in
  let low = fc580ce_seed v 2 (`&1`, `&87 / &50`) in
  let wallF = fc580ce_auxpt 4096 1 (fc580ce_comp v 4) in
  let wallMarker = fc580ce_seed v 4096 (`&457 / &500`, `&2`) in
  let missing = ASSUME (mk_neg goal) in
  let near = fc580ce_pullx v 2304 CCMNP_POINTS_ORIGINAL
    [markSW; markNW; fc580ce_excl v 2304 512 inwardSE; missing; fc580ce_excl v 2304 2 low;
     fc580ce_excl v 2304 4096 wallF; fc580ce_excl v 2304 4096 wallMarker] in
  let first = CONJUNCT1 near in
  let se = fc580ce_inst v FC580CE_SOUTHEAST_NEAR.(v) in
  let ap = SPECL [`&41 / &20`; `&39 / &20`] (REWRITE_RULE[ldisj] (fc580ce_apart v 2304 512)) in
  let f = MP (NOT_ELIM ap) (CONJ first se) in
  fc580ce_prove v goal (CCONTR goal f));;

(* Lean: northeast_top *)
let FC580CE_NORTHEAST_TOP = Array.init 2 (fun v ->
  let north = fc580ce_comp v 8 in
  let merged = fc580ce_inst v FC580CE_MERGED_INWARD.(v) in
  let no5 = REWRITE_RULE[SPECL (FC580CE_VARS @ [`1024`]) (oo_aux_point 5)]
              (fc580ce_excl v 1024 2304 merged) in
  let seven = REWRITE_RULE[no5] north in
  let th = CONJ (fc580ce_auxpt 1024 7 seven) (fc580ce_claim v 8) in
  fc580ce_prove v (mk_conj(fc580ce_own 1024 `&12 / &5` `&3`, fc580ce_own 1024 `&113 / &50` `&3`)) th);;

(* Lean: merged_center *)
let FC580CE_MERGED_CENTER = Array.init 2 (fun v ->
  let markSW = fc580ce_seed v 2304 (`&33 / &20`, `&33 / &20`) in
  let markNW = fc580ce_seed v 2304 (`&33 / &20`, `&47 / &20`) in
  let low = fc580ce_seed v 2 (`&1`, `&87 / &50`) in
  let high = fc580ce_auxpt 4096 1 (fc580ce_comp v 4) in
  let inward = fc580ce_auxpt 512 4 (fc580ce_comp v 5) in
  let bottom = fc580ce_auxpt 1 2 (fc580ce_comp v 0) in
  let topPoint = fc580ce_auxpt 32768 3 (fc580ce_comp v 7) in
  let wallMarker = fc580ce_seed v 4096 (`&457 / &500`, `&2`) in
  let wallHigh = fc580ce_claim v 5 in
  let th = SPECL (fc580ce_tuple 2304 @ fc580ce_tuple 4096) FCMLC_POINT in
  let th = fc580ce_discharge v [2304; 4096] th
    [markSW; markNW; fc580ce_excl v 2304 2 low; fc580ce_excl v 2304 4096 high;
     fc580ce_excl v 2304 512 inward; fc580ce_excl v 2304 1 bottom;
     fc580ce_excl v 2304 32768 topPoint; wallMarker; wallHigh; fc580ce_apart v 2304 4096] in
  fc580ce_prove v (fc580ce_own 2304 `&2` `&2`) th);;
