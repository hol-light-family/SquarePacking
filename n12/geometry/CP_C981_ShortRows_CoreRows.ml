(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShortRows/CoreRows.lean                   *)
(* (N12Compact.C981CompletionShortRows).  Whole original row 101.            *)
(* ExcludesVector = c981vd_excludes_vector, representativeVectors =          *)
(* c981vd_representative_vectors (VectorData).  insidePoints / outsidePoints *)
(* are the OCaml lists c981srcr_inside / c981srcr_outside; `Check v` and     *)
(* `excludes v checked` are the producer c981srcr_excludes V (literal V): it *)
(* builds every point with c981br_in / c981br_out (Bridge_C981Row27.ml),     *)
(* which fail exactly when a point is not in queryInsidePoints /             *)
(* queryOutsidePoints, and returns |- c981vd_excludes_vector V.              *)
(* owners p i = owner of mask EL i c981ow_masks.  swapFrame A =              *)
(* (cA, --sA, vA, uA, aA) (C981SRCR_INSIDE_SWAPFRAME); canonical_frame =     *)
(* CLF_CANONICAL_FRAME; C981CompletionWallAdvance.point = C981WA_POINT;      *)
(* C981CompletionShortSqueeze.impossible = C981SQ_IMPOSSIBLE; Normal =       *)
(* c977cc_normal.  Tag C981SRCR_.                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_ShortRows_CoreSqueeze.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: insidePoints *)
let c981srcr_inside =
  [0, [(`&187 / &100`, `&19 / &25`)];
   1, [(`&19 / &25`, `&187 / &100`)];
   2, [(`&3`, `&1`)];
   4, [(`&1`, `&3`)];
   5, [(`&47 / &20`, `&33 / &20`); (`&3`, `&87 / &50`)];
   6, [(`&47 / &20`, `&47 / &20`); (`&87 / &50`, `&2`); (`&2`, `&87 / &50`)];
   7, [(`&33 / &20`, `&47 / &20`); (`&87 / &50`, `&3`)];
   8, [(`&457 / &500`, `&2`); (`&1`, `&12 / &5`)];
   9, [(`&2`, `&457 / &500`); (`&12 / &5`, `&1`)]];;

(* Lean: outsidePoints *)
let c981srcr_outside =
  [6, [(`&33 / &20`, `&47 / &20`); (`&47 / &20`, `&33 / &20`)];
   8, [(`&1`, `&87 / &50`)];
   9, [(`&87 / &50`, `&1`)]];;

(* swapFrame / inside_swapFrame (private) *)
let C981SRCR_INSIDE_SWAPFRAME = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: Check, excludes *)
let c981srcr_excludes vtm =
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let ins = List.concat (map (fun (i, ps) -> map (fun p -> (i, p, MP (SPEC_ALL (c981br_in vtm i p)) h)) ps)
                          c981srcr_inside) in
  let outs = List.concat (map (fun (i, ps) -> map (fun p -> MP (SPEC_ALL (c981br_out vtm i p)) h) ps)
                           c981srcr_outside) in
  let pin i p = let (_, _, th) = find (fun (j, q, _) -> j = i && q = p) ins in th in
  let apart i j = MP (SPEC_ALL (c981br_apart vtm i j)) h in
  let excl i j th =
    let x = rand (rator (concl th)) and y = rand (concl th) in
    REWRITE_RULE[th] (SPECL [x; y] (REWRITE_RULE[ldisj] (apart i j))) in
  let mt i = mk_small_numeral (c981br_mask i) in
  let unit i = SPEC (mt i) (MATCH_MP OO_UNIT np) and box i = SPEC (mt i) (MATCH_MP OO_BOX np) in
  let side = MATCH_MP OO_SIDE np in
  let apply lemma bx i ths =
    let tuple = snd (strip_comb (concl bx)) in
    let th = CONV_RULE (REWRITE_CONV[LINSIDE_PULLSW] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
               (SPECL tuple lemma) in
    MP th (TAC_PROOF(([], lhand (concl th)), REPEAT CONJ_TAC THEN
      FIRST [FIRST (map ACCEPT_TAC (bx :: ths)); MP_TAC (unit i) THEN REAL_ARITH_TAC;
             MP_TAC side THEN REAL_ARITH_TAC])) in
  let leftFar = apply C981WA_POINT (box 8) 8
    [pin 8 (`&457 / &500`, `&2`); pin 8 (`&1`, `&12 / &5`); el 2 outs;
     excl 8 1 (pin 1 (`&19 / &25`, `&187 / &100`)); excl 8 7 (pin 7 (`&33 / &20`, `&47 / &20`))] in
  let bottomFar = apply C981WA_POINT (MATCH_MP LCONT_PULLSW (box 9)) 9
    [pin 9 (`&2`, `&457 / &500`); pin 9 (`&12 / &5`, `&1`); el 3 outs;
     excl 9 0 (pin 0 (`&187 / &100`, `&19 / &25`)); excl 9 5 (pin 5 (`&47 / &20`, `&33 / &20`))] in
  let facts = [leftFar; bottomFar; side; unit 5; unit 6; unit 7;
               pin 6 (`&47 / &20`, `&47 / &20`); pin 6 (`&87 / &50`, `&2`); pin 6 (`&2`, `&87 / &50`);
               el 0 outs; el 1 outs;
               pin 5 (`&47 / &20`, `&33 / &20`); pin 5 (`&3`, `&87 / &50`);
               excl 5 2 (pin 2 (`&3`, `&1`)); excl 5 9 bottomFar;
               pin 7 (`&33 / &20`, `&47 / &20`); pin 7 (`&87 / &50`, `&3`);
               excl 7 4 (pin 4 (`&1`, `&3`)); excl 7 8 leftFar;
               REWRITE_RULE[ldisj] (apart 6 5); REWRITE_RULE[ldisj] (apart 6 7)] in
  let frame tuple names =
    MP_TAC(SPECL tuple CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> let [c; s; u; v; a] = names in
      X_CHOOSE_THEN c (X_CHOOSE_THEN s (X_CHOOSE_THEN u (X_CHOOSE_THEN v
        (X_CHOOSE_THEN a STRIP_ASSUME_TAC)))) th) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) && lhs (concl th) = el 4 names)) in
  let close =
    REWRITE_TAC[ldisj; C981SRCR_INSIDE_SWAPFRAME; LINSIDE_PULLSW] THEN
    ASM_REWRITE_TAC[LINSIDE_PULLSW] THEN REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
           RASM_ARITH_TAC] in
  let o7 = c981br_owner 7 in
  let sw7 = [el 1 o7; el 0 o7; el 2 o7; mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, el 3 o7)) `l:real`; `l:real`] in
  prove(mk_comb(`c981vd_excludes_vector`, vtm),
    REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY ASSUME_TAC facts THEN
    frame (c981br_owner 6) [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
    ASM_CASES_TAC `&0 <= sA` THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THENL
     [frame (c981br_owner 5) [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
      MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `l:real`;
                    `cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`] C981SQ_IMPOSSIBLE) THEN
      ANTS_TAC THENL [close; REWRITE_TAC[]];
      frame sw7 [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
      MP_TAC(SPECL [`cA:real`; `--sA`; `vA:real`; `uA:real`; `l:real`;
                    `cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`] C981SQ_IMPOSSIBLE) THEN
      ANTS_TAC THENL [close; REWRITE_TAC[]]]);;

(* Lean: coveredIds *)
let c981srcr_covered_ids = new_definition
 `c981srcr_covered_ids = [101]`;;

(* Lean: checked *)
let C981SRCR_CHECKED = map (fun i -> c981br_rep_excluded i c981srcr_excludes) [101];;

(* Lean: covered_excluded *)
let C981SRCR_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981srcr_covered_ids] (c981br_covered [101] C981SRCR_CHECKED);;

(* Lean: representative101_excluded *)
let C981SRCR_REPRESENTATIVE101_EXCLUDED = hd C981SRCR_CHECKED;;
