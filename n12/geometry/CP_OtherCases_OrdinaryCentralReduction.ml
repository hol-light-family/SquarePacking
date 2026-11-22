(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryCentralReduction.lean       *)
(* (N12Compact.Completion.OtherCases.OrdinaryCentralReduction).  Theorem 1  *)
(* of C1092-MPPM-ORDINARY-CENTRAL-REDUCTION in the original packing.        *)
(* Conventions of CP_C1092_MPPMEntrance.ml: owners p i is the owner 5-tuple  *)
(* at mask EL i c1092wc_code (c1092mppe_in i x y), hf is C1092AE_HYP,        *)
(* WallContext p mppm is c1092wc_ctx c1 c2 a b l c1092mppe_mppm.             *)
(* The private charts leftChart / bottomChart / rightChart / topChart are   *)
(* explicit 5-tuples with the Lean `*_actual` characterisations             *)
(* (C1092OCR_LEFT_ACTUAL etc.); foreign_bar_impossible is                   *)
(* OCOCRG_FOREIGN_BAR_IMPOSSIBLE, inside_segment CES_INSIDE_SEGMENT,         *)
(* corner_points C1092WC_CORNER_POINTS, owners_markers via c1092mppe_marker, *)
(* owners_disjoint C1092WC_OWNERS_DISJOINT, wall_auxiliaries                 *)
(* C1092MPPE_WALL_AUXILIARIES.  Tag C1092OCR_.                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_OrdinaryCentralReductionGeometry.ml";;
needs "n12/geometry/CP_C1092_MPPMEntrance.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: side_gt (private) *)
let C1092OCR_SIDE_GT = C1092MPPE_SIDE_GT;;

(* Lean: leftChart, bottomChart, rightChart, topChart (private), as tuples *)
let C1092OCR_CHARTS =
  [`c:real`, `s:real`, `u - c - s`, `v - c + s`;
   `s:real`, `--c`, `u - &3 * c - s`, `v - c + &3 * s`;
   `--c`, `--s`, `u - &3 * c - &3 * s`, `v + &3 * s - &3 * c`;
   `--s`, `c:real`, `u - c - &3 * s`, `v + s - &3 * c`];;

let c1092ocr_chart k q =
  let (c', s', u', v') = el k C1092OCR_CHARTS in
  let th = zip q [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] in
  map (vsubst th) [c'; s'; u'; v'; `a:real`];;

(* Lean: left_actual, bottom_actual, right_actual, top_actual (private) *)
let C1092OCR_ACTUALS =
  let q0 = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] in
  map2 (fun k (x, y) ->
    let t = c1092ocr_chart k q0 in
    prove(list_mk_forall(q0 @ [`x:real`; `y:real`],
            mk_iff(list_mk_comb(`linside`, t @ [`x:real`; `y:real`]),
                   list_mk_comb(`linside`, q0 @ [x; y]))),
          REWRITE_TAC[linside] THEN REAL_ARITH_TAC))
   (0--3) [`&1 + x`, `&1 + y`; `&3 - y`, `&1 + x`; `&3 - x`, `&3 - y`; `&1 + y`, `&3 - x`];;
let [C1092OCR_LEFT_ACTUAL; C1092OCR_BOTTOM_ACTUAL; C1092OCR_RIGHT_ACTUAL; C1092OCR_TOP_ACTUAL] =
  C1092OCR_ACTUALS;;

(* the charts keep unit normals and disjointness *)
let C1092OCR_UNITS =
  let q0 = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] in
  map (fun k -> let t = c1092ocr_chart k q0 in
    prove(mk_forall(`c:real`, mk_forall(`s:real`, mk_imp(`c * c + s * s = &1`,
            mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (el 0 t) (el 0 t))
                    (mk_binop `( * ):real->real->real` (el 1 t) (el 1 t)), `&1`)))),
          REAL_ARITH_TAC)) (0--3);;

let C1092OCR_DISJS =
  let q0 = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
  and q1 = [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] in
  map2 (fun k act ->
    prove(list_mk_forall(q0 @ q1, mk_imp(list_mk_comb(`ldisj`, q0 @ q1),
            list_mk_comb(`ldisj`, c1092ocr_chart k q0 @ c1092ocr_chart k q1))),
          REWRITE_TAC[ldisj; act] THEN MESON_TAC[])) (0--3) C1092OCR_ACTUALS;;

let c1092ocr_own i = map (fun f -> mk_comb(f, mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral i),
                                                       `c1092wc_code`)))
  [`ooc c1 c2 a b l`; `oos c1 c2 a b l`; `oou c1 c2 a b l`; `oov c1 c2 a b l`] @ [`l:real`];;

let C1092OCR_H = parse_term ("(" ^ C1092AE_HYP ^ ") /\\ " ^ C1092MPPE_CTX);;

(* Theorem shared by the four statements: chart k, central owner ci, wall owner wi,
   corner index kc, segment owner si from (sx0, sy0) (hypothesis) to the wall auxiliary
   (sx1, sy1); central hypothesis point (cx, cy); markers (central mk_c at pc, wall mk_w at pw);
   conclusion ~ wall owner at the inner point (ix, iy). *)
let c1092ocr_case k ci wi kc si (sx0, sy0) (sx1, sy1) (cx, cy) (codec, mkc, pc) (codew, mkw, pw) (ix, iy) =
  let inn i (x, y) = parse_term (c1092mppe_in i x y) in
  let tm str = parse_term str in
  let hseg = inn si (sx0, sy0) and hcen = inn ci (cx, cy) and inner = inn wi (ix, iy) in
  let stmt = parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ %s ==> ~%s" C1092AE_P C1092AE_HYP
               C1092MPPE_CTX (c1092mppe_in si sx0 sy0) (c1092mppe_in ci cx cy) (c1092mppe_in wi ix iy)) in
  let hall = ASSUME C1092OCR_H in
  let hh = CONJUNCT1 hall in
  let np = CONJUNCT1 hh in
  let v = C1092MMEN_V in
  let walls = MP (SPECL v C1092MPPE_WALL_AUXILIARIES) (CONJ np (CONJUNCT2 hall)) in
  let wallpt = find (fun th -> concl th = inn si (sx1, sy1)) (CONJUNCTS walls) in
  let seg = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (MP (SPECL (c1092ocr_own si @ [tm sx0; tm sy0; tm sx1; tm sy1; `&5 / &14`]) CES_INSIDE_SEGMENT)
        (end_itlist CONJ [ASSUME hseg; wallpt; REAL_ARITH `&0 <= &5 / &14`; REAL_ARITH `&5 / &14 <= &1`])) in
  let marker i code mk (x, y) = MP (SPEC_ALL (c1092mppe_marker i code mk x y)) hh in
  let corner = prove(mk_imp(C1092OCR_H, inn kc (List.nth ["&1","&1"; "&3","&1"; "&3","&3"; "&1","&3"] kc)),
    STRIP_TAC THEN
    MP_TAC(SPECL (v @ [mk_small_numeral kc]) C1092WC_CORNER_POINTS) THEN ASM_REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[c1092wc_corner; c1092wc_cpoint] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[FST; SND]) in
  let corner = MP corner hall in
  let disj i j = MP (SPECL (v @ [mk_small_numeral i; mk_small_numeral j]) C1092WC_OWNERS_DISJOINT)
    (end_itlist CONJ [CONJUNCT1 hh; CONJUNCT2 hh; EQT_ELIM (NUM_REDUCE_CONV (tm (Printf.sprintf "%d < 12" i)));
                      EQT_ELIM (NUM_REDUCE_CONV (tm (Printf.sprintf "%d < 12" j)));
                      EQF_ELIM (NUM_REDUCE_CONV (tm (Printf.sprintf "%d = %d" i j)))]) in
  let excl i j pt =
    let d = REWRITE_RULE[ldisj] (disj i j) in
    let args = snd (strip_comb (concl pt)) in
    let d2 = SPECL [el 5 args; el 6 args] d in
    let a = lhand (rand (concl d2)) in
    NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) pt))) in
  let qc = c1092ocr_own ci and qw = c1092ocr_own wi in
  let unit = MP (SPECL [el 0 qc; el 1 qc] (el k C1092OCR_UNITS))
                (SPECL (v @ [mk_comb(mk_comb(`EL:num->num list->num`, mk_small_numeral ci), `c1092wc_code`)]) OO_UNIT |> fun th -> MP th np) in
  let side = MP (SPECL v C1092MPPE_SIDE_GT) np in
  let cdisj = MP (SPECL (qc @ qw) (el k C1092OCR_DISJS)) (disj ci wi) in
  let facts = [unit; side; cdisj; ASSUME hcen; marker ci codec mkc pc; excl ci kc corner; excl ci si seg;
               marker wi codew mkw pw; ASSUME inner] in
  let conv = REWRITE_CONV[el k C1092OCR_ACTUALS] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let nf = map (CONV_RULE conv) facts in
  let spec = SPECL (c1092ocr_chart k qc @ c1092ocr_chart k qw) OCOCRG_FOREIGN_BAR_IMPOSSIBLE in
  let pa t =
    try find (fun f -> aconv (concl f) t) facts with Failure _ ->
    let eq = conv t in
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) (rhs (concl eq))) nf)
    with Failure _ -> failwith ("c1092ocr_case: " ^ string_of_term t) in
  let f = MP spec (end_itlist CONJ (map pa (conjuncts (lhand (concl spec))))) in
  let th = NOT_INTRO (DISCH inner f) in
  let hyp = parse_term C1092AE_HYP and ctx = parse_term C1092MPPE_CTX in
  let th = PROVE_HYP (CONJ (CONJ (ASSUME (lhand hyp)) (ASSUME (rand hyp))) (ASSUME ctx)) th in
  prove(stmt, REPEAT GEN_TAC THEN STRIP_TAC THEN ACCEPT_TAC th);;

(* Lean: left_inner_absent *)
let C1092OCR_LEFT_INNER_ABSENT = c1092ocr_case 0 4 8 0 9 ("&8 / &5", "&1") ("&87 / &50", "&1")
  ("&1", "&87 / &50") (256, 8, ("&33 / &20", "&33 / &20")) (4096, 12, ("&457 / &500", "&2"))
  ("&87 / &50", "&2");;

(* Lean: bottom_inner_absent *)
let C1092OCR_BOTTOM_INNER_ABSENT = c1092ocr_case 1 5 9 1 10 ("&3", "&8 / &5") ("&3", "&87 / &50")
  ("&113 / &50", "&1") (512, 9, ("&47 / &20", "&33 / &20")) (8192, 13, ("&2", "&457 / &500"))
  ("&2", "&87 / &50");;

(* Lean: right_inner_absent *)
let C1092OCR_RIGHT_INNER_ABSENT = c1092ocr_case 2 6 10 2 11 ("&12 / &5", "&3") ("&113 / &50", "&3")
  ("&3", "&113 / &50") (1024, 10, ("&47 / &20", "&47 / &20")) (16384, 14, ("&1543 / &500", "&2"))
  ("&113 / &50", "&2");;

(* Lean: top_inner_absent *)
let C1092OCR_TOP_INNER_ABSENT = c1092ocr_case 3 7 11 3 8 ("&1", "&12 / &5") ("&1", "&113 / &50")
  ("&87 / &50", "&3") (2048, 11, ("&33 / &20", "&47 / &20")) (32768, 15, ("&2", "&1543 / &500"))
  ("&2", "&113 / &50");;
