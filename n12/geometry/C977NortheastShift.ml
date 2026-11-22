(* ========================================================================= *)
(* Port of Compact/Bridge/C977NortheastShift.lean                            *)
(* (N12Compact.C977NortheastShift; Lean header: "Source-only").  All-angle   *)
(* original northeast-corner ending.  Conventions of C977NortheastFarther.ml *)
(* / C977NextBottomWall.ml: p.square (orderedOwner p i) is c977wc_sq i; the  *)
(* family q is qc qs qu qv qa with C977CI_QHYP; Normal c t is c977cc_normal;  *)
(* transposePacking p is (c2, c1, b, a, l) (SwapReduction.ml); swapFrame A   *)
(* is (c, --s, v, u, a) (CCPI_INSIDE_SWAPFRAME); the private ownerSwap is    *)
(* c977nes_swap (a list), transpose_owner is C977NES_TRANSPOSE_OWNER; the    *)
(* transported family Q i = swapFrame (q (ownerSwap i)) is the five lambda   *)
(* terms c977nes_Q (C977NES_TRANSPOSE_QHYP).  Tag C977NES_.                  *)
(* ========================================================================= *)

needs "n12/geometry/C977NortheastFarther.ml";;
needs "n12/geometry/UpperRightNegativeCornerPositiveTop.ml";;
needs "n12/geometry/SwapReduction.ml";;
needs "n12/geometry/CentralCenterPairIncoming.ml";;
needs "n12/geometry/C977NextBottomWall.ml";;

(* Lean: ownerSwap (private) *)
let c977nes_swap = new_definition `c977nes_swap = [1;0;4;3;2;5;7;6;9;8;11;10]`;;
let C977NES_SWAP_LIST = [1;0;4;3;2;5;7;6;9;8;11;10];;

let c977nes_enum_tac v n =
  let tm = list_mk_disj (map (fun k -> mk_eq(v, mk_small_numeral k)) (0--(n-1))) in
  SUBGOAL_THEN tm MP_TAC THENL
  [UNDISCH_TAC (mk_binop `(<):num->num->bool` v (mk_small_numeral n)) THEN ARITH_TAC;
   DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)];;

let C977NES_SWAP_LT = prove
 (`forall i. i < 12 ==> EL i c977nes_swap < 12`,
  GEN_TAC THEN DISCH_TAC THEN c977nes_enum_tac `i:num` 12 THEN
  REWRITE_TAC[c977nes_swap] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN ARITH_TAC);;

let C977NES_V5 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C977NES_V5T = [`c2:num->real`; `c1:num->real`; `b:num->real`; `a:num->real`; `l:real`];;
let C977NES_QV = [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

(* transpose_owner at a literal index, as C977NBW_TRANSPOSED_WALL_OWNER *)
let c977nes_owner i =
  let j = List.nth C977NES_SWAP_LIST i in
  let mi = List.nth C977SR_FAMILY_LIST j in
  prove
   (subst [mk_small_numeral i, `ii:num`; mk_small_numeral j, `jj:num`]
     `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
       ==> c977av_ordered_owner c2 c1 b a l ii = c977av_ordered_owner c1 c2 a b l jj`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP C977SR_TRANSPOSE_FAMILY (C977CI_HYPS ())) THEN STRIP_TAC THEN
    MATCH_MP_TAC OWNMASK_INJ THEN
    MAP_EVERY EXISTS_TAC C977NES_V5T THEN
    REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM c977av_ordered_owner] THEN
    GEN_REWRITE_TAC RAND_CONV [C977SR_CODE_RAW] THEN
    MP_TAC(SPECL (C977NES_V5 @ [mk_small_numeral j]) C977AV_ORDERED_OWNER_CODE) THEN
    MP_TAC(SPECL (C977NES_V5T @ [mk_small_numeral i]) C977AV_ORDERED_OWNER_CODE) THEN
    ASM_REWRITE_TAC[ARITH; C977AV_CODE_EL.(i); C977AV_CODE_EL.(j)] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[C977SR_TRANSPOSE_DIAGONAL; c981cr_diag_mask mi]);;

let C977NES_OWNERS = map c977nes_owner (0--11);;

(* Lean: transpose_owner (private) *)
let C977NES_TRANSPOSE_OWNER = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12
     ==> c977av_ordered_owner c2 c1 b a l i = c977av_ordered_owner c1 c2 a b l (EL i c977nes_swap)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN c977nes_enum_tac `i:num` 12 THEN
  REWRITE_TAC[c977nes_swap] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC C977NES_OWNERS);;

(* Lean: swapFrame / inside_swapFrame (private) *)
let C977NES_INSIDE_SWAPFRAME = CCPI_INSIDE_SWAPFRAME;;

(* Q i = swapFrame (q (ownerSwap i)) *)
let c977nes_Q =
  [`\i. (qc:num->real) (EL i c977nes_swap)`; `\i. --((qs:num->real) (EL i c977nes_swap))`;
   `\i. (qv:num->real) (EL i c977nes_swap)`; `\i. (qu:num->real) (EL i c977nes_swap)`;
   `\i. (qa:num->real) (EL i c977nes_swap)`];;

let C977NES_QHYP = parse_term C977CI_QHYP;;
let C977NES_QHYP_T =
  vsubst (zip (C977NES_V5T @ c977nes_Q) (C977NES_V5 @ C977NES_QV)) C977NES_QHYP;;

let C977NES_UNIT_FA =
  `forall i. i < 12 ==> (qc:num->real) i * qc i + (qs:num->real) i * qs i = &1 /\ &0 < (qa:num->real) i`;;
let C977NES_SIDE_FA = `forall i. i < 12 ==> (qa:num->real) i = l`;;

(* the transported family satisfies the hypotheses for transposePacking p *)
let C977NES_TRANSPOSE_QHYP = prove
 (list_mk_forall(C977NES_V5 @ C977NES_QV, mk_imp(C977NES_QHYP, C977NES_QHYP_T)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP C977SR_TRANSPOSE_FAMILY (C977CI_HYPS ())) THEN STRIP_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(MATCH_MP (ASSUME C977NES_UNIT_FA) (MATCH_MP C977NES_SWAP_LT (ASSUME `i < 12`))) THEN
    SIMP_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC (ASSUME C977NES_SIDE_FA) THEN ASM_SIMP_TAC[C977NES_SWAP_LT];
    MAP_EVERY X_GEN_TAC [`i:num`; `x:real`; `y:real`] THEN DISCH_TAC THEN
    MP_TAC(SPECL (C977NES_V5 @ [`i:num`]) C977NES_TRANSPOSE_OWNER) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[C977NES_INSIDE_SWAPFRAME; C977SR_TRANSPOSE_INSIDE] THEN
    FIRST_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
      then MP_TAC(SPECL [`EL i c977nes_swap`; `y:real`; `x:real`] th) else NO_TAC) THEN
    ASM_SIMP_TAC[C977NES_SWAP_LT]]);;

let C977NES_HYP () = CONJ (ASSUME `NPACK c1 c2 a b l`)
  (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`);;

let C977NES_EL_TAC =
  REWRITE_TAC[c977nes_swap] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV);;

(* side conditions: assumptions, literal index bounds, Normal / abs arithmetic *)
let C977NES_SIDE_TAC =
  FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ARITH] THEN NO_TAC;
    REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_ABS_NEG] THEN C977NES_EL_TAC THEN
    RASM_ARITH_TAC];;

let c977nes_use th tms =
  MP_TAC(SPECL tms th) THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN C977NES_SIDE_TAC; DISCH_TAC];;

let c977nes_apply th tms =
  MATCH_MP_TAC (SPECL tms th) THEN REPEAT CONJ_TAC THEN C977NES_SIDE_TAC;;

let C977NES_START_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  C977CI_INST_TAC [3; 10; 11];;

let c977nes_q i = c977ci_qt i;;
let c977nes_sw i = match c977ci_qt i with
  [c; s; u; v; a] -> [c; mk_comb(`(--):real->real`, s); v; u; a] | _ -> failwith "sw";;

(* the transposed squares 3 and 11 are swapFrame (q 3) and swapFrame (q 10) *)
let C977NES_TIFF i =
  let j = List.nth C977NES_SWAP_LIST i in
  let th = SPECL (C977NES_V5 @ C977NES_QV) C977NES_TRANSPOSE_QHYP in
  let th1 = UNDISCH th in
  let fa = find (fun t -> is_forall t && length (fst (strip_forall t)) = 3) (conjuncts (concl th1)) in
  let th2 = SPEC (mk_small_numeral i) (find (fun c -> concl c = fa) (CONJUNCTS th1)) in
  let th3 = CONV_RULE (REWRITE_CONV[ARITH] THENC DEPTH_CONV BETA_CONV THENC
                       REWRITE_CONV[c977nes_swap] THENC ONCE_DEPTH_CONV EL_CONV) th2 in
  ignore j; DISCH_ALL th3;;

let C977NES_TIFF3 = C977NES_TIFF 3;;
let C977NES_TIFF11 = C977NES_TIFF 11;;

let C977NES_TRANSPOSED_TAC =
  MP_TAC(MATCH_MP C977SR_TRANSPOSE_FAMILY (C977NES_HYP ())) THEN STRIP_TAC THEN
  MP_TAC C977NES_TIFF3 THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC C977NES_TIFF11 THEN ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC];;

(* Lean: frame_point *)
let C977NES_FRAME_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 3) (--(qs 3)) /\\ abs (qs 10) <= qc 10
      ==> linside %s (&3) (&7 / &2)" C977CI_QHYP (c977ci_q 3)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [3; 10] THEN
  C977NES_TRANSPOSED_TAC THEN
  ONCE_REWRITE_TAC[GSYM C977NES_INSIDE_SWAPFRAME] THEN
  c977nes_apply C977NEF_FRAME_POINT (C977NES_V5T @ c977nes_sw 3 @ c977nes_sw 10));;

(* Lean: positive_top_frame_point *)
let C977NES_POSITIVE_TOP_FRAME_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 3) <= qc 3 /\\ abs (qs 10) <= qc 10 /\\ c977cc_normal (qc 11) (qs 11)
      ==> linside %s (&7 / &2) (&3)" C977CI_QHYP (c977ci_q 3)),
  C977NES_START_TAC THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 3` THENL
   [c977nes_apply C977NEF_FRAME_POINT (C977NES_V5 @ c977nes_q 3 @ c977nes_q 11);
    c977nes_use C977NES_FRAME_POINT (C977NES_V5 @ C977NES_QV) THEN
    c977nes_apply C977NEF_NEGATIVE_FRAME_POINT (C977NES_V5 @ c977nes_q 3 @ c977nes_q 11)]);;

(* Lean: positive_top_right_shift_excludes *)
let C977NES_POSITIVE_TOP_RIGHT_SHIFT_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 3) <= qc 3 /\\ c977cc_normal (qc 10) (qs 10) /\\ c977cc_normal (qc 11) (qs 11) /\\
      &3 * qc 10 + &2 * qs 10 <= qu 10
      ==> F" C977CI_QHYP),
  C977NES_START_TAC THEN
  c977nes_use C977NES_POSITIVE_TOP_FRAME_POINT (C977NES_V5 @ C977NES_QV) THEN
  c977nes_apply C977NEF_RIGHT_SHIFT_OF_FARTHER (C977NES_V5 @ C977NES_QV));;

(* Lean: negative_positive_point *)
let C977NES_NEGATIVE_POSITIVE_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 3) (--(qs 3)) /\\ abs (qs 10) <= qc 10 /\\ c977cc_normal (qc 11) (qs 11)
      ==> linside %s (&7 / &2) (&3)" C977CI_QHYP (c977ci_q 3)),
  C977NES_START_TAC THEN
  c977nes_use C977NES_FRAME_POINT (C977NES_V5 @ C977NES_QV) THEN
  c977nes_apply C977NEF_NEGATIVE_FRAME_POINT (C977NES_V5 @ c977nes_q 3 @ c977nes_q 11));;

(* Lean: all_frame_point *)
let C977NES_ALL_FRAME_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 3) <= qc 3 /\\ abs (qs 10) <= qc 10 /\\ abs (qs 11) <= qc 11
      ==> linside %s (&7 / &2) (&3)" C977CI_QHYP (c977ci_q 3)),
  C977NES_START_TAC THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 3` THENL
   [c977nes_apply C977NEF_FRAME_POINT (C977NES_V5 @ c977nes_q 3 @ c977nes_q 11);
    c977nes_use C977NES_FRAME_POINT (C977NES_V5 @ C977NES_QV) THEN
    ASM_CASES_TAC `&0 <= (qs:num->real) 11` THENL
     [c977nes_apply C977NEF_NEGATIVE_FRAME_POINT (C977NES_V5 @ c977nes_q 3 @ c977nes_q 11);
      c977nes_apply C977NEF_NEGATIVE_PAIR_FRAME_POINT (C977NES_V5 @ c977nes_q 3 @ c977nes_q 11)]]);;

(* Lean: right_shift_excludes *)
let C977NES_RIGHT_SHIFT_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 3) <= qc 3 /\\ abs (qs 11) <= qc 11 /\\ c977cc_normal (qc 10) (qs 10) /\\
      &3 * qc 10 + &2 * qs 10 <= qu 10
      ==> F" C977CI_QHYP),
  C977NES_START_TAC THEN
  c977nes_use C977NES_ALL_FRAME_POINT (C977NES_V5 @ C977NES_QV) THEN
  c977nes_apply C977NEF_RIGHT_SHIFT_OF_FARTHER (C977NES_V5 @ C977NES_QV));;

(* the transported family as assumptions *)
let C977NES_QT_TAC =
  MP_TAC(SPECL (C977NES_V5 @ C977NES_QV) C977NES_TRANSPOSE_QHYP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

(* Lean: all_top_shift_excludes *)
let C977NES_ALL_TOP_SHIFT_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 3) <= qc 3 /\\ abs (qs 10) <= qc 10 /\\ c977cc_normal (qc 11) (--(qs 11)) /\\
      &3 * qc 11 - &2 * qs 11 <= qv 11
      ==> F" C977CI_QHYP),
  C977NES_START_TAC THEN C977NES_QT_TAC THEN
  c977nes_apply C977NES_RIGHT_SHIFT_EXCLUDES (C977NES_V5T @ c977nes_Q));;

(* Lean: right_shift_negative_signs *)
let C977NES_RIGHT_SHIFT_NEGATIVE_SIGNS = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 3) <= qc 3 /\\ abs (qs 11) <= qc 11 /\\ c977cc_normal (qc 10) (qs 10) /\\
      &3 * qc 10 + &2 * qs 10 <= qu 10
      ==> qs 3 < &0 /\\ qs 11 < &0" C977CI_QHYP),
  C977NES_START_TAC THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 3` THENL
   [MATCH_MP_TAC(TAUT `false ==> p`) THEN
    c977nes_apply C977NEF_RIGHT_SHIFT_EXCLUDES (C977NES_V5 @ C977NES_QV);
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 11` THENL
   [MATCH_MP_TAC(TAUT `false ==> p`) THEN
    c977nes_use C977NES_NEGATIVE_POSITIVE_POINT (C977NES_V5 @ C977NES_QV) THEN
    c977nes_apply C977NEF_RIGHT_SHIFT_OF_FARTHER (C977NES_V5 @ C977NES_QV);
    RASM_ARITH_TAC]);;

(* Lean: top_shift_excludes *)
let C977NES_TOP_SHIFT_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 3) (--(qs 3)) /\\ abs (qs 10) <= qc 10 /\\
      c977cc_normal (qc 11) (--(qs 11)) /\\ &3 * qc 11 - &2 * qs 11 <= qv 11
      ==> F" C977CI_QHYP),
  C977NES_START_TAC THEN C977NES_QT_TAC THEN
  c977nes_apply C977NEF_RIGHT_SHIFT_EXCLUDES (C977NES_V5T @ c977nes_Q));;

(* Lean: simultaneous_excludes *)
let C977NES_SIMULTANEOUS_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 3) <= qc 3 /\\ abs (qs 10) <= qc 10 /\\ abs (qs 11) <= qc 11 /\\
      (&0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 <= qu 10) /\\
      (qs 11 <= &0 /\\ &3 * qc 11 - &2 * qs 11 <= qv 11)
      ==> F" C977CI_QHYP),
  C977NES_START_TAC THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 3` THENL
   [c977nes_apply C977NEF_RIGHT_SHIFT_EXCLUDES (C977NES_V5 @ C977NES_QV);
    c977nes_apply C977NES_TOP_SHIFT_EXCLUDES (C977NES_V5 @ C977NES_QV)]);;
