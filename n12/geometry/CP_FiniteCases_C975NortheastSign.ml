(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C975NortheastSign.lean             *)
(* (namespace N12Compact.FiniteCases.C975Selection; Lean header: "Source     *)
(* only").  The actual C975 northeast sign and the consequent top angle.     *)
(* owner p m is the 5-tuple (ooc .. m) .. l.  A Lean OpenSquare N (R, W) is  *)
(* cN sN uN vN aN with its unit normal and positive side explicit; `shape`   *)
(* N.side = (owner p m).side is aN = l; `inside` is the stated equivalence.  *)
(* N.translated 2 3 = (c, s, u - (c 2 + s 3), v - (--s 2 + c 3), a)          *)
(* (C975CP_TRANSLATED); turnFrame (c,s,u,v,a) = (--s, c, v, --u - a, a)      *)
(* (C975NS_TURN_INSIDE).  C976NegativeTop.Alternative = cc976f_alternative,  *)
(* angle = C976NTM_ANGLE; C976MergedLeft.mixed_top_advance / top_only_advance *)
(* = OCC976MLTT_MIXED_TOP_ADVANCE / OCC976MLTT_TOP_ONLY_ADVANCE;             *)
(* TopOnlyLeftPoint.point_original = OCTOLP_POINT_ORIGINAL;                  *)
(* C981CompletionCornerAdvance.upper_wall = C981CA_UPPER_WALL;               *)
(* horizontal_segment = OO_HORIZONTAL_SEGMENT.  top_origin = C975TO_TOP_     *)
(* ORIGIN, northeast_selection = C975SEL_NORTHEAST_SELECTION,                *)
(* southeast_g6_point = C975RS_SOUTHEAST_G6_POINT, southeast_east =          *)
(* C975CP_SOUTHEAST_EAST, northeast_upper_sharp = C975RS_NORTHEAST_UPPER_    *)
(* SHARP, right_bar = C975RS_RIGHT_BAR, top_halfpoint_excluded =             *)
(* C975CR_TOP_HALFPOINT_EXCLUDED, C975IncomingCut.top_left / right_high =    *)
(* C975IC_TOP_LEFT / C975IC_RIGHT_HIGH, fixed = C975SS_* seeds.              *)
(* Tag C975NS_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975CornerReduction.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_TopTransfers.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_Main.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;

let C975NS_V5 = C975IC_V5;;
let c975ns_owner = c975ic_owner and c975ns_own = c975ic_own;;
let c975ns_sq nm = map (fun f -> mk_var(f ^ nm, `:real`)) ["c"; "s"; "u"; "v"; "a"];;
let c975ns_lin q x y = list_mk_comb(`linside`, q @ [x; y]);;
let c975ns_unit q = match q with
    c :: s :: _ -> mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                                                         (mk_binop `( * ):real->real->real` s s), `&1`)
  | _ -> failwith "c975ns_unit";;
let c975ns_pos q = mk_binop `(<):real->real->bool` `&0` (el 4 q);;
(* !x y. linside q x y <=> linside (owner m) (fx x) (fy y) *)
let c975ns_iff q m fx fy =
  list_mk_forall([`x:real`; `y:real`],
    mk_iff(c975ns_lin q `x:real` `y:real`, c975ns_own m (fx `x:real`) (fy `y:real`)));;
let c975ns_id t = t;;
let c975ns_stmt sqs hyps concl =
  list_mk_forall(C975NS_V5 @ flat sqs,
    mk_imp(list_mk_conj([`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = c975d_family`] @ hyps),
           concl));;

let C975NS_N = c975ns_sq "N" and C975NS_R = c975ns_sq "R" and C975NS_W = c975ns_sq "W";;

(* a contradiction from two distinct owners containing the same point *)
let C975NS_CLASH_TAC (asl, w as g) =
  let owned = List.filter_map (fun (_, th) ->
     let t = concl th in
     try let f, args = strip_comb t in
         if f <> `linside` then failwith "" else
         let m = dest_small_numeral (rand (hd args)) in
         Some (m, (el 5 args, el 6 args), th)
     with _ -> None) asl in
  let pairs = flat (map (fun (m, p, th) -> List.filter_map (fun (n, q, th') ->
     if m < n && aconv (fst p) (fst q) && aconv (snd p) (snd q) then Some (m, n, p) else None) owned)
     owned) in
  if pairs = [] then failwith "C975NS_CLASH_TAC" else
  let (m, n, (x, y)) = hd pairs in
  (MP_TAC(SPECL [x; y] (REWRITE_RULE[ldisj] (c975cr_inst (oo_apart C975D_F m n)))) THEN
   ASM_REWRITE_TAC[]) g;;

let c975ns_inst = c975cr_inst and c975ns_inst1 = c975cr_inst1;;
let C975NS_HAVE th = STRIP_ASSUME_TAC (c975ns_inst th);;
let C975NS_HAVE1 th h = STRIP_ASSUME_TAC (c975ns_inst1 th (ASSUME h));;
let C975NS_SIDE = ASSUME_TAC C975CR_SIDE;;
let C975NS_OWNER m = ASSUME_TAC (c975cr_unit m) THEN ASSUME_TAC (c975cr_box m);;
let c975ns_apart m n = REWRITE_RULE[ldisj] (c975ns_inst (oo_apart C975D_F m n));;
let C975NS_WALL_TAC m =
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c975cr_box m))) THEN
  REAL_ARITH_TAC;;
let C975NS_SIDE_TAC extra =
  FIRST ([FIRST_ASSUM ACCEPT_TAC;
          ASM_REWRITE_TAC[] THEN NO_TAC] @ extra @
         [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C975NS_CLASH_TAC;
          RASM_ARITH_TAC]);;
(* !y. lo <= y ==> y <= hi ==> ~linside N (&3) y, from the right bar *)
let C975NS_BAR_TAC =
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPECL (C975NS_V5 @ [`y:real`]) C975RS_RIGHT_BAR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN C975NS_CLASH_TAC;;

let C975NS_TURN_INSIDE = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C975NS_HSEG_TAC x0 x1 =
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [x0; x1] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;;

let C975NS_HALF = c975ns_own 34816 `&3 / &2` `&3`;;

let c975ns_withl q = fst (chop_list 4 q) @ [`l:real`];;
let C975NS_NL = c975ns_withl C975NS_N;;

(* Lean: nonnegative_northeast_impossible *)
let C975NS_NONNEGATIVE_NORTHEAST_IMPOSSIBLE = prove
 (c975ns_stmt [C975NS_N]
   [c975ns_unit C975NS_N; c975ns_pos C975NS_N; `aN:real = l`;
    c975ns_iff C975NS_N 1024 c975ns_id c975ns_id;
    `&0 < cN`; `&0 <= sN`; `sN <= cN`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  C975NS_HAVE C975CR_TOP_HALFPOINT_EXCLUDED THEN C975NS_SIDE THEN
  C975NS_HAVE C975TO_TOP_ORIGIN THEN
  C975NS_HAVE C975SEL_NORTHEAST_SELECTION THEN
  C975NS_HAVE C975SS_TOP_MARKER THEN C975NS_HAVE C975SS_NE_MARKER THEN
  C975NS_OWNER 34816 THEN C975NS_OWNER 1024 THEN
  SUBGOAL_THEN (list_mk_comb(`ldisj`, C975NS_NL @ c975ns_owner 34816)) ASSUME_TAC THENL
   [REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[c975ns_apart 1024 34816]; ALL_TAC] THEN
  ASM_CASES_TAC (c975ns_own 1024 `&2` `&113 / &50`) THENL
   [C975NS_HAVE C975RS_SOUTHEAST_G6_POINT THEN
    ASSUME_TAC (REWRITE_RULE[GSYM (oo_aux_point 3)] (c975ns_inst C975IC_TOP_LEFT)) THEN
    MP_TAC (SPECL (C975NS_NL @ c975ns_owner 34816) OCC976MLTT_MIXED_TOP_ADVANCE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN C975NS_SIDE_TAC [C975NS_WALL_TAC 34816]; DISCH_TAC] THEN
    UNDISCH_TAC (mk_neg C975NS_HALF) THEN REWRITE_TAC[] THEN
    C975NS_HSEG_TAC `&127 / &100` `&2`;
    C975NS_HAVE1 C975RS_NORTHEAST_UPPER_SHARP (mk_neg (c975ns_own 1024 `&2` `&113 / &50`)) THEN
    C975NS_HAVE C975RS_CORNER THEN
    MP_TAC (SPECL (C975NS_NL @ c975ns_owner 34816) OCC976MLTT_TOP_ONLY_ADVANCE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN C975NS_SIDE_TAC [C975NS_WALL_TAC 34816; C975NS_BAR_TAC];
      DISCH_TAC] THEN
    UNDISCH_TAC (mk_neg C975NS_HALF) THEN REWRITE_TAC[] THEN
    C975NS_HSEG_TAC `&6 / &5` `&2`]);;

(* Lean: northeast_negative *)
let C975NS_NORTHEAST_NEGATIVE = prove
 (c975ns_stmt [C975NS_N]
   [c975ns_unit C975NS_N; c975ns_pos C975NS_N; `aN:real = l`;
    c975ns_iff C975NS_N 1024 c975ns_id c975ns_id;
    `&0 < cN`; `abs sN <= cN`] `sN < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC (SPECL (C975NS_V5 @ C975NS_N) C975NS_NONNEGATIVE_NORTHEAST_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `abs sN <= cN`)) THEN REAL_ARITH_TAC);;

(* Lean: negative_alternative *)
let C975NS_NEGATIVE_ALTERNATIVE = prove
 (c975ns_stmt [C975NS_N]
   [c975ns_unit C975NS_N; c975ns_pos C975NS_N;
    c975ns_iff C975NS_N 1024 (fun x -> mk_binop `(+):real->real->real` `&2` x)
                             (fun y -> mk_binop `(+):real->real->real` `&3` y)]
   (list_mk_comb(`cc976f_alternative`, C975NS_N)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[cc976f_alternative] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_CASES_TAC (c975ns_own 1024 `&2` `&113 / &50`) THEN ASM_REWRITE_TAC[] THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN DISCH_TAC THEN
    C975NS_HAVE C975RS_SOUTHEAST_G6_POINT THEN C975NS_HAVE C975CP_SOUTHEAST_EAST THEN
    SUBGOAL_THEN (c975ns_own 512 `&2 + x` `&2`) ASSUME_TAC THENL
     [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`&113 / &50`; `&5 / &2`] THEN
      ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
      C975NS_CLASH_TAC];
    C975NS_SIDE THEN
    C975NS_HAVE C975TO_TOP_ORIGIN THEN
    C975NS_HAVE C975SEL_NORTHEAST_SELECTION THEN
    C975NS_HAVE C975SS_NE_MARKER THEN
    C975NS_HAVE1 C975RS_NORTHEAST_UPPER_SHARP (mk_neg (c975ns_own 1024 `&2` `&113 / &50`)) THEN
    C975NS_HAVE C975RS_CORNER THEN
    C975NS_OWNER 1024 THEN
    MATCH_MP_TAC (SPECL (c975ns_owner 1024) OCTOLP_POINT_ORIGINAL) THEN
    REPEAT CONJ_TAC THEN C975NS_SIDE_TAC [C975NS_BAR_TAC]]);;

(* Lean: top_left_excluded *)
let C975NS_TOP_LEFT_EXCLUDED = prove
 (c975ns_stmt [] [] (mk_neg (c975ns_own 34816 `&32 / &25` `&3`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975NS_HAVE C975TO_TOP_ORIGIN THEN C975NS_HAVE C975CR_TOP_HALFPOINT_EXCLUDED THEN
  DISCH_TAC THEN
  UNDISCH_TAC (mk_neg C975NS_HALF) THEN REWRITE_TAC[] THEN
  C975NS_HSEG_TAC `&32 / &25` `&2`);;

(* translated 2 3 and turnFrame tuples *)
let c975ns_tr23 q = match q with
    [c; s; u; v; a] ->
      let mul x y = mk_binop `( * ):real->real->real` x y
      and add x y = mk_binop `(+):real->real->real` x y
      and sub x y = mk_binop `(-):real->real->real` x y in
      [c; s; sub u (add (mul c `&2`) (mul s `&3`));
       sub v (add (mul (mk_comb(`(--):real->real`, s)) `&2`) (mul c `&3`)); a]
  | _ -> failwith "c975ns_tr23";;
let c975ns_turn q = match q with
    [c; s; u; v; a] -> [mk_comb(`(--):real->real`, s); c; v;
                        mk_binop `(-):real->real->real` (mk_comb(`(--):real->real`, u)) a; a]
  | _ -> failwith "c975ns_turn";;

(* Lean: top_negative_shallow *)
let C975NS_TOP_NEGATIVE_SHALLOW =
  let tN = c975ns_tr23 (c975ns_withl C975NS_R) and tT = c975ns_tr23 (c975ns_withl C975NS_W) in
  let conv = REWRITE_CONV[C975NS_TURN_INSIDE; C975CP_TRANSLATED] THENC
             ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let ang q = CONV_RULE conv (SPECL (tN @ q @ [`--sR`]) C976NTM_ANGLE) in
  let altth = SPECL (C975NS_V5 @ tN) C975NS_NEGATIVE_ALTERNATIVE in
  let side_tac =
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           REWRITE_TAC[REAL_NEG_NEG] THEN NO_TAC;
           REWRITE_TAC[REAL_NEG_MUL2] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
           FIRST_ASSUM ACCEPT_TAC;
           ASM_REWRITE_TAC[] THEN NO_TAC;
           REWRITE_TAC[ldisj; C975NS_TURN_INSIDE] THEN
           FIRST_ASSUM(ACCEPT_TAC o REWRITE_RULE[ldisj]);
           MATCH_MP_TAC C981CA_UPPER_WALL THEN REPEAT CONJ_TAC THEN
           FIRST [FIRST_ASSUM ACCEPT_TAC;
                  REWRITE_TAC[REAL_NEG_MUL2] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
                  FIRST_ASSUM ACCEPT_TAC;
                  REWRITE_TAC[C975NS_TURN_INSIDE] THEN FIRST_ASSUM ACCEPT_TAC];
           ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C975NS_CLASH_TAC;
           RASM_ARITH_TAC] in
  prove
   (c975ns_stmt [C975NS_R; C975NS_W]
     [c975ns_unit C975NS_R; c975ns_pos C975NS_R; `aR:real = l`;
      c975ns_iff C975NS_R 1024 c975ns_id c975ns_id;
      `&0 < cR`; `sR < &0`; `--sR <= cR`;
      c975ns_unit C975NS_W; c975ns_pos C975NS_W; `aW:real = l`;
      c975ns_iff C975NS_W 34816 c975ns_id c975ns_id;
      `&0 < cW`; `abs sW <= cW`]
     `sW < &0 /\ --sW < (&2 / &3) * cW`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aR:real = l`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = l`)) THEN
    C975NS_SIDE THEN
    C975NS_HAVE C975TO_TOP_ORIGIN THEN
    C975NS_HAVE C975SEL_NORTHEAST_SELECTION THEN
    C975NS_HAVE C975SS_NE_MARKER THEN
    C975NS_HAVE C975IC_RIGHT_HIGH THEN
    C975NS_HAVE C975NS_TOP_LEFT_EXCLUDED THEN
    SUBGOAL_THEN (list_mk_comb(`cc976f_alternative`, tN)) ASSUME_TAC THENL
     [MATCH_MP_TAC altth THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[C975CP_TRANSLATED] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (list_mk_forall([`x:real`; `y:real`],
                    mk_imp(c975ns_lin tT `x:real` `y:real`, `y <= &1`))) ASSUME_TAC THENL
     [REWRITE_TAC[C975CP_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
      REPEAT GEN_TAC THEN
      DISCH_THEN (MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c975cr_box 34816))) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN (list_mk_comb(`ldisj`, tN @ tT)) ASSUME_TAC THENL
     [REWRITE_TAC[ldisj; C975CP_TRANSLATED] THEN ASM_REWRITE_TAC[c975ns_apart 1024 34816];
      ALL_TAC] THEN
    ASM_CASES_TAC `&0 <= sW` THENL
     [MP_TAC (ang tT) THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN side_tac; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `abs sW <= cW`)) THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `sW < &0` ASSUME_TAC THENL
       [UNDISCH_TAC `~(&0 <= sW)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC (ang (c975ns_turn tT)) THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN side_tac; ALL_TAC] THEN
      UNDISCH_TAC `sW < &0` THEN REAL_ARITH_TAC]);;
