(* ========================================================================= *)
(* Port of Compact/Bridge/C977PositiveBottomWest.lean                        *)
(* (N12Compact.C977PositiveBottomWest).  Original C977 positive-bottom west- *)
(* point entrance, the left singleton's sign selected internally.  (Lean     *)
(* header: "Source only: no assembled Lean replay has yet been run".)        *)
(* Conventions of C977OwnedWestCorner.ml / C977PositiveCornerOrder.ml:       *)
(* p.square (orderedOwner p i) is the 5-tuple c977cre_sq i; the family       *)
(* q : Fin 12 -> OpenSquare is five functions qc qs qu qv qa : num->real     *)
(* with unit normals and positive sides for i < 12; shape (qa i = l, the     *)
(* side of every packing square) and equivalent are stated for i < 12.      *)
(* Normal: c977cc_normal.  PositiveCentralPositiveLeftWest.west: PCPLW_WEST; *)
(* PositiveCentralNegativeLeft.west: PCNL_WEST; C977OwnedWestCorner.         *)
(* frame_excludes: C977OWW_FRAME_EXCLUDES; C977PositiveWallOwnedWest.        *)
(* frame_excludes: C977PWOW_FRAME_EXCLUDES; C977CornerReach.frame_point_or_  *)
(* left_corner: C977CRC_FRAME_POINT_OR_LEFT_CORNER; ClosedFrames.canonical_  *)
(* frame: CLF_CANONICAL_FRAME.  Tag C977PBW_.                                *)
(* ========================================================================= *)

needs "n12/geometry/C977OwnedWestCorner.ml";;
needs "n12/geometry/C977PositiveWallOwnedWest.ml";;
needs "n12/geometry/PositiveCentralNegativeLeft.ml";;
needs "n12/geometry/PositiveCentralPositiveLeftWest.ml";;

(* Lean: apart (private) is C977CRC_APART *)

let C977PBW_QHYP = Printf.sprintf
  "(!i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\\ &0 < qa i) /\\
   (!i. i < 12 ==> qa i = l) /\\
   (!i x y. i < 12 ==> (linside (qc i) (qs i) (qu i) (qv i) (qa i) x y <=> linside %s x y))"
  (c977pco_sqv "i");;

let C977PBW_HYPS () = CONJ (ASSUME `NPACK c1 c2 a b l`)
  (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`);;

(* the facts of frame q i (unit normal, side, equivalence) *)
let C977PBW_Q_TAC i =
  let n = mk_small_numeral i in
  FIRST_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
    then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\ &0 < qa i`) (concl th)
    then STRIP_ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qa i = l`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC);;

let C977PBW_EQ i =
  parse_term (Printf.sprintf "!x y. linside (qc %d) (qs %d) (qu %d) (qv %d) (qa %d) x y <=> linside %s x y"
    i i i i i (c977cre_sq i));;
let C977PBW_EQL =
  parse_term (Printf.sprintf "!x y. linside cL sL uL vL aL x y <=> linside %s x y" (c977cre_sq 1));;

let C977PBW_CLOSE_TAC =
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[lcont; ldisj] THEN
  REWRITE_TAC[ASSUME (C977PBW_EQ 0); ASSUME (C977PBW_EQ 5); ASSUME C977PBW_EQL] THEN
  REWRITE_TAC[GSYM lcont] THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC) ORELSE
   (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
   (REWRITE_TAC[REAL_POW_2] THEN UNDISCH_TAC `cL * cL + sL * sL = &1` THEN REAL_ARITH_TAC));;

(* Lean: frame_west *)
let C977PBW_FRAME_WEST = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\ c977cc_normal (qc 5) (qs 5) /\\
      ~linside %s (&1) (&1) /\\ ~linside %s (&2) (&2)
      ==> linside %s (&1) (&2)"
   C977CRE_HYP C977PBW_QHYP (c977cre_sq 0) (c977cre_sq 5) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C977PBW_Q_TAC 0 THEN C977PBW_Q_TAC 5 THEN
  (* cornerOriginal *)
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `(qc:num->real) 5`; `(qs:num->real) 5`; `(qu:num->real) 5`; `(qv:num->real) 5`; `(qa:num->real) 5`] C977CRC_FRAME_POINT_OR_LEFT_CORNER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `c977cc_normal (qc 5) (qs 5)`)) THEN
    REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  (* facts of the original squares *)
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_DATA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C977WC_FACTS_TAC 0 THEN C977WC_FACTS_TAC 1 THEN C977WC_FACTS_TAC 5 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 1`] C977AN_CODE_TWO_ORIGINAL_ANCHORS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977AN_CODE_ONE_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_anchors] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MAP_EVERY (fun (i, j) -> ASSUME_TAC (MP (C977CRC_APART_AT i j) (C977PBW_HYPS ())))
    [(0, 5); (0, 1); (1, 5)] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&457 / &500) /\\ ~linside %s (&2) (&457 / &500) /\\
     linside %s (&1) (&8 / &5) /\\ lcont %s /\\ lcont %s"
    (c977cre_sq 0) (c977cre_sq 0) (c977cre_sq 1) (c977cre_sq 0) (c977cre_sq 1)))
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&1`, `&457 / &500`)));
      C977WC_TO_OO_TAC 0 THEN MP_TAC(C977WC_INST (oo_missing 1 13)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      (* lowOriginal: auxiliary 10 is forced by the pruned domain of slot 1 *)
      C977WC_TO_OO_TAC 1 THEN REWRITE_TAC[oo_aux_point 10] THEN C977WC_DOMAIN_CASES_TAC 1;
      C977WC_TO_OO_TAC 0 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 1 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  (* foreignLow *)
  ASSUME_TAC(REWRITE_RULE[ASSUME (parse_term (Printf.sprintf "linside %s (&1) (&8 / &5)" (c977cre_sq 1)))]
    (SPECL [`&1`; `&8 / &5`] (MP (C977CRC_APART_AT 5 1) (C977PBW_HYPS ())))) THEN
  (* centerCap *)
  let eq5 = ASSUME (C977PBW_EQ 5) in
  SUBGOAL_THEN `qu 5 + qa 5 <= &2 * (qc 5 + qs 5)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC (parse_term (Printf.sprintf "~linside %s (&2) (&2)" (c977cre_sq 5))) THEN
    REWRITE_TAC[GSYM eq5] THEN
    MP_TAC(ASSUME `c977cc_normal (qc 5) (qs 5)`) THEN
    DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)) THEN
    MAP_EVERY (fun (x, y) ->
      let e = SPECL [x; y] eq5 in
      STRIP_ASSUME_TAC(REWRITE_RULE[linside] (EQ_MP (SYM e) (ASSUME (rand(concl e))))))
     [(`&33 / &20`, `&33 / &20`); (`&2`, `&87 / &50`); (`&87 / &50`, `&2`)] THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  (* the left singleton's canonical frame *)
  MP_TAC(SPECL (c977crc_comps 1) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM eq5] THEN
  ASM_CASES_TAC `&0 <= sL` THENL
   [MATCH_MP_TAC PCPLW_WEST THEN
    MAP_EVERY EXISTS_TAC [`(qc:num->real) 0`; `(qs:num->real) 0`; `(qu:num->real) 0`; `(qv:num->real) 0`; `(qa:num->real) 0`;
                          `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN
    C977PBW_CLOSE_TAC;
    MATCH_MP_TAC PCNL_WEST THEN
    MAP_EVERY EXISTS_TAC [`(qc:num->real) 0`; `(qs:num->real) 0`; `(qu:num->real) 0`; `(qv:num->real) 0`; `(qa:num->real) 0`;
                          `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `--sL:real`] THEN
    C977PBW_CLOSE_TAC]);;

(* Lean: frame_negative_wall_excludes *)
let C977PBW_FRAME_NEGATIVE_WALL_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\ c977cc_normal (qc 5) (qs 5) /\\
      c977cc_normal (qc 8) t /\\ qs 8 = --t /\\
      ~linside %s (&1) (&1) /\\ ~linside %s (&2) (&2)
      ==> F"
   C977CRE_HYP C977PBW_QHYP (c977cre_sq 0) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`]
    C977PBW_FRAME_WEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC C977OWW_FRAME_EXCLUDES THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`; `t:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: frame_excludes *)
let C977PBW_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\ c977cc_normal (qc 5) (qs 5) /\\
      ~linside %s (&1) (&1) /\\ ~linside %s (&2) (&2)
      ==> F"
   C977CRE_HYP C977PBW_QHYP (c977cre_sq 0) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`]
    C977PBW_FRAME_WEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977WC_FACTS_TAC 8 THEN
  MP_TAC(SPECL (c977crc_comps 8) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = l`)) THEN
  ASM_CASES_TAC `&0 <= sW` THENL
   [MATCH_MP_TAC C977PWOW_FRAME_EXCLUDES THEN
    MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                          `cW:real`; `sW:real`; `uW:real`; `vW:real`; `l:real`] THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  (* q' = q with the wall frame W at index 8 *)
  MATCH_MP_TAC C977OWW_FRAME_EXCLUDES THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
    `\i. if i = 8 then cW else (qc:num->real) i`; `\i. if i = 8 then sW else (qs:num->real) i`;
    `\i. if i = 8 then uW else (qu:num->real) i`; `\i. if i = 8 then vW else (qv:num->real) i`;
    `\i. if i = 8 then l else (qa:num->real) i`; `--sW:real`] THEN
  REWRITE_TAC[ARITH] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
         FIRST_X_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
           then MATCH_ACCEPT_TAC th else NO_TAC);
         REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
         REPEAT STRIP_TAC THEN RASM_ARITH_TAC;
         REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC;
         REAL_ARITH_TAC]);;

(* Lean: frame_point_or_corner *)
let C977PBW_FRAME_POINT_OR_CORNER = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      c977cc_normal (qc 0) (qs 0) /\\ c977cc_normal (qc 5) (qs 5)
      ==> linside %s (&1) (&1) \\/ linside %s (&2) (&2)"
   C977CRE_HYP C977PBW_QHYP (c977cre_sq 0) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`]
    C977PBW_FRAME_EXCLUDES) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* Lean: frame_residual *)
let C977PBW_FRAME_RESIDUAL = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      abs (qs 0) <= qc 0 /\\ abs (qs 5) <= qc 5 /\\
      ~linside %s (&1) (&1) /\\ ~linside %s (&2) (&2)
      ==> qs 0 < &0 /\\ &0 < qs 5 /\\ linside %s (&1) (&1)"
   C977CRE_HYP C977PBW_QHYP (c977cre_sq 0) (c977cre_sq 5) (c977cre_sq 1)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C977PBW_Q_TAC 0 THEN C977PBW_Q_TAC 5 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `(qc:num->real) 5`; `(qs:num->real) 5`; `(qu:num->real) 5`; `(qv:num->real) 5`; `(qa:num->real) 5`] C977CRC_FRAME_POINT_OR_LEFT_CORNER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`]
    C977PBW_FRAME_EXCLUDES) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC);;
