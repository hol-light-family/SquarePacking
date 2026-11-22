(* ========================================================================= *)
(* Port of Compact/Bridge/C977OwnedWestCorner.lean                           *)
(* (N12Compact.C977OwnedWestCorner).  Original-family C977 exclusion of the  *)
(* positive-bottom / negative-left-wall cell when the southwest central      *)
(* square owns (1,2) and misses (2,2).  (Lean header: "Source only,          *)
(* uncompiled".)  Conventions of C977PositiveCornerOrder.ml: p.square        *)
(* (orderedOwner p i) is the 5-tuple c977cre_sq i; the family q : Fin 12 ->  *)
(* OpenSquare is five functions qc qs qu qv qa : num->real with unit normals *)
(* and positive sides for i < 12; shape and equivalent are stated for i < 12.*)
(* CornerWallMarkerCycle.impossible: CWMCY_IMPOSSIBLE (Data = cwmcy_data);   *)
(* ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME.  Tag C977OWW_.         *)
(* ========================================================================= *)

needs "n12/geometry/C977PositiveCornerOrder.ml";;
needs "n12/geometry/C977CornerReach.ml";;
needs "n12/geometry/CornerWallMarkerCycle.ml";;
needs "n12/geometry/NegativeWallTopSeed.ml";;
needs "n12/geometry/NegativeWallMarkerCap.ml";;
needs "n12/geometry/C696PositiveCorner.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: apart (private) is C977CRC_APART; forced_auxiliary (private) is replaced by
   the pruned-domain case split C977WC_LEFT_AUXILIARY *)

let C977OWW_CLOSE_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC ORELSE
   (REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC) ORELSE ALL_TAC);;

(* Lean: frame_excludes *)
let C977OWW_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\
      (!i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\\ &0 < qa i) /\\
      (!i. i < 12 ==> qa i = l) /\\
      (!i x y. i < 12 ==> (linside (qc i) (qs i) (qu i) (qv i) (qa i) x y <=> linside %s x y)) /\\
      c977cc_normal (qc 0) (qs 0) /\\ c977cc_normal (qc 5) (qs 5) /\\ c977cc_normal (qc 8) t /\\
      qs 8 = --t /\\
      ~linside %s (&1) (&1) /\\ ~linside %s (&2) (&2) /\\ linside %s (&1) (&2)
      ==> F"
   C977CRE_HYP (c977pco_sqv "i") (c977cre_sq 0) (c977cre_sq 5) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* order: the angle comparison of C977PositiveCornerOrder *)
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`; `t:real`]
    C977PCO_FRAME_ANGLE_ORDER_OF_WEST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the three frames used *)
  MAP_EVERY (fun i ->
    let n = mk_small_numeral i in
    FIRST_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
      then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\ &0 < qa i`) (concl th)
      then STRIP_ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qa i = l`) (concl th)
      then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC)) [0; 5; 8] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `qs 8 = --t` then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
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
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977WC_LEFT_AUXILIARY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C977WC_FACTS_TAC 0 THEN C977WC_FACTS_TAC 1 THEN C977WC_FACTS_TAC 5 THEN C977WC_FACTS_TAC 8 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 1`] C977AN_CODE_TWO_ORIGINAL_ANCHORS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977AN_CODE_ONE_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_anchors] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  let hyps = CONJ (ASSUME `NPACK c1 c2 a b l`)
                  (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`) in
  MAP_EVERY (fun (i, j) -> ASSUME_TAC (MP (C977CRC_APART_AT i j) hyps))
    [(0, 1); (1, 8); (5, 8); (8, 1)] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&457 / &500) /\\ ~linside %s (&2) (&457 / &500) /\\
     linside %s (&457 / &500) (&1) /\\
     linside %s (&457 / &500) (&2) /\\ ~linside %s (&457 / &500) (&3) /\\
     ~linside %s (&33 / &20) (&47 / &20) /\\
     lcont %s /\\ lcont %s /\\ lcont %s"
    (c977cre_sq 0) (c977cre_sq 0) (c977cre_sq 1) (c977cre_sq 8) (c977cre_sq 8) (c977cre_sq 8)
    (c977cre_sq 0) (c977cre_sq 1) (c977cre_sq 8)))
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&1`, `&457 / &500`)));
      C977WC_TO_OO_TAC 0 THEN MP_TAC(C977WC_INST (oo_missing 1 13)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 1 THEN ACCEPT_TAC(C977WC_INST (oo_seed 2 (`&457 / &500`, `&1`)));
      C977WC_TO_OO_TAC 8 THEN ACCEPT_TAC(C977WC_INST (oo_seed 4096 (`&457 / &500`, `&2`)));
      C977WC_TO_OO_TAC 8 THEN MP_TAC(C977WC_INST (oo_missing 4096 7)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 8 THEN MP_TAC(C977WC_INST (oo_missing 4096 11)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 0 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 1 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 8 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  (* wMissingFar *)
  ASSUME_TAC(REWRITE_RULE[ASSUME (parse_term (Printf.sprintf "linside %s (&19 / &25) (&187 / &100)" (c977cre_sq 1)))]
    (SPECL [`&19 / &25`; `&187 / &100`] (MP (C977CRC_APART_AT 8 1) hyps))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont]) THEN
  (* centerCap *)
  let eq5 = ASSUME (parse_term (Printf.sprintf
    "!x y. linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) x y <=> linside %s x y" (c977cre_sq 5))) in
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
  (* lower, top, northwest, wallRange *)
  MP_TAC(SPECL [`(qc:num->real) 5`; `(qs:num->real) 5`; `(qu:num->real) 5`; `(qv:num->real) 5`; `(qa:num->real) 5`; `(qc:num->real) 8`; `--t`; `(qu:num->real) 8`; `(qv:num->real) 8`; `(qa:num->real) 8`; `t:real`]
    NWTS_LOWER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ldisj] THEN C977OWW_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`(qc:num->real) 8`; `--t`; `(qu:num->real) 8`; `(qv:num->real) 8`; `(qa:num->real) 8`; `t:real`] NWMC_UPPER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977OWW_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`(qc:num->real) 8`; `--t`; `(qu:num->real) 8`; `(qv:num->real) 8`; `(qa:num->real) 8`; `t:real`] NWMC_UPPER_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977OWW_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`(qc:num->real) 8`; `t:real`; `(qa:num->real) 8`; `(qv:num->real) 8`; `(qv:num->real) 8 + (qa:num->real) 8`] NWMC_SECTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C977OWW_CLOSE_TAC; STRIP_TAC] THEN
  (* oFaces *)
  MP_TAC(SPECL [`(qc:num->real) 0`; `(qs:num->real) 0`; `(qu:num->real) 0`; `(qv:num->real) 0`; `(qa:num->real) 0`] C696PC_CORNER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[lcont] THEN C977OWW_CLOSE_TAC; STRIP_TAC] THEN
  (* the left singleton's canonical frame *)
  MP_TAC(SPECL (c977crc_comps 1) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC CWMCY_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`(qc:num->real) 0`; `(qs:num->real) 0`; `(qu:num->real) 0`; `(qv:num->real) 0`; `(qa:num->real) 0`; `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                        `(qc:num->real) 8`; `--t`; `(qu:num->real) 8`; `(qv:num->real) 8`; `(qa:num->real) 8`; `t:real`] THEN
  ASM_REWRITE_TAC[cwmcy_data; lcont; ldisj; GSYM CWMMB_BOUNDARY_DEF] THEN
  REWRITE_TAC[CWMMB_BOUNDARY_DEF; GSYM c696cm_boundary] THEN
  ASM_REWRITE_TAC[] THEN C977OWW_CLOSE_TAC);;
