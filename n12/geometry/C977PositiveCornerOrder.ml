(* ========================================================================= *)
(* Port of Compact/Bridge/C977PositiveCornerOrder.lean                       *)
(* (N12Compact.C977PositiveCornerOrder).  Original-packing entrance to the   *)
(* owned-west-point angle comparison.  Conventions of C977CentralReach.ml    *)
(* (p.square (orderedOwner p i) is the 5-tuple c977cre_sq i).  The family    *)
(* q : Fin 12 -> OpenSquare is five functions qc qs qu qv qa : num->real     *)
(* with unit normals and positive sides for i < 12; shape and equivalent are *)
(* stated for i < 12.  PositiveCentralWallAngleOrder.angle_order:            *)
(* PCWAO_ANGLE_ORDER.  Tag C977PCO_.                                         *)
(* ========================================================================= *)

needs "n12/geometry/C977CentralReach.ml";;
needs "n12/geometry/PositiveCentralWallAngleOrder.ml";;
needs "n12/geometry/C977CornerReach.ml";;

let c977pco_sqv iv =
  let w = Printf.sprintf "(c977av_ordered_owner c1 c2 a b l %s)" iv in
  Printf.sprintf "(a %s) (b %s) (a %s * c1 %s + b %s * c2 %s - l / &2) (--b %s * c1 %s + a %s * c2 %s - l / &2) l"
    w w w w w w w w w w;;

let c977pco_q i =
  map (fun f -> mk_comb(f, mk_small_numeral i))
    [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

(* Lean: apart (private) is C977CRC_APART; forced_auxiliary (private) is C977OWC-style domain cases *)

(* Lean: frame_angle_order_of_west *)
let C977PCO_FRAME_ANGLE_ORDER_OF_WEST = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\
      (!i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\\ &0 < qa i) /\\
      (!i. i < 12 ==> qa i = l) /\\
      (!i x y. i < 12 ==> (linside (qc i) (qs i) (qu i) (qv i) (qa i) x y <=> linside %s x y)) /\\
      c977cc_normal (qc 0) (qs 0) /\\ c977cc_normal (qc 5) (qs 5) /\\ c977cc_normal (qc 8) t /\\
      qs 8 = --t /\\
      ~linside %s (&1) (&1) /\\ ~linside %s (&2) (&2) /\\ linside %s (&1) (&2)
      ==> qs 0 < t"
   C977CRE_HYP (c977pco_sqv "i") (c977cre_sq 0) (c977cre_sq 5) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the three frames used *)
  MAP_EVERY (fun i ->
    let n = mk_small_numeral i in
    FIRST_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
      then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\ &0 < qa i`) (concl th)
      then STRIP_ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qa i = l`) (concl th)
      then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC)) [0; 5; 8] THEN
  (* facts of the original squares *)
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_DATA) THEN
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
    [(0, 5); (5, 8); (5, 1); (8, 1)] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&457 / &500) /\\ ~linside %s (&2) (&457 / &500) /\\
     linside %s (&1) (&8 / &5) /\\
     linside %s (&457 / &500) (&2) /\\ linside %s (&1) (&113 / &50) /\\
     ~linside %s (&457 / &500) (&3) /\\
     lcont %s /\\ lcont %s"
    (c977cre_sq 0) (c977cre_sq 0) (c977cre_sq 1) (c977cre_sq 8) (c977cre_sq 8) (c977cre_sq 8)
    (c977cre_sq 0) (c977cre_sq 8)))
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&1`, `&457 / &500`)));
      C977WC_TO_OO_TAC 0 THEN MP_TAC(C977WC_INST (oo_missing 1 13)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 1 THEN REWRITE_TAC[oo_aux_point 10] THEN C977WC_DOMAIN_CASES_TAC 1;
      C977WC_TO_OO_TAC 8 THEN ACCEPT_TAC(C977WC_INST (oo_seed 4096 (`&457 / &500`, `&2`)));
      C977WC_TO_OO_TAC 8 THEN REWRITE_TAC[oo_aux_point 1] THEN C977WC_DOMAIN_CASES_TAC 8;
      C977WC_TO_OO_TAC 8 THEN MP_TAC(C977WC_INST (oo_missing 4096 7)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 0 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 8 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  ASSUME_TAC(REWRITE_RULE[ASSUME (parse_term (Printf.sprintf "linside %s (&1) (&8 / &5)" (c977cre_sq 1)))]
    (SPECL [`&1`; `&8 / &5`] (MP (C977CRC_APART_AT 5 1) hyps))) THEN
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
  MATCH_MP_TAC PCWAO_ANGLE_ORDER THEN
  MAP_EVERY EXISTS_TAC ((let q0 = c977pco_q 0 in hd q0 :: tl (tl q0)) @ c977pco_q 5 @ c977pco_q 8) THEN
  ASM_REWRITE_TAC[lcont; ldisj] THEN
  REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC ORELSE
    (REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC) ORELSE ALL_TAC));;
