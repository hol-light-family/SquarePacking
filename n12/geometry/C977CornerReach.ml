(* ========================================================================= *)
(* Port of Compact/Bridge/C977CornerReach.lean (N12Compact.C977CornerReach). *)
(* Original-family entrance to the completed continuous corner sectors.     *)
(* Conventions of C977CentralReach.ml (p.square (orderedOwner p i) is the   *)
(* 5-tuple c977cre_sq i); an OpenSquare A = cA sA uA vA aA carries its unit *)
(* normal and positive side as explicit hypotheses.  SouthwestNegativeCorner *)
(* .point / SouthwestCornerTranspose.point: SNC_POINT / SCT_POINT;           *)
(* ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME.  Tag C977CRC_.         *)
(* ========================================================================= *)

needs "n12/geometry/C977CentralReach.ml";;
needs "n12/geometry/SouthwestCornerTranspose.ml";;
needs "n12/geometry/C977WallCenters.ml";;

(* Lean: apart (private) *)
let C977CRC_APART = prove
 (`forall c1 c2 a b l i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> forall x y. ~(linside (a (c977av_ordered_owner c1 c2 a b l i)) (b (c977av_ordered_owner c1 c2 a b l i))
                   (a (c977av_ordered_owner c1 c2 a b l i) * c1 (c977av_ordered_owner c1 c2 a b l i) +
                    b (c977av_ordered_owner c1 c2 a b l i) * c2 (c977av_ordered_owner c1 c2 a b l i) - l / &2)
                   (--b (c977av_ordered_owner c1 c2 a b l i) * c1 (c977av_ordered_owner c1 c2 a b l i) +
                    a (c977av_ordered_owner c1 c2 a b l i) * c2 (c977av_ordered_owner c1 c2 a b l i) - l / &2) l x y /\
                 linside (a (c977av_ordered_owner c1 c2 a b l j)) (b (c977av_ordered_owner c1 c2 a b l j))
                   (a (c977av_ordered_owner c1 c2 a b l j) * c1 (c977av_ordered_owner c1 c2 a b l j) +
                    b (c977av_ordered_owner c1 c2 a b l j) * c2 (c977av_ordered_owner c1 c2 a b l j) - l / &2)
                   (--b (c977av_ordered_owner c1 c2 a b l j) * c1 (c977av_ordered_owner c1 c2 a b l j) +
                    a (c977av_ordered_owner c1 c2 a b l j) * c2 (c977av_ordered_owner c1 c2 a b l j) - l / &2) l x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM ldisj] THEN
  MATCH_MP_TAC NPACK_LDISJ THEN ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN
  MATCH_MP_TAC C977WC_DISTINCT THEN ASM_REWRITE_TAC[]);;

let C977CRC_APART_AT i j =
  REWRITE_RULE[ARITH] (SPECL [mk_small_numeral i; mk_small_numeral j]
    (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] C977CRC_APART));;

let c977crc_comps i =
  let w = Printf.sprintf "(c977av_ordered_owner c1 c2 a b l %d)" i in
  map parse_term
   [Printf.sprintf "(a:num->real) %s" w; Printf.sprintf "(b:num->real) %s" w;
    Printf.sprintf "a %s * c1 %s + b %s * (c2:num->real) %s - l / &2" w w w w;
    Printf.sprintf "--b %s * c1 %s + a %s * (c2:num->real) %s - l / &2" w w w w; "l:real"];;

(* Lean: frame_point_or_left_corner *)
let C977CRC_FRAME_POINT_OR_LEFT_CORNER = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cA sA uA vA aA. %s /\\ ~linside %s (&1) (&1) /\\
      cA * cA + sA * sA = &1 /\\ &0 < aA /\\ abs sA <= cA /\\ aA = l /\\
      (!x y. linside cA sA uA vA aA x y <=> linside %s x y)
      ==> linside %s (&2) (&2) \\/ (&0 < sA /\\ linside %s (&1) (&1))"
   C977CRE_HYP (c977cre_sq 0) (c977cre_sq 5) (c977cre_sq 5) (c977cre_sq 1)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = l`)) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_DATA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C977WC_FACTS_TAC 0 THEN C977WC_FACTS_TAC 1 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 1`] C977AN_CODE_TWO_ORIGINAL_ANCHORS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977AN_CODE_ONE_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_anchors] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(MP (C977CRC_APART_AT 0 5) (CONJ (ASSUME `NPACK c1 c2 a b l`)
     (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`))) THEN
  MP_TAC(MP (C977CRC_APART_AT 5 1) (CONJ (ASSUME `NPACK c1 c2 a b l`)
     (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`))) THEN
  MP_TAC(MP (C977CRC_APART_AT 1 5) (CONJ (ASSUME `NPACK c1 c2 a b l`)
     (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`))) THEN
  MP_TAC(MP (C977CRC_APART_AT 5 0) (CONJ (ASSUME `NPACK c1 c2 a b l`)
     (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`))) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&457 / &500) /\\ linside %s (&457 / &500) (&1) /\\
     ~linside %s (&2) (&457 / &500) /\\ ~linside %s (&457 / &500) (&2) /\\
     lcont %s /\\ lcont %s"
    (c977cre_sq 0) (c977cre_sq 1) (c977cre_sq 0) (c977cre_sq 1) (c977cre_sq 0) (c977cre_sq 1)))
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&1`, `&457 / &500`)));
      C977WC_TO_OO_TAC 1 THEN ACCEPT_TAC(C977WC_INST (oo_seed 2 (`&457 / &500`, `&1`)));
      C977WC_TO_OO_TAC 0 THEN MP_TAC(C977WC_INST (oo_missing 1 13)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 1 THEN MP_TAC(C977WC_INST (oo_missing 2 12)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 0 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 1 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  let close = ASM_REWRITE_TAC[REAL_NEG_NEG; c977cc_normal; ldisj] THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC in
  ASM_CASES_TAC `sA <= &0` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `linside cA sA uA vA l (&2) (&2)` MP_TAC THENL
     [MATCH_MP_TAC SNC_POINT THEN
      MAP_EVERY EXISTS_TAC (c977crc_comps 0 @ c977crc_comps 1 @ [`--sA`]) THEN close;
      ASM_REWRITE_TAC[]];
    ASM_CASES_TAC (parse_term (Printf.sprintf "linside %s (&1) (&1)" (c977cre_sq 1))) THENL
     [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    DISJ1_TAC THEN
    SUBGOAL_THEN `linside cA sA uA vA l (&2) (&2)` MP_TAC THENL
     [MATCH_MP_TAC SCT_POINT THEN
      MAP_EVERY EXISTS_TAC (c977crc_comps 0 @ c977crc_comps 1) THEN close;
      ASM_REWRITE_TAC[]]]);;

(* Lean: central_point_or_positive_corner *)
let C977CRC_CENTRAL_POINT_OR_POSITIVE_CORNER = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ ~linside %s (&1) (&1)
      ==> linside %s (&2) (&2) \\/
          ?cA sA uA vA aA. cA * cA + sA * sA = &1 /\\ &0 < aA /\\
            &0 < sA /\\ sA <= cA /\\ aA = l /\\
            (!x y. linside cA sA uA vA aA x y <=> linside %s x y) /\\
            linside %s (&1) (&1)"
   C977CRE_HYP (c977cre_sq 0) (c977cre_sq 5) (c977cre_sq 5) (c977cre_sq 1)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977WC_FACTS_TAC 5 THEN
  MP_TAC(SPECL (c977crc_comps 5) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    C977CRC_FRAME_POINT_OR_LEFT_CORNER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;
