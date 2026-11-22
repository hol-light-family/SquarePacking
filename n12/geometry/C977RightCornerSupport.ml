(* ========================================================================= *)
(* Port of Compact/Bridge/C977RightCornerSupport.lean                        *)
(* (N12Compact.C977RightCornerSupport).  Right/top wall support bounds from  *)
(* the paired northeast owner's corner.  Conventions of C977OuterWings.ml:   *)
(* p.square (orderedOwner p i) is c977wc_sq i.  A square R : OpenSquare is   *)
(* cR sR uR vR aR with unit normal and positive side; shape is aR = l.  The  *)
(* family q : Fin 12 -> OpenSquare is qc qs qu qv qa : num->real as in       *)
(* C977PositiveCornerOrder.ml.  lower/upper: ABT_lower/ABT_upper; Normal:    *)
(* c977cc_normal; CentralRightCornerSupport: CRCS_ theorems.  Tag C977RCS_.  *)
(* ========================================================================= *)

needs "n12/geometry/C977OuterWings.ml";;
needs "n12/geometry/CentralRightCornerSupport.ml";;
needs "n12/geometry/C977PositiveCornerOrder.ml";;

let C977RCS_SEED_TAC i m p =
  C977WC_TO_OO_TAC i THEN ACCEPT_TAC(C977WC_INST (oo_seed m p));;

(* Lean: northeast_corner *)
let C977RCS_NORTHEAST_CORNER = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> linside %s (&3) (&3)" C977WC_HYP (c977wc_sq 3)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977RCS_SEED_TAC 3 48 (`&3`, `&3`));;

(* Lean: southeast_corner *)
let C977RCS_SOUTHEAST_CORNER = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> linside %s (&3) (&1)" C977WC_HYP (c977wc_sq 2)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977RCS_SEED_TAC 2 12 (`&3`, `&1`));;

(* Lean: northwest_corner *)
let C977RCS_NORTHWEST_CORNER = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> linside %s (&1) (&3)" C977WC_HYP (c977wc_sq 4)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977RCS_SEED_TAC 4 192 (`&1`, `&3`));;

(* a point owned by slot j is missing from slot i *)
let C977RCS_MISSING_TAC i j corner (x, y) =
  MP_TAC(SPECL [x; y] (MP (C977CRC_APART_AT i j)
    (CONJ (ASSUME `NPACK c1 c2 a b l`) (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`)))) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] corner) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];;

(* Lean: missing_corner (private) *)
let C977RCS_MISSING_CORNER = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ ~(i = 3)
     ==> ~linside (a (c977av_ordered_owner c1 c2 a b l i)) (b (c977av_ordered_owner c1 c2 a b l i))
           (a (c977av_ordered_owner c1 c2 a b l i) * c1 (c977av_ordered_owner c1 c2 a b l i) +
            b (c977av_ordered_owner c1 c2 a b l i) * c2 (c977av_ordered_owner c1 c2 a b l i) - l / &2)
           (--b (c977av_ordered_owner c1 c2 a b l i) * c1 (c977av_ordered_owner c1 c2 a b l i) +
            a (c977av_ordered_owner c1 c2 a b l i) * c2 (c977av_ordered_owner c1 c2 a b l i) - l / &2)
           l (&3) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`; `3`]
    C977CRC_APART) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o SPECL [`&3`; `&3`]) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977RCS_NORTHEAST_CORNER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let C977RCS_MISSING_AT i =
  REWRITE_RULE[ARITH] (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
    mk_small_numeral i] C977RCS_MISSING_CORNER);;

let c977rcs_hyp i swap =
  Printf.sprintf
   "%s /\\ cR * cR + sR * sR = &1 /\\ &0 < aR /\\ abs sR <= cR /\\ aR = l /\\
    (!x y. linside cR sR uR vR aR x y <=> linside %s %s)"
   C977WC_HYP (c977wc_sq i) (if swap then "y x" else "x y");;

(* the R-side facts used by every support bound: 1 <= aR, lcont R, marker, ~(3,3) *)
let C977RCS_SETUP_TAC i swap =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aR:real = l`)) THEN
  C977WC_FACTS_TAC i THEN
  let hyps = CONJ (ASSUME `NPACK c1 c2 a b l`)
                  (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`) in
  ASSUME_TAC(MP (C977RCS_MISSING_AT i) hyps) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "lcont %s" (c977wc_sq i))) ASSUME_TAC THENL
   [C977WC_TO_OO_TAC i THEN ASM_SIMP_TAC[OO_BOX]; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "linside %s %s" (c977wc_sq i)
                  (if swap then "(&2) (&1543 / &500)" else "(&1543 / &500) (&2)"))) ASSUME_TAC THENL
   [if swap then C977RCS_SEED_TAC i 32768 (`&2`, `&1543 / &500`)
    else C977RCS_SEED_TAC i 16384 (`&1543 / &500`, `&2`); ALL_TAC] THEN
  SUBGOAL_THEN `lcont cR sR uR vR l` ASSUME_TAC THENL
   [REWRITE_TAC[lcont] THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[lcont] o
      check (fun th -> concl th = parse_term (Printf.sprintf "lcont %s" (c977wc_sq i)))) THEN
    DISCH_THEN(MP_TAC o SPECL (if swap then [`y:real`; `x:real`] else [`x:real`; `y:real`])) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC];;

let C977RCS_CLOSE_TAC =
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC);;

(* Lean: right_canonical_support *)
let C977RCS_RIGHT_CANONICAL_SUPPORT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cR sR uR vR aR c s. %s /\\ c977cc_normal c s
      ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1" (c977rcs_hyp 10 false)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977RCS_SETUP_TAC 10 false THEN
  MATCH_MP_TAC CRCS_CANONICAL_LOWER_SUPPORT THEN C977RCS_CLOSE_TAC);;

(* Lean: right_support *)
let C977RCS_RIGHT_SUPPORT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cR sR uR vR aR c s. %s /\\
      cR * cR + sR * sR = &1 /\\ &0 < aR /\\ c977cc_normal cR sR /\\ aR = l /\\
      (!x y. linside cR sR uR vR aR x y <=> linside %s x y) /\\ c977cc_normal c s
      ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1" C977WC_HYP (c977wc_sq 10)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C977RCS_RIGHT_CANONICAL_SUPPORT THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal cR sR` THEN
  REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC);;

(* Lean: top_canonical_support *)
let C977RCS_TOP_CANONICAL_SUPPORT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cR sR uR vR aR c s. %s /\\ c977cc_normal c s
      ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1" (c977rcs_hyp 11 true)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977RCS_SETUP_TAC 11 true THEN
  MATCH_MP_TAC CRCS_CANONICAL_LOWER_SUPPORT THEN C977RCS_CLOSE_TAC);;

(* Lean: top_support *)
let C977RCS_TOP_SUPPORT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cR sR uR vR aR c s. %s /\\
      cR * cR + sR * sR = &1 /\\ &0 < aR /\\ c977cc_normal cR sR /\\ aR = l /\\
      (!x y. linside cR sR uR vR aR x y <=> linside %s y x) /\\ c977cc_normal c s
      ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1" C977WC_HYP (c977wc_sq 11)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C977RCS_TOP_CANONICAL_SUPPORT THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c977cc_normal cR sR` THEN
  REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC);;

(* Lean: right_signed_support *)
let C977RCS_RIGHT_SIGNED_SUPPORT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cR sR uR vR aR c s. %s /\\ abs s <= c /\\ c pow 2 + s pow 2 = &1
      ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1" (c977rcs_hyp 10 false)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977RCS_SETUP_TAC 10 false THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "~linside %s (&3) (&1)" (c977wc_sq 10))) ASSUME_TAC THENL
   [C977RCS_MISSING_TAC 10 2 C977RCS_SOUTHEAST_CORNER (`&3`, `&1`); ALL_TAC] THEN
  MATCH_MP_TAC CRCS_SIGNED_DIRECTION_SUPPORT THEN C977RCS_CLOSE_TAC);;

(* Lean: top_signed_support *)
let C977RCS_TOP_SIGNED_SUPPORT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cR sR uR vR aR c s. %s /\\ abs s <= c /\\ c pow 2 + s pow 2 = &1
      ==> ABT_lower cR sR uR vR aR c s <= &2 * (c + s) + &1" (c977rcs_hyp 11 true)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977RCS_SETUP_TAC 11 true THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "~linside %s (&1) (&3)" (c977wc_sq 11))) ASSUME_TAC THENL
   [C977RCS_MISSING_TAC 11 4 C977RCS_NORTHWEST_CORNER (`&1`, `&3`); ALL_TAC] THEN
  MATCH_MP_TAC CRCS_SIGNED_DIRECTION_SUPPORT THEN C977RCS_CLOSE_TAC);;

(* the family hypotheses (as in C977PositiveCornerOrder.ml) *)
let C977RCS_QHYP = Printf.sprintf
  "%s /\\
   (!i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\\ &0 < qa i) /\\
   (!i. i < 12 ==> qa i = l) /\\
   (!i x y. i < 12 ==> (linside (qc i) (qs i) (qu i) (qv i) (qa i) x y <=> linside %s x y)) /\\
   linside %s (&2) (&2) /\\
   ABT_upper (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (qc 6) (qs 6) <= qu 6 /\\
   qu 6 + qa 6 <= ABT_lower (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (qc 6) (qs 6)"
  C977WC_HYP (c977pco_sqv "i") (c977wc_sq 5);;

let C977RCS_CHAIN_TAC support extra =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun i ->
    let n = mk_small_numeral i in
    FIRST_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
      then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\ &0 < qa i`) (concl th)
      then STRIP_ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> qa i = l`) (concl th)
      then ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC n th)) else NO_TAC)) [5; 6; 10] THEN
  C977WC_FACTS_TAC 6 THEN
  SUBGOAL_THEN `(qc:num->real) 6 pow 2 + (qs:num->real) 6 pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`(qc:num->real) 5`; `(qs:num->real) 5`; `(qu:num->real) 5`; `(qv:num->real) 5`;
                `(qa:num->real) 5`; `&2`; `&2`; `(qc:num->real) 6`; `(qs:num->real) 6`] ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `(qc:num->real) 10`; `(qs:num->real) 10`; `(qu:num->real) 10`; `(qv:num->real) 10`;
                `(qa:num->real) 10`; `(qc:num->real) 6`; `(qs:num->real) 6`] support) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN extra; DISCH_TAC] THEN
  ASM_REAL_ARITH_TAC;;

(* Lean: center_chain_signed_excludes *)
let C977RCS_CENTER_CHAIN_SIGNED_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ abs (qs 6) <= qc 6 /\\ abs (qs 10) <= qc 10 ==> F" C977RCS_QHYP),
  C977RCS_CHAIN_TAC C977RCS_RIGHT_SIGNED_SUPPORT ALL_TAC);;

(* Lean: center_chain_canonical_excludes *)
let C977RCS_CENTER_CHAIN_CANONICAL_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ c977cc_normal (qc 6) (qs 6) /\\ abs (qs 10) <= qc 10 ==> F"
   C977RCS_QHYP),
  C977RCS_CHAIN_TAC C977RCS_RIGHT_CANONICAL_SUPPORT ALL_TAC);;

(* Lean: center_chain_excludes *)
let C977RCS_CENTER_CHAIN_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ c977cc_normal (qc 6) (qs 6) /\\ c977cc_normal (qc 10) (qs 10) ==> F"
   C977RCS_QHYP),
  C977RCS_CHAIN_TAC C977RCS_RIGHT_SUPPORT ALL_TAC);;
