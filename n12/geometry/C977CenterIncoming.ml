(* ========================================================================= *)
(* Port of Compact/Bridge/C977CenterIncoming.lean                            *)
(* (N12Compact.C977CenterIncoming).  Original-center incoming-axis           *)
(* classification.  Conventions of C977RightCornerSupport.ml: p.square       *)
(* (orderedOwner p i) is c977wc_sq i; the family q : Fin 12 -> OpenSquare is *)
(* qc qs qu qv qa : num->real with, for i < 12, unit normal and positive     *)
(* side (OpenSquare fields), shape qa i = l, equivalent                      *)
(*   linside (q i) x y <=> linside (c977wc_sq i) x y,                       *)
(* canonical  &0 < qc i /\ abs (qs i) <= qc i.  lower/upper: ABT_lower /     *)
(* ABT_upper; Normal: c977cc_normal.  CentralCenterPairIncoming:             *)
(* CCPI_RIGHT_ALTERNATIVES / CCPI_TOP_ALTERNATIVES; CentralPositiveTransverse *)
(* .impossible: CPTR_IMPOSSIBLE; C977CenterCaps.frame_caps: C977CC_FRAME_CAPS. *)
(* Tag C977CI_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/C977CenterCaps.ml";;
needs "n12/geometry/CentralCenterPairIncoming.ml";;
needs "n12/geometry/CentralPositiveTransverse.ml";;
needs "n12/geometry/C977RightCornerSupport.ml";;

(* the family hypotheses (shape, equivalent; OpenSquare fields of q) *)
let C977CI_QHYP = Printf.sprintf
  "%s /\\
   (!i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\\ &0 < qa i) /\\
   (!i. i < 12 ==> qa i = l) /\\
   (!i x y. i < 12 ==> (linside (qc i) (qs i) (qu i) (qv i) (qa i) x y <=> linside %s x y))"
  C977WC_HYP (c977pco_sqv "i");;

let C977CI_CANON = "(!i. i < 12 ==> &0 < qc i /\\ abs (qs i) <= qc i)";;

let c977ci_q i = Printf.sprintf "(qc %d) (qs %d) (qu %d) (qv %d) (qa %d)" i i i i i;;
let c977ci_qt i = map (fun f -> mk_comb(f, mk_small_numeral i))
  [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

(* instances at slots is of the universally quantified family hypotheses *)
let C977CI_INST_TAC is =
  MAP_EVERY (fun i ->
    let n = mk_small_numeral i in
    let inst th = REWRITE_RULE[ARITH] (SPEC n th) in
    FIRST_ASSUM(fun th -> if is_forall (concl th) && length (fst (strip_forall (concl th))) = 3
      then ASSUME_TAC(inst th) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> (qc:num->real) i * qc i + (qs:num->real) i * qs i = &1 /\ &0 < (qa:num->real) i`) (concl th)
      then STRIP_ASSUME_TAC(inst th) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> (qa:num->real) i = l`) (concl th)
      then ASSUME_TAC(inst th) else NO_TAC) THEN
    TRY (FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> &0 < (qc:num->real) i /\ abs ((qs:num->real) i) <= qc i`) (concl th)
      then STRIP_ASSUME_TAC(inst th) else NO_TAC))) is;;

(* the q squares with side l, after C977CI_SUBST_TAC *)
let c977ci_ql i = map (fun f -> mk_comb(f, mk_small_numeral i))
  [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`] @ [`l:real`];;
let C977CI_SUBST_TAC =
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && rhs (concl th) = `l:real` && is_comb (lhs (concl th)) &&
    rator (lhs (concl th)) = `qa:num->real`)));;

let C977CI_HYPS () = CONJ (ASSUME `NPACK c1 c2 a b l`)
  (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`);;

(* the original-square facts used below *)
let C977CI_FACTS_TAC =
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_DATA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&47 / &20) (&33 / &20) /\\ linside %s (&3) (&87 / &50)"
    (c977wc_sq 6) (c977wc_sq 6))) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [C977WC_TO_OO_TAC 6 THEN ACCEPT_TAC(C977WC_INST (oo_seed 512 (`&47 / &20`, `&33 / &20`)));
      C977WC_TO_OO_TAC 6 THEN REWRITE_TAC[oo_aux_point 8] THEN C977WC_DOMAIN_CASES_TAC 6];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&33 / &20) (&47 / &20) /\\ linside %s (&87 / &50) (&3)"
    (c977wc_sq 7) (c977wc_sq 7))) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [C977WC_TO_OO_TAC 7 THEN ACCEPT_TAC(C977WC_INST (oo_seed 2048 (`&33 / &20`, `&47 / &20`)));
      C977WC_TO_OO_TAC 7 THEN REWRITE_TAC[oo_aux_point 14] THEN C977WC_DOMAIN_CASES_TAC 7];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

(* apart of slots i, j as ldisj of the q squares *)
let C977CI_LDISJ i j =
  let th = C977CRC_APART_AT i j in
  let th = MP th (C977CI_HYPS ()) in
  th;;

(* Lean: frame_cover *)
let C977CI_FRAME_COVER = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\ linside %s (&2) (&2)
      ==> (qu 5 + qa 5 <= ABT_lower %s (qc 5) (qs 5) \\/
           ABT_upper %s (qc 6) (qs 6) <= qu 6 \\/
           (&3 * qc 6 < &7 * qs 6 /\\ qv 6 + qa 6 <= ABT_lower %s (--(qs 6)) (qc 6))) /\\
          (qv 5 + qa 5 <= ABT_lower %s (--(qs 5)) (qc 5) \\/
           ABT_upper %s (--(qs 7)) (qc 7) <= qv 7 \\/
           (&7 * qs 7 < -- &3 * qc 7 /\\ qu 7 + qa 7 <= ABT_lower %s (qc 7) (qs 7)))"
   C977CI_QHYP C977CI_CANON (c977wc_sq 5) (c977ci_q 6) (c977ci_q 5) (c977ci_q 5)
   (c977ci_q 7) (c977ci_q 5) (c977ci_q 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [5; 6; 7] THEN
  MP_TAC(SPECL ([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] @
                c977ci_qt 5) C977CC_FRAME_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  C977CI_FACTS_TAC THEN
  ASSUME_TAC(C977CI_LDISJ 5 6) THEN ASSUME_TAC(C977CI_LDISJ 5 7) THEN
  C977CI_SUBST_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC (SPECL (c977ci_ql 5 @ c977ci_ql 6) CCPI_RIGHT_ALTERNATIVES);
    MATCH_MP_TAC (SPECL (c977ci_ql 5 @ c977ci_ql 7) CCPI_TOP_ALTERNATIVES)] THEN
  ASM_REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[]);;

(* Lean: positive_right_transverse_excludes *)
let C977CI_POSITIVE_RIGHT_TRANSVERSE_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 5) (qs 5) /\\ c977cc_normal (qc 6) (qs 6) /\\
      linside %s (&2) (&2) /\\
      qv 6 + qa 6 <= ABT_lower %s (--(qs 6)) (qc 6)
      ==> F"
   C977CI_QHYP (c977wc_sq 5) (c977ci_q 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [5; 6] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal ((qc:num->real) 5) ((qs:num->real) 5)`)) THEN
  MP_TAC(SPECL ([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] @
                c977ci_qt 5) C977CC_FRAME_CAPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c977cc_normal ((qc:num->real) 5) ((qs:num->real) 5)` THEN
    REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  C977CI_FACTS_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "~linside %s (&3) (&1)" (c977wc_sq 6))) ASSUME_TAC THENL
   [C977RCS_MISSING_TAC 6 2 C977RCS_SOUTHEAST_CORNER (`&3`, `&1`); ALL_TAC] THEN
  C977CI_SUBST_TAC THEN MATCH_MP_TAC (SPECL (c977ci_ql 5 @ c977ci_ql 6) CPTR_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive_right_alternatives *)
let C977CI_POSITIVE_RIGHT_ALTERNATIVES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\ %s /\\
      c977cc_normal (qc 5) (qs 5) /\\ linside %s (&2) (&2)
      ==> qu 5 + qa 5 <= ABT_lower %s (qc 5) (qs 5) \\/
          ABT_upper %s (qc 6) (qs 6) <= qu 6"
   C977CI_QHYP C977CI_CANON (c977wc_sq 5) (c977ci_q 6) (c977ci_q 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C977CI_FRAME_COVER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(DISJ_CASES_TAC) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN
  MATCH_MP_TAC C977CI_POSITIVE_RIGHT_TRANSVERSE_EXCLUDES THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                        `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`] THEN
  ASM_REWRITE_TAC[] THEN C977CI_INST_TAC [6] THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;
