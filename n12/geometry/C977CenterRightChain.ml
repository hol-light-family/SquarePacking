(* ========================================================================= *)
(* Port of Compact/Bridge/C977CenterRightChain.lean                          *)
(* (N12Compact.C977CenterRightChain).  Original center-owned C977 entrance   *)
(* to the positive B/R chain.  Conventions of C977CenterIncoming.ml          *)
(* (C977CI_QHYP: the family q is qc qs qu qv qa with OpenSquare fields,      *)
(* shape and equivalent; p.square (orderedOwner p i) is c977wc_sq i).        *)
(* Lean original_apart (private) is C977CRC_APART.  CornerBudgetReach        *)
(* .upper_left: CBR_UPPER_LEFT; CentralRightChain.lower_shift /              *)
(* negative_impossible: CRCH_LOWER_SHIFT / CRCH_NEGATIVE_IMPOSSIBLE;         *)
(* strict_bounds: ABT_STRICT_BOUNDS.  Tag C977CRCH_.                         *)
(* ========================================================================= *)

needs "n12/geometry/C977RightCornerSupport.ml";;
needs "n12/geometry/C977CenterIncoming.ml";;
needs "n12/geometry/CentralRightChain.ml";;
needs "n12/geometry/CornerBudgetReach.ml";;
needs "n12/geometry/gen_bridge.ml";;

(* a seed / owned auxiliary point of slot i (code mask m) *)
let C977CRCH_SEED_TAC i m p = C977WC_TO_OO_TAC i THEN ACCEPT_TAC(C977WC_INST (oo_seed m p));;
let C977CRCH_AUX_TAC i j =
  C977WC_TO_OO_TAC i THEN REWRITE_TAC[oo_aux_point j] THEN C977WC_DOMAIN_CASES_TAC i;;

(* Lean: corner_outward *)
let C977CRCH_CORNER_OUTWARD = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> linside %s (&16 / &5) (&3)"
   C977WC_HYP (c977wc_sq 3)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&3) (&1543 / &500) /\\ linside %s (&1543 / &500) (&3) /\\
     linside %s (&12 / &5) (&3) /\\ linside %s (&3) (&12 / &5) /\\ lcont %s"
    (c977wc_sq 3) (c977wc_sq 3) (c977wc_sq 11) (c977wc_sq 10) (c977wc_sq 3))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977CRCH_SEED_TAC 3 48 (`&3`, `&1543 / &500`);
      C977CRCH_SEED_TAC 3 48 (`&1543 / &500`, `&3`);
      C977CRCH_AUX_TAC 11 7;
      C977CRCH_AUX_TAC 10 19;
      C977WC_TO_OO_TAC 3 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&12 / &5`; `&3`] (MP (C977CRC_APART_AT 3 11) (C977CI_HYPS ()))) THEN
  MP_TAC(SPECL [`&3`; `&12 / &5`] (MP (C977CRC_APART_AT 3 10) (C977CI_HYPS ()))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C977WC_FACTS_TAC 3 THEN
  let pulled = pull_params (false, true, false) (c977crc_comps 3) in
  MP_TAC(REWRITE_RULE[LINSIDE_PULLX] (SPECL pulled CBR_UPPER_LEFT)) THEN
  CONV_TAC(DEPTH_CONV (fun t ->
    if is_binop `(-):real->real->real` t && lhand t = `&4` && is_ratconst (rand t)
    then REAL_RAT_REDUCE_CONV t else failwith "")) THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC LCONT_PULLX THEN ASM_REWRITE_TAC[]]);;

(* the facts of slots 5, 6, 10 used by the chain (q side) *)
let C977CRCH_SETUP_TAC slots =
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC slots THEN
  C977CI_FACTS_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1543 / &500) (&2) /\\ linside %s (&3) (&12 / &5) /\\ lcont %s"
    (c977wc_sq 10) (c977wc_sq 10) (c977wc_sq 10))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977CRCH_SEED_TAC 10 16384 (`&1543 / &500`, `&2`);
      C977CRCH_AUX_TAC 10 19;
      C977WC_TO_OO_TAC 10 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  ASSUME_TAC(C977CI_LDISJ 6 10) THEN
  (* strict_bounds of q5 at (2, 2) in the direction of q6 *)
  MP_TAC(SPECL (c977ci_qt 5 @ [`&2`; `&2`; `(qc:num->real) 6`; `(qs:num->real) 6`]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; STRIP_TAC] THEN
  C977CI_SUBST_TAC THEN
  SUBGOAL_THEN `lcont (qc 10) (qs 10) (qu 10) (qv 10) l` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term (Printf.sprintf "lcont %s" (c977wc_sq 10)))) THEN
    REWRITE_TAC[lcont] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* Lean: frame_shift *)
let C977CRCH_FRAME_SHIFT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 6) (qs 6) /\\ c977cc_normal (qc 10) (qs 10) /\\
      linside %s (&2) (&2) /\\ linside %s (&113 / &50) (&2) /\\
      ABT_upper %s (qc 6) (qs 6) <= qu 6
      ==> &3 * qc 10 + &2 * qs 10 < qu 10"
   C977CI_QHYP (c977wc_sq 5) (c977wc_sq 6) (c977ci_q 5)),
  C977CRCH_SETUP_TAC [5; 6; 10] THEN
  ASSUME_TAC(C977RCS_MISSING_AT 10 |> fun th -> MP th (C977CI_HYPS ())) THEN
  MATCH_MP_TAC (SPECL (c977ci_ql 6 @ c977ci_ql 10) CRCH_LOWER_SHIFT) THEN
  ASM_REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: negative_frame_excludes *)
let C977CRCH_NEGATIVE_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\
      c977cc_normal (qc 6) (qs 6) /\\ c977cc_normal (qc 10) t /\\ qs 10 = --t /\\ &0 < t /\\
      linside %s (&2) (&2) /\\ linside %s (&113 / &50) (&2) /\\
      ABT_upper %s (qc 6) (qs 6) <= qu 6
      ==> F"
   C977CI_QHYP (c977wc_sq 5) (c977wc_sq 6) (c977ci_q 5)),
  C977CRCH_SETUP_TAC [5; 6; 10; 3] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1543 / &500) (&3) /\\ linside %s (&3) (&1543 / &500) /\\
     linside %s (&16 / &5) (&3) /\\ linside %s (&3) (&3)"
    (c977wc_sq 3) (c977wc_sq 3) (c977wc_sq 3) (c977wc_sq 3))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977CRCH_SEED_TAC 3 48 (`&1543 / &500`, `&3`);
      C977CRCH_SEED_TAC 3 48 (`&3`, `&1543 / &500`);
      MATCH_MP_TAC C977CRCH_CORNER_OUTWARD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC C977RCS_NORTHEAST_CORNER THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASSUME_TAC(C977CI_LDISJ 3 10) THEN
  MATCH_MP_TAC (SPECL (c977ci_ql 6 @ c977ci_ql 10 @ c977ci_ql 3 @ [`t:real`]) CRCH_NEGATIVE_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: canonical_frame_shift *)
let C977CRCH_CANONICAL_FRAME_SHIFT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 6) (qs 6) /\\ abs (qs 10) <= qc 10 /\\
      linside %s (&2) (&2) /\\ linside %s (&113 / &50) (&2) /\\
      ABT_upper %s (qc 6) (qs 6) <= qu 6
      ==> &0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 < qu 10"
   C977CI_QHYP (c977wc_sq 5) (c977wc_sq 6) (c977ci_q 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(qc:num->real) 10 * qc 10 + (qs:num->real) 10 * qs 10 = &1` ASSUME_TAC THENL
   [C977CI_INST_TAC [10] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  let vs = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
            `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`] in
  ASM_CASES_TAC `&0 <= (qs:num->real) 10` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL vs C977CRCH_FRAME_SHIFT) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    MP_TAC(SPECL (vs @ [`--(qs:num->real) 10`]) C977CRCH_NEGATIVE_FRAME_EXCLUDES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]]]);;
