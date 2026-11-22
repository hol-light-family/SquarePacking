(* ========================================================================= *)
(* Port of Compact/Bridge/C977CenterCornerAlternatives.lean                  *)
(* (N12Compact.C977CenterCornerAlternatives).  Actual original corner         *)
(* alternatives for the center-owned, B-owned incoming central axis.         *)
(* Conventions of C977CenterIncoming.ml / C977CenterRightChain.ml: the       *)
(* family q : Fin 12 -> OpenSquare is qc qs qu qv qa with C977CI_QHYP (its   *)
(* OpenSquare fields, shape and equivalent); p.square (orderedOwner p i) is  *)
(* c977wc_sq i; (q i).side is qa i; Lean upper / lower are ABT_upper /       *)
(* ABT_lower; Normal is c977cc_normal.  The private right_data / corner_data  *)
(* are the seed / pruned-domain facts of C977CRCH_SETUP_TAC and MPCCA_CORNER_ *)
(* TAC.  An arbitrary OpenSquare R is cR sR uR vR aR with its invariants as   *)
(* hypotheses.  Tag C977CCA_.                                                *)
(* ========================================================================= *)

needs "n12/geometry/C977CenterRightChain.ml";;
needs "n12/geometry/CentralRightCornerAlternatives.ml";;
needs "n12/geometry/CentralRightIncomingPositive.ml";;
needs "n12/geometry/CentralRightIncomingOrdered.ml";;

(* the corner-square (slot 3) facts and the missing southeast corner of slot 6 *)
let C977CCA_CORNER_TAC =
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1543 / &500) (&3) /\\ linside %s (&3) (&1543 / &500) /\\
     linside %s (&16 / &5) (&3) /\\ linside %s (&3) (&3)"
    (c977wc_sq 3) (c977wc_sq 3) (c977wc_sq 3) (c977wc_sq 3))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977CRCH_SEED_TAC 3 48 (`&1543 / &500`, `&3`);
      C977CRCH_SEED_TAC 3 48 (`&3`, `&1543 / &500`);
      MATCH_MP_TAC C977CRCH_CORNER_OUTWARD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC C977RCS_NORTHEAST_CORNER THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

let C977CCA_MISSING_TAC =
  SUBGOAL_THEN (parse_term (Printf.sprintf "~linside %s (&3) (&1)" (c977wc_sq 6))) ASSUME_TAC THENL
   [C977RCS_MISSING_TAC 6 2 C977RCS_SOUTHEAST_CORNER (`&3`, `&1`); ALL_TAC];;

let C977CCA_C3 = ["(a:num->real) (c977av_ordered_owner c1 c2 a b l 3)";
                  "(b:num->real) (c977av_ordered_owner c1 c2 a b l 3)"];;

(* Lean: negative_wall_point *)
let C977CCA_NEGATIVE_WALL_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cR sR uR vR aR t. %s /\\
      cR * cR + sR * sR = &1 /\\ &0 < aR /\\ c977cc_normal cR t /\\ sR = --t /\\ aR = l /\\
      (!x y. linside cR sR uR vR aR x y <=> linside %s x y)
      ==> linside cR sR uR vR aR (&3) (&2)"
   C977WC_HYP (c977wc_sq 10)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aR:real = l`)) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1543 / &500) (&2) /\\ linside %s (&3) (&12 / &5) /\\ lcont %s"
    (c977wc_sq 10) (c977wc_sq 10) (c977wc_sq 10))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977CRCH_SEED_TAC 10 16384 (`&1543 / &500`, `&2`);
      C977CRCH_AUX_TAC 10 19;
      C977WC_TO_OO_TAC 10 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  C977CCA_CORNER_TAC THEN
  ASSUME_TAC(REWRITE_RULE[ldisj] (MP (C977CRC_APART_AT 3 10) (C977CI_HYPS ()))) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "%s * %s + %s * %s = &1"
    (el 0 C977CCA_C3) (el 0 C977CCA_C3) (el 1 C977CCA_C3) (el 1 C977CCA_C3))) ASSUME_TAC THENL
   [C977WC_FACTS_TAC 3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASSUME_TAC(MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE)
    (ASSUME `NPACK c1 c2 a b l`)) THEN
  MATCH_MP_TAC (SPECL ([`cR:real`; `sR:real`; `uR:real`; `vR:real`; `l:real`] @ c977crc_comps 3 @ [`t:real`])
    PCPW_NEGATIVE_RIGHT_POINT) THEN
  ASM_REWRITE_TAC[ldisj; lcont] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont]) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let C977CCA_VS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;
let c977cca_ql i = String.concat " " (map (fun f -> Printf.sprintf "(%s %d)" f i) ["qc"; "qs"; "qu"; "qv"]) ^ " l";;

(* slot 6 owns (3, 2) (assumption, original form): R = slot 10 misses it, and the
   right wall gives the shift (nonnegative R) or a contradiction (negative R) *)
let C977CCA_WALL_TAIL_TAC =
  SUBGOAL_THEN (parse_term (Printf.sprintf "~linside %s (&3) (&2)" (c977wc_sq 10))) ASSUME_TAC THENL
   [MP_TAC(SPECL [`&3`; `&2`] (REWRITE_RULE[ldisj] (MP (C977CRC_APART_AT 6 10) (C977CI_HYPS ())))) THEN
    MATCH_MP_TAC(TAUT `a ==> ~(a /\ b) ==> ~b`) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISJ2_TAC THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 10` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC (SPECL (c977ci_ql 10) CRCA_POSITIVE_WALL_MISSING) THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL ([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] @
                  c977ci_ql 10 @ [`--(qs:num->real) 10`]) C977CCA_NEGATIVE_WALL_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]]];;

(* negative_frame_alternatives at t = --(q 6).s (helper) *)
let C977CCA_NEGATIVE_FRAME_ALTERNATIVES_AUX = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 6) (--(qs 6)) /\\ abs (qs 10) <= qc 10 /\\
      linside %s (&2) (&2) /\\ ABT_upper %s (qc 6) (qs 6) <= qu 6
      ==> qu 6 + qa 6 <= &3 * qc 6 - --(qs 6) \\/ (&0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 <= qu 10)"
   C977CI_QHYP (c977wc_sq 5) (c977ci_q 5)),
  C977CRCH_SETUP_TAC [5; 6; 10; 3] THEN C977CCA_CORNER_TAC THEN C977CCA_MISSING_TAC THEN
  ASSUME_TAC(C977CI_LDISJ 3 10) THEN
  MATCH_MP_TAC (SPECL (c977ci_ql 6 @ c977ci_ql 10 @ c977ci_ql 3 @ [`--(qs:num->real) 6`]) CRCA_ALTERNATIVES) THEN
  ASM_REWRITE_TAC[ldisj; REAL_NEG_NEG] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: negative_frame_alternatives *)
let C977CCA_NEGATIVE_FRAME_ALTERNATIVES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\
      c977cc_normal (qc 6) t /\\ qs 6 = --t /\\ abs (qs 10) <= qc 10 /\\
      linside %s (&2) (&2) /\\ ABT_upper %s (qc 6) (qs 6) <= qu 6
      ==> qu 6 + qa 6 <= &3 * qc 6 - t \\/ (&0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 <= qu 10)"
   C977CI_QHYP (c977wc_sq 5) (c977ci_q 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C977CCA_VS C977CCA_NEGATIVE_FRAME_ALTERNATIVES_AUX) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* Lean: canonical_frame_alternatives *)
let C977CCA_CANONICAL_FRAME_ALTERNATIVES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 6) <= qc 6 /\\ abs (qs 10) <= qc 10 /\\
      linside %s (&2) (&2) /\\ (&0 <= qs 6 ==> linside %s (&113 / &50) (&2)) /\\
      ABT_upper %s (qc 6) (qs 6) <= qu 6
      ==> (qs 6 <= &0 /\\ qu 6 + qa 6 <= &3 * qc 6 + qs 6) \\/
          (&0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 <= qu 10)"
   C977CI_QHYP (c977wc_sq 5) (c977wc_sq 6) (c977ci_q 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(qc:num->real) 6 * qc 6 + (qs:num->real) 6 * qs 6 = &1` ASSUME_TAC THENL
   [C977CI_INST_TAC [6] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (qs:num->real) 6` THENL
   [FIRST_X_ASSUM(fun th -> if is_imp (concl th) && lhand (concl th) = `&0 <= (qs:num->real) 6`
      then ASSUME_TAC (MP th (ASSUME `&0 <= (qs:num->real) 6`)) else NO_TAC) THEN
    MP_TAC(SPECL C977CCA_VS C977CRCH_CANONICAL_FRAME_SHIFT) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN DISJ2_TAC THEN ASM_REAL_ARITH_TAC];
    MP_TAC(SPECL (C977CCA_VS @ [`--(qs:num->real) 6`]) C977CCA_NEGATIVE_FRAME_ALTERNATIVES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN DISJ_CASES_TAC THENL
       [DISJ1_TAC THEN ASM_REAL_ARITH_TAC; DISJ2_TAC THEN ASM_REWRITE_TAC[]]]]);;

(* Lean: all_frame_alternatives *)
let C977CCA_ALL_FRAME_ALTERNATIVES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 6) <= qc 6 /\\ abs (qs 10) <= qc 10 /\\
      linside %s (&2) (&2) /\\ ABT_upper %s (qc 6) (qs 6) <= qu 6
      ==> (qs 6 < &0 /\\ qu 6 + qa 6 <= &3 * qc 6 + qs 6) \\/
          (&0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 <= qu 10)"
   C977CI_QHYP (c977wc_sq 5) (c977ci_q 5)),
  C977CRCH_SETUP_TAC [5; 6; 10; 3] THEN C977CCA_CORNER_TAC THEN C977CCA_MISSING_TAC THEN
  ASSUME_TAC(C977CI_LDISJ 3 10) THEN
  MATCH_MP_TAC (SPECL (c977ci_ql 6 @ c977ci_ql 10 @ c977ci_ql 3) CRCA_CANONICAL_ALTERNATIVES) THEN
  ASM_REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* the strict lower bound 2 (C + S) < lower B C S from the center of A and the incoming axis *)
let C977CCA_STRICT_TAC =
  SUBGOAL_THEN `linside ((qc:num->real) 5) ((qs:num->real) 5) ((qu:num->real) 5) ((qv:num->real) 5) l (&2) (&2)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "&2 * (qc 5 + qs 5) < ABT_lower %s (qc 5) (qs 5)" (c977cca_ql 6)))
    ASSUME_TAC THENL
   [UNDISCH_TAC `linside ((qc:num->real) 5) ((qs:num->real) 5) ((qu:num->real) 5) ((qv:num->real) 5) l (&2) (&2)` THEN
    UNDISCH_TAC (parse_term (Printf.sprintf "qu 5 + l <= ABT_lower %s (qc 5) (qs 5)" (c977cca_ql 6))) THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC];;

(* positive_axis_alternatives at t = --(q 6).s (helper) *)
let C977CCA_POSITIVE_AXIS_ALTERNATIVES_AUX = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 5) (qs 5) /\\ c977cc_normal (qc 6) (--(qs 6)) /\\
      abs (qs 10) <= qc 10 /\\
      linside %s (&2) (&2) /\\ qu 5 + qa 5 <= ABT_lower %s (qc 5) (qs 5)
      ==> qu 6 + qa 6 <= &3 * qc 6 - --(qs 6) \\/ (&0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 <= qu 10)"
   C977CI_QHYP (c977wc_sq 5) (c977ci_q 6)),
  C977CRCH_SETUP_TAC [5; 6; 10] THEN C977CCA_MISSING_TAC THEN C977CCA_STRICT_TAC THEN
  MP_TAC(SPECL (c977ci_ql 6 @ [`--(qs:num->real) 6`]) CRCA_CORNER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG]; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 6 @ [`--(qs:num->real) 6`; `(qc:num->real) 5`; `(qs:num->real) 5`]) CRIP_LOWER_ESCAPE_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_NEG_NEG]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977CCA_WALL_TAIL_TAC);;

(* Lean: positive_axis_alternatives *)
let C977CCA_POSITIVE_AXIS_ALTERNATIVES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\
      c977cc_normal (qc 5) (qs 5) /\\ c977cc_normal (qc 6) t /\\ qs 6 = --t /\\
      abs (qs 10) <= qc 10 /\\
      linside %s (&2) (&2) /\\ qu 5 + qa 5 <= ABT_lower %s (qc 5) (qs 5)
      ==> qu 6 + qa 6 <= &3 * qc 6 - t \\/ (&0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 <= qu 10)"
   C977CI_QHYP (c977wc_sq 5) (c977ci_q 6)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C977CCA_VS C977CCA_POSITIVE_AXIS_ALTERNATIVES_AUX) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* Lean: ordered_axis_alternatives *)
let C977CCA_ORDERED_AXIS_ALTERNATIVES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      abs (qs 5) <= qc 5 /\\ abs (qs 6) <= qc 6 /\\ abs (qs 10) <= qc 10 /\\
      &0 <= qs 5 * qc 6 - qc 5 * qs 6 /\\
      linside %s (&2) (&2) /\\ qu 5 + qa 5 <= ABT_lower %s (qc 5) (qs 5)
      ==> (qs 6 < &0 /\\ qu 6 + qa 6 <= &3 * qc 6 + qs 6) \\/
          (&0 <= qs 10 /\\ &3 * qc 10 + &2 * qs 10 <= qu 10)"
   C977CI_QHYP (c977wc_sq 5) (c977ci_q 6)),
  C977CRCH_SETUP_TAC [5; 6; 10] THEN C977CCA_MISSING_TAC THEN C977CCA_STRICT_TAC THEN
  MP_TAC(SPECL (c977ci_ql 6) CRCA_CANONICAL_CORNER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(qs:num->real) 6 < &0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL (c977ci_ql 6 @ [`(qc:num->real) 5`; `(qs:num->real) 5`]) CRIO_UPPER_U_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL (c977ci_ql 6 @ [`(qc:num->real) 5`; `(qs:num->real) 5`]) CRIO_LOWER_ESCAPE_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977CCA_WALL_TAIL_TAC);;
