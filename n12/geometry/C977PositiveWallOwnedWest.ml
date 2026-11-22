(* ========================================================================= *)
(* Port of Compact/Bridge/C977PositiveWallOwnedWest.lean                     *)
(* (N12Compact.C977PositiveWallOwnedWest).  (Lean header: "Source only,      *)
(* uncompiled".)  The positive-wall / owned-west cell of C977.  Conventions  *)
(* of C977OuterWings.ml: p.square (orderedOwner p i) is c977wc_sq i.  The    *)
(* wall frame W : OpenSquare is cW sW uW vW aW with unit normal and positive *)
(* side; shape is aW = l.  Normal: c977cc_normal.  CornerBudgetReach.        *)
(* upper_left: CBR_UPPER_LEFT; PositiveWallOwnedWestFaces: PWOWF_ theorems;  *)
(* PositiveWallOwnedWestCorner.impossible: PWOWC_IMPOSSIBLE.  Tag C977PWOW_. *)
(* ========================================================================= *)

needs "n12/geometry/C977OuterWings.ml";;
needs "n12/geometry/CornerBudgetReach.ml";;
needs "n12/geometry/PositiveWallOwnedWestCorner.ml";;
needs "n12/geometry/PositiveWallOwnedWestFaces.ml";;
needs "n12/geometry/C977CornerReach.ml";;

(* Lean: apart (private) is C977CRC_APART *)

let C977PWOW_HYPS () = CONJ (ASSUME `NPACK c1 c2 a b l`)
  (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`);;

(* Lean: wall_high (private) *)
let C977PWOW_WALL_HIGH = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> linside %s (&1) (&12 / &5)" C977WC_HYP (c977wc_sq 8)),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> ACCEPT_TAC(CONJUNCT1(MATCH_MP C977WC_LEFT_AUXILIARY th))));;

(* Lean: corner_outward *)
let C977PWOW_CORNER_OUTWARD = prove
 (parse_term (Printf.sprintf "!c1 c2 a b l. %s ==> linside %s (&4 / &5) (&3)" C977WC_HYP (c977wc_sq 4)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&1543 / &500) /\\ linside %s (&457 / &500) (&3) /\\ lcont %s"
    (c977wc_sq 4) (c977wc_sq 4) (c977wc_sq 4))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 4 THEN ACCEPT_TAC(C977WC_INST (oo_seed 192 (`&1`, `&1543 / &500`)));
      C977WC_TO_OO_TAC 4 THEN ACCEPT_TAC(C977WC_INST (oo_seed 192 (`&457 / &500`, `&3`)));
      C977WC_TO_OO_TAC 4 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] C977OW_POINTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] C977PWOW_WALL_HIGH) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&8 / &5`; `&3`] (MP (C977CRC_APART_AT 4 7) (C977PWOW_HYPS ()))) THEN
  MP_TAC(SPECL [`&1`; `&12 / &5`] (MP (C977CRC_APART_AT 4 8) (C977PWOW_HYPS ()))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C977WC_FACTS_TAC 4 THEN
  MATCH_MP_TAC CBR_UPPER_LEFT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let C977PWOW_WHYP = Printf.sprintf
  "%s /\\ cW * cW + sW * sW = &1 /\\ &0 < aW /\\ c977cc_normal cW sW /\\ aW = l /\\
   (!x y. linside cW sW uW vW aW x y <=> linside %s x y)"
  C977WC_HYP (c977wc_sq 8);;

(* owner facts used for the wall frame *)
let C977PWOW_SETUP_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = l`)) THEN
  C977WC_FACTS_TAC 8 THEN C977WC_FACTS_TAC 4 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] C977PWOW_WALL_HIGH) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] C977PWOW_CORNER_OUTWARD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&457 / &500) (&2) /\\ ~linside %s (&457 / &500) (&3) /\\ lcont %s /\\
     linside %s (&1) (&1543 / &500) /\\ linside %s (&1) (&3)"
    (c977wc_sq 8) (c977wc_sq 8) (c977wc_sq 8) (c977wc_sq 4) (c977wc_sq 4))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 8 THEN ACCEPT_TAC(C977WC_INST (oo_seed 4096 (`&457 / &500`, `&2`)));
      C977WC_TO_OO_TAC 8 THEN MP_TAC(C977WC_INST (oo_missing 4096 7)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 8 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 4 THEN ACCEPT_TAC(C977WC_INST (oo_seed 192 (`&1`, `&1543 / &500`)));
      C977WC_TO_OO_TAC 4 THEN ACCEPT_TAC(C977WC_INST (oo_seed 192 (`&1`, `&3`)))];
    ALL_TAC] THEN
  C977WC_FACTS_TAC 1 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 1`] C977AN_CODE_TWO_ORIGINAL_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
  ASSUME_TAC(REWRITE_RULE[ASSUME (parse_term (Printf.sprintf "linside %s (&19 / &25) (&187 / &100)" (c977wc_sq 1)))]
    (SPECL [`&19 / &25`; `&187 / &100`] (MP (C977CRC_APART_AT 8 1) (C977PWOW_HYPS ())))) THEN
  ASSUME_TAC(REWRITE_RULE[ASSUME (parse_term (Printf.sprintf "linside %s (&4 / &5) (&3)" (c977wc_sq 4)))]
    (SPECL [`&4 / &5`; `&3`] (MP (C977CRC_APART_AT 8 4) (C977PWOW_HYPS ())))) THEN
  ASSUME_TAC(MP (C977CRC_APART_AT 4 8) (C977PWOW_HYPS ())) THEN
  SUBGOAL_THEN `lcont cW sW uW vW l` ASSUME_TAC THENL
   [REWRITE_TAC[lcont] THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o REWRITE_RULE[lcont] o
      check (fun th -> concl th = parse_term (Printf.sprintf "lcont %s" (c977wc_sq 8)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC];;

let C977PWOW_CLOSE_TAC =
  ASM_REWRITE_TAC[ldisj] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REAL_ARITH_TAC ORELSE
   (REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC));;

(* Lean: faces_of_missing (private) *)
let C977PWOW_FACES_OF_MISSING = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cW sW uW vW aW. %s /\\ ~linside cW sW uW vW aW (&1) (&2)
      ==> &2 * cW - sW <= vW /\\ vW + aW <= &3 * cW - (&457 / &500) * sW /\\
          &0 < sW /\\ sW < &43 / &250" C977PWOW_WHYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977PWOW_SETUP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `l:real`] PWOWF_LOWER_FACE) THEN
  ANTS_TAC THENL [C977PWOW_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `l:real`] PWOWF_UPPER_V) THEN
  ANTS_TAC THENL [C977PWOW_CLOSE_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `l:real`; `vW:real`] PWOWF_TILT) THEN
  ANTS_TAC THENL [C977PWOW_CLOSE_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[]);;

let C977PWOW_IMPOSSIBLE_TAC =
  MATCH_MP_TAC PWOWC_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC ([`cW:real`; `sW:real`; `uW:real`; `vW:real`; `l:real`] @ c977owc_comps 4) THEN
  C977PWOW_CLOSE_TAC;;

(* Lean: frame_point *)
let C977PWOW_FRAME_POINT = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cW sW uW vW aW. %s ==> linside cW sW uW vW aW (&1) (&2)" C977PWOW_WHYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C977PWOW_FACES_OF_MISSING) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C977PWOW_SETUP_TAC THEN C977PWOW_IMPOSSIBLE_TAC);;

(* Lean: frame_faces *)
let C977PWOW_FRAME_FACES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cW sW uW vW aW. %s /\\ linside %s (&1) (&2)
      ==> &2 * cW - sW <= vW /\\ vW + aW <= &3 * cW - (&457 / &500) * sW /\\
          &0 < sW /\\ sW < &43 / &250" C977PWOW_WHYP (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = l`)) THEN
  MATCH_MP_TAC C977PWOW_FACES_OF_MISSING THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `uW:real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&1`; `&2`] (MP (C977CRC_APART_AT 8 5) (C977PWOW_HYPS ()))) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: frame_excludes *)
let C977PWOW_FRAME_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cW sW uW vW aW. %s /\\ linside %s (&1) (&2) ==> F" C977PWOW_WHYP (c977wc_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C977PWOW_FRAME_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C977PWOW_SETUP_TAC THEN C977PWOW_IMPOSSIBLE_TAC);;
