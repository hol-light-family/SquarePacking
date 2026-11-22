(* ========================================================================= *)
(* Port of Compact/Bridge/C977NortheastFarther.lean                          *)
(* (N12Compact.C977NortheastFarther; Lean header: "Source only").  Actual    *)
(* C977 northeast-pair reach for a positive canonical corner.  Conventions   *)
(* of C977CenterRightChain.ml / C977CenterIncoming.ml: p.square (orderedOwner *)
(* p i) is c977wc_sq i (side l); the family q is qc qs qu qv qa with          *)
(* C977CI_QHYP; arbitrary OpenSquares E, T are cE sE uE vE aE / cT .. aT with  *)
(* their invariants as hypotheses ((x).side = (p.square ..).side is aE = l).  *)
(* The private apart is C977CRC_APART_AT.  FrameData is c977nef_frame_data.   *)
(* Tag C977NEF_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/C977CenterRightChain.ml";;
needs "n12/geometry/C977OppositeWallCenters.ml";;
needs "n12/geometry/WallBranches.ml";;
needs "n12/geometry/UpperRightCornerTopLongitudinal.ml";;
needs "n12/geometry/UpperRightNegativeTopReach.ml";;
needs "n12/geometry/UpperRightNegativeCornerPositiveTop.ml";;
needs "n12/geometry/UpperRightNegativePairReach.ml";;
needs "n12/geometry/RightWallOuterSegment.ml";;

(* Lean: FrameData (structure) *)
let c977nef_frame_data = new_definition
 `c977nef_frame_data (cE:real) (sE:real) (uE:real) (vE:real) (aE:real)
                     (cT:real) (sT:real) (uT:real) (vT:real) (aT:real) <=>
    &1 < aE /\ aE = aT /\ lcont cE sE uE vE aE /\ lcont cT sT uT vT aT /\
    linside cE sE uE vE aE (&3) (&3) /\ linside cE sE uE vE aE (&16 / &5) (&3) /\
    ~linside cE sE uE vE aE (&3) (&12 / &5) /\
    linside cT sT uT vT aT (&2) (&1543 / &500) /\ linside cT sT uT vT aT (&12 / &5) (&3) /\
    ~linside cT sT uT vT aT (&87 / &50) (&3) /\
    ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
    ldisj cE sE uE vE aE cT sT uT vT aT`;;

let C977NEF_ET = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                  `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`];;
let C977NEF_ETL = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `l:real`;
                   `cT:real`; `sT:real`; `uT:real`; `vT:real`; `l:real`];;
let c977nef_hyp extra = Printf.sprintf
  "%s /\\
   cE * cE + sE * sE = &1 /\\ &0 < aE /\\ cT * cT + sT * sT = &1 /\\ &0 < aT /\\ %s
   aE = l /\\ aT = l /\\
   (!x y. linside cE sE uE vE aE x y <=> linside %s x y) /\\
   (!x y. linside cT sT uT vT aT x y <=> linside %s x y)"
  C977WC_HYP extra (c977wc_sq 3) (c977wc_sq 11);;

let C977NEF_APART i j =
  REWRITE_RULE[ldisj] (MP (C977CRC_APART_AT i j) (C977CI_HYPS ()));;

(* Lean: frame_data *)
let C977NEF_FRAME_DATA = prove
 (parse_term ("!c1 c2 a b l cE sE uE vE aE cT sT uT vT aT. " ^ c977nef_hyp "" ^
   " ==> c977nef_frame_data cE sE uE vE aE cT sT uT vT aT"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `aE:real = l` || concl th = `aT:real = l`))) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&3) (&3) /\\ linside %s (&16 / &5) (&3) /\\ linside %s (&3) (&12 / &5) /\\
     linside %s (&2) (&1543 / &500) /\\ linside %s (&12 / &5) (&3) /\\
     linside %s (&87 / &50) (&3) /\\ lcont %s /\\ lcont %s"
    (c977wc_sq 3) (c977wc_sq 3) (c977wc_sq 10) (c977wc_sq 11) (c977wc_sq 11) (c977wc_sq 7)
    (c977wc_sq 3) (c977wc_sq 11))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC C977RCS_NORTHEAST_CORNER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC C977CRCH_CORNER_OUTWARD THEN ASM_REWRITE_TAC[];
      C977CRCH_AUX_TAC 10 19;
      C977CRCH_SEED_TAC 11 32768 (`&2`, `&1543 / &500`);
      C977CRCH_AUX_TAC 11 7;
      C977CRCH_AUX_TAC 7 14;
      C977WC_TO_OO_TAC 3 THEN ASM_SIMP_TAC[OO_BOX];
      C977WC_TO_OO_TAC 11 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 11`] C977WB_UNUSED_MARKER_TEN) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; C977OWC_MARKER10] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN DISCH_TAC THEN
  ASSUME_TAC(C977NEF_APART 3 10) THEN ASSUME_TAC(C977NEF_APART 11 7) THEN
  ASSUME_TAC(C977NEF_APART 3 11) THEN
  ASSUME_TAC(MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE)
    (ASSUME `NPACK c1 c2 a b l`)) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "~linside %s (&3) (&12 / &5) /\\ ~linside %s (&87 / &50) (&3)"
    (c977wc_sq 3) (c977wc_sq 11))) STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`&3`; `&12 / &5`] (C977NEF_APART 3 10));
      MP_TAC(SPECL [`&87 / &50`; `&3`] (C977NEF_APART 11 7))] THEN
    MATCH_MP_TAC(TAUT `b ==> ~(a /\ b) ==> ~a`) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[c977nef_frame_data; ldisj; lcont] THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont]) THEN ASM_REWRITE_TAC[]);;

let C977NEF_DATA_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C977NEF_FRAME_DATA) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `aE:real = l` || concl th = `aT:real = l`))) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[c977nef_frame_data]);;

(* Lean: frame_point *)
let C977NEF_FRAME_POINT = prove
 (parse_term ("!c1 c2 a b l cE sE uE vE aE cT sT uT vT aT. " ^
   c977nef_hyp "c977cc_normal cE sE /\\ abs sT <= cT /\\" ^
   " ==> linside cE sE uE vE aE (&7 / &2) (&3)"),
  C977NEF_DATA_TAC THEN
  ASM_CASES_TAC `&0 <= sT` THENL
   [MATCH_MP_TAC (SPECL C977NEF_ETL URCTL_POINT);
    MATCH_MP_TAC (SPECL (C977NEF_ETL @ [`--sT:real`]) URNTR_POINT)] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* Lean: negative_frame_point *)
let C977NEF_NEGATIVE_FRAME_POINT = prove
 (parse_term ("!c1 c2 a b l cE sE uE vE aE cT sT uT vT aT. " ^
   c977nef_hyp "c977cc_normal cE (--sE) /\\ c977cc_normal cT sT /\\ linside cE sE uE vE aE (&3) (&7 / &2) /\\" ^
   " ==> linside cE sE uE vE aE (&7 / &2) (&3)"),
  C977NEF_DATA_TAC THEN
  MATCH_MP_TAC (SPECL (C977NEF_ETL @ [`--sE:real`]) URNCPT_POINT) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* Lean: negative_pair_frame_point *)
let C977NEF_NEGATIVE_PAIR_FRAME_POINT = prove
 (parse_term ("!c1 c2 a b l cE sE uE vE aE cT sT uT vT aT. " ^
   c977nef_hyp "c977cc_normal cE (--sE) /\\ c977cc_normal cT (--sT) /\\ linside cE sE uE vE aE (&3) (&7 / &2) /\\" ^
   " ==> linside cE sE uE vE aE (&7 / &2) (&3)"),
  C977NEF_DATA_TAC THEN
  MATCH_MP_TAC (SPECL (C977NEF_ETL @ [`--sE:real`; `--sT:real`]) URNPR_POINT) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* Lean: right_shift_of_farther *)
let C977NEF_RIGHT_SHIFT_OF_FARTHER = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 10) (qs 10) /\\ &3 * qc 10 + &2 * qs 10 <= qu 10 /\\
      linside %s (&7 / &2) (&3)
      ==> F" C977CI_QHYP (c977ci_q 3)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CI_INST_TAC [3; 10] THEN C977CI_SUBST_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&16 / &5) (&3) /\\ linside %s (&1543 / &500) (&2) /\\ lcont %s"
    (c977wc_sq 3) (c977wc_sq 10) (c977wc_sq 10))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC C977CRCH_CORNER_OUTWARD THEN ASM_REWRITE_TAC[];
      C977CRCH_SEED_TAC 10 16384 (`&1543 / &500`, `&2`);
      C977WC_TO_OO_TAC 10 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  ASSUME_TAC(C977NEF_APART 3 10) THEN
  ASSUME_TAC(MP (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE)
    (ASSUME `NPACK c1 c2 a b l`)) THEN
  MATCH_MP_TAC (SPECL (c977ci_ql 10 @ c977ci_ql 3) RWOS_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[ldisj; lcont] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont]) THEN ASM_REWRITE_TAC[]);;

(* Lean: right_shift_excludes *)
let C977NEF_RIGHT_SHIFT_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa. %s /\\
      c977cc_normal (qc 3) (qs 3) /\\ abs (qs 11) <= qc 11 /\\
      c977cc_normal (qc 10) (qs 10) /\\ &3 * qc 10 + &2 * qs 10 <= qu 10
      ==> F" C977CI_QHYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPEC_ALL C977NEF_RIGHT_SHIFT_OF_FARTHER) THEN ASM_REWRITE_TAC[] THEN
  C977CI_INST_TAC [3; 11] THEN
  MATCH_MP_TAC (SPECL ([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] @
    c977ci_qt 3 @ c977ci_qt 11) C977NEF_FRAME_POINT) THEN
  ASM_REWRITE_TAC[]);;
