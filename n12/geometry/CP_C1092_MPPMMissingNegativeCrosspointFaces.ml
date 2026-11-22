(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointFaces.lean  *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointGeometry; Lean header:      *)
(* "Source only").  The negative missing-successor profile in the common     *)
(* chart.  Squares E = cE sE uE vE aE and B = cB sB uB vB aB with their      *)
(* OpenSquare invariants as hypotheses.  RecipientInput / RecipientFaces:    *)
(* c1092mncf_recipientInput / c1092mncf_recipientFaces.  The triple          *)
(* MMMPEndingAxes.clockwise of E is (cE, sE, vE, --uE - aE, aE)              *)
(* (C1092MNCF_INSIDE_TRIPLE).  MissingNegativeProfile Core / strong_profile /*)
(* StrongFaces.sine_lower: c1092mnpg_core / C1092MNPG_STRONG_PROFILE /       *)
(* C1092MNA_STRONGFACES_SINE_LOWER.  Tag C1092MNCF_.                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMMissingNegativeActual.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointScalars.ml";;

(* Lean: RecipientInput (structure) *)
let c1092mncf_recipientInput = new_definition
 `c1092mncf_recipientInput cE sE uE vE aE (cB:real) (sB:real) (uB:real) (vB:real) (aB:real) <=>
    &1 < aE /\ c977cc_normal cE (--sE) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    linside cE sE uE vE aE (&1 / &2) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (--(&1)) /\
    ~linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
    (forall y. --(&14 / &25) <= y ==> y <= --(&13 / &50) ==> ~linside cE sE uE vE aE (&1) y) /\
    linside cB sB uB vB aB (&0) (--(&1)) /\
    ldisj cB sB uB vB aB cE sE uE vE aE`;;

(* Lean: RecipientFaces (structure) *)
let c1092mncf_recipientFaces = new_definition
 `c1092mncf_recipientFaces c s u v a <=>
    --(&13 / &50) * s <= u /\ u + a <= c - s /\
    --c <= v /\ v + a <= --s - (&14 / &25) * c /\
    s < &0 /\ &252 / &373 <= --s`;;

let C1092MNCF_INSIDE_TRIPLE = prove
 (`forall c s u v a x y. linside c s v (--u - a) a x y <=> linside c s u v a (--y) x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: recipient_faces *)
let C1092MNCF_RECIPIENT_FACES = prove
 (`forall cE sE uE vE aE cB sB uB vB aB.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092mncf_recipientInput cE sE uE vE aE cB sB uB vB aB
     ==> c1092mncf_recipientFaces cE sE uE vE aE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mncf_recipientInput] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c1092mnpg_core cE sE vE (--uE - aE) aE` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mnpg_core; C1092MNCF_INSIDE_TRIPLE] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~linside cE sE vE (--uE - aE) aE (--(&1)) (&0)` ASSUME_TAC THENL
   [REWRITE_TAC[C1092MNCF_INSIDE_TRIPLE] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `ldisj cB sB uB vB aB cE sE uE vE aE` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `--(&1)`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `vE:real`; `--uE - aE`; `aE:real`] C1092MNPG_STRONG_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `vE:real`; `--uE - aE`; `aE:real`] C1092MNA_STRONGFACES_SINE_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `c1092mnpg_strong_faces cE sE vE (--uE - aE) aE` THEN
  REWRITE_TAC[c1092mnpg_strong_faces; c1092mnpg_faces; c1092mncf_recipientFaces] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
