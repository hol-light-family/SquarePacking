(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/UpperSectorCore.lean *)
(* (namespace N12Compact.MergedPending).  Local upper-merged reduction with  *)
(* literal physical inputs; squares A H O L are the tuples cA sA uA vA aA,   *)
(* cH .., cO .., cL ..; their OpenSquare invariants are lsquare.             *)
(* Normal c t: c977cc_normal; C868UpperPoint.point: C868UP_POINT;            *)
(* C868UpperPointNegative.point: C868UPN_POINT; SouthwestNegativeCorner.     *)
(* point: SNC_POINT; ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME.      *)
(* "?a b : OpenSquare" is an existential over two 5-tuples together with     *)
(* their OpenSquare invariants (as in ClosedFrames.ml).                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C868UpperPointNegative.ml";;
needs "n12/geometry/SouthwestNegativeCorner.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: UpperData (structure) *)
let mpusc_upper_data = new_definition
 `mpusc_upper_data (cA:real) (sA:real) (uA:real) (vA:real) (aA:real)
                   (cH:real) (sH:real) (uH:real) (vH:real) (aH:real)
                   (cO:real) (sO:real) (uO:real) (vO:real) (aO:real)
                   (cL:real) (sL:real) (uL:real) (vL:real) (aL:real) <=>
    &1 < aA /\ aA = aH /\ aO = aA /\ lcont cO sO uO vO aO /\
    linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
    linside cA sA uA vA aA (&2) (&87 / &50) /\
    linside cA sA uA vA aA (&87 / &50) (&2) /\
    linside cA sA uA vA aA (&3 / &2) (&2) /\
    linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
    linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
    linside cO sO uO vO aO (&1) (&457 / &500) /\
    linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
    (forall x. &28 / &25 <= x /\ x <= &87 / &50 ==> linside cO sO uO vO aO x (&1)) /\
    (forall y. &28 / &25 <= y /\ y <= &87 / &50 ==> linside cL sL uL vL aL (&1) y) /\
    ~linside cO sO uO vO aO (&2) (&457 / &500) /\
    ldisj cA sA uA vA aA cH sH uH vH aH /\
    ldisj cO sO uO vO aO cA sA uA vA aA /\
    ldisj cA sA uA vA aA cL sL uL vL aL /\
    ~linside cH sH uH vH aH (&87 / &50) (&3)`;;

let MPUSC_BAR_TAC = FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;;

(* Lean: UpperData.positive_impossible *)
let MPUSC_POSITIVE_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cH sH uH vH aH /\
     lsquare cO sO uO vO aO /\ lsquare cL sL uL vL aL /\
     mpusc_upper_data cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL /\
     c977cc_normal cA sA /\ c977cc_normal cH sH ==> false`,
  REWRITE_TAC[mpusc_upper_data; lsquare] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linside cO sO uO vO aO (&8 / &5) (&1) /\ linside cL sL uL vL aL (&1) (&8 / &5)`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MPUSC_BAR_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~linside cH sH uH vH aH (&87 / &50) (&3)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC C868UP_POINT THEN
  MAP_EVERY EXISTS_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `ldisj cO sO uO vO aO cA sA uA vA aA` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&8 / &5`; `&1`]) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `ldisj cA sA uA vA aA cL sL uL vL aL` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1`; `&8 / &5`]) THEN ASM_REWRITE_TAC[]]);;

(* Lean: UpperData.negative_corner_impossible *)
let MPUSC_NEGATIVE_CORNER_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cH sH uH vH aH /\
     lsquare cO sO uO vO aO /\ lsquare cL sL uL vL aL /\
     mpusc_upper_data cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL /\
     c977cc_normal cA (--sA) /\ c977cc_normal cH sH /\
     ~linside cO sO uO vO aO (&1) (&1) ==> false`,
  REWRITE_TAC[mpusc_upper_data; lsquare] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aO:real = aA`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aH`)) THEN
  SUBGOAL_THEN `linside cA sA uA vA aH (&2) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SNC_POINT THEN
    MAP_EVERY EXISTS_TAC [`cO:real`; `sO:real`; `uO:real`; `vO:real`; `aH:real`;
                          `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `--sA:real`] THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT CONJ_TAC THEN MPUSC_BAR_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~linside cH sH uH vH aH (&87 / &50) (&3)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC C868UPN_POINT THEN
  MAP_EVERY EXISTS_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aH:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: UpperData.reframe *)
let MPUSC_REFRAME = prove
 (`forall cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL
    ca sa ua va aa cb sb ub vb ab.
     mpusc_upper_data cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL /\
     aa = aA /\ ab = aH /\
     (forall x y. linside ca sa ua va aa x y <=> linside cA sA uA vA aA x y) /\
     (forall x y. linside cb sb ub vb ab x y <=> linside cH sH uH vH aH x y)
     ==> mpusc_upper_data ca sa ua va aa cb sb ub vb ab cO sO uO vO aO cL sL uL vL aL`,
  REWRITE_TAC[mpusc_upper_data; ldisj] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th)) && type_of (lhs (concl th)) = `:real`))) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: UpperResidue *)
let mpusc_upper_residue = new_definition
 `mpusc_upper_residue (cA:real) (sA:real) (uA:real) (vA:real) (aA:real)
                      (cH:real) (sH:real) (uH:real) (vH:real) (aH:real)
                      (cO:real) (sO:real) (uO:real) (vO:real) (aO:real) <=>
    exists ca sa ua va aa cb sb ub vb ab.
      ca * ca + sa * sa = &1 /\ &0 < aa /\ cb * cb + sb * sb = &1 /\ &0 < ab /\
      &0 < ca /\ abs sa <= ca /\ &0 < cb /\ abs sb <= cb /\
      aa = aA /\ ab = aH /\
      (forall x y. linside ca sa ua va aa x y <=> linside cA sA uA vA aA x y) /\
      (forall x y. linside cb sb ub vb ab x y <=> linside cH sH uH vH aH x y) /\
      (sb < &0 \/ sa < &0 /\ linside cO sO uO vO aO (&1) (&1))`;;

(* Lean: UpperData.remaining *)
let MPUSC_REMAINING = prove
 (`forall cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cH sH uH vH aH /\
     lsquare cO sO uO vO aO /\ lsquare cL sL uL vL aL /\
     mpusc_upper_data cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL
     ==> mpusc_upper_residue cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[lsquare]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aa:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[lsquare]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `ab:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aa:real = aA`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `ab:real = aH`)) THEN
  SUBGOAL_THEN `mpusc_upper_data ca sa ua va aA cb sb ub vb aH cO sO uO vO aO cL sL uL vL aL`
    ASSUME_TAC THENL
   [MATCH_MP_TAC MPUSC_REFRAME THEN
    MAP_EVERY EXISTS_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                          `cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mpusc_upper_residue] THEN
  MAP_EVERY EXISTS_TAC [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aA:real`;
                        `cb:real`; `sb:real`; `ub:real`; `vb:real`; `aH:real`] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[lsquare]) THEN
  ASM_CASES_TAC `&0 <= sb` THENL
   [ALL_TAC; DISJ1_TAC THEN RASM_ARITH_TAC] THEN
  ASM_CASES_TAC `&0 <= sa` THENL
   [MP_TAC(SPECL [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aA:real`;
                  `cb:real`; `sb:real`; `ub:real`; `vb:real`; `aH:real`;
                  `cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
       MPUSC_POSITIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[lsquare; c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  DISJ2_TAC THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`ca:real`; `sa:real`; `ua:real`; `va:real`; `aA:real`;
                `cb:real`; `sb:real`; `ub:real`; `vb:real`; `aH:real`;
                `cO:real`; `sO:real`; `uO:real`; `vO:real`; `aO:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
     MPUSC_NEGATIVE_CORNER_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[lsquare; c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  RASM_ARITH_TAC);;
