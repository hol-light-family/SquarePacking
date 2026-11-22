(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedPending/UpperCenterCore.lean  *)
(* (namespace N12Compact.MergedPending).  Family-independent content of the *)
(* upper-merged center transfer.  Squares H T A O L are the tuples cH sH uH *)
(* vH aH, cT .., cA .., cO .., cL ...  The square turnFrame (antidiagonal q) *)
(* of q = (c,s,u,v,a) is (c, --s, 4c - 4s - v - a, 4c + 4s - u - a, a)      *)
(* (MPUCC_ANTIDIAGONAL: Inside x y <=> q.Inside (4-y) (4-x)); the plain      *)
(* antidiagonal T is used only through Inside / container / side, so the    *)
(* same tuple serves for L.  MergedLeftNegative.point: MLN_POINT; UpperData: *)
(* mpusc_upper_data (MPUSC_POSITIVE_IMPOSSIBLE,                              *)
(* MPUSC_NEGATIVE_CORNER_IMPOSSIBLE).                                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/MergedLeftNegative.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_UpperSectorCore.ml";;

(* Lean: inside_antidiagonal (private), composed with turnFrame_inside *)
let MPUCC_ANTIDIAGONAL = prove
 (`forall c s u v a x y.
     linside c (--s) (&4 * c - &4 * s - v - a) (&4 * c + &4 * s - u - a) a x y <=>
     linside c s u v a (&4 - y) (&4 - x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let MPUCC_ANTI_CONT = prove
 (`forall c s u v a. lcont c s u v a
     ==> lcont c (--s) (&4 * c - &4 * s - v - a) (&4 * c + &4 * s - u - a) a`,
  REWRITE_TAC[lcont; MPUCC_ANTIDIAGONAL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `linside c s u v a (&4 - y) (&4 - x)`)) THEN
  REAL_ARITH_TAC);;

(* Lean: upper_center *)
let MPUCC_UPPER_CENTER = prove
 (`forall cH sH uH vH aH cT sT uT vT aT.
     cH * cH + sH * sH = &1 /\ &0 < aH /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aH /\ aH = aT /\ lcont cT sT uT vT aT /\
     &0 < cH /\ &0 <= sH /\ sH <= cH /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     ~linside cH sH uH vH aH (&113 / &50) (&3) /\
     ~linside cH sH uH vH aH (&87 / &50) (&3) /\
     ~linside cH sH uH vH aH (&1) (&12 / &5) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&8 / &5) (&3) /\
     ldisj cH sH uH vH aH cT sT uT vT aT
     ==> linside cH sH uH vH aH (&2) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cH:real`; `--sH`; `&4 * cH - &4 * sH - vH - aH`; `&4 * cH + &4 * sH - uH - aH`;
                `aH:real`; `cT:real`; `--sT`; `&4 * cT - &4 * sT - vT - aT`;
                `&4 * cT + &4 * sT - uT - aT`; `aT:real`] MLN_POINT) THEN
  REWRITE_TAC[ldisj; MPUCC_ANTIDIAGONAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MPUCC_ANTI_CONT] THEN
    ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
    REPEAT CONJ_TAC THEN
    FIRST [RASM_ARITH_TAC; REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC];
    REWRITE_TAC[]]);;

(* Lean: southwest_upper_face *)
let MPUCC_SOUTHWEST_UPPER_FACE = prove
 (`forall cA sA uA vA aA.
     &0 < cA /\ sA < &0 /\ --sA <= cA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     ~linside cA sA uA vA aA (&2) (&2)
     ==> vA + aA <= &2 * (cA - sA)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  RASM_ARITH_TAC);;

(* Lean: UpperData.nonnegative_residue *)
let MPUCC_NONNEGATIVE_RESIDUE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL.
     lsquare cA sA uA vA aA /\ lsquare cH sH uH vH aH /\
     lsquare cO sO uO vO aO /\ lsquare cL sL uL vL aL /\
     mpusc_upper_data cA sA uA vA aA cH sH uH vH aH cO sO uO vO aO cL sL uL vL aL /\
     &0 < cA /\ abs sA <= cA /\ c977cc_normal cH sH /\
     linside cH sH uH vH aH (&2) (&2) /\ linside cA sA uA vA aA (&2) (&3 / &2)
     ==> sA < &0 /\ linside cO sO uO vO aO (&1) (&1) /\ vA + aA <= &2 * (cA - sA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let vs = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`; `cH:real`; `sH:real`;
            `uH:real`; `vH:real`; `aH:real`; `cO:real`; `sO:real`; `uO:real`; `vO:real`;
            `aO:real`; `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] in
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[lsquare] o
    check (fun th -> concl th = `lsquare cA sA uA vA aA`)) THEN
  SUBGOAL_THEN `sA < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c977cc_normal cA sA` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL vs MPUSC_POSITIVE_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cA (--sA)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_NEG; ARITH; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linside cO sO uO vO aO (&1) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(SPECL vs MPUSC_NEGATIVE_CORNER_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MPUCC_SOUTHWEST_UPPER_FACE THEN EXISTS_TAC `uA:real` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[mpusc_upper_data; ldisj] o
    check (can (term_match [] `mpusc_upper_data a b c d e f g h i j k l m n o' p q r s t`) o
           concl)) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC THEN NO_TAC;
         DISCH_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPECL [`&2`; `&2`] o check (fun th -> concl th =
           `forall x y. ~(linside cA sA uA vA aA x y /\ linside cH sH uH vH aH x y)`)) THEN
         ASM_REWRITE_TAC[]]);;
