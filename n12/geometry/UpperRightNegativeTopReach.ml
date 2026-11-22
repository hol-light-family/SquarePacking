(* ========================================================================= *)
(* Port of Compact/Geometry/UpperRightNegativeTopReach.lean (Jatloe).         *)
(* The farther northeast corner point for a positive corner E and a negative *)
(* top square T (sT = --s).                                                  *)
(* K, H, Q, F, P, L, V of the Lean proofs are written out.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperRightNegativeTopBounds.ml";;
needs "n12/geometry/UpperRightCornerLongitudinal.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let URNTR_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let URNTR_POS_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&0`; `y:real`; `k:real`] REAL_LT_LMUL_EQ) THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

let URNTR_MUL_NONPOS = prove
 (`forall a b. &0 <= a /\ b <= &0 ==> a * b <= &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:real`; `--b:real`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: top_wall *)
let URNTR_TOP_WALL = prove
 (`forall c sT u v a s. c * c + sT * sT = &1 /\ &0 < a /\ sT = --s /\ lcont c sT u v a
     ==> --s * u + c * (v + a) <= &4`,
  REWRITE_TAC[lcont] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &4 + s * u - c * (v + a) ==> --s * u + c * (v + a) <= &4`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `s + c:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + e) - --s * (v + a - e)`;
                                `--s * (u + e) + c * (v + a - e)`]) THEN
  ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
  [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: faces *)
let URNTR_FACES = prove
 (`forall c sT u v a s.
     c * c + sT * sT = &1 /\ &0 < a /\ sT = --s /\ c977cc_normal c s /\ &1 < a /\
     linside c sT u v a (&2) (&1543 / &500) /\
     linside c sT u v a (&12 / &5) (&3) /\
     ~linside c sT u v a (&87 / &50) (&3) /\
     ~linside c sT u v a (&47 / &20) (&47 / &20)
     ==> (&47 / &20) * (c + s) <= v /\
         ((&87 / &50) * c - &3 * s <= u \/ &3 * c + (&87 / &50) * s <= v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  C977CSB_NORMAL_TAC THEN
  URNTR_UNFOLD_TAC `linside c (--s) u v a (&2) (&1543 / &500)` THEN
  URNTR_UNFOLD_TAC `linside c (--s) u v a (&12 / &5) (&3)` THEN
  SUBGOAL_THEN `(&87 / &50) * c - &3 * s <= u \/ &3 * c + (&87 / &50) * s <= v`
  ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c (--s) u v a (&87 / &50) (&3)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `u + a <= (&47 / &20) * (c - s) \/ (&47 / &20) * (c + s) <= v`
  MP_TAC THENL
  [UNDISCH_TAC `~linside c (--s) u v a (&47 / &20) (&47 / &20)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&61 / &100) * c + (&13 / &20) * s < &1` ASSUME_TAC THENL
  [SUBGOAL_THEN `((&61 / &100) * c + (&13 / &20) * s) * ((&61 / &100) * c + (&13 / &20) * s)
                 <= &3973 / &5000` MP_TAC THENL
   [MP_TAC(SPEC `(&13 / &20) * c - (&61 / &100) * s` REAL_LE_SQUARE) THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SPEC_TAC(`(&61 / &100) * c + (&13 / &20) * s`,`w:real`) THEN GEN_TAC THEN
   DISCH_TAC THEN NLIN_TAC [SQ_NONNEG `w - &1`]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN RASM_ARITH_TAC);;

(* Lean: coefficients (private) *)
let URNTR_COEFFICIENTS = prove
 (`forall cE sE cT s. c977cc_normal cE sE /\ c977cc_normal cT s
     ==> &0 <= cE * cT - sE * s /\ &0 <= cE * s + sE * cT /\
         &0 < (cE * cT - sE * s) + (cE * s + sE * cT)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= cE * (cT - s) /\ &0 <= s * (cE - sE) /\ &0 <= cE * s /\
                &0 <= sE * cT /\ &0 < cE * cT /\ &0 <= sE * (cT - s)` MP_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
    MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: support_growth *)
let URNTR_SUPPORT_GROWTH = prove
 (`forall cT sT uT vT aT s e f.
     cT * cT + sT * sT = &1 /\ &0 < aT /\ sT = --s /\
     c977cc_normal e f /\ c977cc_normal cT s /\ &1 < aT /\ lcont cT sT uT vT aT /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20)
     ==> (&7 / &2) * e + &3 * f + (&3 / &5) * f < ABT_upper cT sT uT vT aT e f + aT`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`; `s:real`] URNTR_FACES) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`; `s:real`] URNTR_TOP_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `s:real`] URNTB_FORWARD_LOWER) THEN
  MP_TAC(SPECL [`e:real`; `f:real`; `cT:real`; `s:real`] URNTB_FORWARD_UPPER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= e * cT - f * s /\ &0 <= e * s + f * cT` STRIP_ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= e * (cT - s) /\ &0 <= s * (e - f) /\ &0 <= e * s /\ &0 <= f * cT`
   MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cT:real`; `--s:real`; `uT:real`; `vT:real`; `aT:real`; `s:real`;
                `e:real`; `f:real`] C977NCO_UPPER_NEGATIVE_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [SUBGOAL_THEN
    `&0 <= (e * cT - f * s) * (uT - ((&87 / &50) * cT - &3 * s)) /\
     &0 <= (e * s + f * cT) * (vT - (&47 / &20) * (cT + s)) /\
     &0 < ((e * cT - f * s) + (e * s + f * cT) + &1) * (aT - &1)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `(e * cT - f * s) * ((&87 / &50) * cT - &3 * s) +
     (e * s + f * cT) * ((&47 / &20) * (cT + s)) +
     (e * cT - f * s) + (e * s + f * cT) + &1 - ((&7 / &2) * e + &3 * f + (&3 / &5) * f) =
     &1 + e * (cT + s - &44 / &25 + (&61 / &100) * s pow 2 - (&13 / &20) * cT * s) +
     f * (cT - s - &5 / &4 + (&13 / &20) * s pow 2 + (&61 / &100) * cT * s)` MP_TAC THENL
   [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC;
   SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `s = &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `cT = &1` ASSUME_TAC THENL
    [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `c <= &1 /\ &1 <= c ==> c = &1`) THEN
     CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    UNDISCH_TAC `--s * uT + cT * (vT + aT) <= &4` THEN
    UNDISCH_TAC `&3 * cT + (&87 / &50) * s <= vT` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 < y - x ==> x < y`) THEN
   MATCH_MP_TAC URNTR_POS_OF_MUL THEN EXISTS_TAC `s:real` THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN
    `&0 <= (e * cT - f * s) * (s * uT - cT * (vT + aT) + &4) /\
     &0 <= e * (vT - (&3 * cT + (&87 / &50) * s)) /\
     &0 <= s * (e * cT - f * s) /\
     &0 < (e + s * (e * cT - f * s) + s) * (aT - &1)` MP_TAC THENL
   [SUBGOAL_THEN `&0 <= s * (e * cT - f * s)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; ASM_REWRITE_TAC[];
     MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `s * ((((e * cT - f * s) * (uT + aT) + (e * s + f * cT) * (vT + aT)) + aT) -
          ((&7 / &2) * e + &3 * f + (&3 / &5) * f)) =
     (e * cT - f * s) * (s * uT - cT * (vT + aT) + &4) +
     e * (vT - (&3 * cT + (&87 / &50) * s)) +
     (aT - &1) * (e + s * (e * cT - f * s) + s) +
     (s + e * (&1 - cT - (&44 / &25) * s + cT * s) + f * ((&2 / &5) * s - s pow 2))`
   MP_TAC THENL
   [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RASM_ARITH_TAC]);;

(* Lean: reach_faces (private) *)
let URNTR_REACH_FACES = prove
 (`forall c s u v a.
     c977cc_normal c s /\
     linside c s u v a (&3) (&3) /\ linside c s u v a (&16 / &5) (&3) /\
     ~linside c s u v a (&7 / &2) (&3)
     ==> u + a <= (&7 / &2) * c + &3 * s \/ &3 * c - (&7 / &2) * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  URNTR_UNFOLD_TAC `linside c s u v a (&3) (&3)` THEN
  URNTR_UNFOLD_TAC `linside c s u v a (&16 / &5) (&3)` THEN
  UNDISCH_TAC `~linside c s u v a (&7 / &2) (&3)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: corner_axis_impossible *)
let URNTR_CORNER_AXIS_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cT sT uT vT aT s.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     sT = --s /\ c977cc_normal cE sE /\ c977cc_normal cT s /\
     aE = aT /\ &1 < aE /\ lcont cE sE uE vE aE /\ lcont cT sT uT vT aT /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     ~linside cE sE uE vE aE (&7 / &2) (&3) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     ABT_upper cT sT uT vT aT cE sE <= uE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`;
                `cE:real`; `sE:real`] URNTR_SUPPORT_GROWTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URNTR_REACH_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C977CSB_NORMAL_TAC THEN
  STRIP_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URCL_TOP_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sE * (uE - ABT_upper cT sT uT vT aE cE sE) /\
    &0 <= cE * (vE - (&3 * cE - (&7 / &2) * sE)) /\
    &0 <= sE * ((ABT_upper cT sT uT vT aE cE sE + aE) -
                ((&7 / &2) * cE + &3 * sE + (&3 / &5) * sE)) /\
    &0 < cE * (aE - &1) /\
    &0 <= (&1 - cE) * ((&3 / &5) * cE - &2 / &5)` MP_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL;
    MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: top_axis_impossible *)
let URNTR_TOP_AXIS_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cT sT uT vT aT s.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     sT = --s /\ c977cc_normal cE sE /\ c977cc_normal cT s /\
     aE = aT /\ &1 < aE /\ lcont cE sE uE vE aE /\ lcont cT sT uT vT aT /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     ~linside cE sE uE vE aE (&3) (&12 / &5) /\
     ~linside cE sE uE vE aE (&7 / &2) (&3) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     uT + aT <= ABT_lower cE sE uE vE aE cT (--s)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`] URNTR_FACES) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`] URNTR_TOP_WALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URCL_TOP_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URCRA_LOWER_FACE) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN C977CSB_NORMAL_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `cT:real`; `s:real`] URNTR_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URNTR_REACH_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY (fun th -> MP_TAC(SPECL [`cE:real`; `sE:real`; `cT:real`; `s:real`] th))
   [URNTB_REVERSE_LOWER_UPPER; URNTB_REVERSE_UPPER_UPPER;
    URNTB_REVERSE_LOWER_LOWER; URNTB_REVERSE_UPPER_LOWER] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `ABT_lower cE sE uE vE aE cT (--s) =
                (cE * cT - sE * s) * uE - (cE * s + sE * cT) * (vE + aE)` ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   SUBGOAL_THEN `abs(cT * cE + --s * sE) = cE * cT - sE * s /\
                 abs(--cT * sE + --s * cE) = cE * s + sE * cT`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  URNTR_UNFOLD_TAC `linside cE sE uE vE aE (&3) (&3)` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `&7 / &2`)) (concl th))) THENL
  [SUBGOAL_THEN
    `aE * (&1 + (cE * cT - sE * s) + (cE * s + sE * cT)) + uT -
     (cE * cT - sE * s) * ((&7 / &2) * cE + &3 * sE) +
     (cE * s + sE * cT) * ((&12 / &5) * cE - &3 * sE) <= &0` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 <= (cE * cT - sE * s) * (((&7 / &2) * cE + &3 * sE) - uE - aE) /\
      &0 <= (cE * s + sE * cT) * (vE - ((&12 / &5) * cE - &3 * sE))` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
     can (find_term ((=) `&87 / &50`)) (concl th))) THENL
   [SUBGOAL_THEN `&0 < (&1 + (cE * cT - sE * s) + (cE * s + sE * cT)) * (aE - &1)`
    MP_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `&1 + (cE * cT - sE * s) + (cE * s + sE * cT) + ((&87 / &50) * cT - &3 * s) -
      (cE * cT - sE * s) * ((&7 / &2) * cE + &3 * sE) +
      (cE * s + sE * cT) * ((&12 / &5) * cE - &3 * sE) =
      &1 + cT * (cE + sE - &63 / &50 - cE pow 2 / &2 - (&3 / &5) * cE * sE) +
      s * (cE - sE - (&3 / &5) * cE pow 2 + cE * sE / &2)` MP_TAC THENL
    [UNDISCH_TAC `cE pow 2 + sE pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN
     `s * (aE * (&1 + (cE * cT - sE * s) + (cE * s + sE * cT)) + uT -
           (cE * cT - sE * s) * ((&7 / &2) * cE + &3 * sE) +
           (cE * s + sE * cT) * ((&12 / &5) * cE - &3 * sE)) <= &0 /\
      &0 <= cT * (vT - (&3 * cT + (&87 / &50) * s)) /\
      &0 < (cT + s * (&1 + (cE * cT - sE * s) + (cE * s + sE * cT))) * (aE - &1)`
    MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC URNTR_MUL_NONPOS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&0 <= s * (&1 + (cE * cT - sE * s) + (cE * s + sE * cT))` MP_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
     ALL_TAC] THEN
    SUBGOAL_THEN
     `cT + s * (&1 + (cE * cT - sE * s) + (cE * s + sE * cT)) +
      cT * (&3 * cT + (&87 / &50) * s) - &4 -
      s * (cE * cT - sE * s) * ((&7 / &2) * cE + &3 * sE) +
      s * (cE * s + sE * cT) * ((&12 / &5) * cE - &3 * sE) =
      cT + s - &1 +
      s * (cT * (cE + sE - &63 / &50 - cE pow 2 / &2 - (&3 / &5) * cE * sE) +
           s * (cE - sE - (&3 / &5) * cE pow 2 + cE * sE / &2))` MP_TAC THENL
    [UNDISCH_TAC `cE pow 2 + sE pow 2 = &1` THEN UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN
     CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC];
   SUBGOAL_THEN `&0 < sE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `sE = &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `cE = &1` ASSUME_TAC THENL
    [UNDISCH_TAC `cE pow 2 + sE pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
     MATCH_MP_TAC(REAL_ARITH `c <= &1 /\ &1 <= c ==> c = &1`) THEN
     CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
    UNDISCH_TAC `sE * (uE + aE) + cE * (vE + aE) <= &4` THEN
    UNDISCH_TAC `&3 * cE - (&7 / &2) * sE <= vE` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `aE * (sE + sE * (cE * cT - sE * s) + cT) + sE * uT +
     cT * (&3 * cE - (&7 / &2) * sE) - &4 * (cE * cT - sE * s) <= &0` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 <= sE * (((cE * cT - sE * s) * uE - (cE * s + sE * cT) * (vE + aE)) - (uT + aE)) /\
      &0 <= (cE * cT - sE * s) * (&4 - sE * (uE + aE) - cE * (vE + aE)) /\
      &0 <= cT * (vE - (&3 * cE - (&7 / &2) * sE))` MP_TAC THENL
    [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(cE * cT - sE * s) * cE + (cE * s + sE * cT) * sE = cT` MP_TAC THENL
    [UNDISCH_TAC `cE pow 2 + sE pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `sE * (((cE * cT - sE * s) * uE - (cE * s + sE * cT) * (vE + aE)) - (uT + aE)) +
      (cE * cT - sE * s) * (&4 - sE * (uE + aE) - cE * (vE + aE)) +
      cT * (vE - (&3 * cE - (&7 / &2) * sE)) =
      --(aE * (sE + sE * (cE * cT - sE * s) + cT) + sE * uT +
         cT * (&3 * cE - (&7 / &2) * sE) - &4 * (cE * cT - sE * s))` MP_TAC THENL
    [UNDISCH_TAC `(cE * cT - sE * s) * cE + (cE * s + sE * cT) * sE = cT` THEN
     CONV_TAC REAL_RING; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= sE * (cE * cT - sE * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
     can (find_term ((=) `&87 / &50`)) (concl th))) THENL
   [SUBGOAL_THEN
     `&0 <= sE * (uT - ((&87 / &50) * cT - &3 * s)) /\
      &0 < (sE + sE * (cE * cT - sE * s) + cT) * (aE - &1)` MP_TAC THENL
    [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `sE + sE * (cE * cT - sE * s) + cT + sE * ((&87 / &50) * cT - &3 * s) +
      cT * (&3 * cE - (&7 / &2) * sE) - &4 * (cE * cT - sE * s) =
      cT * (&1 - cE) * (&1 - sE) + sE * (&1 - (&19 / &25) * cT) + s * sE * (&1 - sE)`
    MP_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC;
    SUBGOAL_THEN
     `s * (aE * (sE + sE * (cE * cT - sE * s) + cT) + sE * uT +
           cT * (&3 * cE - (&7 / &2) * sE) - &4 * (cE * cT - sE * s)) <= &0 /\
      &0 <= (sE * cT) * (vT - (&3 * cT + (&87 / &50) * s)) /\
      &0 <= sE * (&4 + s * uT - cT * (vT + aE)) /\
      &0 < (s * (sE + sE * (cE * cT - sE * s) + cT) + sE * cT) * (aE - &1)` MP_TAC THENL
    [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC URNTR_MUL_NONPOS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `&0 <= s * (sE + sE * (cE * cT - sE * s) + cT) /\ &0 < sE * cT`
      MP_TAC THENL
      [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
       ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]; ALL_TAC] THEN
    SUBGOAL_THEN
     `s * (sE + sE * (cE * cT - sE * s) + cT) + sE * cT +
      sE * cT * (&3 * cT + (&87 / &50) * s) - &4 * sE +
      s * cT * (&3 * cE - (&7 / &2) * sE) - &4 * s * (cE * cT - sE * s) =
      cT * sE * (&1 - cT) + s * cT * (&1 - cE) * (&1 - sE) +
      s * sE * (&1 - s * sE - (&19 / &25) * cT)` MP_TAC THENL
    [UNDISCH_TAC `cT pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    RASM_ARITH_TAC]]);;

(* Lean: point *)
let URNTR_POINT = prove
 (`forall cE sE uE vE aE cT sT uT vT aT s.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     sT = --s /\ c977cc_normal cE sE /\ c977cc_normal cT s /\
     aE = aT /\ &1 < aE /\ lcont cE sE uE vE aE /\ lcont cT sT uT vT aT /\
     linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\
     ~linside cE sE uE vE aE (&3) (&12 / &5) /\
     linside cT sT uT vT aT (&2) (&1543 / &500) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ~linside cT sT uT vT aT (&87 / &50) (&3) /\
     ~linside cT sT uT vT aT (&47 / &20) (&47 / &20) /\
     ldisj cE sE uE vE aE cT sT uT vT aT
     ==> linside cE sE uE vE aE (&7 / &2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aE:real = aT`)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`]
    URNTR_CORNER_AXIS_IMPOSSIBLE) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`]
    URNTR_TOP_AXIS_IMPOSSIBLE) THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aE:real`; `s:real`] URNTR_FACES) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sT:real = --s`)) THEN
  C977CSB_NORMAL_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] URCRA_LOWER_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_conj (concl th) &&
    can (find_term ((=) `&47 / &20`)) (concl th) then ASSUME_TAC(CONJUNCT1 th)
    else NO_TAC) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let sep nx ny = SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                   `cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`; nx; ny]
                  ABT_SEPARATED in
  let sb sq x y nx ny =
    let c,s',u,v = sq in
    MP_TAC(SPECL [c; s'; u; v; `aE:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  let qE = (`cE:real`,`sE:real`,`uE:real`,`vE:real`)
  and qT = (`cT:real`,`--s:real`,`uT:real`,`vT:real`) in
  let use_sep nx ny swap radius =
    MP_TAC(sep nx ny) THEN ANTS_TAC THENL
    [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
      else ALL_TAC) THEN
     MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC[]; ALL_TAC] in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [use_sep `cE:real` `sE:real` false
     (SPECL [`cE:real`; `sE:real`; `aE:real`; `cT:real`; `--s:real`; `aE:real`]
       ABT_PARALLEL_RADIUS) THEN
   sb qE `&3` `&3` `cE:real` `sE:real` THEN
   sb qT `&2` `&1543 / &500` `cE:real` `sE:real` THEN
   DISCH_THEN DISJ_CASES_TAC THENL
   [RASM_ARITH_TAC; POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[]];
   MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                 `cT:real`; `--s:real`; `uT:real`; `vT:real`; `aE:real`]
     URCRA_NOT_CORNER_TRANSVERSE) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] ORELSE ALL_TAC) THEN
    MATCH_MP_TAC ABT_SEPARATED THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `aE:real`; `cT:real`; `--s:real`; `aE:real`]
       ABT_TRANSVERSE_RADIUS) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[]; REWRITE_TAC[]];
   use_sep `cT:real` `--s:real` true
     (SPECL [`cT:real`; `--s:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`]
       ABT_PARALLEL_RADIUS) THEN
   sb qE `&3` `&3` `cT:real` `--s:real` THEN
   sb qT `&2` `&1543 / &500` `cT:real` `--s:real` THEN
   DISCH_THEN DISJ_CASES_TAC THENL
   [RASM_ARITH_TAC; POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[]];
   use_sep `-- --s:real` `cT:real` true
     (SPECL [`cT:real`; `--s:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`]
       ABT_TRANSVERSE_RADIUS) THEN
   sb qE `&3` `&3` `-- --s:real` `cT:real` THEN
   sb qT `&12 / &5` `&3` `-- --s:real` `cT:real` THEN
   DISCH_THEN DISJ_CASES_TAC THEN RASM_ARITH_TAC]);;
