(* ========================================================================= *)
(* Port of Compact/Geometry/CentralRightIncomingOrdered.lean (Jatloe,        *)
(* N12-jatloe; namespace N12Compact.CentralRightIncomingOrdered).  The       *)
(* incoming central-axis support comparison is homogeneous in its test      *)
(* direction.  lower is ABT_lower (ABTransverse.ml), lower_in_bands          *)
(* C977NCO_LOWER_IN_BANDS.  The Lean local abbreviations dx, dy are          *)
(* introduced as variables with their defining equations; K, H are written  *)
(* out.  The OpenSquare invariants are explicit hypotheses.  Tag CRIO_.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let CRIO_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: normal_bounds (private) *)
let CRIO_NORMAL_BOUNDS = prove
 (`forall c s. c * c + s * s = &1 /\ abs s <= c ==> &0 < c /\ c <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [ASM_CASES_TAC `&0 < c` THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `c = &0 /\ s = &0` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]]);;

(* Lean: margin (private) *)
let CRIO_MARGIN = prove
 (`forall c s C S. c * c + s * s = &1 /\ abs S <= C /\ abs s <= c /\ &0 <= S * c - C * s
     ==> (C * c + S * s) * (&3 * c + &2 * s - &1) +
         (S * c - C * s) * ((&33 / &20) * c - (&47 / &20) * s) <= &2 * (C + S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CRIO_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `--c <= s /\ s <= c /\ --C <= S /\ S <= C /\ &0 <= C` STRIP_ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists dx. dx = &1 - c - (&13 / &20) * s pow 2 + (&7 / &20) * c * s`
    (X_CHOOSE_TAC `dx:real`) THENL [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `exists dy. dy = --(&7 / &20) + (&7 / &20) * s pow 2 + (&13 / &20) * c * s - s`
    (X_CHOOSE_TAC `dy:real`) THENL [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c * dx + s * dy = c - &1` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `dx + dy = --(c + s) * (&1 - (&13 / &20) * c - (&7 / &20) * s)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  CRIO_PROD_TAC `c + s` `&1 - (&13 / &20) * c - (&7 / &20) * s` THEN
  SUBGOAL_THEN `dx + dy <= &0` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `C * dx + S * dy <= &0` ASSUME_TAC THENL
  [ASM_CASES_TAC `c:real = s` THENL
   [SUBGOAL_THEN `C:real = S` ASSUME_TAC THENL
    [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
     SUBGOAL_THEN `C <= S` ASSUME_TAC THENL [NLIN_TAC []; ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `C:real = S`)) THEN
    CRIO_PROD_TAC `C:real` `--(dx + dy)` THEN NLIN_TAC ~deg2:false [];
    SUBGOAL_THEN `&0 < c - s` ASSUME_TAC THENL
    [UNDISCH_TAC `~(c:real = s)` THEN UNDISCH_TAC `s <= c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CRIO_PROD_TAC `C - S` `&1 - c` THEN
    CRIO_PROD_TAC `S * c - C * s` `--(dx + dy)` THEN
    SUBGOAL_THEN `(c - s) * (C * dx + S * dy) =
                  (C - S) * (c - &1) + (S * c - C * s) * (dx + dy)` ASSUME_TAC THENL
    [UNDISCH_TAC `c * dx + s * dy = c - &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `(c - s) * (C * dx + S * dy) <= &0` ASSUME_TAC THENL
    [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c - s`; `C * dx + S * dy`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  SUBGOAL_THEN
   `(C * c + S * s) * (&3 * c + &2 * s - &1) +
    (S * c - C * s) * ((&33 / &20) * c - (&47 / &20) * s) - &2 * (C + S) = C * dx + S * dy`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: upper_u_bound *)
let CRIO_UPPER_U_BOUND = prove
 (`forall c s u v a C S.
     c * c + s * s = &1 /\ &0 < a /\
     abs S <= C /\ abs s <= c /\ &0 <= S * c - C * s /\ &1 <= a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     u + a <= &3 * c + &2 * s
     ==> ABT_lower c s u v a C S <= &2 * (C + S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C:real`; `S:real`] CRIO_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `abs(S * s) <= C * c` ASSUME_TAC THENL
  [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
   ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * c + S * s` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower c s u v a C S = (C * c + S * s) * u + (S * c - C * s) * v`
    SUBST1_TAC THENL
  [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   REWRITE_TAC[REAL_ARITH `--C * s + S * c = S * c - C * s`] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[linside]
    (ASSUME `linside c s u v a (&47 / &20) (&33 / &20)`)) THEN
  CRIO_PROD_TAC `C * c + S * s` `&3 * c + &2 * s - &1 - u` THEN
  CRIO_PROD_TAC `S * c - C * s` `(&33 / &20) * c - (&47 / &20) * s - v` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lower_escape_point *)
let CRIO_LOWER_ESCAPE_POINT = prove
 (`forall c s u v a C S.
     c * c + s * s = &1 /\ &0 < a /\
     abs S <= C /\ abs s <= c /\ &0 <= S * c - C * s /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&87 / &50) /\ c - &3 * s <= v /\
     &2 * (C + S) < ABT_lower c s u v a C S
     ==> linside c s u v a (&3) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `linside c s u v a (&3) (&2)` THENL
  [FIRST_ASSUM ACCEPT_TAC; MATCH_MP_TAC(TAUT `false ==> p`)] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CRIO_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `u + a <= &3 * c + &2 * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (&3) (&2)` THEN REWRITE_TAC[] THEN
   STRIP_ASSUME_TAC(REWRITE_RULE[linside]
     (ASSUME `linside c s u v a (&47 / &20) (&33 / &20)`)) THEN
   STRIP_ASSUME_TAC(REWRITE_RULE[linside]
     (ASSUME `linside c s u v a (&3) (&87 / &50)`)) THEN
   REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `C:real`; `S:real`]
    CRIO_UPPER_U_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
