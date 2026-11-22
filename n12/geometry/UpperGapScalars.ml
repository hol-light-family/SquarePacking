(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperGapScalars.lean (Jatloe, N12-jatloe).     *)
(* Exact C868 upper-sector scalar margins.  Normal: c977cc_normal;           *)
(* C1092WallProfileScalars.half / quarter_data: C1092WPS_half /              *)
(* C1092WPS_QUARTER_DATA.  The private firstA/firstB/secondA/secondB are     *)
(* written inline.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperGapPolynomials.ml";;

let C868GS_NORMAL_TAC =
  FIRST_X_ASSUM(fun th ->
    let th' = check (fun th -> fst(strip_comb(concl th)) = `c977cc_normal`) th in
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th') THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th'));;

let C868GS_PROD tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC];;

(* rational parametrisation: (1+x^2)^4 (1 - firstA^2 - firstB^2) *)
let C868GS_FIRST_IDENTITY = prove
 (`forall c s x. (&1 + x pow 2) * c = &1 - x pow 2 /\ (&1 + x pow 2) * s = &2 * x
     ==> (&1 + x pow 2) pow 4 *
         (&1 - (c - &2 + (&61 / &100) * c * s + (&13 / &20) * s pow 2) pow 2 -
          (--s - &33 / &50 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s) pow 2) =
         C868GP_firstPolynomial x / &10000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(&1 + x pow 2) pow 2 * (c - &2 + (&61 / &100) * c * s + (&13 / &20) * s pow 2) =
    (&1 + x pow 2) * ((&1 + x pow 2) * c) - &2 * (&1 + x pow 2) pow 2 +
    &61 / &100 * ((&1 + x pow 2) * c) * ((&1 + x pow 2) * s) +
    &13 / &20 * ((&1 + x pow 2) * s) pow 2` MP_TAC THENL
  [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(&1 + x pow 2) pow 2 *
    (--s - &33 / &50 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s) =
    --((&1 + x pow 2) * ((&1 + x pow 2) * s)) - &33 / &50 * (&1 + x pow 2) pow 2 +
    &61 / &100 * ((&1 + x pow 2) * c) pow 2 +
    &13 / &20 * ((&1 + x pow 2) * c) * ((&1 + x pow 2) * s)` MP_TAC THENL
  [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(&1 + x pow 2) pow 4 *
    (&1 - (c - &2 + (&61 / &100) * c * s + (&13 / &20) * s pow 2) pow 2 -
     (--s - &33 / &50 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s) pow 2) =
    (&1 + x pow 2) pow 4 -
    ((&1 + x pow 2) pow 2 * (c - &2 + (&61 / &100) * c * s + (&13 / &20) * s pow 2)) pow 2 -
    ((&1 + x pow 2) pow 2 *
     (--s - &33 / &50 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s)) pow 2`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[C868GP_firstPolynomial] THEN REAL_ARITH_TAC);;

let C868GS_SECOND_IDENTITY = prove
 (`forall c s x. (&1 + x pow 2) * c = &1 - x pow 2 /\ (&1 + x pow 2) * s = &2 * x
     ==> (&1 + x pow 2) pow 4 *
         (&1 - (c + s - &2 - (&13 / &25) * c * s) pow 2 -
          (c - s - &2 / &5 - (&13 / &50) * (c pow 2 - s pow 2)) pow 2) =
         C868GP_secondPolynomial x / &2500`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(&1 + x pow 2) pow 2 * (c + s - &2 - (&13 / &25) * c * s) =
    (&1 + x pow 2) * ((&1 + x pow 2) * c) + (&1 + x pow 2) * ((&1 + x pow 2) * s) -
    &2 * (&1 + x pow 2) pow 2 -
    &13 / &25 * ((&1 + x pow 2) * c) * ((&1 + x pow 2) * s)` MP_TAC THENL
  [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(&1 + x pow 2) pow 2 * (c - s - &2 / &5 - (&13 / &50) * (c pow 2 - s pow 2)) =
    (&1 + x pow 2) * ((&1 + x pow 2) * c) - (&1 + x pow 2) * ((&1 + x pow 2) * s) -
    &2 / &5 * (&1 + x pow 2) pow 2 -
    &13 / &50 * (((&1 + x pow 2) * c) pow 2 - ((&1 + x pow 2) * s) pow 2)` MP_TAC THENL
  [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(&1 + x pow 2) pow 4 *
    (&1 - (c + s - &2 - (&13 / &25) * c * s) pow 2 -
     (c - s - &2 / &5 - (&13 / &50) * (c pow 2 - s pow 2)) pow 2) =
    (&1 + x pow 2) pow 4 -
    ((&1 + x pow 2) pow 2 * (c + s - &2 - (&13 / &25) * c * s)) pow 2 -
    ((&1 + x pow 2) pow 2 * (c - s - &2 / &5 - (&13 / &50) * (c pow 2 - s pow 2))) pow 2`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[C868GP_secondPolynomial] THEN REAL_ARITH_TAC);;

(* from (1+x^2)^4 * w = p / k with 0 <= p to 0 <= w *)
let C868GS_CANCEL = prove
 (`forall w x p k. (&1 + x pow 2) pow 4 * w = p / k /\ &0 <= p /\ &0 < k ==> &0 <= w`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(CONJUNCT1 C1092WPS_CANCEL) THEN
  EXISTS_TAC `(&1 + x pow 2) pow 4` THEN CONJ_TAC THENL
  [MATCH_MP_TAC REAL_POW_LT THEN MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
   REAL_ARITH_TAC;
   ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]);;

let C868GS_QUARTER_TAC =
  FIRST_ASSUM(fun th ->
    let th' = check (fun th -> fst(strip_comb(concl th)) = `c977cc_normal`) th in
    let c,s = match snd(strip_comb(concl th')) with [c;s] -> c,s | _ -> fail() in
    MP_TAC(SPECL [c; s] C1092WPS_QUARTER_DATA) THEN
    ANTS_TAC THENL
    [MP_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th') THEN
     MP_TAC(REWRITE_RULE[c977cc_normal] th') THEN REAL_ARITH_TAC;
     STRIP_TAC]);;

(* Lean: first_disk (private) *)
let C868GS_FIRST_DISK = prove
 (`forall c s. c977cc_normal c s /\ &9 * c <= &35 * s
     ==> (c - &2 + (&61 / &100) * c * s + (&13 / &20) * s pow 2) pow 2 +
         (--s - &33 / &50 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s) pow 2 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `C1092WPS_half c s` C868GP_FIRST_POLYNOMIAL) THEN
  ASM_SIMP_TAC[C868GP_HALF_LOWER_OF_TILT; C868GP_HALF_UPPER] THEN DISCH_TAC THEN
  C868GS_QUARTER_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C1092WPS_half c s`] C868GS_FIRST_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &1 - a - b ==> a + b <= &1`) THEN
  MATCH_MP_TAC C868GS_CANCEL THEN
  MAP_EVERY EXISTS_TAC [`C1092WPS_half c s`;
    `C868GP_firstPolynomial (C1092WPS_half c s)`; `&10000`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: second_disk (private) *)
let C868GS_SECOND_DISK = prove
 (`forall c s. c977cc_normal c s /\ &1 / &8 <= C1092WPS_half c s
     ==> (c + s - &2 - (&13 / &25) * c * s) pow 2 +
         (c - s - &2 / &5 - (&13 / &50) * (c pow 2 - s pow 2)) pow 2 <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `C1092WPS_half c s` C868GP_SECOND_POLYNOMIAL) THEN
  ASM_SIMP_TAC[C868GP_HALF_UPPER] THEN DISCH_TAC THEN
  C868GS_QUARTER_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `C1092WPS_half c s`] C868GS_SECOND_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &1 - a - b ==> a + b <= &1`) THEN
  MATCH_MP_TAC C868GS_CANCEL THEN
  MAP_EVERY EXISTS_TAC [`C1092WPS_half c s`;
    `C868GP_secondPolynomial (C1092WPS_half c s)`; `&2500`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: first *)
let C868GS_FIRST = prove
 (`forall c s C t. c977cc_normal c s /\ c977cc_normal C t /\ &9 * c <= &35 * s
     ==> &0 <= &1 + C * (c - &2 + (&61 / &100) * c * s + (&13 / &20) * s pow 2) +
                t * (--s - &33 / &50 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C868GP_DISK_MARGIN THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[c977cc_normal];
   MATCH_MP_TAC C868GS_FIRST_DISK THEN ASM_REWRITE_TAC[]]);;

(* Lean: second *)
let C868GS_SECOND = prove
 (`forall c s C t. c977cc_normal c s /\ c977cc_normal C t
     ==> &0 <= &1 + C * (c + s - &2 - (&13 / &25) * c * s) +
                t * (c - s - &2 / &5 - (&13 / &50) * (c pow 2 - s pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&1 / &8 <= C1092WPS_half c s` THENL
  [MATCH_MP_TAC C868GP_DISK_MARGIN THEN CONJ_TAC THENL
   [ASM_MESON_TAC[c977cc_normal];
    MATCH_MP_TAC C868GS_SECOND_DISK THEN ASM_REWRITE_TAC[]];
   FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE])] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C868GP_CIRCLE_ARC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT C868GS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  C868GS_PROD `&0 <= c * s` THEN
  C868GS_PROD `&0 <= (&1 + c) * (&1 / &8 - C1092WPS_half c s)` THEN
  SUBGOAL_THEN `s <= &1 / &4` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&24 / &25 <= c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C868GS_PROD `&0 <= (&24 / &25 - c) * (&24 / &25 + c)` THEN
   C868GS_PROD `&0 <= s * (&1 / &4 - s)` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + (c + s - &2 - (&13 / &25) * c * s)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c - s - &2 / &5 - (&13 / &50) * (c pow 2 - s pow 2)`
    ASSUME_TAC THENL
  [C868GS_PROD `&0 <= s * s` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C868GS_PROD `&0 <= C * (&1 + (c + s - &2 - (&13 / &25) * c * s))` THEN
  C868GS_PROD `&0 <= t * (c - s - &2 / &5 - (&13 / &50) * (c pow 2 - s pow 2))` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: third *)
let C868GS_THIRD = prove
 (`forall c s C t. c977cc_normal c s /\ c977cc_normal C t /\
             &9 * c <= &35 * s /\ &13 * t <= C
     ==> &0 <= C * (c - &1 + (&61 / &100) * c * s + (&13 / &20) * s pow 2) +
                t * (--s - &13 / &25 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT C868GS_NORMAL_TAC THEN
  C868GS_PROD `&0 <= c * s` THEN
  C868GS_PROD `&0 <= c * c` THEN
  C868GS_PROD `&0 <= (&1 - c) * ((&13 / &20) * (&1 + c) - &1)` THEN
  C868GS_PROD `&0 <= s * (c - &7 / &10)` THEN
  SUBGOAL_THEN `&0 <= c - &1 + (&13 / &20) * s pow 2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c - &1 + (&61 / &100) * c * s + (&13 / &20) * s pow 2 /\
                &0 <= &13 * (c - &1 + (&61 / &100) * c * s + (&13 / &20) * s pow 2) +
                      (--s - &13 / &25 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s)`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C868GS_PROD `&0 <= (C - &13 * t) *
                 (c - &1 + (&61 / &100) * c * s + (&13 / &20) * s pow 2)` THEN
  C868GS_PROD `&0 <= t *
                 (&13 * (c - &1 + (&61 / &100) * c * s + (&13 / &20) * s pow 2) +
                  (--s - &13 / &25 + (&61 / &100) * c pow 2 + (&13 / &20) * c * s))` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: fourth *)
let C868GS_FOURTH = prove
 (`forall c s C t. c977cc_normal c s /\ c977cc_normal C t /\ &13 * t <= C
     ==> &0 <= C * (c + s - &1 - (&13 / &25) * c * s) +
                t * (c - s - (&13 / &50) * (c pow 2 - s pow 2) - &13 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C868GP_CIRCLE_ARC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT C868GS_NORMAL_TAC THEN
  C868GS_PROD `&0 <= s * (c - &7 / &10)` THEN
  C868GS_PROD `&0 <= (c - &7 / &10) * (&1 - c)` THEN
  SUBGOAL_THEN `&0 <= c + s - &1 - (&13 / &25) * c * s /\
                &0 <= &13 * (c + s - &1 - (&13 / &25) * c * s) +
                      (c - s - (&13 / &50) * (c pow 2 - s pow 2) - &13 / &50)`
    STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C868GS_PROD `&0 <= (C - &13 * t) * (c + s - &1 - (&13 / &25) * c * s)` THEN
  C868GS_PROD `&0 <= t * (&13 * (c + s - &1 - (&13 / &25) * c * s) +
                      (c - s - (&13 / &50) * (c pow 2 - s pow 2) - &13 / &50))` THEN
  NLIN_TAC ~deg2:false []);;
