(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointCentralAll.lean             *)
(* (N12Compact.C1092MPPMCrosspointSupport.Central), STEEP-POSITIVE-CENTRAL-  *)
(* SCALAR section 4.  Normal is c977cc_normal; G00, k, kC, kE, deltaC,       *)
(* deltaE, C0, E0, Quarter are c1092mcs_*; aligned_C C1092MCCA_ALIGNED_C;    *)
(* aligned_E C1092MCCE_ALIGNED_E; UnitCircleChord CCUCC_*.  The Lean Bool    *)
(* arguments are HOL bools.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointCentralEndpointE.ml";;

let C1092MCAL_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MCAL_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; C1092MCAL_LP_TAC]; ALL_TAC];;

let C1092MCAL_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092MCAL_DEFS = [c1092mcs_G00; c1092mcs_k; c1092mcs_kC; c1092mcs_kE; c1092mcs_deltaC;
                      c1092mcs_deltaE; c1092mcs_C0; c1092mcs_E0];;

(* Lean: coordinateValue (private definition) *)
let c1092mcal_coordinateValue = new_definition
 `c1092mcal_coordinateValue (c:real) (s:real) (d:real) (t:real) =
    d * (&1 - c - (&543 / &500) * s) + s * (&1 - (&11 / &25) * t)`;;

(* Lean: coordinate_lower (private) *)
let C1092MCAL_COORDINATE_LOWER = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s
     ==> &1 / &3125 <= c1092mcal_coordinateValue c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092PRS_STEEP_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN C1092MCAL_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  C1092MCAL_PROD `&0 <= s * (&4 * s - &3 * c)` THEN
  SUBGOAL_THEN `c + s / &3 <= &1` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092MCAL_PROD `&0 < (c + s / &3 - &1) * (c + s / &3 + &1)` THEN C1092MCAL_LP_TAC;
   ALL_TAC] THEN
  C1092MCAL_PROD `&0 <= d * (&1 - c - (&143 / &500) * s)` THEN
  C1092MCAL_PROD `&0 <= s * t` THEN
  SUBGOAL_THEN `(&4 / &5) * d + t / &2 < &19 / &20` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092MCAL_PROD `&0 <= ((&4 / &5) * d + t / &2 - &19 / &20) * ((&4 / &5) * d + t / &2 + &19 / &20)` THEN
   C1092MCAL_PROD `&0 <= (d / &2 - (&4 / &5) * t) * (d / &2 - (&4 / &5) * t)` THEN
   C1092MCAL_LP_TAC; ALL_TAC] THEN
  C1092MCAL_PROD `&0 < s * (&19 / &20 - (&4 / &5) * d - t / &2)` THEN
  REWRITE_TAC[c1092mcal_coordinateValue] THEN C1092MCAL_LP_TAC);;

(* Lean: sign, piece, coefficientX, coefficientY, constant (private definitions) *)
let c1092mcal_sign = new_definition
 `c1092mcal_sign (b:bool) = if b then &1 else -- &1`;;
let c1092mcal_piece = new_definition
 `c1092mcal_piece b e c s d t h r =
    (c1092mcs_k c s d t * (h + r) +
     d * (c1092mcs_kC c s h r + c1092mcal_sign b * c1092mcs_deltaC c s h r) +
     s * (c1092mcs_kE d t h r + c1092mcal_sign e * c1092mcs_deltaE d t h r)) / &2 -
    &2 * c1092mcs_k c s d t - d * c1092mcs_C0 s - s * c1092mcs_E0 d t`;;
let c1092mcal_coefficientX = new_definition
 `c1092mcal_coefficientX b e (c:real) s d t =
    (c1092mcs_k c s d t + d * (c - c1092mcal_sign b * s) + s * (d - c1092mcal_sign e * t)) / &2`;;
let c1092mcal_coefficientY = new_definition
 `c1092mcal_coefficientY b e (c:real) s d t =
    (c1092mcs_k c s d t + d * (s + c1092mcal_sign b * c) + s * (t + c1092mcal_sign e * d)) / &2`;;
let c1092mcal_constant = new_definition
 `c1092mcal_constant (c:real) s d t =
    -- &2 * c1092mcs_k c s d t - d * c1092mcs_C0 s - s * c1092mcs_E0 d t`;;

(* Lean: piece_form (private) *)
let C1092MCAL_PIECE_FORM = prove
 (`forall b e c s d t h r.
     c1092mcal_piece b e c s d t h r =
     c1092mcal_constant c s d t + c1092mcal_coefficientX b e c s d t * h +
     c1092mcal_coefficientY b e c s d t * r`,
  REWRITE_TAC[c1092mcal_piece; c1092mcal_constant; c1092mcal_coefficientX;
              c1092mcal_coefficientY; c1092mcs_kC; c1092mcs_kE; c1092mcs_deltaC;
              c1092mcs_deltaE] THEN REAL_ARITH_TAC);;

(* Lean: sign_abs (private) *)
let C1092MCAL_SIGN_ABS = prove
 (`forall b x. c1092mcal_sign b * x <= abs x`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[c1092mcal_sign] THEN REAL_ARITH_TAC);;

(* Lean: piece_below (private) *)
let C1092MCAL_PIECE_BELOW = prove
 (`forall c s d t b e h r. c977cc_normal c s /\ c977cc_normal d t
     ==> c1092mcal_piece b e c s d t h r <= c1092mcs_G00 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCAL_NORMAL_TAC THEN
  REWRITE_TAC[c1092mcal_piece; c1092mcs_G00] THEN
  MP_TAC(SPECL [`b:bool`; `c1092mcs_deltaC c s h r`] C1092MCAL_SIGN_ABS) THEN
  MP_TAC(SPECL [`e:bool`; `c1092mcs_deltaE d t h r`] C1092MCAL_SIGN_ABS) THEN
  REPEAT DISCH_TAC THEN
  C1092MCAL_PROD `&0 <= d * (abs(c1092mcs_deltaC c s h r) -
                             c1092mcal_sign b * c1092mcs_deltaC c s h r)` THEN
  C1092MCAL_PROD `&0 <= s * (abs(c1092mcs_deltaE d t h r) -
                             c1092mcal_sign e * c1092mcs_deltaE d t h r)` THEN
  C1092MCAL_LP_TAC);;

(* Lean: coefficient_nonnegative (private) *)
let C1092MCAL_COEFFICIENT_NONNEGATIVE = prove
 (`forall c s d t b e. c977cc_normal c s /\ c977cc_normal d t
     ==> &0 <= c1092mcal_coefficientX b e c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MCAL_NORMAL_TAC THEN
  REWRITE_TAC[c1092mcal_coefficientX; c1092mcs_k] THEN
  C1092MCAL_PROD `&0 <= c * d` THEN C1092MCAL_PROD `&0 <= s * t` THEN
  BOOL_CASES_TAC `b:bool` THEN BOOL_CASES_TAC `e:bool` THEN
  REWRITE_TAC[c1092mcal_sign] THEN
  C1092MCAL_PROD `&0 <= d * (c - s)` THEN C1092MCAL_PROD `&0 <= s * (d - t)` THEN
  C1092MCAL_PROD `&0 <= d * (c + s)` THEN C1092MCAL_PROD `&0 <= s * (d + t)` THEN
  C1092MCAL_LP_TAC);;

(* Lean: piece_arc (private).  Lean C, S are CC, SS. *)
let C1092MCAL_PIECE_ARC = prove
 (`forall c s d t h r H R CC SS b e.
     c977cc_normal c s /\ c977cc_normal d t /\ c1092mcs_quarter h r /\
     c1092mcs_quarter H R /\ c1092mcs_quarter CC SS /\ R <= r /\ r <= SS /\
     &1 / &3125 <= c1092mcal_piece b e c s d t H R /\
     &1 / &3125 <= c1092mcal_piece b e c s d t CC SS
     ==> &1 / &3125 <= c1092mcs_G00 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `b:bool`; `e:bool`]
    C1092MCAL_COEFFICIENT_NONNEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092MCAL_PIECE_FORM; c1092mcs_quarter]) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`; `b:bool`; `e:bool`; `h:real`; `r:real`]
    C1092MCAL_PIECE_BELOW) THEN
  ASM_REWRITE_TAC[C1092MCAL_PIECE_FORM] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`H:real`; `R:real`; `CC:real`; `SS:real`; `h:real`; `r:real`;
                `c1092mcal_constant c s d t - &1 / &3125`;
                `c1092mcal_coefficientX b e c s d t`;
                `c1092mcal_coefficientY b e c s d t`] CCUCC_LINEAR_NONNEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
                  RASM_ARITH_TAC]);;

(* Lean: coordinate_zero (private) *)
let C1092MCAL_COORDINATE_ZERO = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> c1092mcal_piece false false c s d t (&1) (&0) = c1092mcal_coordinateValue c s d t`,
  REWRITE_TAC[c1092mcal_piece; c1092mcal_sign; c1092mcal_coordinateValue] THEN
  REWRITE_TAC C1092MCAL_DEFS THEN REAL_ARITH_TAC);;

(* Lean: coordinate_vertical (private) *)
let C1092MCAL_COORDINATE_VERTICAL = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t
     ==> c1092mcal_piece true true c s d t (&0) (&1) = c1092mcal_coordinateValue c s d t`,
  REWRITE_TAC[c1092mcal_piece; c1092mcal_sign; c1092mcal_coordinateValue] THEN
  REWRITE_TAC C1092MCAL_DEFS THEN REAL_ARITH_TAC);;

let C1092MCAL_AT_TAC cross =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC cross THEN ANTS_TAC THENL
  [C1092MCAL_NORMAL_TAC THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[c1092mcal_piece; c1092mcs_G00; c1092mcs_deltaC; c1092mcs_deltaE;
              REAL_ARITH `c * s - s * c = &0`; REAL_ARITH `d * t - t * d = &0`; REAL_ABS_0] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c * t - s * d ==> abs(d * s - t * c) = c * t - s * d`;
               REAL_ARITH `&0 <= d * s - t * c ==> abs(d * s - t * c) = d * s - t * c`;
               REAL_ARITH `&0 <= c * t - s * d ==> abs(c * t - s * d) = c * t - s * d`;
               REAL_ARITH `&0 <= d * s - t * c ==> abs(c * t - s * d) = d * s - t * c`] THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[c1092mcal_sign] THEN REAL_ARITH_TAC;;

(* Lean: at_C_up (private) *)
let C1092MCAL_AT_C_UP = prove
 (`forall c s d t b. c977cc_normal c s /\ c977cc_normal d t /\ t <= s
     ==> c1092mcs_G00 c s d t c s = c1092mcal_piece b true c s d t c s`,
  C1092MCAL_AT_TAC (SPECL [`d:real`; `t:real`; `c:real`; `s:real`] CCUCC_CROSS_ORDER));;

(* Lean: at_C_down (private) *)
let C1092MCAL_AT_C_DOWN = prove
 (`forall c s d t b. c977cc_normal c s /\ c977cc_normal d t /\ s <= t
     ==> c1092mcs_G00 c s d t c s = c1092mcal_piece b false c s d t c s`,
  C1092MCAL_AT_TAC (SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CCUCC_CROSS_ORDER));;

(* Lean: at_E_up (private) *)
let C1092MCAL_AT_E_UP = prove
 (`forall c s d t b. c977cc_normal c s /\ c977cc_normal d t /\ s <= t
     ==> c1092mcs_G00 c s d t d t = c1092mcal_piece true b c s d t d t`,
  C1092MCAL_AT_TAC (SPECL [`c:real`; `s:real`; `d:real`; `t:real`] CCUCC_CROSS_ORDER));;

(* Lean: at_E_down (private) *)
let C1092MCAL_AT_E_DOWN = prove
 (`forall c s d t b. c977cc_normal c s /\ c977cc_normal d t /\ t <= s
     ==> c1092mcs_G00 c s d t d t = c1092mcal_piece false b c s d t d t`,
  C1092MCAL_AT_TAC (SPECL [`d:real`; `t:real`; `c:real`; `s:real`] CCUCC_CROSS_ORDER));;

(* Lean: g00_lower *)
let C1092MCAL_G00_LOWER = prove
 (`forall c s d t h r. c977cc_normal c s /\ c977cc_normal d t /\ &3 / &5 <= s /\
                 c1092mcs_quarter h r
                 ==> &1 / &3125 <= c1092mcs_G00 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCAL_COORDINATE_LOWER) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCAL_COORDINATE_ZERO) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCAL_COORDINATE_VERTICAL) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCCA_ALIGNED_C) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCCE_ALIGNED_E) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c1092mcs_quarter c s /\ c1092mcs_quarter d t /\ c1092mcs_quarter (&1) (&0) /\
                c1092mcs_quarter (&0) (&1)` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092mcs_quarter] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
   C1092MCAL_NORMAL_TAC THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &1 /\ &0 <= r` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `c1092mcs_quarter h r` THEN REWRITE_TAC[c1092mcs_quarter; REAL_POW_2] THEN
   STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NLIN_TAC [SQ_NONNEG `h:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &3125 <= c1092mcal_piece false false c s d t (&1) (&0) /\
                &1 / &3125 <= c1092mcal_piece true true c s d t (&0) (&1)` STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  let arc x y z w b e =
    MATCH_MP_TAC C1092MCAL_PIECE_ARC THEN
    MAP_EVERY EXISTS_TAC [x; y; z; w; b; e] THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC in
  ASM_CASES_TAC `t <= s` THENL
  [MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCAL_AT_C_UP) THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCAL_AT_E_DOWN) THEN
   ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
   SUBGOAL_THEN `forall b. &1 / &3125 <= c1092mcal_piece b true c s d t c s /\
                     &1 / &3125 <= c1092mcal_piece false b c s d t d t` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `r <= t` THENL
   [arc `&1` `&0` `d:real` `t:real` `false` `false`;
    ASM_CASES_TAC `r <= s` THENL
    [arc `d:real` `t:real` `c:real` `s:real` `false` `true`;
     arc `c:real` `s:real` `&0` `&1` `true` `true`]];
   SUBGOAL_THEN `s <= t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCAL_AT_C_DOWN) THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C1092MCAL_AT_E_UP) THEN
   ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
   SUBGOAL_THEN `forall b. &1 / &3125 <= c1092mcal_piece b false c s d t c s /\
                     &1 / &3125 <= c1092mcal_piece true b c s d t d t` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `r <= s` THENL
   [arc `&1` `&0` `c:real` `s:real` `false` `false`;
    ASM_CASES_TAC `r <= t` THENL
    [arc `c:real` `s:real` `d:real` `t:real` `true` `false`;
     arc `d:real` `t:real` `&0` `&1` `true` `true`]]]);;
