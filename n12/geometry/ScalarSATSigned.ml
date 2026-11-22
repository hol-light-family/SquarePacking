(* ========================================================================= *)
(* Port of Compact/Geometry/ScalarSATSigned.lean (N12Compact.SATSigned).     *)
(* Scalar SAT for an arbitrary relative orientation (half-side 1).          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ScalarSATPositive.ml";;

(* Lean: Overlap *)
let SSS_overlap = new_definition
 `SSS_overlap c s U V <=>
    exists x y:real. abs x < &1 /\ abs y < &1 /\
               abs(c * x + s * y - U) < &1 /\ abs(--s * x + c * y - V) < &1`;;

(* Lean: flip_s *)
let SSS_FLIP_S = prove
 (`forall c s U V. SSS_overlap c (--s) U (--V) ==> SSS_overlap c s U V`,
  REWRITE_TAC[SSS_overlap] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `--y:real`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: flip_c *)
let SSS_FLIP_C = prove
 (`forall c s U V. SSS_overlap (--c) s U (--V) ==> SSS_overlap c s U V`,
  REWRITE_TAC[SSS_overlap] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`--x:real`; `y:real`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: nonneg_c_overlap *)
let SSS_NONNEG_C_OVERLAP = prove
 (`forall c s X Y U V.
     &0 <= c /\ c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < &1 + abs c + abs s /\ abs Y < &1 + abs c + abs s /\
     abs U < &1 + abs c + abs s /\ abs V < &1 + abs c + abs s
     ==> SSS_overlap c s U V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 <= s` THENL
   [REWRITE_TAC[SSS_overlap] THEN MATCH_MP_TAC SSP_NONNEGATIVE_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`X:real`; `Y:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SSS_FLIP_S THEN REWRITE_TAC[SSS_overlap] THEN
    MATCH_MP_TAC SSP_NONNEGATIVE_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`X:real`; `--Y:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC]);;

(* Lean: overlap *)
let SSS_OVERLAP = prove
 (`forall c s X Y U V.
     c pow 2 + s pow 2 = &1 /\
     U = c * X + s * Y /\ V = --s * X + c * Y /\
     abs X < &1 + abs c + abs s /\ abs Y < &1 + abs c + abs s /\
     abs U < &1 + abs c + abs s /\ abs V < &1 + abs c + abs s
     ==> SSS_overlap c s U V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `&0 <= c` THENL
   [MATCH_MP_TAC SSS_NONNEG_C_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`X:real`; `Y:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SSS_FLIP_C THEN MATCH_MP_TAC SSS_NONNEG_C_OVERLAP THEN
    MAP_EVERY EXISTS_TAC [`--X:real`; `Y:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC]);;
