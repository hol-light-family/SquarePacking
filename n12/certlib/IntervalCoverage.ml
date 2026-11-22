(* ========================================================================= *)
(* Port of source/S12/IntervalCoverage.lean (Jatloe, N12-jatloe).            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/AngleEnclosure.ml";;

(* Lean: CoversInterval *)
let covers_interval = define
 `(covers_interval l h [] <=> false) /\
  (covers_interval l h (CONS w ws) <=>
     ae_lower w <= l /\ l <= ae_upper w /\ (h <= ae_upper w \/ covers_interval (ae_upper w) h ws))`;;

(* Lean: coversInterval_sound *)
let IC_COVERSINTERVAL_SOUND = prove
 (`forall ws lo hi x. covers_interval lo hi ws /\ lo <= x /\ x <= hi
     ==> exists w. MEM w ws /\ ae_lower w <= x /\ x <= ae_upper w`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[covers_interval; MEM] THEN
  MAP_EVERY X_GEN_TAC [`lo:real`; `hi:real`; `x:real`] THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `x <= ae_upper h` THENL
   [EXISTS_TAC `h:angle_enc` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ae_upper h`; `hi:real`; `x:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[]]);;
