(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeRightSeparation.lean   *)
(* (N12Compact.Completion.OtherCases.C983.NegativeRightSeparation).  The     *)
(* southeast/right separator has positive coordinates.  Squares E, R are     *)
(* cE sE uE vE aE, cR sR uR vR aR (unit normals / positive sides explicit).  *)
(* NegativeTripleFaces.Data E t = ccntf_data; RightTripleData.RightProfile = *)
(* ocrtd_rightprofile; ClosedInside = lclosed; upper / lower / strict_bounds *)
(* / closed_bounds = ABT_*; CanonicalScalars.bounds = CCCS_BOUNDS;           *)
(* WallProfile.vertex / upper_neg / lower_neg = OCWPVG_*;                    *)
(* faceSeparation_of_disjoint + separated + radii = ABT_FOUR_AXES.  The      *)
(* local `reverse` of separators is C983NRS_REVERSE.  Tag C983NRS_.          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_NegativeTripleNorthSeparation.ml";;

let C983NRS_LIN = NLIN_TAC ~deg2:false [];;

let C983NRS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC THEN
   C983NRS_LIN; ALL_TAC];;

(* Lean: southeast_vertex_coordinates *)
let C983NRS_SOUTHEAST_VERTEX_COORDINATES = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t
     ==> lclosed c s u v a (c * (u + a) + t * (v + a)) (--t * (u + a) + c * (v + a)) /\
         &1 < c * (u + a) + t * (v + a) /\
         --t * (u + a) + c * (v + a) < &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ccntf_data; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --t`)) THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [C983NRS_LIN; ALL_TAC] THEN
    UNDISCH_TAC `c * c + --t * --t = &1` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983NRS_PROD `&0 <= (c - &1) * (c + &1)` THEN
    C983NRS_PROD `&0 < t * t` THEN C983NRS_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `t < &1` ASSUME_TAC THENL [C983NRS_LIN; ALL_TAC] THEN
  C983NRS_PROD `&0 < c * ((u + a) - &1)` THEN
  C983NRS_PROD `&0 < t * (a - &1)` THEN
  SUBGOAL_THEN `&1 < c * (u + a) + t * (v + a)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [C983NRS_PROD `&0 <= t * (v - (&4 / &5 * t - c))` THEN
      C983NRS_PROD `&0 < (&1 - c) * (&4 / &5 * c + t - &1 / &5)` THEN
      SUBGOAL_THEN `c + t * (&1 + &4 / &5 * t - c) - &1 = (&1 - c) * (&4 / &5 * c + t - &1 / &5)`
        ASSUME_TAC THENL
       [UNDISCH_TAC `c * c + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      C983NRS_LIN;
      C983NRS_PROD `&0 <= t * (&1 - t * (u + a) + c * v)` THEN
      C983NRS_PROD `&0 < c * (t * (a - &1))` THEN
      C983NRS_PROD `&0 < (&1 - c) * (&1 - t)` THEN
      SUBGOAL_THEN `c * (c * (u + a) + t * (v + a)) = (u + a) + c * t * a + t * (c * v - t * (u + a))`
        ASSUME_TAC THENL
       [UNDISCH_TAC `c * c + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C983NRS_PROD `&0 <= c * (&1 - (c * (u + a) + t * (v + a)))` THEN
      C983NRS_LIN];
    ALL_TAC] THEN
  SUBGOAL_THEN `--t * (u + a) + c * (v + a) < &0` ASSUME_TAC THENL
   [C983NRS_PROD `&0 < t * ((u + a) - &1)` THEN
    C983NRS_PROD `&0 <= c * (t - (v + a))` THEN
    C983NRS_PROD `&0 < t * (&1 - c)` THEN C983NRS_LIN; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `u + a:real`; `v + a:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NRS_LIN; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `c * U - --t * H = c * U + t * H`] THEN DISCH_THEN ACCEPT_TAC);;

(* Lean: southeast_vertex *)
let C983NRS_SOUTHEAST_VERTEX = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t
     ==> exists x y. lclosed c s u v a x y /\ &1 < x /\ y < &0`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C983NRS_SOUTHEAST_VERTEX_COORDINATES) THEN
  MESON_TAC[]);;

(* Lean: cone *)
let C983NRS_CONE = prove
 (`forall cE sE uE vE aE cR sR uR vR aR t nx ny.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     ccntf_data cE sE uE vE aE t /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\ linside cR sR uR vR aR (&1) (&0) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cR sR uR vR aR nx ny
     ==> &0 < nx /\ &0 < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `&13 / &50`; `&0`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `&1`; `&0`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < nx` ASSUME_TAC THENL [C983NRS_LIN; ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`]
    C983NRS_SOUTHEAST_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `y:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `x:real`; `y:real`;
                `nx:real`; `ny:real`] ABT_CLOSED_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C983NRS_PROD `&0 < nx * (x - &1)` THEN
  C983NRS_PROD `&0 <= --ny * --y` THEN
  C983NRS_LIN);;

(* local reverse of separators *)
let C983NRS_REVERSE = prove
 (`forall cE sE uE vE aE cR sR uR vR aR nx ny.
     ABT_upper cR sR uR vR aR nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> ABT_upper cE sE uE vE aE (--nx) (--ny) <= ABT_lower cR sR uR vR aR (--nx) (--ny)`,
  REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN REAL_ARITH_TAC);;

(* Lean: separators *)
let C983NRS_SEPARATORS = prove
 (`forall cE sE uE vE aE cR sR uR vR aR t.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     aE = aR /\ ccntf_data cE sE uE vE aE t /\ ocrtd_rightprofile cR sR uR vR aR /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     ldisj cE sE uE vE aE cR sR uR vR aR
     ==> ABT_upper cE sE uE vE aE (--sE) cE <= ABT_lower cR sR uR vR aR (--sE) cE \/
         ABT_upper cE sE uE vE aE (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sE < &0` ASSUME_TAC THENL
   [UNDISCH_TAC `ccntf_data cE sE uE vE aE t` THEN REWRITE_TAC[ccntf_data] THEN
    STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o filter (not o is_eq o concl) o CONJUNCTS o
    REWRITE_RULE[ccntf_data] o check (fun th -> concl th = `ccntf_data cE sE uE vE aE t`)) THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[ocrtd_rightprofile] o
    check (fun th -> concl th = `ocrtd_rightprofile cR sR uR vR aR`)) THEN
  let tE = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
  and tR = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] in
  let cone nx ny =
    MP_TAC(SPECL (tE @ tR @ [`t:real`; nx; ny]) C983NRS_CONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
      STRIP_TAC THEN RASM_ARITH_TAC] in
  MP_TAC(SPECL (tE @ tR) ABT_FOUR_AXES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C983NRS_REVERSE th))) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         cone `cE:real` `sE:real`; cone `--cE` `--sE`; cone `sE:real` `--cE`;
         cone `cR:real` `sR:real`; cone `--cR` `--sR`; cone `sR:real` `--cR`]);;
