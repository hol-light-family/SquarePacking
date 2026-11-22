(* ========================================================================= *)
(* Port of source/S12/AngleEnclosure.lean (Jatloe, N12-jatloe).              *)
(* Rational half-angle enclosures of a unit normal.                          *)
(* Also ports S12.first_quadrant_rational (source/S12/WallNormalBounds.lean).*)
(* An AngleEnclosure <lower,upper,c,s,outer,inner,wall> : Q^7 is the HOL     *)
(* value AngleEnc lower upper c s outer inner wall (reals; the data are      *)
(* rational literals).                                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/QuadraticInterval.ml";;

(* Lean: normalC *)
let normalC = new_definition `normalC t = (&1 - t pow 2) / (&1 + t pow 2)`;;
(* Lean: normalS *)
let normalS = new_definition `normalS t = (&2 * t) / (&1 + t pow 2)`;;

let AE_DEN_POS = prove
 (`forall t. &0 < &1 + t pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let AE_NORMAL_MUL = prove
 (`forall t. normalC t * (&1 + t pow 2) = &1 - t pow 2 /\
       normalS t * (&1 + t pow 2) = &2 * t`,
  GEN_TAC THEN REWRITE_TAC[normalC; normalS] THEN
  MP_TAC(SPEC `t:real` AE_DEN_POS) THEN CONV_TAC REAL_FIELD);;

(* Lean: normal_unit *)
let AE_NORMAL_UNIT = prove
 (`forall t. normalC t pow 2 + normalS t pow 2 = &1`,
  GEN_TAC THEN REWRITE_TAC[normalC; normalS] THEN
  MP_TAC(SPEC `t:real` AE_DEN_POS) THEN CONV_TAC REAL_FIELD);;

(* Lean: normal_nonnegative *)
let AE_NORMAL_NONNEGATIVE = prove
 (`forall t. &0 <= t /\ t <= &1 ==> &0 <= normalC t /\ &0 <= normalS t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[normalC; normalS] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POW_2] THEN
  CONJ_TAC THEN NLIN_TAC []);;

(* Lean: supportQuadratic (A := d*u-e*v, B := d*v+e*u) *)
let support_quad = new_definition
 `support_quad u v out signD signE =
    Quadratic (out + (signD * u - signE * v)) (--(&2) * (signD * v + signE * u))
              (out - (signD * u - signE * v))`;;

(* Lean: wallQuadratic *)
let wall_quad = new_definition
 `wall_quad wl = Quadratic (-- &1 - wl) (&2) (&1 - wl)`;;

(* Lean: structure AngleEnclosure *)
let angle_enc_INDUCT,angle_enc_RECURSION =
  define_type "angle_enc = AngleEnc real real real real real real real";;

let ae_lower = define `ae_lower (AngleEnc l h c s ou i w) = l`;;
let ae_upper = define `ae_upper (AngleEnc l h c s ou i w) = h`;;
let ae_c = define `ae_c (AngleEnc l h c s ou i w) = c`;;
let ae_s = define `ae_s (AngleEnc l h c s ou i w) = s`;;
let ae_outer = define `ae_outer (AngleEnc l h c s ou i w) = ou`;;
let ae_inner = define `ae_inner (AngleEnc l h c s ou i w) = i`;;
let ae_wall = define `ae_wall (AngleEnc l h c s ou i w) = w`;;
let AE_ACCESSORS = [ae_lower; ae_upper; ae_c; ae_s; ae_outer; ae_inner; ae_wall];;

(* Lean: AngleEnclosure.Check *)
let ae_check = new_definition
 `ae_check w <=>
    &0 <= ae_lower w /\ ae_upper w <= &1 /\ ae_c w pow 2 + ae_s w pow 2 = &1 /\
    &0 < ae_outer w /\ &0 < ae_inner w /\ ae_inner w * ae_outer w <= &1 /\
    quad_check_on (support_quad (ae_c w) (ae_s w) (ae_outer w) (&1) (&1)) (ae_lower w) (ae_upper w) /\
    quad_check_on (support_quad (ae_c w) (ae_s w) (ae_outer w) (&1) (-- &1)) (ae_lower w) (ae_upper w) /\
    quad_check_on (support_quad (ae_c w) (ae_s w) (ae_outer w) (-- &1) (&1)) (ae_lower w) (ae_upper w) /\
    quad_check_on (support_quad (ae_c w) (ae_s w) (ae_outer w) (-- &1) (-- &1)) (ae_lower w) (ae_upper w) /\
    quad_check_on (wall_quad (ae_wall w)) (ae_lower w) (ae_upper w)`;;

(* Lean: supportQuadratic_sound *)
let AE_SUPPORT_QUADRATIC_SOUND = prove
 (`forall u v out d e l h t.
     quad_check_on (support_quad u v out d e) l h /\ l <= t /\ t <= h
     ==> d * (u * normalC t + v * normalS t) + e * (--v * normalC t + u * normalS t) <= out`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP QI_QUADRATIC_SOUND) THEN
  REWRITE_TAC[support_quad; quad_eval] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN MATCH_MP_TAC QI_NONNEG_FACTOR THEN
  EXISTS_TAC `&1 + t pow 2` THEN REWRITE_TAC[AE_DEN_POS] THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_MUL) THEN
  SPEC_TAC(`normalC t`,`X:real`) THEN SPEC_TAC(`normalS t`,`Y:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `&0 <= x ==> x = y ==> &0 <= y`)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

(* Lean: AngleEnclosure.support *)
let AE_SUPPORT = prove
 (`forall w t. ae_check w /\ ae_lower w <= t /\ t <= ae_upper w
     ==> abs(ae_c w * normalC t + ae_s w * normalS t) +
         abs(--(ae_s w) * normalC t + ae_c w * normalS t) <= ae_outer w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ae_check] THEN STRIP_TAC THEN
  MAP_EVERY (fun (d,e) ->
    MP_TAC(SPECL [`ae_c w`; `ae_s w`; `ae_outer w`; d; e; `ae_lower w`; `ae_upper w`; `t:real`]
      AE_SUPPORT_QUADRATIC_SOUND) THEN ASM_REWRITE_TAC[])
    [`&1`,`&1`; `&1`,`-- &1`; `-- &1`,`&1`; `-- &1`,`-- &1`] THEN
  REAL_ARITH_TAC);;

(* Lean: AngleEnclosure.wall_bound *)
let AE_WALL_BOUND = prove
 (`forall w t. ae_check w /\ ae_lower w <= t /\ t <= ae_upper w
     ==> ae_wall w <= normalC t + normalS t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ae_check] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`wall_quad (ae_wall w)`; `ae_lower w`; `ae_upper w`; `t:real`]
    QI_QUADRATIC_SOUND) THEN ASM_REWRITE_TAC[wall_quad; quad_eval] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN MATCH_MP_TAC QI_NONNEG_FACTOR THEN
  EXISTS_TAC `&1 + t pow 2` THEN REWRITE_TAC[AE_DEN_POS] THEN
  MP_TAC(SPEC `t:real` AE_NORMAL_MUL) THEN
  SPEC_TAC(`normalC t`,`X:real`) THEN SPEC_TAC(`normalS t`,`Y:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH `&0 <= x ==> x = y ==> &0 <= y`)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

(* Lean: S12.first_quadrant_rational (source/S12/WallNormalBounds.lean) *)
let AE_FIRST_QUADRANT_RATIONAL = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> exists t. &0 <= t /\ t <= &1 /\
             c = (&2 * t) / (&1 + t pow 2) /\ s = (&1 - t pow 2) / (&1 + t pow 2)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `c / (&1 + s)` THEN
  SUBGOAL_THEN `&0 < &1 + s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
    NLIN_TAC []; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + (c / (&1 + s)) pow 2 = &2 / (&1 + s)` SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `&0 < &1 + s` THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `&0 < &1 + s` THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Decision procedure for AngleEnclosure.Check on rational literal data.     *)
(* ae_check_conv `ae_check (AngleEnc ...)` proves |- ae_check (AngleEnc ...) *)
(* (all arithmetic by REAL_RAT_REDUCE_CONV, checked by the kernel).          *)
(* ------------------------------------------------------------------------- *)

let AE_CHECK_RULE =
  let pre = REWRITE_CONV([ae_check; support_quad; wall_quad; quad_check_on; quad_eval] @ AE_ACCESSORS) in
  fun tm ->
    let th = (pre THENC REAL_RAT_REDUCE_CONV THENC REWRITE_CONV[]) tm in
    EQT_ELIM th;;
