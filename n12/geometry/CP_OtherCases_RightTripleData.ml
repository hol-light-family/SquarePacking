(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/RightTripleData.lean                *)
(* (N12Compact.Completion.OtherCases.RightTripleData).  The physical three-  *)
(* square entrance for the remaining negative ending.  Structures            *)
(* RightProfile / Input are the predicates ocrtd_rightprofile / ocrtd_input  *)
(* (unit normal and side positivity of the squares are separate hypotheses,  *)
(* as for the other p2 structure predicates).  NegativeTripleFaces.Data is   *)
(* ccntf_data, TopOnlyQuadrantProfile.Data is octoqp_data;                   *)
(* WallProfile.negative_frame / vertex: OCWPVG_NEGATIVE_FRAME / OCWPVG_VERTEX;*)
(* DerivedWalls.closed_affine_bound: OCDW_CLOSED_AFFINE_BOUND.  Tag OCRTD_.  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_NegativeTripleFaces.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyQuadrantScalars.ml";;
needs "n12/geometry/CP_OtherCases_DerivedWalls.ml";;

(* Lean: RightProfile (structure) *)
let ocrtd_rightprofile = new_definition
 `ocrtd_rightprofile (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    &0 < c /\ s <= &0 /\
    linside c s u v a (&1) (&0) /\
    linside c s u v a (&1) (&14 / &25) /\
    c * (u + a) - s * (v + a) <= &2`;;

(* Lean: right_frame *)
let OCRTD_RIGHT_FRAME = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     linside c s u v a (&1) (&0) /\ linside c s u v a (&1) (&14 / &25) /\
     (forall x y. linside c s u v a x y ==> x <= &2)
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y) /\
           ocrtd_rightprofile c' s' u' v' a'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCWPVG_NEGATIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  ASM_REWRITE_TAC[ocrtd_rightprofile] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`;
                `u1 + a1:real`; `v1 + a1:real`] OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`;
                `-- &1`; `&0`; `-- &2`; `&1`; `&0`;
                `c1 * (u1 + a1) - s1 * (v1 + a1)`; `s1 * (u1 + a1) + c1 * (v1 + a1)`]
    OCDW_CLOSED_AFFINE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o
      check (fun th -> can (term_match [] `forall x y. linside c s u v a x y ==> x <= &2`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Lean: Input (structure) *)
let ocrtd_input = new_definition
 `ocrtd_input (cE:real) (sE:real) (uE:real) (vE:real) (aE:real)
              (cN:real) (sN:real) (uN:real) (vN:real) (aN:real)
              (cR:real) (sR:real) (uR:real) (vR:real) (aR:real) <=>
    aE = aN /\ aE = aR /\
    ccntf_data cE sE uE vE aE (--sE) /\
    octoqp_data cN sN uN vN aN /\
    ocrtd_rightprofile cR sR uR vR aR /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (&0) /\
    linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
    linside cN sN uN vN aN (&1 / &2) (&1) /\
    linside cN sN uN vN aN (&0) (&31 / &50) /\
    (forall x y. ~(linside cE sE uE vE aE x y /\ linside cR sR uR vR aR x y)) /\
    (forall x y. ~(linside cN sN uN vN aN x y /\ linside cR sR uR vR aR x y))`;;
