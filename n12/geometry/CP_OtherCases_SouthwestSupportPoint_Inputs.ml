(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SouthwestSupportPoint/Inputs.lean   *)
(* (namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint).      *)
(* Literal centred premises of C974-C976-SW-SUPPORT-POINT Theorem 1.        *)
(* A square q is c s u v a with c * c + s * s = &1 and &0 < a.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: Input (structure) *)
let ocswsp_input = new_definition
 `ocswsp_input (c:real) s u v a <=>
    &1 < a /\
    linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
    linside c s u v a (&0) (--(&13 / &50)) /\
    linside c s u v a (--(&13 / &50)) (&0) /\
    linside c s u v a (--(&1 / &2)) (&0) /\
    linside c s u v a (&0) (--(&1 / &2)) /\
    ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
    ~linside c s u v a (&7 / &20) (--(&7 / &20)) /\
    ~linside c s u v a (&0) (--(&1)) /\
    ~linside c s u v a (--(&1)) (--(&2 / &5)) /\
    ~linside c s u v a (--(&1)) (--(&13 / &50)) /\
    (forall x. --(&1 / &2) <= x ==> x <= --(&13 / &50) ==> ~linside c s u v a x (--(&1))) /\
    (forall t. &0 <= t ==> t <= &1 ==>
         ~linside c s u v a (&7 / &20 - &9 / &100 * t) (--(&7 / &20) + &7 / &20 * t))`;;

(* Lean: Input.reframe *)
let OCSWSP_INPUT_REFRAME = prove
 (`forall c s u v a c' s' u' v' a'.
      ocswsp_input c s u v a /\ a' = a /\
      (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)
      ==> ocswsp_input c' s' u' v' a'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `ocswsp_input c s u v a` THEN ASM_REWRITE_TAC[ocswsp_input]);;
