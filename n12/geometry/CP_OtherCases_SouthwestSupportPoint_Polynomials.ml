(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/SouthwestSupportPoint/              *)
(* Polynomials.lean (N12Compact.Completion.OtherCases.SouthwestSupportPoint. *)
(* Polynomials).  The five quartics and their Bernstein certificates.       *)
(* BernsteinQuartic.value / positive: ccbq_value / CCBQ_POSITIVE.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_BernsteinQuartic.ml";;

(* Lean: p1 *)
let ocswspp_p1 = new_definition
 `ocswspp_p1 (t:real) = (&35 + &926 * t - &654 * t pow 2 - &11326 * t pow 3 - &8765 * t pow 4) / &100`;;
(* Lean: p2 *)
let ocswspp_p2 = new_definition
 `ocswspp_p2 (t:real) = (--(&199) + &2026 * t + &3614 * t pow 2 + &1574 * t pow 3 - &7199 * t pow 4) / &100`;;
(* Lean: p3 *)
let ocswspp_p3 = new_definition
 `ocswspp_p3 (t:real) = (&1 - &4 * t - &17 * t pow 2 + &104 * t pow 3 - &49 * t pow 4) / &25`;;
(* Lean: p4 *)
let ocswspp_p4 = new_definition
 `ocswspp_p4 (t:real) = (&35 - &206 * t + &4946 * t pow 2 + &10606 * t pow 3 - &8765 * t pow 4) / &100`;;
(* Lean: p5 *)
let ocswspp_p5 = new_definition
 `ocswspp_p5 (t:real) = (&35 - &674 * t + &1306 * t pow 2 + &11074 * t pow 3 - &8765 * t pow 4) / &100`;;

(* p t = value z b0..b4 with z = zt, then Bernstein positivity *)
let OCSWSPP_TAC pdef zt bs =
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN (mk_eq(lhand(snd(dest_forall(concl pdef))) |> (fun l -> l),
                list_mk_comb(`ccbq_value`, zt :: bs)))
    SUBST1_TAC THENL
   [REWRITE_TAC[pdef; ccbq_value] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CCBQ_POSITIVE THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REAL_ARITH_TAC;;

(* Lean: p1_positive *)
let OCSWSPP_P1_POSITIVE = prove
 (`forall t. &0 <= t /\ t <= &1 / &7 ==> &0 < ocswspp_p1 t`,
  OCSWSPP_TAC ocswspp_p1 `&7 * t`
   [`&7 / &20`; `&953 / &1400`; `&4847 / &4900`; `&167 / &140`; `&14078 / &12005`]);;

(* Lean: p2_positive *)
let OCSWSPP_P2_POSITIVE = prove
 (`forall t. &1 / &8 <= t /\ t <= &5 / &12 ==> &0 < ocswspp_p2 t`,
  OCSWSPP_TAC ocswspp_p2 `(&24 * t - &3) / &7`
   [`&458897 / &409600`; `&2008619 / &614400`; `&16363519 / &2764800`;
    `&12362191 / &1382400`; `&24250201 / &2073600`]);;

(* Lean: p3_positive *)
let OCSWSPP_P3_POSITIVE = prove
 (`forall t. &0 <= t /\ t <= &1 / &3 ==> &0 < ocswspp_p3 t`,
  OCSWSPP_TAC ocswspp_p3 `&3 * t`
   [`&1 / &25`; `&2 / &75`; `&1 / &1350`; `&1 / &1350`; `&83 / &2025`]);;

(* Lean: p4_positive *)
let OCSWSPP_P4_POSITIVE = prove
 (`forall t. &0 <= t /\ t <= &5 / &12 ==> &0 < ocswspp_p4 t`,
  OCSWSPP_TAC ocswspp_p4 `&12 / &5 * t`
   [`&7 / &20`; `&13 / &96`; `&11681 / &8640`; `&409031 / &69120`; `&5436479 / &414720`]);;

(* Lean: p5_positive *)
let OCSWSPP_P5_POSITIVE = prove
 (`forall t. &4 / &25 <= t /\ t <= &5 / &12 ==> &0 < ocswspp_p5 t`,
  OCSWSPP_TAC ocswspp_p5 `(&300 * t - &48) / &77`
   [`&16287 / &7812500`; `&10925491 / &37500000`; `&31314797 / &27000000`;
    `&24524261 / &8640000`; `&429475 / &82944`]);;
