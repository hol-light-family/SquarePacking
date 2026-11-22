(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingNegativeCrosspointScalars.lean *)
(* (N12Compact.C1092MPPMMissingNegativeCrosspointSupport).  Literal supports *)
(* in STEEP-POSITIVE-MISSING-NEGATIVE-WALL-SCALARS; definitions only, as in *)
(* the Lean file.  The abbrevs Quarter, ell, kC, deltaC, kE, deltaE, C0, FC, *)
(* width are the c1092mncs_* constants of                                    *)
(* CP_C1092_MPPMNegativeCrosspointSupportScalars.ml.  Tag c1092mmncs_.       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointSupportScalars.ml";;

(* Lean: E0 (definition) *)
let c1092mmncs_E0 = new_definition
 `c1092mmncs_E0 (d:real) t = t - (&14 / &25) * d - &1`;;

(* Lean: FE (definition) *)
let c1092mmncs_FE = new_definition
 `c1092mmncs_FE (d:real) t h r =
    if &0 <= c1092mncs_deltaE d t h r then
      --c1092mncs_deltaE d t h r * (&1 + (&13 / &50) * t) +
      c1092mncs_kE d t h r * c1092mmncs_E0 d t
    else --c1092mncs_deltaE d t h r * (d + t - &1) +
         c1092mncs_kE d t h r * c1092mmncs_E0 d t`;;

(* Lean: G00, G01, G10, G11 (definitions) *)
let c1092mmncs_G00 = new_definition
 `c1092mmncs_G00 (c:real) s d t h r =
    c1092mncs_width c s d t h r / &2 - &2 * c1092mncs_ell c s d t -
    t * c1092mncs_C0 s - s * c1092mmncs_E0 d t`;;
let c1092mmncs_G01 = new_definition
 `c1092mmncs_G01 (c:real) s d t h r =
    (c1092mncs_kC c s h r * (h + r) + h * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r)) +
     s) / &2 -
    &2 * c1092mncs_kC c s h r - h * c1092mncs_C0 s - s * c1092mmncs_FE d t h r`;;
let c1092mmncs_G10 = new_definition
 `c1092mmncs_G10 (c:real) s d t h r =
    (c1092mncs_kE d t h r * (h + r) + t + r * (c1092mncs_kE d t h r + abs(c1092mncs_deltaE d t h r))) /
    &2 - &2 * c1092mncs_kE d t h r - t * c1092mncs_FC c s h r - r * c1092mmncs_E0 d t`;;
let c1092mmncs_G11 = new_definition
 `c1092mmncs_G11 (c:real) s d t h r =
    h + r - &2 - h * c1092mncs_FC c s h r - r * c1092mmncs_FE d t h r`;;

(* Lean: G00star, G01star, G10star, G11star (definitions) *)
let c1092mmncs_G00star = new_definition
 `c1092mmncs_G00star epsilon (c:real) s d t h r =
    c1092mmncs_G00 c s d t h r - epsilon * s * t`;;
let c1092mmncs_G01star = new_definition
 `c1092mmncs_G01star epsilon (c:real) s d t h r =
    c1092mmncs_G01 c s d t h r - epsilon * s * h`;;
let c1092mmncs_G10star = new_definition
 `c1092mmncs_G10star epsilon (c:real) s d t h r =
    c1092mmncs_G10 c s d t h r - epsilon * s * t * c1092mncs_kC c s h r`;;
let c1092mmncs_G11star = new_definition
 `c1092mmncs_G11star epsilon (c:real) s d t h r =
    c1092mmncs_G11 c s d t h r - epsilon * s * h * c1092mncs_kC c s h r`;;
