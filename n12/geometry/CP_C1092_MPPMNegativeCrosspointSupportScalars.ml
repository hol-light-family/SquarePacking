(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeCrosspointSupportScalars.lean *)
(* (N12Compact.C1092MPPMNegativeCrosspointSupport).  Literal continuous      *)
(* support expressions for STEEP-POSITIVE-NEGATIVE-WALL-SCALARS;             *)
(* definitions only, as in the Lean file.  Tag c1092mncs_.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointSupportScalars.ml";;

(* Lean: Quarter (abbrev of C1092MPPMCrosspointSupport.Quarter) *)
let c1092mncs_quarter = new_definition
 `c1092mncs_quarter (h:real) (r:real) <=> c1092mcs_quarter h r`;;

(* Lean: ell, kC, deltaC, kE, deltaE, C0, E0 (definitions) *)
let c1092mncs_ell = new_definition `c1092mncs_ell (c:real) s d t = c * t + s * d`;;
let c1092mncs_kC = new_definition `c1092mncs_kC (c:real) s h r = c * h + s * r`;;
let c1092mncs_deltaC = new_definition `c1092mncs_deltaC (c:real) s h r = c * r - s * h`;;
let c1092mncs_kE = new_definition `c1092mncs_kE (d:real) t h r = t * h + d * r`;;
let c1092mncs_deltaE = new_definition `c1092mncs_deltaE (d:real) t h r = t * r - d * h`;;
let c1092mncs_C0 = new_definition `c1092mncs_C0 (s:real) = s - &1`;;
let c1092mncs_E0 = new_definition `c1092mncs_E0 (d:real) t = (&13 / &50) * t - d`;;

(* Lean: FC (definition) *)
let c1092mncs_FC = new_definition
 `c1092mncs_FC (c:real) s h r =
    if &0 <= c1092mncs_deltaC c s h r then
      c1092mncs_deltaC c s h r * (c + s) + c1092mncs_kC c s h r * s -
      (c1092mncs_kC c s h r + c1092mncs_deltaC c s h r)
    else
      (c / &2) * c1092mncs_deltaC c s h r + c1092mncs_kC c s h r * s -
      (c1092mncs_kC c s h r - c1092mncs_deltaC c s h r)`;;

(* Lean: P, Q, P2, Q2 (definitions) *)
let c1092mncs_P = new_definition
 `c1092mncs_P (d:real) t = (&37 / &50) * d * t - (&13 / &50) * t pow 2`;;
let c1092mncs_Q = new_definition
 `c1092mncs_Q (d:real) t = &1 - (&37 / &50) * t pow 2 - (&13 / &50) * d * t`;;
let c1092mncs_P2 = new_definition
 `c1092mncs_P2 (d:real) t = d - &7 / &20 + (&61 / &100) * t pow 2 - (&13 / &20) * d * t`;;
let c1092mncs_Q2 = new_definition
 `c1092mncs_Q2 (d:real) t = -- &1 - t + (&13 / &20) * t pow 2 + (&61 / &100) * d * t`;;

(* Lean: FE (definition) *)
let c1092mncs_FE = new_definition
 `c1092mncs_FE (d:real) t h r =
    if &0 <= c1092mncs_deltaE d t h r then
      c1092mncs_P2 d t * h + c1092mncs_Q2 d t * r
    else --c1092mncs_P d t * h - c1092mncs_Q d t * r`;;

(* Lean: width (definition) *)
let c1092mncs_width = new_definition
 `c1092mncs_width (c:real) s d t h r =
    c1092mncs_ell c s d t * (h + r) +
    t * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r)) +
    s * (c1092mncs_kE d t h r + abs(c1092mncs_deltaE d t h r))`;;

(* Lean: G00, G01, G10, G11 (definitions) *)
let c1092mncs_G00 = new_definition
 `c1092mncs_G00 (c:real) s d t h r =
    c1092mncs_width c s d t h r / &2 - &2 * c1092mncs_ell c s d t -
    t * c1092mncs_C0 s - s * c1092mncs_E0 d t`;;
let c1092mncs_G01 = new_definition
 `c1092mncs_G01 (c:real) s d t h r =
    (c1092mncs_kC c s h r * (h + r) + h * (c1092mncs_kC c s h r + abs(c1092mncs_deltaC c s h r)) +
     s) / &2 -
    &2 * c1092mncs_kC c s h r - h * c1092mncs_C0 s - s * c1092mncs_FE d t h r`;;
let c1092mncs_G10 = new_definition
 `c1092mncs_G10 (c:real) s d t h r =
    (c1092mncs_kE d t h r * (h + r) + t + r * (c1092mncs_kE d t h r + abs(c1092mncs_deltaE d t h r))) /
    &2 - &2 * c1092mncs_kE d t h r - t * c1092mncs_FC c s h r - r * c1092mncs_E0 d t`;;
let c1092mncs_G11 = new_definition
 `c1092mncs_G11 (c:real) s d t h r =
    h + r - &2 - h * c1092mncs_FC c s h r - r * c1092mncs_FE d t h r`;;
