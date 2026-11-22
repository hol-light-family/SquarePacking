(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCrosspointSupportScalars.lean          *)
(* (N12Compact.C1092MPPMCrosspointSupport).  Literal scalar expressions;     *)
(* definitions only, as in the Lean file.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

(* Lean: Quarter (structure) *)
let c1092mcs_quarter = new_definition
 `c1092mcs_quarter (h:real) (r:real) <=> &0 <= h /\ &0 <= r /\ h pow 2 + r pow 2 = &1`;;

(* Lean: k, kC, deltaC, kE, deltaE, C0, E0 (definitions) *)
let c1092mcs_k = new_definition `c1092mcs_k (c:real) s d t = c * d + s * t`;;
let c1092mcs_kC = new_definition `c1092mcs_kC (c:real) s h r = c * h + s * r`;;
let c1092mcs_deltaC = new_definition `c1092mcs_deltaC (c:real) s h r = c * r - s * h`;;
let c1092mcs_kE = new_definition `c1092mcs_kE (d:real) t h r = d * h + t * r`;;
let c1092mcs_deltaE = new_definition `c1092mcs_deltaE (d:real) t h r = d * r - t * h`;;
let c1092mcs_C0 = new_definition `c1092mcs_C0 (s:real) = (&543 / &500) * s - &1`;;
let c1092mcs_E0 = new_definition `c1092mcs_E0 (d:real) t = d - (&14 / &25) * t - &1`;;

(* Lean: FC (definition) *)
let c1092mcs_FC = new_definition
 `c1092mcs_FC (c:real) s h r =
    if &0 <= c1092mcs_deltaC c s h r then
      c1092mcs_deltaC c s h r * (c + s) + c1092mcs_kC c s h r * (&543 / &500) * s -
      (c1092mcs_kC c s h r + c1092mcs_deltaC c s h r)
    else
      (c / &2) * c1092mcs_deltaC c s h r + c1092mcs_kC c s h r * (&543 / &500) * s -
      (c1092mcs_kC c s h r - c1092mcs_deltaC c s h r)`;;

(* Lean: FE (definition) *)
let c1092mcs_FE = new_definition
 `c1092mcs_FE (d:real) t h r =
    if &0 <= c1092mcs_deltaE d t h r then
      c1092mcs_kE d t h r * c1092mcs_E0 d t + c1092mcs_deltaE d t h r * (--d - (&2 / &5) * t)
    else c1092mcs_kE d t h r * c1092mcs_E0 d t - (d / &2) * c1092mcs_deltaE d t h r`;;

(* Lean: G00, G01, G10, G11 (definitions) *)
let c1092mcs_G00 = new_definition
 `c1092mcs_G00 (c:real) s d t h r =
    (c1092mcs_k c s d t * (h + r) + d * (c1092mcs_kC c s h r + abs(c1092mcs_deltaC c s h r)) +
     s * (c1092mcs_kE d t h r + abs(c1092mcs_deltaE d t h r))) / &2 -
    &2 * c1092mcs_k c s d t - d * c1092mcs_C0 s - s * c1092mcs_E0 d t`;;
let c1092mcs_G01 = new_definition
 `c1092mcs_G01 (c:real) s d t h r =
    (c1092mcs_kC c s h r * (h + r) + h * (c1092mcs_kC c s h r + abs(c1092mcs_deltaC c s h r)) +
     s) / &2 -
    &2 * c1092mcs_kC c s h r - h * c1092mcs_C0 s - s * c1092mcs_FE d t h r`;;
let c1092mcs_G10 = new_definition
 `c1092mcs_G10 (c:real) s d t h r =
    (c1092mcs_kE d t h r * (h + r) + d + r * (c1092mcs_kE d t h r + abs(c1092mcs_deltaE d t h r))) /
    &2 - &2 * c1092mcs_kE d t h r - d * c1092mcs_FC c s h r - r * c1092mcs_E0 d t`;;
let c1092mcs_G11 = new_definition
 `c1092mcs_G11 (c:real) s d t h r =
    h + r - &2 - h * c1092mcs_FC c s h r - r * c1092mcs_FE d t h r`;;
