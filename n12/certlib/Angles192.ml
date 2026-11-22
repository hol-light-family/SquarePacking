(* ========================================================================= *)
(* The 192 angle enclosures as one indexed family, as in Lean's              *)
(* N12Compact.C713Shared.angles : Fin 192 -> {w // w.Check}                  *)
(* (Compact/Cases/C713/SharedDictionary.lean): index < 64 is the 64-grid,    *)
(* index >= 64 is the 128-grid.  (Lean's getD default is unreachable for     *)
(* i : Fin 192.)                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/AngleData64.ml";;
needs "n12/certlib/AngleData128.ml";;

(* Lean: N12Compact.C713Shared.angles (value part) *)
let s12_angles = new_definition
 `s12_angles i = if i < 64 then EL i angles64 else EL (i - 64) angles128`;;

(* Lean: N12Compact.C713Shared.angles (property part): every enclosure is checked *)
let S12_ANGLES_CHECKED = prove
 (`forall i. i < 192 ==> ae_check (s12_angles i)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[s12_angles] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC ANGLES64_CHECKED THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ANGLES128_CHECKED THEN ASM_ARITH_TAC]);;

(* Lean: angles64_cover_kernel / angles128_cover_kernel (Preservation/InitialBank) *)
let S12_ANGLES64_COVER = ANGLES64_COVER;;
let S12_ANGLES128_COVER = ANGLES128_COVER;;
