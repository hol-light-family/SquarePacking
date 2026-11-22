(* ========================================================================= *)
(* Port of Compact/Cases/C868/AdditionalOwnership.lean (N12Compact.C868).    *)
(* Further consequences of the nine original C868 domains (Ownership.ml).    *)
(* Lean additionalClaims_checked + ForcedAuxiliary.contains = fa_contains;   *)
(* withoutSoutheastG / withoutSoutheastG_checked + the by_contra argument    *)
(* of southeast_g_cover = fa_cover with the index list [16; 18].             *)
(* Statements indexed by i : Fin 8 are OCaml arrays.  Tag C868AO_.           *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C868_Ownership.ml";;

(* Lean: additionalClaims *)
let C868AO_ADDITIONAL_CLAIMS =
  [(16,7); (16,17); (4096,1); (4096,11); (8192,6); (8192,15); (32768,3); (512,8)];;

(* Lean: additionalClaims_checked (+ ForcedAuxiliary.contains):
   |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = c868_family ==> j IN ooaux c1 c2 a b l m *)
let C868AO_ADDITIONAL_POINT =
  Array.of_list (map (fun (m, j) -> fa_contains C868OW_F C868OW_DOMAINS m j) C868AO_ADDITIONAL_CLAIMS);;

(* Lean: additional_inside
   |- !c1 c2 a b l. NPACK .. /\ IMAGE .. = c868_family ==> linside (owner m) x_j y_j *)
let C868AO_ADDITIONAL_INSIDE = Array.map c868_point_of_mem C868AO_ADDITIONAL_POINT;;

(* Lean: withoutSoutheastG_checked (private): 16 or 18 belongs to owner 512 *)
let C868AO_SOUTHEAST_G_MEM = fa_cover C868OW_F C868OW_DOMAINS 512 [16; 18];;

(* Lean: southeast_g_cover *)
let C868AO_SOUTHEAST_G_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family
     ==> linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                 (oov c1 c2 a b l 512) l (&113 / &50) (&2) \/
         linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                 (oov c1 c2 a b l 512) l (&3) (&8 / &5)`,
  REWRITE_TAC[oo_aux_point 16; oo_aux_point 18] THEN
  ACCEPT_TAC C868AO_SOUTHEAST_G_MEM);;
