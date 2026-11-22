(* ========================================================================= *)
(* Port of Compact/Cases/C868/ActualCrosspoints.lean (N12Compact.C868).      *)
(* Actual singleton segments force both southwest crosspoints of owner 256;  *)
(* owner 512 owns G8 = (3, 8/5).                                             *)
(* SouthwestCentralReach.left / below = SWCR_LEFT / SWCR_BELOW,              *)
(* ElbowPoint.points_original = OCEP_POINTS_ORIGINAL.  The local haves        *)
(* (marker, missing, ...) are facts under C868_H (Ownership.ml toolkit).     *)
(* Tag C868AC_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/AdditionalOwnership.ml";;
needs "n12/geometry/SouthwestCentralReach.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;

let C868AC_FACTS_256 =
  [c868_seed_f 256 (`&33 / &20`, `&33 / &20`);
   c868_forced_f 0; c868_forced_f 1;
   c868_excl_f 256 3072 (c868_seed_f 3072 (`&47 / &20`, `&47 / &20`));
   c868_excl_f 256 3072 (c868_seed_f 3072 (`&33 / &20`, `&47 / &20`));
   c868_excl_f 256 512 (c868_seed_f 512 (`&47 / &20`, `&33 / &20`));
   c868_seed_f 1 (`&28 / &25`, `&1`); c868_forced_f 5;
   c868_seed_f 2 (`&1`, `&28 / &25`); c868_forced_f 6];;

(* Lean: southwest_crosspoints *)
let C868AC_SOUTHWEST_CROSSPOINTS = c868_check
 `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family
     ==> linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                 (oov c1 c2 a b l 256) l (&3 / &2) (&2) /\
         linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                 (oov c1 c2 a b l 256) l (&2) (&3 / &2)`
 (c868_gen (CONJ (c868_apply SWCR_LEFT (c868_own 256 @ c868_own 1) C868AC_FACTS_256)
                 (c868_apply SWCR_BELOW (c868_own 256 @ c868_own 2) C868AC_FACTS_256)));;

(* Lean: southeast_g8 *)
let C868AC_SOUTHEAST_G8 = c868_check
 `forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family
     ==> linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                 (oov c1 c2 a b l 512) l (&3) (&8 / &5)`
 (let g = `linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                   (oov c1 c2 a b l 512) l (&3) (&8 / &5)` in
  let cover = c868_mp C868AO_SOUTHEAST_G_COVER in
  let missingG = ASSUME (mk_neg g) in
  let elbow = DISJ_CASES cover (ASSUME (lhand (concl cover)))
                (CONTR (lhand (concl cover)) (MP (NOT_ELIM missingG) (ASSUME g))) in
  let facts = [c868_seed_f 512 (`&47 / &20`, `&33 / &20`); elbow;
               c868_mp C868AO_ADDITIONAL_INSIDE.(7); missingG;
               c868_excl_f 512 3072 (c868_seed_f 3072 (`&47 / &20`, `&47 / &20`));
               c868_excl_f 512 16416 (c868_seed_f 16416 (`&1543 / &500`, `&2`))] in
  let dup = CONJUNCT1 (c868_apply OCEP_POINTS_ORIGINAL (c868_own 512) facts) in
  let sw = CONJUNCT2 (c868_mp C868AC_SOUTHWEST_CROSSPOINTS) in
  let d = SPECL [`&2`; `&3 / &2`] (REWRITE_RULE[ldisj] (c868_apart_f 256 512)) in
  let f = MP (NOT_ELIM d) (CONJ sw dup) in
  c868_gen (CCONTR g f));;
