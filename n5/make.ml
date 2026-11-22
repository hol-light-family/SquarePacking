(* ========================================================================= *)
(* Build of  |- square_packing_side 5 = &2 + sqrt(&2) / &2.                  *)
(* Start HOL Light in the project root, then   loadt "n5/make.ml";;          *)
(* The statement proved, and what its constants mean: n5/statement.ml.      *)
(* ========================================================================= *)
needs "n5/square5.ml";;
PACKS_5;;
SQUARE_PACKING_SIDE_5;;
axioms();;
loadt "n5/statement.ml";;
