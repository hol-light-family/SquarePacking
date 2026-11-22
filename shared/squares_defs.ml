(* ========================================================================= *)
(* Packing unit squares in a square: basic definitions.                      *)
(*                                                                           *)
(* A unit square is any congruent copy of [0,1]^2 in the plane, i.e. the     *)
(* image of [0,1]^2 under an isometry (arbitrary rotations, reflections and  *)
(* translations).  n unit squares pack into the square [0,t]^2 if they all   *)
(* lie inside it and have pairwise disjoint interiors (boundary contact is   *)
(* allowed).  s(n) = square_packing_side n is the infimum of such t.         *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

let unit_square = new_definition
 `unit_square (S:real^2->bool) <=>
    exists f:real^2->real^2. (forall x y. dist(f x,f y) = dist(x,y)) /\
                       S = IMAGE f (interval[vec 0,vec 1])`;;

let packs = new_definition
 `packs n (t:real) <=>
    exists sq:num->real^2->bool.
       (forall i. i < n ==> unit_square(sq i) /\
                      sq i SUBSET interval[vec 0,t % vec 1]) /\
       (forall i j. i < n /\ j < n /\ ~(i = j)
              ==> DISJOINT (interior(sq i)) (interior(sq j)))`;;

let square_packing_side = new_definition
 `square_packing_side n = inf {t | packs n t}`;;
