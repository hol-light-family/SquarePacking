(* =========================================================================

                     THE STATEMENT PROVED FOR n = 5

        square_packing_side 5 = &2 + sqrt(&2) / &2,   i.e.  s(5) = 2 + 1/sqrt 2

   This file is meant to be READ by auditors.  It states, as HOL terms, the
   two theorems that n5/make.ml proves, explains every constant occurring in
   them (with the file and line where it is defined), and -- when it is loaded
   at the end of n5/make.ml -- checks mechanically that the proved theorems
   have exactly these conclusions, no hypotheses, and depend only on HOL
   Light's three standard axioms.

   Problem source: squaremath.org.  s(n) is the side of the smallest square
   into which n non-overlapping unit squares can be packed.
   ========================================================================= *)

(* -------------------------------------------------------------------------
   1. The statements.

   Each theorem NAME proved by n5/make.ml is compared in section 5 with the
   term NAME_STATEMENT given here.

   SQUARE_PACKING_SIDE_5: the value of s(5).
   ------------------------------------------------------------------------- *)

let SQUARE_PACKING_SIDE_5_STATEMENT = `square_packing_side 5 = &2 + sqrt(&2) / &2`;;

(* -------------------------------------------------------------------------
   PACKS_5: the containers that admit a packing are exactly those of
   side at least 2 + sqrt(2)/2.
   This is slightly stronger than the value of s(5): it also says that the
   infimum is attained (there is a packing of side exactly 2 + sqrt(2)/2).
   ------------------------------------------------------------------------- *)

let PACKS_5_STATEMENT = `forall t. packs 5 t <=> &2 + sqrt(&2) / &2 <= t`;;

(* Notation: `&2` is the real number 2 (`&` injects num into real); sqrt is
   the real square root (section 3).
*)

(* -------------------------------------------------------------------------
   2. The project's definitions (shared/squares_defs.ml; the same for every n).

   unit_square S  <=>  exists f:real^2->real^2.
                          (forall x y. dist(f x,f y) = dist(x,y)) /\
                          S = IMAGE f (interval[vec 0,vec 1])

      A unit square is the image of the closed square [0,1]^2 under an
      isometry of the plane (any rotation, reflection and translation).

   packs n t  <=>  exists sq:num->real^2->bool.
                      (forall i. i < n
                                 ==> unit_square(sq i) /\
                                     sq i SUBSET interval[vec 0,t % vec 1]) /\
                      (forall i j. i < n /\ j < n /\ ~(i = j)
                                   ==> DISJOINT (interior(sq i))
                                                (interior(sq j)))

      n unit squares fit into the square [0,t]^2 with pairwise disjoint
      interiors (they may touch along their boundaries).

   square_packing_side n = inf {t | packs n t}

      s(n): the infimum of the admissible container sides.
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   3. HOL Light library constants used above.  File names are relative to
      the HOL Light distribution; line numbers are those of the version used
      for the build (git commit 096417c, November 2026).

   inf s           sets.ml:5049
                   the greatest lower bound of a set of reals:
                   inf s = @a. (forall x. x IN s ==> a <= x) /\
                               (forall b. (forall x. x IN s ==> b <= x)
                                          ==> b <= a)
   IMAGE f s       sets.ml:144          {f x | x IN s}
   s SUBSET t      sets.ml:116          forall x. x IN s ==> x IN t
   DISJOINT s t    sets.ml:122          s INTER t = {}
   interior s      Multivariate/topology.ml:1944
                   {x | exists t. open t /\ x IN t /\ t SUBSET s}
   open s          Multivariate/topology.ml:20  (the Euclidean topology)
   interval[a,b]   Multivariate/vectors.ml:10053  (closed_interval)
                   the closed box  {x | forall i. 1 <= i /\ i <= dimindex(:N)
                                              ==> a$i <= x$i /\ x$i <= b$i}
                   (here N = 2, so interval[vec 0,t % vec 1] = [0,t]^2)
   vec n           Multivariate/vectors.ml:87   the vector (n,...,n)
   c % x           Multivariate/vectors.ml:80   scalar multiplication
   dist(x,y)       Multivariate/vectors.ml:416  norm(x - y)
   norm x          Multivariate/vectors.ml:411  the Euclidean norm
   real^2          the Euclidean plane (finite Cartesian product, cart.ml)
   sqrt x          real.ml:1663  the real square root (for x >= 0, the
                   nonnegative y with y pow 2 = x)
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   4. Where the proof is (for orientation; not needed to read the statement;
      see n5/README.md).

   n5/square5.ml       PACKS_5 and SQUARE_PACKING_SIDE_5.
                       Upper bound: Goebel's packing (four corner squares plus
                       one at 45 degrees).  Lower bound: the Goebel/Friedman
                       "unavoidable points" argument -- for side
                       2 + sqrt(2)/2 - e, every unit square in the container
                       contains one of four fixed points in its interior, so
                       five squares with disjoint interiors cannot fit.
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   5. Mechanical check.  Runs at the end of n5/make.ml, which proves
      SQUARE_PACKING_SIDE_5 and PACKS_5.
   ------------------------------------------------------------------------- *)

let () =
  let chk name th tm =
    if not (hyp th = []) then failwith ("statement: " ^ name ^ " has hypotheses");
    if not (aconv (concl th) tm) then failwith ("statement: " ^ name ^ ": wrong conclusion") in
  chk "SQUARE_PACKING_SIDE_5" SQUARE_PACKING_SIDE_5 SQUARE_PACKING_SIDE_5_STATEMENT;
  chk "PACKS_5" PACKS_5 PACKS_5_STATEMENT;
  check_axioms ();
  print_string "n=5 STATEMENT CHECKED: |- square_packing_side 5 = &2 + sqrt(&2) / &2 \
                (no hypotheses; axioms: INFINITY_AX, SELECT_AX, ETA_AX only)\n";;
