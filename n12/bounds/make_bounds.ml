(* ========================================================================= *)
(* The earlier, independent bounds  7943/2000 <= s(12) <= 4  (weighted point  *)
(* covers; not needed for s(12) = 4, see n12/README.md).                      *)
(*                                                                           *)
(* From the project root:  shared/build.sh n12/bounds/make_bounds.ml          *)
(* The lower bound replays a box-tree certificate; generate the data file     *)
(* first with n12/scripts/gen_tree.py (n12/README.md).  SQ_CERT selects the   *)
(* data file, SQ_DOMAINS the number of OCaml domains.                         *)
(* ========================================================================= *)

needs "n12/bounds/square12_bounds.ml";;

let sq_domains =
  try int_of_string(Sys.getenv "SQ_DOMAINS")
  with _ -> max 1 (Domain.recommended_domain_count() - 1);;

let sq_cert = try Sys.getenv "SQ_CERT" with Not_found -> "n12/bounds/data/s12_3.9715r.dat";;

let S12_LOWER = certificate_theorem_par "s12c" sq_cert 12 sq_domains 100;;

let S12_BOUNDS = MATCH_MP SIDE_BOUNDS_FROM (CONJ S12_LOWER PACKS_12_4);;

(* The results. *)
PACKS_12_4;;
S12_LOWER;;
S12_BOUNDS;;

(* Only HOL Light's three standard axioms are used. *)
axioms();;

(* Mechanical check: S12_BOUNDS is  m <= square_packing_side 12 /\ square_packing_side 12 <= &4
   (m depends on the certificate, 7943/2000 for the default SQ_CERT), with no hypotheses, and
   check_axioms () passes.  The line "STATEMENT CHECKED" tells shared/build.sh that the build
   succeeded. *)
let () =
  let s12 = `square_packing_side 12` in
  let (lo, hi) = dest_conj (concl S12_BOUNDS) in
  if not (hyp S12_BOUNDS = []) then failwith "bounds: S12_BOUNDS has hypotheses";
  let le = `(<=):real->real->bool` in
  if not (fst (strip_comb lo) = le && rand lo = s12 && hi = mk_binop le s12 `&4`)
  then failwith "bounds: S12_BOUNDS: wrong conclusion";
  check_axioms ();
  print_string ("n=12 bounds STATEMENT CHECKED: " ^ string_of_thm S12_BOUNDS ^
                " (no hypotheses; axioms: INFINITY_AX, SELECT_AX, ETA_AX only)\n");;
