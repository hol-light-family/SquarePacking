(* ========================================================================= *)
(* Phase 2: Compact/Cases/C981V116.lean (namespace N12Compact.C981V116).     *)
(* Original C981 representative 116 with its exact owner assignment,         *)
(* excluded by C981Midpoint.excludes (= C981MP_EXCLUDES) at owners 6 and 3.  *)
(* vector : Fin 12 -> Finset Nat is c981v116_vector : num -> num -> bool     *)
(* (EL i of the literal list); List.ofFn vector is list_of_seq .. 12.        *)
(* owners_query_inside / owners_query_outside: c981br_in / c981br_out        *)
(* (Bridge_C981Row27.ml, over CC_C981_Ownership producers).                  *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/C981Midpoint.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;

(* Lean: vector *)
let c981v116_vector = new_definition
 `c981v116_vector (i:num) =
    EL i [{2, 12}; {0, 10}; {}; {7, 19}; {}; {4, 16}; {9, 17}; {5, 13}; {1, 11}; {6, 15}; {8, 18}; {3, 14}]`;;

let C981V116_LIST = prove
 (`list_of_seq c981v116_vector 12 =
    [{2, 12}; {0, 10}; {}; {7, 19}; {}; {4, 16}; {9, 17}; {5, 13}; {1, 11}; {6, 15}; {8, 18}; {3, 14}]`,
  REWRITE_TAC[LIST_EQ; LENGTH_LIST_OF_SEQ; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[EL_LIST_OF_SEQ; c981v116_vector]);;

(* Lean: excluded *)
let C981V116_EXCLUDED =
  let v = rand (concl C981V116_LIST) in
  let th = c981br_prove_excl v C981MP_EXCLUDES [6; 3]
   [c981br_in v 6 (`&113 / &50`, `&3`);
    c981br_in v 6 (`&3`, `&113 / &50`);
    c981br_out v 6 (`&2`, `&113 / &50`);
    c981br_out v 6 (`&113 / &50`, `&2`);
    c981br_in v 3 (`&12 / &5`, `&3`);
    c981br_in v 3 (`&3`, `&12 / &5`);
    c981br_apart v 6 3] in
  REWRITE_RULE[GSYM C981V116_LIST] th;;

(* Lean: representative116_excluded *)
let C981V116_REPRESENTATIVE116_EXCLUDED = prove
 (`c981vd_excludes_vector (EL 116 c981vd_representative_vectors)`,
  REWRITE_TAC[c981br_rep_el 116; GSYM C981V116_LIST; C981V116_EXCLUDED]);;
