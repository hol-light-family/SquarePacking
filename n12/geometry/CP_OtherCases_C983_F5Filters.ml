(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F5Filters.lean.               *)
(* The authentic merged-F5 entrance (actual p 7 owns F5 = label 5).         *)
(* Conventions of CP_OtherCases_C983_F4Filters.ml / SharpApplications.ml:    *)
(* actual p i = c983e_actual c1 c2 a b l i, originalComponents i =           *)
(* EL i c983e_original_components, absent_of_foreign = c983f4f_absent,       *)
(* merged_g3 = C983F4F_MERGED_G3, top_origin_of_f3 = C983FO_TOP_ORIGIN_OF_F3,*)
(* right_bar_of_f8 = C983FO_RIGHT_BAR_OF_F8.  Lean `x ∈ L` for a list of   *)
(* Finsets is MEM.  Packing statements have hypotheses NPACK /\ IMAGE .. =   *)
(* c983ri_family /\ ...  Tag C983F5_.                                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_SharpApplications.ml";;

(* apply a packing statement |- !c1 c2 a b l. NPACK /\ IMAGE /\ h1 /\ .. ==> C to facts *)
let c983f5_use th hs =
  MP (SPECL C983E_VARS th) (end_itlist CONJ (ASSUME C983F4F_NP :: ASSUME C983F4F_IMG :: hs));;
(* from |- p \/ q and |- ~p (resp. ~q) get q (resp. p) *)
let c983f5_res_left d n =
  let p = lhand (concl d) and q = rand (concl d) in
  DISJ_CASES d (CONTR q (MP (NOT_ELIM n) (ASSUME p))) (ASSUME q);;
let c983f5_res_right d n =
  let p = lhand (concl d) and q = rand (concl d) in
  DISJ_CASES d (ASSUME p) (CONTR p (MP (NOT_ELIM n) (ASSUME q)));;
let c983f5_mps th hs = itlist (fun a t -> MP t a) (rev hs) th;;
let c983f5_check defs = REWRITE_TAC defs THEN c983f4f_check_tac;;
let c983f5_g3 () = c983f5_use C983F4F_MERGED_G3 [];;

(* Lean: southeast_no_g6_check (private) *)
let C983F5_SOUTHEAST_NO_G6_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==> ~(5 IN s) ==> ~(16 IN s) ==>
       (4 IN s \/ 8 IN s) /\ 18 IN s`, c983f5_check []);;

(* Lean: right_avoiding_f8_check (private) *)
let C983F5_RIGHT_AVOIDING_F8_CHECK = prove
 (`forall s. MEM s (EL 10 c983e_original_components) ==> ~(8 IN s) ==> 9 IN s /\ 19 IN s`,
  c983f5_check []);;

(* Lean: northeast_outward_check (private) *)
let C983F5_NORTHEAST_OUTWARD_CHECK = prove
 (`forall s. MEM s (EL 6 c983e_original_components) ==> ~(5 IN s) ==> ~(13 IN s) ==> ~(8 IN s) ==>
       ~(9 IN s) ==> ~(19 IN s) ==> 7 IN s`, c983f5_check []);;

(* Lean: top_avoiding_f5_f7_check (private) *)
let C983F5_TOP_AVOIDING_F5_F7_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> ~(5 IN s) ==> ~(7 IN s) ==> 3 IN s /\ 14 IN s`,
  c983f5_check []);;

let c983f5_f5 () = ASSUME (c983f4f_mem 5 7);;

let c983f5_southeast_g6 () =
  let f5 = c983f5_f5 () in
  let noG6 = ASSUME (mk_neg (c983f4f_mem 16 5)) in
  let noF5 = c983f4f_absent 7 5 f5 in
  let outward = c983f5_mps (MATCH_MP C983F5_SOUTHEAST_NO_G6_CHECK (c983f4f_orig 5)) [noF5; noG6] in
  let noF4 = NOT_INTRO (DISCH (c983f4f_mem 4 5)
    (c983f5_use C983SA_SOUTHEAST_INWARD_OUTWARD_EXCLUSION
       [ASSUME (c983f4f_mem 4 5); CONJUNCT2 outward; noG6])) in
  let f8 = c983f5_res_left (CONJUNCT1 outward) noF4 in
  let right = MP (MATCH_MP C983F5_RIGHT_AVOIDING_F8_CHECK (c983f4f_orig 10)) (c983f4f_absent 5 10 f8) in
  let nNoF5 = c983f4f_absent 7 6 f5 in
  let nF7 = c983f5_mps (MATCH_MP C983F5_NORTHEAST_OUTWARD_CHECK (c983f4f_orig 6))
    [nNoF5; c983f4f_absent 7 6 (c983f5_g3 ()); c983f4f_absent 5 6 f8;
     c983f4f_absent 10 6 (CONJUNCT1 right); c983f4f_absent 10 6 (CONJUNCT2 right)] in
  let top = c983f5_mps (MATCH_MP C983F5_TOP_AVOIDING_F5_F7_CHECK (c983f4f_orig 11))
    [c983f4f_absent 7 11 f5; c983f4f_absent 6 11 nF7] in
  let upperPoint = c983f5_use C983SA_NORTHEAST_UPPER_POINT
    [nF7; nNoF5; c983f5_use C983FO_TOP_ORIGIN_OF_F3 [CONJUNCT1 top];
     c983f5_use C983FO_RIGHT_BAR_OF_F8 [f8; CONJUNCT1 right; CONJUNCT2 right]] in
  let lowerPoint = c983f5_use C983SA_SOUTHEAST_OUTWARD_POINT [f8; CONJUNCT2 outward; noG6] in
  let ap = REWRITE_RULE[ldisj] (MP (SPECL C983E_VARS (oo_apart C983E_F 512 1024)) (c983f4f_hh ())) in
  let f = MP (NOT_ELIM (SPECL [`&101 / &40`; `&17 / &8`] ap)) (CONJ lowerPoint upperPoint) in
  CCONTR (c983f4f_mem 16 5) f;;

(* Lean: f5_southeast_g6 *)
let C983F5_F5_SOUTHEAST_G6 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 7] (c983f4f_mem 16 5)) (c983f5_southeast_g6 ());;

(* Lean: f5NortheastComponents *)
let c983f5_northeast_components = new_definition
 `c983f5_northeast_components : (num->bool)list =
    [{7, 17}; {7, 19}; {7, 17, 19}; {9, 17}; {9, 19}; {9, 17, 19}; {7, 9, 17}; {7, 9, 19}; {7, 9, 17, 19}]`;;

(* Lean: northeast_f5_check (private) *)
let C983F5_NORTHEAST_F5_CHECK = prove
 (`forall s. MEM s (EL 6 c983e_original_components) ==> ~(5 IN s) ==> ~(13 IN s) ==> ~(16 IN s) ==>
       MEM s c983f5_northeast_components`, c983f5_check [c983f5_northeast_components]);;

let c983f5_northeast_components_th () =
  let f5 = c983f5_f5 () in
  c983f5_mps (MATCH_MP C983F5_NORTHEAST_F5_CHECK (c983f4f_orig 6))
    [c983f4f_absent 7 6 f5; c983f4f_absent 7 6 (c983f5_g3 ());
     c983f4f_absent 5 6 (c983f5_use C983F5_F5_SOUTHEAST_G6 [f5])];;

let c983f5_act_mem i def = mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, c983f4f_act i), def);;

(* Lean: f5_northeast_components *)
let C983F5_F5_NORTHEAST_COMPONENTS = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 7] (c983f5_act_mem 6 `c983f5_northeast_components`))
  (c983f5_northeast_components_th ());;

(* Lean: northeast_cover_check (private) *)
let C983F5_NORTHEAST_COVER_CHECK = prove
 (`forall s. MEM s c983f5_northeast_components ==> (7 IN s \/ 9 IN s) /\ (17 IN s \/ 19 IN s)`,
  c983f5_check [c983f5_northeast_components]);;

let c983f5_northeast_cover () = MATCH_MP C983F5_NORTHEAST_COVER_CHECK (c983f5_northeast_components_th ());;

(* Lean: f5_northeast_cover *)
let C983F5_F5_NORTHEAST_COVER = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 7]
     (mk_conj(mk_disj(c983f4f_mem 7 6, c983f4f_mem 9 6), mk_disj(c983f4f_mem 17 6, c983f4f_mem 19 6))))
  (c983f5_northeast_cover ());;

(* Lean: right_outer_check (private) *)
let C983F5_RIGHT_OUTER_CHECK = prove
 (`forall s. MEM s (EL 10 c983e_original_components) ==> 8 IN s \/ 9 IN s`, c983f5_check []);;

(* Lean: right_f7_check (private) *)
let C983F5_RIGHT_F7_CHECK = prove
 (`forall s. MEM s (EL 10 c983e_original_components) ==> ~(16 IN s) ==> 7 IN s ==> 9 IN s`,
  c983f5_check []);;

let c983f5_g6 () = c983f5_use C983F5_F5_SOUTHEAST_G6 [c983f5_f5 ()];;

let c983f5_right_avoids_f7 () =
  let rightF7 = ASSUME (c983f4f_mem 7 10) in
  let rightF9 = c983f5_mps (MATCH_MP C983F5_RIGHT_F7_CHECK (c983f4f_orig 10))
    [c983f4f_absent 5 10 (c983f5_g6 ()); rightF7] in
  let nNoF7 = c983f4f_absent 10 6 rightF7 and nNoF9 = c983f4f_absent 10 6 rightF9 in
  let f = MP (NOT_ELIM nNoF9) (c983f5_res_left (CONJUNCT1 (c983f5_northeast_cover ())) nNoF7) in
  NOT_INTRO (DISCH (c983f4f_mem 7 10) f);;

(* Lean: f5_right_avoids_f7 *)
let C983F5_F5_RIGHT_AVOIDS_F7 = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 7] (mk_neg (c983f4f_mem 7 10))) (c983f5_right_avoids_f7 ());;

(* Lean: f5SoutheastComponents *)
let c983f5_southeast_components = new_definition
 `c983f5_southeast_components : (num->bool)list =
    [{4, 16}; {4, 16, 18}; {8, 16}; {8, 16, 18}; {4, 8, 16}; {4, 8, 16, 18}; {4, 9, 16}]`;;

(* Lean: southeast_f5_check (private) *)
let C983F5_SOUTHEAST_F5_CHECK = prove
 (`forall s. MEM s (EL 5 c983e_original_components) ==> ~(5 IN s) ==> 16 IN s ==> ~(8 IN s /\ 9 IN s) ==>
       MEM s c983f5_southeast_components`, c983f5_check [c983f5_southeast_components]);;

(* Lean: f5_southeast_components *)
let C983F5_F5_SOUTHEAST_COMPONENTS =
  let f5 = c983f5_f5 () in
  let both = mk_conj(c983f4f_mem 8 5, c983f4f_mem 9 5) in
  let b = ASSUME both in
  let noF8 = c983f4f_absent 5 10 (CONJUNCT1 b) and noF9 = c983f4f_absent 5 10 (CONJUNCT2 b) in
  let outer = MATCH_MP C983F5_RIGHT_OUTER_CHECK (c983f4f_orig 10) in
  let f = MP (NOT_ELIM noF9) (c983f5_res_left outer noF8) in
  let th = c983f5_mps (MATCH_MP C983F5_SOUTHEAST_F5_CHECK (c983f4f_orig 5))
    [c983f4f_absent 7 5 f5; c983f5_g6 (); NOT_INTRO (DISCH both f)] in
  c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] (c983f5_act_mem 5 `c983f5_southeast_components`)) th;;

(* Lean: f5RightComponents *)
let c983f5_right_components = new_definition
 `c983f5_right_components : (num->bool)list =
    [{8, 18}; {9, 19}; {8, 9, 18}; {8, 9, 19}; {8, 9, 18, 19}]`;;

(* Lean: right_f5_check (private) *)
let C983F5_RIGHT_F5_CHECK = prove
 (`forall s. MEM s (EL 10 c983e_original_components) ==> ~(16 IN s) ==> ~(7 IN s) ==>
       MEM s c983f5_right_components`, c983f5_check [c983f5_right_components]);;

let c983f5_right_components_th () =
  c983f5_mps (MATCH_MP C983F5_RIGHT_F5_CHECK (c983f4f_orig 10))
    [c983f4f_absent 5 10 (c983f5_g6 ()); c983f5_use C983F5_F5_RIGHT_AVOIDS_F7 [c983f5_f5 ()]];;

(* Lean: f5_right_components *)
let C983F5_F5_RIGHT_COMPONENTS = c983f4f_close
  (c983sa_stmt [c983f4f_mem 5 7] (c983f5_act_mem 10 `c983f5_right_components`))
  (c983f5_right_components_th ());;

(* Lean: northeast_avoiding_right_check (private) *)
let C983F5_NORTHEAST_AVOIDING_RIGHT_CHECK = prove
 (`forall s. MEM s c983f5_northeast_components ==> ~(9 IN s) ==> ~(19 IN s) ==> s = {7, 17}`,
  c983f5_check [c983f5_northeast_components]);;

(* Lean: right_g9_check (private) *)
let C983F5_RIGHT_G9_CHECK = prove
 (`forall s. MEM s c983f5_right_components ==> 19 IN s ==> 9 IN s`,
  c983f5_check [c983f5_right_components]);;

(* Lean: top_avoiding_central_check (private) *)
let C983F5_TOP_AVOIDING_CENTRAL_CHECK = prove
 (`forall s. MEM s (EL 11 c983e_original_components) ==> ~(5 IN s) ==> ~(7 IN s) ==> ~(17 IN s) ==>
       s = {3, 14}`, c983f5_check []);;

(* Lean: f5_upper_of_right_g9 *)
let C983F5_F5_UPPER_OF_RIGHT_G9 =
  let f5 = c983f5_f5 () and g9 = ASSUME (c983f4f_mem 19 10) in
  let rightF9 = MP (MATCH_MP C983F5_RIGHT_G9_CHECK (c983f5_right_components_th ())) g9 in
  let northeast = c983f5_mps (MATCH_MP C983F5_NORTHEAST_AVOIDING_RIGHT_CHECK (c983f5_northeast_components_th ()))
    [c983f4f_absent 10 6 rightF9; c983f4f_absent 10 6 g9] in
  let memo j = EQT_ELIM (REWRITE_CONV[northeast; IN_INSERT; NOT_IN_EMPTY] (c983f4f_mem j 6)) in
  let nF7 = memo 7 and nG7 = memo 17 in
  let top = c983f5_mps (MATCH_MP C983F5_TOP_AVOIDING_CENTRAL_CHECK (c983f4f_orig 11))
    [c983f4f_absent 7 11 f5; c983f4f_absent 6 11 nF7; c983f4f_absent 6 11 nG7] in
  c983f4f_close
    (c983sa_stmt [c983f4f_mem 5 7; c983f4f_mem 19 10]
       (mk_conj(mk_eq(c983f4f_act 6, `{7, 17}`), mk_eq(c983f4f_act 11, `{3, 14}`))))
    (CONJ northeast top);;
