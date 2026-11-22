(* ========================================================================= *)
(* Phase 2: Compact/Completion/CommonCases/C48Entrance.lean.                 *)
(* The C48 / C573 / C574 entrance (Lean Kind = c48 | c573 | c574, index 0,1,2 *)
(* of the OCaml arrays below; bottom k = 4, 8192, 8196).  Domains are the    *)
(* theorems C48E_DOMAINS.(k) (|- cdom (family k) mask list); the private     *)
(* *_checked cuts are evaluated inside OO_CHAIN_TAC.  Lean BasePairs k p is  *)
(* c48e_basepairs (bottom k) c1 c2 a b l.                                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: family *)
let c48e_family_c48 = new_definition
 `c48e_family_c48 = {1,2,4,8,48,192,256,1536,2048,4096,16384,32768}`;;
let c48e_family_c573 = new_definition
 `c48e_family_c573 = {1,2,8,48,192,256,1536,2048,4096,8192,16384,32768}`;;
let c48e_family_c574 = new_definition
 `c48e_family_c574 = {1,2,8,48,192,256,1536,2048,4096,8196,16384,32768}`;;
let C48E_FAM = [| `c48e_family_c48`; `c48e_family_c573`; `c48e_family_c574` |];;
(* Lean: bottom *)
let C48E_BOTTOM = [| 4; 8192; 8196 |];;

(* Lean: budget_counts (private) *)
let C48E_BUDGET_COUNTS = Array.map (fun f -> CONJ (card_exempt f 0) (card_exempt f 1)) C48E_FAM;;

(* Lean: southAllowed .. leftAllowed (private) *)
let c48e_south_allowed = new_definition `c48e_south_allowed = [{0,10}; {0,12}; {0,13}; {2,10}; {2,12}; {2,13}; {4,10}; {4,12}; {4,13}; {0,1,13}; {0,2,10}; {0,2,12}; {0,2,13}; {0,4,10}; {0,4,12}; {0,4,13}; {0,5,13}; {1,4,13}; {2,4,10}; {2,4,12}; {2,4,13}; {4,5,13}]`;;
let c48e_bottom_allowed = new_definition `c48e_bottom_allowed = [{2,12}; {6,15}; {2,4,12}; {4,6,15}]`;;
let c48e_right_allowed = new_definition `c48e_right_allowed = [{8,18}; {9,19}; {6,8,18}; {7,9,19}; {8,9,18}; {8,9,19}]`;;
let c48e_top_allowed = new_definition `c48e_top_allowed = [{3,14}; {7,17}; {3,5,14}; {5,7,17}]`;;
let c48e_north_allowed = new_definition `c48e_north_allowed = [{1,11}; {1,13}; {1,14}; {3,11}; {3,13}; {3,14}; {5,11}; {5,13}; {5,14}; {0,1,13}; {0,5,13}; {1,3,11}; {1,3,13}; {1,3,14}; {1,4,13}; {1,5,11}; {1,5,13}; {1,5,14}; {3,5,11}; {3,5,13}; {3,5,14}; {4,5,13}]`;;
let c48e_left_allowed = new_definition `c48e_left_allowed = [{0,10}; {1,11}; {0,1,10}; {0,1,11}; {0,2,10}; {1,3,11}]`;;

(* Lean: southDomain, bottomDomain, rightDomain, topDomain, northDomain, leftDomain (private) *)
let C48E_DOMAINS = Array.map (fun f ->
  let d n def = cdom_named (oo_restrict23 (ro_combined f n)) def in
  [256, d 6 c48e_south_allowed; 8192, d 19 c48e_bottom_allowed; 16384, d 21 c48e_right_allowed;
   32768, d 24 c48e_top_allowed; 2048, d 13 c48e_north_allowed; 4096, d 17 c48e_left_allowed]) C48E_FAM;;

(* Lean: seed_point is oo_seed; auxiliary_point, pair_from_points *)
let C48E_AUXILIARY_POINT = prove
 (`forall c1 c2 a b l m owned j. owned SUBSET ooaux c1 c2 a b l m /\ j < 20 /\ j IN owned
     ==> linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                 (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2)`,
  REWRITE_TAC[SUBSET] THEN MESON_TAC[OO_AUX_EXACT]);;
let C48E_PAIR_FROM_POINTS = OO_PAIR_FROM_POINTS;;

(* Lean: BasePairs *)
let c48e_basepairs = new_definition
 `c48e_basepairs bm (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    {2, 12} SUBSET ooaux c1 c2 a b l 1 /\ {0, 10} SUBSET ooaux c1 c2 a b l 2 /\
    {8, 18} SUBSET ooaux c1 c2 a b l 8 /\ {6, 15} SUBSET ooaux c1 c2 a b l bm /\
    {4, 13} SUBSET ooaux c1 c2 a b l 256 /\ {1, 11} SUBSET ooaux c1 c2 a b l 4096 /\
    {9, 19} SUBSET ooaux c1 c2 a b l 16384 /\ {7, 17} SUBSET ooaux c1 c2 a b l 32768 /\
    14 IN ooaux c1 c2 a b l 2048`;;

let c48e_stmt k body = list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
  mk_imp(mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, C48E_FAM.(k))), body));;
let c48e_mem j m = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j), ooaux_tm m);;
let C48E_HAVE_TAC t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;

(* Lean: entrance *)
let C48E_ENTRANCE = Array.init 3 (fun k ->
  let f = C48E_FAM.(k) and bm = C48E_BOTTOM.(k) in
  let q = nlin_rat in
  let pt x y = (term_of_rat (q x), term_of_rat (q y)) in
  let seedmem m j pts = C48E_HAVE_TAC (c48e_mem j m) (OO_SEED_MEM_TAC f m j pts) in
  let bottom_tac =
    if k = 0 then seedmem 4 6 [pt "113/50" "1"; pt "72/25" "1"] THEN seedmem 4 15 [pt "113/50" "1"]
    else if k = 2 then seedmem 8196 6 [pt "9/4" "1"; pt "11/4" "1"] THEN seedmem 8196 15 [pt "9/4" "1"; pt "11/4" "1"]
    else ALL_TAC in
  let chain = (if k = 1 then [8192, [6; 15]] else []) @
              [256, [4; 13]; 4096, [1; 11]; 16384, [9; 19]; 2048, [14]; 32768, [7; 17]] in
  prove(c48e_stmt k (list_mk_comb(`c48e_basepairs`, [mk_small_numeral bm; `c1:num->real`; `c2:num->real`;
                                                     `a:num->real`; `b:num->real`; `l:real`])),
    REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c48e_basepairs; INSERT_SUBSET; EMPTY_SUBSET] THEN
    seedmem 1 2 [pt "28/25" "1"; pt "87/50" "1"] THEN seedmem 1 12 [pt "87/50" "1"] THEN
    seedmem 2 0 [pt "1" "87/50"] THEN seedmem 2 10 [pt "1" "28/25"; pt "1" "87/50"] THEN
    seedmem 8 8 [pt "3" "87/50"] THEN seedmem 8 18 [pt "3" "28/25"; pt "3" "87/50"] THEN
    bottom_tac THEN OO_CHAIN_TAC f C48E_DOMAINS.(k) chain));;

(* Lean: north_outward *)
let C48E_NORTH_OUTWARD = Array.init 3 (fun k ->
  let f = C48E_FAM.(k) and bm = C48E_BOTTOM.(k) in
  let bp = list_mk_comb(`c48e_basepairs`, [mk_small_numeral bm; `c1:num->real`; `c2:num->real`;
                                            `a:num->real`; `b:num->real`; `l:real`]) in
  let w = `linside (ooc c1 c2 a b l 1536) (oos c1 c2 a b l 1536) (oou c1 c2 a b l 1536)
                   (oov c1 c2 a b l 1536) l (&2) (&113 / &50)` in
  prove(list_mk_forall([`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`],
          mk_imp(list_mk_conj [`NPACK c1 c2 a b l`; mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, f); bp; w],
                 `{3, 14} SUBSET ooaux c1 c2 a b l 2048`)),
    REPEAT GEN_TAC THEN REWRITE_TAC[c48e_basepairs; INSERT_SUBSET; EMPTY_SUBSET] THEN STRIP_TAC THEN
    C48E_HAVE_TAC (c48e_mem 5 1536) (REWRITE_TAC[GSYM (oo_aux_point 5)] THEN ASM_REWRITE_TAC[]) THEN
    OO_CHAIN_TAC f C48E_DOMAINS.(k) [2048, [3; 14]]));;
