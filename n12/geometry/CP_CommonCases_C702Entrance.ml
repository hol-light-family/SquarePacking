(* ========================================================================= *)
(* Phase 2: Compact/Completion/CommonCases/C702Entrance.lean.                *)
(* Small authentic ownership cuts for C702 (real F3/G2 budget).             *)
(* The private domains are the theorems C702E_*_DOMAIN (|- cdom ..); the    *)
(* private *_checked cuts are evaluated inside OO_CHAIN_TAC.                *)
(* {a,b} SUBSET auxiliaries p m  is  {a, b} SUBSET ooaux c1 c2 a b l m.     *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: family *)
let c702e_family = new_definition
 `c702e_family = {1,2,12,16,32,192,256,1536,6144,8192,16384,32768}`;;
let C702E_F = `c702e_family`;;

(* Lean: budget_counts (private) *)
let C702E_BUDGET_COUNTS = CONJ (card_exempt C702E_F 0) (card_exempt C702E_F 1);;

(* Lean: southDomain, bottomDomain, rightDomain, topDomain (private; direct = restrict_budget23 o ofCombined) *)
let C702E_SOUTH_DOMAIN = cdom_cache (oo_restrict23 (ro_combined C702E_F 6)) `[{0,10}; {0,12}; {0,13}; {2,10}; {2,12}; {2,13}; {4,10}; {4,12}; {4,13}; {0,1,13}; {0,2,10}; {0,2,12}; {0,2,13}; {0,4,10}; {0,4,12}; {0,4,13}; {0,5,13}; {1,4,13}; {2,4,10}; {2,4,12}; {2,4,13}; {4,5,13}]`;;
let C702E_BOTTOM_DOMAIN = cdom_cache (oo_restrict23 (ro_combined C702E_F 19)) `[{2,12}; {6,15}; {2,4,12}; {4,6,15}]`;;
let C702E_RIGHT_DOMAIN = cdom_cache (oo_restrict23 (ro_combined C702E_F 21)) `[{8,18}; {9,19}; {6,8,18}; {7,9,19}; {8,9,18}; {8,9,19}]`;;
let C702E_TOP_DOMAIN = cdom_cache (oo_restrict23 (ro_combined C702E_F 24)) `[{3,14}; {7,17}; {3,5,14}; {5,7,17}]`;;
let C702E_DOMS = [256, C702E_SOUTH_DOMAIN; 8192, C702E_BOTTOM_DOMAIN; 16384, C702E_RIGHT_DOMAIN;
                  32768, C702E_TOP_DOMAIN];;

(* Lean: pair_from_points *)
let C702E_PAIR_FROM_POINTS = OO_PAIR_FROM_POINTS;;

(* Lean: base_pairs *)
let C702E_BASE_PAIRS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c702e_family /\
     {2, 12} SUBSET ooaux c1 c2 a b l 1 /\ {0, 10} SUBSET ooaux c1 c2 a b l 2 /\
     {7, 17} SUBSET ooaux c1 c2 a b l 16 /\ {9, 19} SUBSET ooaux c1 c2 a b l 32
     ==> {4, 13} SUBSET ooaux c1 c2 a b l 256 /\ {6, 15} SUBSET ooaux c1 c2 a b l 8192 /\
         {8, 18} SUBSET ooaux c1 c2 a b l 16384 /\ {3, 14} SUBSET ooaux c1 c2 a b l 32768`,
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  OO_CHAIN_TAC C702E_F C702E_DOMS [256, [4; 13]; 8192, [6; 15]; 16384, [8; 18]; 32768, [3; 14]]);;

(* Lean: some_auxiliary *)
let C702E_SOME_AUXILIARY = prove
 (`forall c1 c2 a b l m k. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c702e_family /\
     m IN c702e_family /\ k < 2 /\ ~(m IN auxex k)
     ==> exists j. j < 10 /\
             linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                     (EL j (AUXPTS k)$1) (EL j (AUXPTS k)$2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_SOME_AUXILIARY THEN EXISTS_TAC C702E_F THEN
  ASM_REWRITE_TAC[]);;
