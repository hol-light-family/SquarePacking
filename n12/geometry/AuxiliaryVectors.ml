(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/AuxiliaryVectors.lean.                     *)
(* Exhaustive case-977 auxiliary ownership vectors (sorted F then G order).  *)
(* Conventions: natCombinedOwners p (ownerIndex p m) is ooaux c1 c2 a b l m  *)
(* (PackingContext.ml);  orderedOwner p i is c977av_ordered_owner c1 c2 a b *)
(* l i = oidx c1 c2 a b l (EL i c977av_code);  natAuxOwners p k j, for a     *)
(* square j with markerCode p j = m, is constrained by |- hdom fam m k al     *)
(* (OwnerBudget.HalfDomain);  combinedSpecN.actual / CertifiedDomain is       *)
(* |- cdom fam m al (pk_combined);  Fin n -> List tables are HOL lists (EL)   *)
(* or functions of i < n;  List.flatMap is c977av_flatmap; List.Forall2 is   *)
(* ALL2; List.Pairwise R is PAIRWISE R; List.Nodup is PAIRWISE (\x y. ~(x =   *)
(* y)); List.sum is c977av_lsum;  a Lean LocalQuery w with w.Check and       *)
(* w.sound is the kernel theorem returned by slq_new (its .four certificate  *)
(* points, transformed as in Phase 1, are re-proved by the HOL kernel).      *)
(* auxiliaryDomains = (finRange 12).map pruningDomain4 is c977av_domains,    *)
(* the 12-element list c977av_prune4.                                        *)
(* ========================================================================= *)

needs "n12/geometry/CornerRoots.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

let C977AV_FAM = `ccc977ri_family`;;

(* ------------------------------------------------------------------------- *)
(* The 48 pair queries (Lean pairQuery0 .. pairQuery47, pair_queries_checked) *)
(* ------------------------------------------------------------------------- *)

(* Lean: pairQuery0 (.four <true,true,false> fourDatum7) *)
let C977AV_PAIR_QUERY0 = slq_new (12, 0, [0],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery1 (.four <true,true,false> fourDatum9) *)
let C977AV_PAIR_QUERY1 = slq_new (12, 0, [1],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery2 (.four <true,true,false> fourDatum1) *)
let C977AV_PAIR_QUERY2 = slq_new (12, 0, [2],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery3 (.four <false,true,false> fourDatum10) *)
let C977AV_PAIR_QUERY3 = slq_new (12, 0, [3],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery4 (.four <true,true,false> fourDatum5) *)
let C977AV_PAIR_QUERY4 = slq_new (12, 0, [4],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery5 (.four <false,true,false> fourDatum8) *)
let C977AV_PAIR_QUERY5 = slq_new (12, 0, [5],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery6 (.four <false,true,false> fourDatum2) *)
let C977AV_PAIR_QUERY6 = slq_new (12, 0, [7],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery7 (.four <false,true,false> fourDatum0) *)
let C977AV_PAIR_QUERY7 = slq_new (12, 0, [9],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery8 (.four <true,true,false> fourDatum2) *)
let C977AV_PAIR_QUERY8 = slq_new (12, 1, [0],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery9 (.four <true,true,false> fourDatum10) *)
let C977AV_PAIR_QUERY9 = slq_new (12, 1, [1],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery10 (.four <true,true,false> fourDatum0) *)
let C977AV_PAIR_QUERY10 = slq_new (12, 1, [2],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery11 (.four <true,true,false> fourDatum8) *)
let C977AV_PAIR_QUERY11 = slq_new (12, 1, [3],
  [(nlin_rat "3", nlin_rat "457/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "457/500"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery12 (.four <false,true,false> fourDatum9) *)
let C977AV_PAIR_QUERY12 = slq_new (12, 1, [4],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery13 (.four <false,true,false> fourDatum5) *)
let C977AV_PAIR_QUERY13 = slq_new (12, 1, [6],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery14 (.four <false,true,false> fourDatum7) *)
let C977AV_PAIR_QUERY14 = slq_new (12, 1, [7],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery15 (.four <false,true,false> fourDatum1) *)
let C977AV_PAIR_QUERY15 = slq_new (12, 1, [9],
  [(nlin_rat "1543/500", nlin_rat "1"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "33/20")]);;
(* Lean: pairQuery16 (.four <true,true,true> fourDatum9) *)
let C977AV_PAIR_QUERY16 = slq_new (48, 0, [0],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery17 (.four <true,true,true> fourDatum7) *)
let C977AV_PAIR_QUERY17 = slq_new (48, 0, [1],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery18 (.four <false,true,true> fourDatum10) *)
let C977AV_PAIR_QUERY18 = slq_new (48, 0, [2],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery19 (.four <true,true,true> fourDatum1) *)
let C977AV_PAIR_QUERY19 = slq_new (48, 0, [3],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "8/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery20 (.four <false,true,true> fourDatum8) *)
let C977AV_PAIR_QUERY20 = slq_new (48, 0, [4],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery21 (.four <true,true,true> fourDatum5) *)
let C977AV_PAIR_QUERY21 = slq_new (48, 0, [5],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery22 (.four <false,true,true> fourDatum2) *)
let C977AV_PAIR_QUERY22 = slq_new (48, 0, [6],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery23 (.four <false,true,true> fourDatum0) *)
let C977AV_PAIR_QUERY23 = slq_new (48, 0, [8],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery24 (.four <true,true,true> fourDatum10) *)
let C977AV_PAIR_QUERY24 = slq_new (48, 1, [0],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery25 (.four <true,true,true> fourDatum2) *)
let C977AV_PAIR_QUERY25 = slq_new (48, 1, [1],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "1", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery26 (.four <false,true,true> fourDatum9) *)
let C977AV_PAIR_QUERY26 = slq_new (48, 1, [2],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery27 (.four <true,true,true> fourDatum8) *)
let C977AV_PAIR_QUERY27 = slq_new (48, 1, [3],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery28 (.four <true,true,true> fourDatum0) *)
let C977AV_PAIR_QUERY28 = slq_new (48, 1, [4],
  [(nlin_rat "3", nlin_rat "1543/500"); (nlin_rat "87/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery29 (.four <false,true,true> fourDatum7) *)
let C977AV_PAIR_QUERY29 = slq_new (48, 1, [5],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery30 (.four <false,true,true> fourDatum5) *)
let C977AV_PAIR_QUERY30 = slq_new (48, 1, [6],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery31 (.four <false,true,true> fourDatum1) *)
let C977AV_PAIR_QUERY31 = slq_new (48, 1, [8],
  [(nlin_rat "1543/500", nlin_rat "3"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "1543/500", nlin_rat "2"); (nlin_rat "47/20", nlin_rat "47/20")]);;
(* Lean: pairQuery32 (.four <false,false,true> fourDatum0) *)
let C977AV_PAIR_QUERY32 = slq_new (192, 0, [0],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "87/50")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery33 (.four <false,false,true> fourDatum2) *)
let C977AV_PAIR_QUERY33 = slq_new (192, 0, [2],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "8/5", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery34 (.four <false,false,true> fourDatum8) *)
let C977AV_PAIR_QUERY34 = slq_new (192, 0, [4],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "2", nlin_rat "87/50")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery35 (.four <true,false,true> fourDatum5) *)
let C977AV_PAIR_QUERY35 = slq_new (192, 0, [5],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "2", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery36 (.four <false,false,true> fourDatum10) *)
let C977AV_PAIR_QUERY36 = slq_new (192, 0, [6],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "12/5", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery37 (.four <true,false,true> fourDatum1) *)
let C977AV_PAIR_QUERY37 = slq_new (192, 0, [7],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "12/5", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery38 (.four <true,false,true> fourDatum9) *)
let C977AV_PAIR_QUERY38 = slq_new (192, 0, [8],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "87/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery39 (.four <true,false,true> fourDatum7) *)
let C977AV_PAIR_QUERY39 = slq_new (192, 0, [9],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "113/50")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery40 (.four <false,false,true> fourDatum1) *)
let C977AV_PAIR_QUERY40 = slq_new (192, 1, [0],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "1", nlin_rat "8/5")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery41 (.four <false,false,true> fourDatum7) *)
let C977AV_PAIR_QUERY41 = slq_new (192, 1, [2],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery42 (.four <false,false,true> fourDatum5) *)
let C977AV_PAIR_QUERY42 = slq_new (192, 1, [3],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "87/50", nlin_rat "2")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery43 (.four <false,false,true> fourDatum9) *)
let C977AV_PAIR_QUERY43 = slq_new (192, 1, [5],
  [(nlin_rat "457/500", nlin_rat "3"); (nlin_rat "113/50", nlin_rat "1")],
  [(nlin_rat "457/500", nlin_rat "2"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery44 (.four <true,false,true> fourDatum8) *)
let C977AV_PAIR_QUERY44 = slq_new (192, 1, [6],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "2")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery45 (.four <true,false,true> fourDatum0) *)
let C977AV_PAIR_QUERY45 = slq_new (192, 1, [7],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "113/50", nlin_rat "3")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery46 (.four <true,false,true> fourDatum10) *)
let C977AV_PAIR_QUERY46 = slq_new (192, 1, [8],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "8/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;
(* Lean: pairQuery47 (.four <true,false,true> fourDatum2) *)
let C977AV_PAIR_QUERY47 = slq_new (192, 1, [9],
  [(nlin_rat "1", nlin_rat "1543/500"); (nlin_rat "3", nlin_rat "12/5")],
  [(nlin_rat "2", nlin_rat "1543/500"); (nlin_rat "33/20", nlin_rat "47/20")]);;

(* ------------------------------------------------------------------------- *)
(* Generic enumeration of disjoint vectors (Lean enumerateVectors etc.).     *)
(* ------------------------------------------------------------------------- *)

(* List.flatMap *)
let c977av_flatmap = new_recursive_definition list_RECURSION
 `(c977av_flatmap (f:A->(B)list) [] = []) /\
  (c977av_flatmap f (CONS h t) = APPEND (f h) (c977av_flatmap f t))`;;

(* List.sum on Nat *)
let c977av_lsum = new_recursive_definition list_RECURSION
 `(c977av_lsum [] = 0) /\ (c977av_lsum (CONS (h:num) t) = h + c977av_lsum t)`;;

(* Lean: enumerateVectors *)
let c977av_enum = new_recursive_definition list_RECURSION
 `(c977av_enum [] (used:A->bool) = [[]]) /\
  (c977av_enum (CONS d ds) used =
     c977av_flatmap (\m. if DISJOINT m used then MAP (CONS m) (c977av_enum ds (used UNION m)) else []) d)`;;

(* Lean: countVectors *)
let c977av_count = new_recursive_definition list_RECURSION
 `(c977av_count [] (used:A->bool) = 1) /\
  (c977av_count (CONS d ds) used =
     c977av_lsum (MAP (\m. if DISJOINT m used then c977av_count ds (used UNION m) else 0) d))`;;

let C977AV_MEM_FLATMAP = prove
 (`forall (f:A->(B)list) l x. MEM x (c977av_flatmap f l) <=> exists y. MEM y l /\ MEM x (f y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[c977av_flatmap; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

let C977AV_LENGTH_FLATMAP = prove
 (`forall (f:A->(B)list) l. LENGTH (c977av_flatmap f l) = c977av_lsum (MAP (\x. LENGTH (f x)) l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[c977av_flatmap; c977av_lsum; MAP; LENGTH; LENGTH_APPEND]);;

let C977AV_PAIRWISE_APPEND = prove
 (`forall (R:A->A->bool) l m. PAIRWISE R (APPEND l m) <=>
      PAIRWISE R l /\ PAIRWISE R m /\ (forall x y. MEM x l /\ MEM y m ==> R x y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; PAIRWISE; MEM; ALL_APPEND] THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

(* Lean: actual_owners_mem_enumerateVectors *)
let C977AV_ACTUAL_OWNERS_MEM_ENUMERATEVECTORS = prove
 (`forall (ds:((A->bool)list)list) owners used.
     ALL2 (\m d. MEM m d) owners ds /\ (forall m. MEM m owners ==> DISJOINT m used) /\
     PAIRWISE DISJOINT owners
     ==> MEM owners (c977av_enum ds used)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2; c977av_enum; MEM] THEN
  X_GEN_TAC `used:A->bool` THEN REWRITE_TAC[PAIRWISE] THEN STRIP_TAC THEN
  REWRITE_TAC[C977AV_MEM_FLATMAP] THEN EXISTS_TAC `h':A->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (h':A->bool) used` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MEM_MAP; CONS_11] THEN EXISTS_TAC `t':(A->bool)list` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    free_in `t:((A->bool)list)list` (concl th) && not (free_in `h:(A->bool)list` (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:A->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[DISJOINT_SYM] THEN REWRITE_TAC[DISJOINT_UNION] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `ALL (DISJOINT (h':A->bool)) t'` THEN REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(MP_TAC o SPEC `n:A->bool`) THEN ASM_REWRITE_TAC[]]);;

(* Lean: enumerateVectors_length *)
let C977AV_ENUMERATEVECTORS_LENGTH = prove
 (`forall (ds:((A->bool)list)list) used. LENGTH (c977av_enum ds used) = c977av_count ds used`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[c977av_enum; c977av_count; LENGTH; ONE] THEN
  REWRITE_TAC[C977AV_LENGTH_FLATMAP] THEN GEN_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH_MAP; LENGTH]);;

let C977AV_FLATMAP_NODUP = prove
 (`forall (f:A->(B)list) l.
     PAIRWISE (\x y. ~(x = y)) l /\ (forall x. MEM x l ==> PAIRWISE (\u v. ~(u = v)) (f x)) /\
     (forall x y u v. MEM x l /\ MEM y l /\ ~(x = y) /\ MEM u (f x) /\ MEM v (f y) ==> ~(u = v))
     ==> PAIRWISE (\u v. ~(u = v)) (c977av_flatmap f l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[c977av_flatmap; PAIRWISE; C977AV_PAIRWISE_APPEND] THEN
  REWRITE_TAC[MEM; C977AV_MEM_FLATMAP] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    UNDISCH_TAC `ALL (\y. ~((h:A) = y)) t` THEN REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[]]);;

(* Lean: enumerateVectors_nodup *)
let C977AV_ENUMERATEVECTORS_NODUP = prove
 (`forall (ds:((A->bool)list)list) used.
     ALL (\d. PAIRWISE (\x y. ~(x = y)) d) ds ==> PAIRWISE (\x y. ~(x = y)) (c977av_enum ds used)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[c977av_enum; PAIRWISE; ALL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977AV_FLATMAP_NODUP THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[PAIRWISE] THEN
    REWRITE_TAC[PAIRWISE_MAP; CONS_11] THEN ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN BETA_TAC THEN
    REPEAT(COND_CASES_TAC THEN REWRITE_TAC[MEM]) THEN
    REWRITE_TAC[MEM_MAP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11]]);;

(* ALL2 and PAIRWISE from indexwise facts *)
let C977AV_ALL2_EL = prove
 (`forall (P:A->B->bool) l1 l2. LENGTH l1 = LENGTH l2 /\ (forall i. i < LENGTH l1 ==> P (EL i l1) (EL i l2))
     ==> ALL2 P l1 l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL2; LENGTH; NOT_SUC; SUC_INJ] THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[EL; HD; LT_0];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN ASM_REWRITE_TAC[EL; TL; LT_SUC]]);;

let C977AV_PAIRWISE_EL = prove
 (`forall (R:A->A->bool) l. (forall i j. i < LENGTH l /\ j < LENGTH l /\ i < j ==> R (EL i l) (EL j l))
     ==> PAIRWISE R l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[PAIRWISE; LENGTH] THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_EXISTS_EL] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `SUC i`]) THEN ASM_REWRITE_TAC[EL; HD; TL; LT_SUC; LT_0];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`SUC i`; `SUC j`]) THEN ASM_REWRITE_TAC[EL; TL; LT_SUC]]);;

(* ------------------------------------------------------------------------- *)
(* Pair single and combined domains.                                         *)
(* ------------------------------------------------------------------------- *)

(* Lean: pairCode *)
let c977av_pair_code = new_definition `c977av_pair_code = [12; 48; 192]`;;
let C977AV_PAIR_CODE_EL = el_lookups c977av_pair_code;;

(* Lean: pairSingleAllowed *)
let c977av_psa = new_definition
 `c977av_psa (i:num) (k:num) : (num->bool)list =
    if i = 0 then (if k = 0 then [{}; {6}; {8}] else [{}; {5}; {8}])
    else if i = 1 then [{}; {7}; {9}]
    else if k = 0 then [{}; {1}; {3}] else [{}; {1}; {4}]`;;

let C977AV_PSA = Array.init 3 (fun i -> Array.init 2 (fun k ->
  (REWRITE_CONV[c977av_psa] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[])
    (list_mk_comb(`c977av_psa`, [mk_small_numeral i; mk_small_numeral k]))));;

(* |- !k. k < n <=> k = n-1 \/ ... \/ k = 0, by the LT recursion (no arithmetic case explosion) *)
let C977AV_LT_CASES =
  let tbl = Hashtbl.create 20 in
  fun n ->
    try Hashtbl.find tbl n with Not_found ->
    let k = `k:num` in
    let rec go m =
      if m = 0 then SPEC k (CONJUNCT1 LT) else
      let th1 = AP_TERM (mk_comb(`(<):num->num->bool`, k)) (num_CONV (mk_small_numeral m)) in
      let th2 = SPECL [k; mk_small_numeral (m - 1)] (CONJUNCT2 LT) in
      let th3 = TRANS th1 th2 in
      CONV_RULE (RAND_CONV (RAND_CONV (K (go (m - 1))))) th3 in
    let th = GEN k (REWRITE_RULE[] (go n)) in
    Hashtbl.add tbl n th; th;;

(* case split on a bounded index v < n (an assumption) *)
let C977AV_ENUM_TAC v n =
  let lt = mk_binop `(<):num->num->bool` v (mk_small_numeral n) in
  FIRST_ASSUM(fun th -> if concl th = lt then MP_TAC(EQ_MP (SPEC v (C977AV_LT_CASES n)) th) else NO_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC);;

let C977AV_IK_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  C977AV_ENUM_TAC `i:num` 3 THEN C977AV_ENUM_TAC `k:num` 2;;

(* Lean: pair_empty_allowed *)
let C977AV_PAIR_EMPTY_ALLOWED = prove
 (`forall i k. i < 3 /\ k < 2 ==> MEM {} (c977av_psa i k)`,
  C977AV_IK_TAC THEN REWRITE_TAC(List.concat (map Array.to_list (Array.to_list C977AV_PSA))) THEN
  REWRITE_TAC[MEM]);;

let C977AV_PAIR_QUERY_TBL = Array.of_list
  [C977AV_PAIR_QUERY0; C977AV_PAIR_QUERY1; C977AV_PAIR_QUERY2; C977AV_PAIR_QUERY3; C977AV_PAIR_QUERY4;
   C977AV_PAIR_QUERY5; C977AV_PAIR_QUERY6; C977AV_PAIR_QUERY7; C977AV_PAIR_QUERY8; C977AV_PAIR_QUERY9;
   C977AV_PAIR_QUERY10; C977AV_PAIR_QUERY11; C977AV_PAIR_QUERY12; C977AV_PAIR_QUERY13; C977AV_PAIR_QUERY14;
   C977AV_PAIR_QUERY15; C977AV_PAIR_QUERY16; C977AV_PAIR_QUERY17; C977AV_PAIR_QUERY18; C977AV_PAIR_QUERY19;
   C977AV_PAIR_QUERY20; C977AV_PAIR_QUERY21; C977AV_PAIR_QUERY22; C977AV_PAIR_QUERY23; C977AV_PAIR_QUERY24;
   C977AV_PAIR_QUERY25; C977AV_PAIR_QUERY26; C977AV_PAIR_QUERY27; C977AV_PAIR_QUERY28; C977AV_PAIR_QUERY29;
   C977AV_PAIR_QUERY30; C977AV_PAIR_QUERY31; C977AV_PAIR_QUERY32; C977AV_PAIR_QUERY33; C977AV_PAIR_QUERY34;
   C977AV_PAIR_QUERY35; C977AV_PAIR_QUERY36; C977AV_PAIR_QUERY37; C977AV_PAIR_QUERY38; C977AV_PAIR_QUERY39;
   C977AV_PAIR_QUERY40; C977AV_PAIR_QUERY41; C977AV_PAIR_QUERY42; C977AV_PAIR_QUERY43; C977AV_PAIR_QUERY44;
   C977AV_PAIR_QUERY45; C977AV_PAIR_QUERY46; C977AV_PAIR_QUERY47];;

(* the query of pairQueries i k refuting the singleton {j} *)
let c977av_pair_query i k j =
  let m = List.nth [12; 48; 192] i in
  let qs = Array.to_list (Array.sub C977AV_PAIR_QUERY_TBL (8 * (2 * i + k)) 8) in
  let tgt = mk_eq(list_mk_comb(`auxown`, [mk_small_numeral k; `c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`]),
                  set_tm [j]) in
  let ownt = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  find (fun th -> let hs = fst (splitlist dest_imp (snd (strip_forall (concl th)))) in
                  List.mem tgt hs && List.mem ownt hs) qs;;

let C977AV_COVER_BODY = `MEM {j} (c977av_psa i k) \/
   (forall c1 c2 a b l. &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
                  owned c1 c2 a b l = bitset (EL i c977av_pair_code) /\ auxown k c1 c2 a b l = {j}
                  ==> false)`;;

let c977av_cover_inst i k j =
  let tm = subst [mk_small_numeral i, `i:num`; mk_small_numeral k, `k:num`; mk_small_numeral j, `j:num`]
             C977AV_COVER_BODY in
  let m = List.nth [12; 48; 192] i in
  let al = map (fun t -> try map dest_small_numeral (dest_setenum t) with Failure _ -> [])
             (dest_list (rhs (concl C977AV_PSA.(i).(k)))) in
  prove(tm,
    REWRITE_TAC(Array.to_list C977AV_PAIR_CODE_EL @ [C977AV_PSA.(i).(k)]) THEN
    if List.mem [j] al then DISJ1_TAC THEN REWRITE_TAC[MEM] else
    (DISJ2_TAC THEN MP_TAC (c977av_pair_query i k j) THEN
     REWRITE_TAC[bitset_bits m; set_of_list] THEN MESON_TAC[]));;

let C977AV_COVER_INSTS =
  List.concat (map (fun i -> List.concat (map (fun k -> map (fun j -> c977av_cover_inst i k j) (0--9)) [0;1])) [0;1;2]);;

(* Lean: pair_singleton_cover  (a checked query of pairQueries i k with mask pairCode i, kind k and
   owned {j} is given by its soundness statement) *)
let C977AV_PAIR_SINGLETON_COVER = prove
 (mk_forall(`i:num`, mk_forall(`k:num`, mk_forall(`j:num`,
    mk_imp(`i < 3 /\ k < 2 /\ j < 10`, C977AV_COVER_BODY)))),
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  C977AV_ENUM_TAC `i:num` 3 THEN C977AV_ENUM_TAC `k:num` 2 THEN C977AV_ENUM_TAC `j:num` 10 THEN
  FIRST (map ACCEPT_TAC C977AV_COVER_INSTS));;

(* Lean: pair_budget_identity *)
let C977AV_PAIR_BUDGET_IDENTITY = prove
 (`forall i k. i < 3 /\ k < 2 ==> EL i c977av_pair_code IN auxex k /\ CARD (ccc977ri_family INTER auxex k) = 3`,
  C977AV_IK_TAC THEN REWRITE_TAC(Array.to_list C977AV_PAIR_CODE_EL) THEN
  REWRITE_TAC[card_exempt C977AV_FAM 0; card_exempt C977AV_FAM 1] THEN
  CONV_TAC AUXEX_CONV);;

(* the six budget half domains (Lean pair_single_actual at literal i, k) *)
let C977AV_PAIR_HDOM = Array.init 3 (fun i -> Array.init 2 (fun k ->
  let m = List.nth [12; 48; 192] i in
  let al = map (fun t -> try map dest_small_numeral (dest_setenum t) with Failure _ -> [])
             (dest_list (rhs (concl C977AV_PSA.(i).(k)))) in
  let th = pk_budget_hdom C977AV_FAM m k al in
  let psa = C977AV_PSA.(i).(k) in
  if rand (concl th) <> rhs (concl psa) then failwith "C977AV_PAIR_HDOM: list" else
  EQ_MP (AP_TERM (rator (concl th)) (SYM psa)) th));;

(* Lean: pair_single_actual *)
let C977AV_PAIR_SINGLE_ACTUAL = prove
 (`forall i k. i < 3 /\ k < 2 ==> hdom ccc977ri_family (EL i c977av_pair_code) k (c977av_psa i k)`,
  C977AV_IK_TAC THEN REWRITE_TAC(Array.to_list C977AV_PAIR_CODE_EL) THEN
  FIRST (map ACCEPT_TAC (List.concat (map Array.to_list (Array.to_list C977AV_PAIR_HDOM)))));;

(* Lean: pairCombinedAllowed *)
let c977av_pca = new_definition
 `c977av_pca (i:num) = c977av_flatmap (\x. MAP (\y. combown x y) (c977av_psa i 1)) (c977av_psa i 0)`;;

let C977AV_PCA_MEM = prove
 (`forall i x y. MEM x (c977av_psa i 0) /\ MEM y (c977av_psa i 1) ==> MEM (combown x y) (c977av_pca i)`,
  REWRITE_TAC[c977av_pca; C977AV_MEM_FLATMAP; MEM_MAP] THEN MESON_TAC[]);;

(* Lean: pair_combined_actual *)
let C977AV_PAIR_COMBINED_ACTUAL = prove
 (`forall i. i < 3 ==> cdom ccc977ri_family (EL i c977av_pair_code) (c977av_pca i)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PK_PRODUCT THEN
  EXISTS_TAC `c977av_psa i 0` THEN EXISTS_TAC `c977av_psa i 1` THEN
  ASM_SIMP_TAC[C977AV_PAIR_SINGLE_ACTUAL; ARITH; C977AV_PCA_MEM]);;

(* the explicit literal form of pairCombinedAllowed i (sorted literals) *)
let C977AV_PCA = Array.init 3 (fun i ->
  let th = (REWRITE_CONV[c977av_pca; C977AV_PSA.(i).(0); C977AV_PSA.(i).(1);
                         c977av_flatmap; MAP; APPEND] THENC DEPTH_CONV BETA_CONV)
           (mk_comb(`c977av_pca`, mk_small_numeral i)) in
  let elts = dest_list (rhs (concl th)) in
  let lit t = let x = lhand t and y = rand t in
    mk_numset (numset_of x @ map (fun j -> j + 10) (numset_of y)) in
  let target = mk_list(map lit elts, `:num->bool`) in
  let eq = prove(mk_eq(rhs (concl th), target),
    REWRITE_TAC[CONS_11; combown; IMAGE_CLAUSES] THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DISJ_ACI]) in
  TRANS th eq);;

(* ------------------------------------------------------------------------- *)
(* Historical owner order.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Lean: auxiliaryCode *)
let c977av_code = new_definition
 `c977av_code = [1; 2; 12; 48; 192; 256; 512; 2048; 4096; 8192; 16384; 32768]`;;
let C977AV_CODE_EL = el_lookups c977av_code;;
let C977AV_CODE_LIST = oo_list_facts C977AV_FAM (rand (concl c977av_code));;
let C977AV_CODE_LENGTH = (REWRITE_CONV[c977av_code; LENGTH] THENC NUM_REDUCE_CONV) `LENGTH c977av_code`;;

(* Lean: auxiliary_code_mem *)
let C977AV_AUXILIARY_CODE_MEM = prove
 (`forall i. i < 12 ==> EL i c977av_code IN ccc977ri_family`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_LIST_MEMBER THEN
  REWRITE_TAC[C977AV_CODE_LENGTH; c977av_code] THEN ASM_REWRITE_TAC[fst C977AV_CODE_LIST]);;

(* Lean: auxiliary_code_injective *)
let C977AV_AUXILIARY_CODE_INJECTIVE = prove
 (`forall i j. i < 12 /\ j < 12 /\ EL i c977av_code = EL j c977av_code ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_DISTINCT_EL THEN
  EXISTS_TAC `c977av_code` THEN ASM_REWRITE_TAC[C977AV_CODE_LENGTH] THEN
  REWRITE_TAC[c977av_code; snd C977AV_CODE_LIST]);;

(* Lean: orderedOwner *)
let c977av_ordered_owner = new_definition
 `c977av_ordered_owner (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (i:num) =
    oidx c1 c2 a b l (EL i c977av_code)`;;

(* Lean: ordered_owner_code *)
let C977AV_ORDERED_OWNER_CODE = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\ i < 12
     ==> ownmask (c1 (c977av_ordered_owner c1 c2 a b l i)) (c2 (c977av_ordered_owner c1 c2 a b l i))
                 (a (c977av_ordered_owner c1 c2 a b l i)) (b (c977av_ordered_owner c1 c2 a b l i)) l =
         EL i c977av_code`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c977av_ordered_owner] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `ccc977ri_family`; `EL i c977av_code`] OO_CODE) THEN
  ASM_SIMP_TAC[C977AV_AUXILIARY_CODE_MEM]);;

(* Lean: ordered_owner_injective *)
let C977AV_ORDERED_OWNER_INJECTIVE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> forall i j. i < 12 /\ j < 12 /\ c977av_ordered_owner c1 c2 a b l i = c977av_ordered_owner c1 c2 a b l j
               ==> i = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C977AV_AUXILIARY_CODE_INJECTIVE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `i:num` (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977AV_ORDERED_OWNER_CODE)) THEN
  MP_TAC(SPEC `j:num` (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977AV_ORDERED_OWNER_CODE)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Lean: ordered_owner_bijective  (Function.Bijective on Fin 12) *)
let C977AV_ORDERED_OWNER_BIJECTIVE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> (forall i j. i < 12 /\ j < 12 /\ c977av_ordered_owner c1 c2 a b l i = c977av_ordered_owner c1 c2 a b l j
                ==> i = j) /\
         (forall k. k < 12 ==> exists i. i < 12 /\ c977av_ordered_owner c1 c2 a b l i = k)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C977AV_ORDERED_OWNER_INJECTIVE) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (c977av_ordered_owner c1 c2 a b l) {i | i < 12} = {k | k < 12}` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[c977av_ordered_owner; OIDX_LT];
      W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CARD_NUMSEG_LT]]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The saved necessary domains (Lean auxiliaryDomain).                       *)
(* ------------------------------------------------------------------------- *)

let C977AV_SPEC_N = [1; 3; -1; -1; -1; 6; 8; 13; 17; 19; 21; 24];;
let C977AV_SPEC_CDOM = Array.of_list (map (fun n ->
  if n < 0 then TRUTH else pk_combined C977AV_FAM n) C977AV_SPEC_N);;

(* Lean: auxiliaryDomain *)
let c977av_aux_domain = new_definition (mk_eq(`c977av_aux_domain:((num->bool)list)list`,
  mk_list(map (fun i -> let n = List.nth C977AV_SPEC_N i in
                  if n < 0 then mk_comb(`c977av_pca`, mk_small_numeral (i - 2))
                  else rand (concl C977AV_SPEC_CDOM.(i))) (0--11), `:(num->bool)list`)));;
let C977AV_AUX_DOMAIN_EL = el_lookups c977av_aux_domain;;

(* cdom fam (EL i code) (EL i auxiliaryDomain), literal i *)
let C977AV_AUX_CDOM = Array.init 12 (fun i ->
  let th = if List.nth C977AV_SPEC_N i < 0 then
             CONV_RULE (RATOR_CONV (RAND_CONV (REWRITE_CONV(Array.to_list C977AV_PAIR_CODE_EL))))
               (MP (SPEC (mk_small_numeral (i - 2)) C977AV_PAIR_COMBINED_ACTUAL)
                   (EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral (i - 2)) `3`))))
           else C977AV_SPEC_CDOM.(i) in
  let m = rand (rator (concl th)) in
  if m <> rhs (concl C977AV_CODE_EL.(i)) then failwith "C977AV_AUX_CDOM: mask" else
  let th1 = CONV_RULE (RATOR_CONV (RAND_CONV (K (SYM C977AV_CODE_EL.(i))))) th in
  CONV_RULE (RAND_CONV (K (SYM C977AV_AUX_DOMAIN_EL.(i)))) th1);;

(* Lean: auxiliary_domain_actual *)
let C977AV_AUXILIARY_DOMAIN_ACTUAL = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> forall i. i < 12 ==> MEM (ooaux c1 c2 a b l (EL i c977av_code)) (EL i c977av_aux_domain)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CDOM_OWNER THEN EXISTS_TAC `ccc977ri_family` THEN
  ASM_SIMP_TAC[C977AV_AUXILIARY_CODE_MEM] THEN C977AV_ENUM_TAC `i:num` 12 THEN
  FIRST (map ACCEPT_TAC (Array.to_list C977AV_AUX_CDOM)));;

(* ------------------------------------------------------------------------- *)
(* Four finite arc-support pruning rounds.                                   *)
(* ------------------------------------------------------------------------- *)

(* Lean: pruningDomain1 *)
let c977av_prune1 = new_definition
 `c977av_prune1 : ((num->bool)list)list =
    [
     [{2, 12}];
     [{0, 10}];
     [{}; {15}; {18}; {6}; {6, 15}; {6, 18}; {8}; {8, 15}; {8, 18}];
     [{}; {17}; {19}; {7}; {7, 17}; {7, 19}; {9}; {9, 17}; {9, 19}];
     [{}; {11}; {14}; {1}; {1, 11}; {1, 14}; {3}; {3, 11}; {3, 14}];
     [{4, 13}; {4, 13, 15}; {4, 13, 16}; {1, 4, 13}; {1, 4, 13, 15}; {1, 4, 13, 16}; {4, 5, 13}; {4, 5, 13, 15}; {4, 5, 13, 16}];
     [{4, 15}; {4, 16}; {4, 18}; {4, 13, 15}; {4, 13, 16}; {4, 15, 16}; {4, 15, 18}; {4, 16, 18}; {6, 15}; {6, 16}; {6, 18}; {6, 15, 16}; {6, 15, 18}; {6, 16, 18}; {8, 15}; {8, 16}; {8, 18}; {8, 15, 16}; {8, 15, 18}; {8, 16, 18}; {4, 5, 16}; {4, 5, 13, 16}; {4, 5, 15, 16}; {4, 5, 16, 18}; {4, 6, 15}; {4, 6, 16}; {4, 6, 18}; {4, 6, 13, 15}; {4, 6, 13, 16}; {4, 6, 15, 16}; {4, 6, 15, 18}; {4, 6, 16, 18}; {4, 8, 15}; {4, 8, 16}; {4, 8, 18}; {4, 8, 13, 15}; {4, 8, 13, 16}; {4, 8, 15, 16}; {4, 8, 15, 18}; {4, 8, 16, 18}; {4, 9, 16}; {4, 9, 13, 16}; {4, 9, 15, 16}; {5, 8, 16}; {5, 8, 15, 16}; {5, 8, 16, 18}; {6, 8, 15}; {6, 8, 16}; {6, 8, 18}; {6, 8, 15, 16}; {6, 8, 15, 18}; {6, 8, 16, 18}];
     [{1, 11}; {1, 13}; {1, 14}; {1, 11, 13}; {1, 11, 14}; {1, 13, 14}; {3, 11}; {3, 13}; {3, 14}; {3, 11, 13}; {3, 11, 14}; {3, 13, 14}; {5, 11}; {5, 13}; {5, 14}; {5, 11, 13}; {5, 11, 14}; {5, 13, 14}; {5, 13, 16}; {5, 13, 17}; {5, 14, 16}; {1, 3, 11}; {1, 3, 13}; {1, 3, 14}; {1, 3, 11, 13}; {1, 3, 11, 14}; {1, 3, 13, 14}; {1, 4, 13}; {1, 4, 11, 13}; {1, 4, 13, 14}; {1, 5, 11}; {1, 5, 13}; {1, 5, 14}; {1, 5, 11, 13}; {1, 5, 11, 14}; {1, 5, 13, 14}; {1, 5, 13, 16}; {1, 5, 13, 17}; {1, 5, 14, 16}; {3, 5, 11}; {3, 5, 13}; {3, 5, 14}; {3, 5, 11, 13}; {3, 5, 11, 14}; {3, 5, 13, 14}; {3, 5, 13, 16}; {3, 5, 14, 16}; {4, 5, 13}; {4, 5, 11, 13}; {4, 5, 13, 14}; {4, 5, 13, 16}; {4, 5, 13, 17}];
     [{1, 11}; {1, 11, 13}; {1, 3, 11}];
     [{6, 15}; {6, 15, 18}; {4, 6, 15}];
     [{8, 18}; {8, 16, 18}; {9, 19}; {9, 16, 19}; {6, 8, 18}; {7, 9, 19}; {8, 9, 18}; {8, 9, 19}; {8, 9, 16, 18}; {8, 9, 16, 19}; {8, 9, 18, 19}];
     [{3, 14}; {3, 11, 14}; {3, 14, 17}; {7, 17}; {7, 14, 17}; {7, 17, 19}; {3, 5, 14}; {3, 5, 14, 17}; {3, 7, 14, 17}; {5, 7, 17}; {5, 7, 14, 17}]
    ]`;;

(* Lean: pruningDomain2 *)
let c977av_prune2 = new_definition
 `c977av_prune2 : ((num->bool)list)list =
    [
     [{2, 12}];
     [{0, 10}];
     [{}; {18}; {8}; {8, 18}];
     [{}; {17}; {19}; {7}; {7, 17}; {7, 19}; {9}; {9, 17}; {9, 19}];
     [{}; {14}; {3}; {3, 14}];
     [{4, 13}; {4, 13, 16}; {4, 5, 13}; {4, 5, 13, 16}];
     [{8, 16}; {8, 18}; {8, 16, 18}; {5, 8, 16}; {5, 8, 16, 18}];
     [{3, 14}; {5, 14}; {5, 14, 16}; {3, 5, 14}; {3, 5, 14, 16}];
     [{1, 11}; {1, 3, 11}];
     [{6, 15}; {6, 15, 18}];
     [{8, 18}; {8, 16, 18}; {9, 19}; {9, 16, 19}; {7, 9, 19}; {8, 9, 18}; {8, 9, 19}; {8, 9, 16, 18}; {8, 9, 16, 19}; {8, 9, 18, 19}];
     [{3, 14}; {3, 14, 17}; {7, 17}; {7, 14, 17}; {7, 17, 19}; {3, 5, 14}; {3, 5, 14, 17}; {3, 7, 14, 17}; {5, 7, 17}; {5, 7, 14, 17}]
    ]`;;

(* Lean: pruningDomain3 *)
let c977av_prune3 = new_definition
 `c977av_prune3 : ((num->bool)list)list =
    [
     [{2, 12}];
     [{0, 10}];
     [{}; {18}];
     [{}; {17}; {19}; {7}; {7, 17}; {7, 19}; {9}; {9, 17}; {9, 19}];
     [{}; {3}];
     [{4, 13}; {4, 13, 16}; {4, 5, 13}; {4, 5, 13, 16}];
     [{8, 16}; {8, 18}; {8, 16, 18}; {5, 8, 16}; {5, 8, 16, 18}];
     [{3, 14}; {5, 14}; {5, 14, 16}; {3, 5, 14}; {3, 5, 14, 16}];
     [{1, 11}; {1, 3, 11}];
     [{6, 15}; {6, 15, 18}];
     [{9, 19}; {9, 16, 19}; {7, 9, 19}];
     [{7, 17}; {7, 17, 19}; {5, 7, 17}]
    ]`;;

(* Lean: pruningDomain4 *)
let c977av_prune4 = new_definition
 `c977av_prune4 : ((num->bool)list)list =
    [
     [{2, 12}];
     [{0, 10}];
     [{}; {18}];
     [{}];
     [{}; {3}];
     [{4, 13}; {4, 13, 16}; {4, 5, 13}; {4, 5, 13, 16}];
     [{8, 16}; {8, 18}; {8, 16, 18}; {5, 8, 16}; {5, 8, 16, 18}];
     [{3, 14}; {5, 14}; {5, 14, 16}; {3, 5, 14}; {3, 5, 14, 16}];
     [{1, 11}; {1, 3, 11}];
     [{6, 15}; {6, 15, 18}];
     [{9, 19}; {9, 16, 19}];
     [{7, 17}; {5, 7, 17}]
    ]`;;

(* Lean: pruningStage *)
let c977av_stage = new_definition
 `c977av_stage (s:num) = EL s [c977av_aux_domain; c977av_prune1; c977av_prune2; c977av_prune3; c977av_prune4]`;;

let C977AV_STAGE = Array.init 5 (fun s ->
  (REWRITE_CONV[c977av_stage] THENC ONCE_DEPTH_CONV EL_CONV) (mk_comb(`c977av_stage`, mk_small_numeral s)));;

(* Lean: PruningStepCheck *)
let c977av_step_check = new_definition
 `c977av_step_check (old:((num->bool)list)list) (next:((num->bool)list)list) (i:num) <=>
    forall m. MEM m (EL i old) /\ (forall j. j < 12 /\ ~(j = i) ==> exists n. MEM n (EL j old) /\ DISJOINT m n)
        ==> MEM m (EL i next)`;;

(* literal forms |- EL i (stage s) = [literal sets] *)
let C977AV_LIT = Array.init 5 (fun s -> Array.init 12 (fun i ->
  if s = 0 then
    let th = C977AV_AUX_DOMAIN_EL.(i) in
    if List.nth C977AV_SPEC_N i < 0 then TRANS th C977AV_PCA.(i - 2) else th
  else (el_lookups (List.nth [c977av_prune1; c977av_prune2; c977av_prune3; c977av_prune4] (s - 1))).(i)));;

let c977av_sets th = map numset_of (dest_list (rhs (concl th)));;
let c977av_disjoint x y = not (exists (fun a -> List.mem a y) x);;

let C977AV_DISJ_CONV =
  REWRITE_CONV[DISJOINT_INSERT; DISJOINT_EMPTY; IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV THENC
  REWRITE_CONV[];;

(* one pruning round for owner i:  |- c977av_step_check OLD NEXT i  (OLD, NEXT the stage constants) *)
let c977av_step_thm s i =
  let oldc = rhs (concl C977AV_STAGE.(s)) and nextc = rhs (concl C977AV_STAGE.(s + 1)) in
  let old = Array.map c977av_sets C977AV_LIT.(s) and next = c977av_sets C977AV_LIT.(s + 1).(i) in
  let goal = list_mk_comb(`c977av_step_check`, [oldc; nextc; mk_small_numeral i]) in
  let wit_tac (asl, w) =
    (* w : (!j. j < 12 /\ ~(j = i) ==> ?n. MEM n (EL j OLD) /\ DISJOINT S n) ==> MEM-disjunction *)
    let hyp = lhand w in
    let body = snd (strip_exists (snd (splitlist dest_imp (snd (dest_forall hyp))))) in
    let st = lhand (rand body) in
    let sl = numset_of st in
    if List.mem sl next then (DISCH_TAC THEN REWRITE_TAC[]) (asl, w) else
    let j = find (fun j -> j <> i && List.for_all (fun n -> not (c977av_disjoint sl n)) old.(j)) (0--11) in
    (DISCH_THEN(MP_TAC o SPEC (mk_small_numeral j)) THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[C977AV_LIT.(s).(j); MEM; RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
     REWRITE_TAC[DISJOINT_INSERT; DISJOINT_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]) (asl, w) in
  prove(goal,
    REWRITE_TAC[c977av_step_check; C977AV_LIT.(s).(i); C977AV_LIT.(s + 1).(i)] THEN
    GEN_TAC THEN REWRITE_TAC[MEM; IMP_CONJ] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN wit_tac);;

let C977AV_STEP = Array.init 4 (fun s -> Array.init 12 (fun i -> c977av_step_thm s i));;

(* Lean: pruning_step_checked *)
let C977AV_PRUNING_STEP_CHECKED = prove
 (`forall s i. s < 4 /\ i < 12 ==> c977av_step_check (c977av_stage s) (c977av_stage (s + 1)) i`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  C977AV_ENUM_TAC `s:num` 4 THEN C977AV_ENUM_TAC `i:num` 12 THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC(Array.to_list C977AV_STAGE) THEN
  FIRST (map ACCEPT_TAC (List.concat (map Array.to_list (Array.to_list C977AV_STEP)))));;

(* Lean: actual_pruning_step *)
let C977AV_ACTUAL_PRUNING_STEP = prove
 (`forall c1 c2 a b l old next. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     (forall i. i < 12 ==> c977av_step_check old next i) /\
     (forall i. i < 12 ==> MEM (ooaux c1 c2 a b l (EL i c977av_code)) (EL i old))
     ==> forall i. i < 12 ==> MEM (ooaux c1 c2 a b l (EL i c977av_code)) (EL i next)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> try fst(dest_const(fst(strip_comb(rand(snd(dest_forall(concl th))))))) = "c977av_step_check" with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[c977av_step_check] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  EXISTS_TAC `ooaux c1 c2 a b l (EL j c977av_code)` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC OO_AUX_DISJOINT THEN EXISTS_TAC `ccc977ri_family` THEN
  ASM_SIMP_TAC[C977AV_AUXILIARY_CODE_MEM] THEN ASM_MESON_TAC[C977AV_AUXILIARY_CODE_INJECTIVE]);;

(* Lean: pruned_auxiliary_domain_actual *)
let C977AV_PRUNED_AUXILIARY_DOMAIN_ACTUAL = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> forall i. i < 12 ==> MEM (ooaux c1 c2 a b l (EL i c977av_code)) (EL i c977av_prune4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall s. s < 5 ==> forall i. i < 12 ==> MEM (ooaux c1 c2 a b l (EL i c977av_code)) (EL i (c977av_stage s))`
    (MP_TAC o SPEC `4`) THENL
   [INDUCT_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[C977AV_STAGE.(0)] THEN
      MATCH_MP_TAC C977AV_AUXILIARY_DOMAIN_ACTUAL THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) && is_forall (rand (concl th)))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `SUC s < 5` THEN ARITH_TAC; DISCH_TAC] THEN
      REWRITE_TAC[ADD1] THEN MATCH_MP_TAC C977AV_ACTUAL_PRUNING_STEP THEN
      EXISTS_TAC `c977av_stage s` THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
        REPEAT STRIP_TAC THEN MATCH_MP_TAC C977AV_PRUNING_STEP_CHECKED THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `SUC s < 5` THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    REWRITE_TAC[C977AV_STAGE.(4); ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* The 57 complete vectors.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Lean: auxiliaryDomains  ((finRange 12).map pruningDomain4) *)
let c977av_domains = new_definition `c977av_domains = c977av_prune4`;;

(* Lean: auxiliaryVectors *)
let c977av_vectors = new_definition `c977av_vectors = c977av_enum c977av_domains {}`;;

(* evaluation of the enumeration by call-by-value on literal sets *)
let C977AV_CS =
  let cs = Compute.bool_compset () in
  Compute.add_thms [c977av_enum; c977av_flatmap; MAP; APPEND; DISJOINT_INSERT; DISJOINT_EMPTY;
    IN_INSERT; EQF_INTRO (SPEC_ALL NOT_IN_EMPTY); UNION_EMPTY; INSERT_UNION_EQ; COND_CLAUSES] cs;
  Compute.add_conv (`(=):num->num->bool`, 2, NUM_EQ_CONV) cs;
  cs;;

(* the explicit table of the 57 vectors *)
let C977AV_VECTORS_EXPLICIT =
  let th = (REWRITE_CONV[c977av_vectors; c977av_domains; c977av_prune4] THENC Compute.CBV_CONV C977AV_CS)
             `c977av_vectors` in
  th;;

(* Lean: auxiliary_vector_count *)
let C977AV_AUXILIARY_VECTOR_COUNT = prove
 (`LENGTH c977av_vectors = 57`,
  REWRITE_TAC[C977AV_VECTORS_EXPLICIT; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* the recursive count agrees (Lean's proof route through enumerateVectors_length) *)
let C977AV_COUNT_VECTORS = prove
 (`c977av_count c977av_domains {} = 57`,
  REWRITE_TAC[GSYM C977AV_ENUMERATEVECTORS_LENGTH; GSYM c977av_vectors; C977AV_AUXILIARY_VECTOR_COUNT]);;

(* Lean: auxiliary_vectors_distinct *)
let C977AV_AUXILIARY_VECTORS_DISTINCT = prove
 (`PAIRWISE (\x y. ~(x = y)) c977av_vectors`,
  REWRITE_TAC[c977av_vectors] THEN MATCH_MP_TAC C977AV_ENUMERATEVECTORS_NODUP THEN
  REWRITE_TAC[c977av_domains; c977av_prune4; ALL; PAIRWISE] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV setlit_eq_dconv) THEN REWRITE_TAC[]);;

(* Lean: actualAuxiliaryVector *)
let c977av_actual = new_definition
 `c977av_actual (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) =
    MAP (\m. ooaux c1 c2 a b l m) c977av_code`;;

(* Lean: actual_auxiliary_slot *)
let C977AV_ACTUAL_AUXILIARY_SLOT = prove
 (`forall c1 c2 a b l i. i < 12 ==> EL i (c977av_actual c1 c2 a b l) = ooaux c1 c2 a b l (EL i c977av_code)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c977av_actual] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_MAP o lhand o snd) THEN
  ASM_REWRITE_TAC[C977AV_CODE_LENGTH] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN REFL_TAC);;

let C977AV_ACTUAL_LENGTH = prove
 (`forall c1 c2 a b l. LENGTH (c977av_actual c1 c2 a b l) = 12`,
  REWRITE_TAC[c977av_actual; LENGTH_MAP; C977AV_CODE_LENGTH]);;

(* Lean: actual_auxiliary_vector_mem *)
let C977AV_ACTUAL_AUXILIARY_VECTOR_MEM = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> MEM (c977av_actual c1 c2 a b l) c977av_vectors`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c977av_vectors] THEN
  MATCH_MP_TAC C977AV_ACTUAL_OWNERS_MEM_ENUMERATEVECTORS THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC C977AV_ALL2_EL THEN
    REWRITE_TAC[C977AV_ACTUAL_LENGTH; c977av_domains] THEN
    REWRITE_TAC[c977av_prune4; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM c977av_prune4] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[C977AV_ACTUAL_AUXILIARY_SLOT] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
      C977AV_PRUNED_AUXILIARY_DOMAIN_ACTUAL) THEN ASM_SIMP_TAC[];
    REWRITE_TAC[DISJOINT_EMPTY];
    MATCH_MP_TAC C977AV_PAIRWISE_EL THEN REWRITE_TAC[C977AV_ACTUAL_LENGTH] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[C977AV_ACTUAL_AUXILIARY_SLOT] THEN
    MATCH_MP_TAC OO_LIST_AUX_DISJOINT THEN EXISTS_TAC `ccc977ri_family` THEN
    ASM_REWRITE_TAC[C977AV_CODE_LENGTH] THEN
    REWRITE_TAC[c977av_code; fst C977AV_CODE_LIST; snd C977AV_CODE_LIST] THEN
    UNDISCH_TAC `(i:num) < j` THEN ARITH_TAC]);;

(* Lean: auxiliary_vector_cover  (AuxExact q 2 S as in CC_C981_Ownership.ml) *)
let C977AV_AUXILIARY_VECTOR_COVER = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
     ==> MEM (c977av_actual c1 c2 a b l) c977av_vectors /\
         ((forall i j. i < 12 /\ j < 12 /\ c977av_ordered_owner c1 c2 a b l i = c977av_ordered_owner c1 c2 a b l j
                 ==> i = j) /\
          (forall k. k < 12 ==> exists i. i < 12 /\ c977av_ordered_owner c1 c2 a b l i = k)) /\
         (forall i. i < 12 ==> ownmask (c1 (c977av_ordered_owner c1 c2 a b l i)) (c2 (c977av_ordered_owner c1 c2 a b l i))
                                 (a (c977av_ordered_owner c1 c2 a b l i)) (b (c977av_ordered_owner c1 c2 a b l i)) l =
                         EL i c977av_code) /\
         (forall i. i < 12 ==>
              forall j. j < 20 ==>
                  (linside (a (c977av_ordered_owner c1 c2 a b l i)) (b (c977av_ordered_owner c1 c2 a b l i))
                     (a (c977av_ordered_owner c1 c2 a b l i) * c1 (c977av_ordered_owner c1 c2 a b l i) +
                      b (c977av_ordered_owner c1 c2 a b l i) * c2 (c977av_ordered_owner c1 c2 a b l i) - l / &2)
                     (--b (c977av_ordered_owner c1 c2 a b l i) * c1 (c977av_ordered_owner c1 c2 a b l i) +
                      a (c977av_ordered_owner c1 c2 a b l i) * c2 (c977av_ordered_owner c1 c2 a b l i) - l / &2) l
                     (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=>
                   j IN EL i (c977av_actual c1 c2 a b l)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP C977AV_ACTUAL_AUXILIARY_VECTOR_MEM);
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o MATCH_MP C977AV_ORDERED_OWNER_BIJECTIVE);
    FIRST_ASSUM(ACCEPT_TAC o CONJUNCT2 o MATCH_MP C977AV_ORDERED_OWNER_BIJECTIVE);
    REPEAT STRIP_TAC THEN MATCH_MP_TAC C977AV_ORDERED_OWNER_CODE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[C977AV_ACTUAL_AUXILIARY_SLOT] THEN
    REWRITE_TAC[c977av_ordered_owner] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `EL i c977av_code`; `j:num`] OO_AUX_EXACT) THEN
    ASM_REWRITE_TAC[ooc; oos; oou; oov]]);;

(* Lean: retained_auxiliary_vector_cover *)
let C977AV_RETAINED_AUXILIARY_VECTOR_COVER = prove
 (`forall r. r < 577 /\ MEM (EL r COVER_IDS) EXPECTED_IDS /\ EL r COVER_IDS = 977
     ==> forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (EL r ROWS)
     ==> MEM (c977av_actual c1 c2 a b l) c977av_vectors /\
         ((forall i j. i < 12 /\ j < 12 /\ c977av_ordered_owner c1 c2 a b l i = c977av_ordered_owner c1 c2 a b l j
                 ==> i = j) /\
          (forall k. k < 12 ==> exists i. i < 12 /\ c977av_ordered_owner c1 c2 a b l i = k)) /\
         (forall i. i < 12 ==> ownmask (c1 (c977av_ordered_owner c1 c2 a b l i)) (c2 (c977av_ordered_owner c1 c2 a b l i))
                                 (a (c977av_ordered_owner c1 c2 a b l i)) (b (c977av_ordered_owner c1 c2 a b l i)) l =
                         EL i c977av_code) /\
         (forall i. i < 12 ==>
              forall j. j < 20 ==>
                  (linside (a (c977av_ordered_owner c1 c2 a b l i)) (b (c977av_ordered_owner c1 c2 a b l i))
                     (a (c977av_ordered_owner c1 c2 a b l i) * c1 (c977av_ordered_owner c1 c2 a b l i) +
                      b (c977av_ordered_owner c1 c2 a b l i) * c2 (c977av_ordered_owner c1 c2 a b l i) - l / &2)
                     (--b (c977av_ordered_owner c1 c2 a b l i) * c1 (c977av_ordered_owner c1 c2 a b l i) +
                      a (c977av_ordered_owner c1 c2 a b l i) * c2 (c977av_ordered_owner c1 c2 a b l i) - l / &2) l
                     (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2) <=>
                   j IN EL i (c977av_actual c1 c2 a b l)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C977AV_AUXILIARY_VECTOR_COVER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `set_of_list (EL r ROWS)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CCC977RI_ROW_FAMILY THEN ASM_REWRITE_TAC[]);;
