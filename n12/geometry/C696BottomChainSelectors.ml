(* ========================================================================= *)
(* Port of Compact/Geometry/C696BottomChainSelectors.lean                    *)
(* (N12Compact.C696BottomChainSelectors).  Directed support selectors for    *)
(* the original bottom boundary chain O - D - E - R - N.                     *)
(* The private four_axes of the Lean file is ABT_FOUR_AXES (ABTransverse).   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: SingletonStep *)
let C696BCS_singletonStep = new_definition
 `C696BCS_singletonStep cO sO uO vO aO cD sD uD vD aD (c:real) (s:real) <=>
    ABT_upper cO sO uO vO aO c s <= ABT_lower cD sD uD vD aD c s \/
    ((&43 / &130) * c < --s /\
     ABT_upper cO sO uO vO aO (--s) c <= ABT_lower cD sD uD vD aD (--s) c)`;;

(* Lean: singleton_wall *)
let C696BCS_SINGLETON_WALL = prove
 (`forall cO sO uO vO aO cD sD uD vD aD.
     cO * cO + sO * sO = &1 /\ &0 < aO /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     &0 < cO /\ &0 < cD /\ sO <= cO /\ sD <= cD /\ aO = aD /\
     linside cO sO uO vO aO (&1) (&457 / &500) /\
     linside cO sO uO vO aO (&87 / &50) (&1) /\
     linside cO sO uO vO aO (&187 / &100) (&19 / &25) /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     ldisj cO sO uO vO aO cD sD uD vD aD
     ==> C696BCS_singletonStep cO sO uO vO aO cD sD uD vD aD cO sO \/
         C696BCS_singletonStep cO sO uO vO aO cD sD uD vD aD cD sD`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C696BCS_singletonStep] THEN
  ABT_PAIR_TAC "O" "D"
    ["O",(`&1`,`&457 / &500`); "O",(`&87 / &50`,`&1`); "O",(`&187 / &100`,`&19 / &25`);
     "D",(`&2`,`&457 / &500`)]);;

(* Lean: CornerStep *)
let C696BCS_cornerStep = new_definition
 `C696BCS_cornerStep cD sD uD vD aD cE sE uE vE aE (c:real) (s:real) <=>
    ABT_upper cD sD uD vD aD c s <= ABT_lower cE sE uE vE aE c s \/
    ((&43 / &543) * c < s /\
     ABT_upper cE sE uE vE aE (--s) c <= ABT_lower cD sD uD vD aD (--s) c) \/
    ((&43 / &220) * c < --s /\
     ABT_upper cD sD uD vD aD (--s) c <= ABT_lower cE sE uE vE aE (--s) c)`;;

(* Lean: wall_corner *)
let C696BCS_WALL_CORNER = prove
 (`forall cD sD uD vD aD cE sE uE vE aE.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &0 < cD /\ &0 < cE /\ aD = aE /\
     linside cD sD uD vD aD (&2) (&457 / &500) /\
     linside cD sD uD vD aD (&64 / &25) (&1) /\
     linside cE sE uE vE aE (&3) (&457 / &500) /\
     linside cE sE uE vE aE (&1543 / &500) (&1) /\
     ldisj cD sD uD vD aD cE sE uE vE aE
     ==> C696BCS_cornerStep cD sD uD vD aD cE sE uE vE aE cD sD \/
         C696BCS_cornerStep cD sD uD vD aD cE sE uE vE aE cE sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C696BCS_cornerStep] THEN
  ABT_PAIR_TAC "D" "E"
    ["D",(`&2`,`&457 / &500`); "D",(`&64 / &25`,`&1`);
     "E",(`&3`,`&457 / &500`); "E",(`&1543 / &500`,`&1`)]);;

(* Lean: CornerTurn *)
let C696BCS_cornerTurn = new_definition
 `C696BCS_cornerTurn cE sE uE vE aE cR sR uR vR aR (c:real) (s:real) <=>
    ABT_upper cE sE uE vE aE (--s) c <= ABT_lower cR sR uR vR aR (--s) c \/
    ((&43 / &220) * c < s /\
     ABT_upper cE sE uE vE aE c s <= ABT_lower cR sR uR vR aR c s) \/
    ((&43 / &543) * c < --s /\
     ABT_upper cR sR uR vR aR c s <= ABT_lower cE sE uE vE aE c s)`;;

(* Lean: corner_wall *)
let C696BCS_CORNER_WALL = prove
 (`forall cE sE uE vE aE cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &0 < cE /\ &0 < cR /\ aE = aR /\
     linside cE sE uE vE aE (&3) (&457 / &500) /\
     linside cE sE uE vE aE (&1543 / &500) (&1) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&36 / &25) /\
     ldisj cE sE uE vE aE cR sR uR vR aR
     ==> C696BCS_cornerTurn cE sE uE vE aE cR sR uR vR aR cE sE \/
         C696BCS_cornerTurn cE sE uE vE aE cR sR uR vR aR cR sR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C696BCS_cornerTurn] THEN
  ABT_PAIR_TAC "E" "R"
    ["E",(`&3`,`&457 / &500`); "E",(`&1543 / &500`,`&1`);
     "R",(`&1543 / &500`,`&2`); "R",(`&3`,`&36 / &25`)]);;

(* Lean: WallSingletonStep *)
let C696BCS_wallSingletonStep = new_definition
 `C696BCS_wallSingletonStep cR sR uR vR aR cN sN uN vN aN (c:real) (s:real) <=>
    ABT_upper cR sR uR vR aR (--s) c <= ABT_lower cN sN uN vN aN (--s) c \/
    ((&43 / &130) * c < s /\
     ABT_upper cR sR uR vR aR c s <= ABT_lower cN sN uN vN aN c s)`;;

(* Lean: wall_singleton *)
let C696BCS_WALL_SINGLETON = prove
 (`forall cR sR uR vR aR cN sN uN vN aN.
     cR * cR + sR * sR = &1 /\ &0 < aR /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     &0 < cR /\ &0 < cN /\ --cR <= sR /\ --cN <= sN /\ aR = aN /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cN sN uN vN aN (&1543 / &500) (&3) /\
     linside cN sN uN vN aN (&3) (&113 / &50) /\
     linside cN sN uN vN aN (&81 / &25) (&213 / &100) /\
     ldisj cR sR uR vR aR cN sN uN vN aN
     ==> C696BCS_wallSingletonStep cR sR uR vR aR cN sN uN vN aN cR sR \/
         C696BCS_wallSingletonStep cR sR uR vR aR cN sN uN vN aN cN sN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C696BCS_wallSingletonStep] THEN
  ABT_PAIR_TAC "R" "N"
    ["R",(`&1543 / &500`,`&2`); "N",(`&1543 / &500`,`&3`);
     "N",(`&3`,`&113 / &50`); "N",(`&81 / &25`,`&213 / &100`)]);;

(* Lean: BottomBarrier *)
let C696BCS_bottomBarrier = new_definition
 `C696BCS_bottomBarrier (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    (&0 <= s ==> v + a <= (&3 / &2) * c - &2 * s) /\
    (s <= &0 ==> &2 * c + (&3 / &2) * s <= u \/ v + a <= (&3 / &2) * c - &2 * s)`;;

(* Lean: central_bottom *)
let C696BCS_CENTRAL_BOTTOM = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ abs s <= c /\
     linside c s u v a (&2) (&457 / &500) /\
     linside c s u v a (&64 / &25) (&1) /\
     ~linside c s u v a (&2) (&3 / &2)
     ==> C696BCS_bottomBarrier c s u v a`,
  REWRITE_TAC[C696BCS_bottomBarrier; linside] THEN REAL_ARITH_TAC);;

(* Lean: RightBarrier *)
let C696BCS_rightBarrier = new_definition
 `C696BCS_rightBarrier (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    (s <= &0 ==> (&5 / &2) * c + &2 * s <= u) /\
    (&0 <= s ==> (&5 / &2) * c + &2 * s <= u \/ v + a <= &2 * c - (&5 / &2) * s)`;;

(* Lean: central_right *)
let C696BCS_CENTRAL_RIGHT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ abs s <= c /\
     linside c s u v a (&1543 / &500) (&2) /\
     linside c s u v a (&3) (&36 / &25) /\
     ~linside c s u v a (&5 / &2) (&2)
     ==> C696BCS_rightBarrier c s u v a`,
  REWRITE_TAC[C696BCS_rightBarrier; linside] THEN REAL_ARITH_TAC);;
