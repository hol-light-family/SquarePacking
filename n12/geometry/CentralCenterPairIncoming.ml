(* ========================================================================= *)
(* Port of Compact/Geometry/CentralCenterPairIncoming.lean (Jatloe).          *)
(* A centre-owning square's marker cap removes its transverse incoming axis. *)
(* upper / lower: ABT_upper / ABT_lower; faceSeparation_of_disjoint,         *)
(* separated, parallel/transverse_radius, ownU/ownV: ABT_FOUR_AXES and       *)
(* ABT_OWNU/ABT_OWNV (via ABT_PAIR_TAC).                                     *)
(* swapFrame (c,s,u,v,a) is the 5-tuple (c, --s, v, u, a).                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CenterPairSeparation.ml";;
needs "n12/geometry/CentralCenterCaps.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

(* Lean: southeast_transverse *)
let CCPI_SOUTHEAST_TRANSVERSE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     abs s <= c /\ &1 < a /\ linside c s u v a (&2) (&2) /\
     v + a <= (&47 / &20) * c - (&33 / &20) * s
     ==> v < (&33 / &20) * c - (&47 / &20) * s /\
         (&33 / &20) * c - (&47 / &20) * s < v + a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c + s) pow 2 <= &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `c - s:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&7 / &10) * (c + s) < &1` ASSUME_TAC THENL
  [NLIN_TAC []; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: right_alternatives *)
let CCPI_RIGHT_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &0 < cA /\ abs sA <= cA /\ &0 < cB /\ abs sB <= cB /\
     aA = aB /\ &1 < aA /\
     linside cA sA uA vA aA (&2) (&2) /\
     linside cA sA uA vA aA (&2) (&3 / &2) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> uA + aA <= ABT_lower cB sB uB vB aB cA sA \/
         ABT_upper cA sA uA vA aA cB sB <= uB \/
         (&3 * cB < &7 * sB /\ vB + aB <= ABT_lower cA sA uA vA aA (--sB) cB)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CCPI_SOUTHEAST_TRANSVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABT_PAIR_TAC "A" "B"
    ["A",(`&2`,`&2`); "A",(`&2`,`&3 / &2`); "A",(`&2`,`&87 / &50`);
     "B",(`&47 / &20`,`&33 / &20`); "B",(`&3`,`&87 / &50`)]);;

(* Lean: inside_swapFrame (private) *)
let CCPI_INSIDE_SWAPFRAME = prove
 (`forall c s u v a x y. linside c (--s) v u a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: upper_swapFrame (private) *)
let CCPI_UPPER_SWAPFRAME = prove
 (`forall c s u v a x y. ABT_upper c (--s) v u a x y = ABT_upper c s u v a y x`,
  REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `x * c + y * --s = --y * s + x * c`;
              REAL_ARITH `--x * --s + y * c = y * c + x * s`] THEN
  REAL_ARITH_TAC);;

(* Lean: lower_swapFrame (private) *)
let CCPI_LOWER_SWAPFRAME = prove
 (`forall c s u v a x y. ABT_lower c (--s) v u a x y = ABT_lower c s u v a y x`,
  REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `x * c + y * --s = --y * s + x * c`;
              REAL_ARITH `--x * --s + y * c = y * c + x * s`] THEN
  REAL_ARITH_TAC);;

(* Lean: top_alternatives *)
let CCPI_TOP_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cC sC uC vC aC.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cC * cC + sC * sC = &1 /\ &0 < aC /\
     &0 < cA /\ abs sA <= cA /\ &0 < cC /\ abs sC <= cC /\
     aA = aC /\ &1 < aA /\
     linside cA sA uA vA aA (&2) (&2) /\
     linside cA sA uA vA aA (&3 / &2) (&2) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     uA + aA <= (&47 / &20) * cA + (&33 / &20) * sA /\
     linside cC sC uC vC aC (&33 / &20) (&47 / &20) /\
     linside cC sC uC vC aC (&87 / &50) (&3) /\
     ldisj cA sA uA vA aA cC sC uC vC aC
     ==> vA + aA <= ABT_lower cC sC uC vC aC (--sA) cA \/
         ABT_upper cA sA uA vA aA (--sC) cC <= vC \/
         (&7 * sC < -- &3 * cC /\ uC + aC <= ABT_lower cA sA uA vA aA cC sC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `--sA`; `vA:real`; `uA:real`; `aA:real`]
    CCPI_SOUTHEAST_TRANSVERSE) THEN
  REWRITE_TAC[CCPI_INSIDE_SWAPFRAME; REAL_ABS_NEG] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ABT_PAIR_TAC "A" "C"
    ["A",(`&2`,`&2`); "A",(`&3 / &2`,`&2`); "A",(`&87 / &50`,`&2`);
     "C",(`&33 / &20`,`&47 / &20`); "C",(`&87 / &50`,`&3`)]);;
