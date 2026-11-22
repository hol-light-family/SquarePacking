(* ========================================================================= *)
(* Port of Compact/Geometry/C981TwoTip.lean (Jatloe N12).                     *)
(* The all-orientation two-tip obstruction.                                  *)
(* short_projections: WFP_SHORT_PROJECTIONS.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C981TT_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* unfold everything, add the short projections of (dx,dy), finish linearly *)
let C981TT_BANDS_TAC dx dy =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  REWRITE_TAC[linside] THEN C981TT_ARITH_TAC;;

(* Lean: first_tip *)
let C981TT_FIRST_TIP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\
     linside c s u v a (&12 / &5) (&3) /\
     ~linside c s u v a (&87 / &50) (&3)
     ==> linside c s u v a (&12 / &5) (&779 / &325)`,
  C981TT_BANDS_TAC `&12 / &5 - &87 / &50` `&779 / &325 - &3`);;

(* Lean: second_tip *)
let C981TT_SECOND_TIP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&3) (&87 / &50)
     ==> linside c s u v a (&4441 / &1850) (&12 / &5)`,
  C981TT_BANDS_TAC `&4441 / &1850 - &3` `&12 / &5 - &87 / &50`);;

(* Lean: common_tip *)
let C981TT_COMMON_TIP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     linside c s u v a (&113 / &50) (&2) /\
     linside c s u v a (&3) (&12 / &5) /\
     linside c s u v a (&4441 / &1850) (&12 / &5)
     ==> linside c s u v a (&12 / &5) (&779 / &325)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let C981TT_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aA /\ &1 < aB /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&12 / &5) (&3) /\
     ~linside cA sA uA vA aA (&87 / &50) (&3) /\
     linside cB sB uB vB aB (&113 / &50) (&2) /\
     linside cB sB uB vB aB (&3) (&12 / &5) /\
     ~linside cB sB uB vB aB (&3) (&87 / &50) /\
     ldisj cA sA uA vA aA cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `ldisj cA sA uA vA aA cB sB uB vB aB` THEN
  REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`&12 / &5`; `&779 / &325`]) THEN
  REWRITE_TAC[TAUT `~p ==> false <=> p`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC C981TT_FIRST_TIP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C981TT_COMMON_TIP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C981TT_SECOND_TIP THEN ASM_REWRITE_TAC[]]);;
