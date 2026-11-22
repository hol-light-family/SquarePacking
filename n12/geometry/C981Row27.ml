(* ========================================================================= *)
(* Port of Compact/Geometry/C981Row27.lean (Jatloe N12,                       *)
(* namespace C981Row27Geometry).  The original row-27 obstruction.           *)
(* short_projections: WFP_SHORT_PROJECTIONS; WallLowerReach.point: WLR_POINT.*)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/WallLowerReach.ml";;

let C981R27_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C981R27_BANDS_TAC dx dy =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  REWRITE_TAC[linside] THEN C981R27_ARITH_TAC;;

(* Lean: first_point *)
let C981R27_FIRST_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&457 / &500) (&2)
     ==> linside c s u v a (&87 / &50) (&54 / &25)`,
  C981R27_BANDS_TAC `&87 / &50 - &457 / &500` `&54 / &25 - &2`);;

(* Lean: second_point *)
let C981R27_SECOND_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&87 / &50) (&54 / &25) /\
     linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&1) (&64 / &25)
     ==> linside c s u v a (&48 / &25) (&64 / &25)`,
  C981R27_BANDS_TAC `&23 / &25` `&0`);;

(* Lean: top_point *)
let C981R27_TOP_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     linside c s u v a (&2) (&113 / &50) /\
     linside c s u v a (&87 / &50) (&3) /\
     linside c s u v a (&12 / &5) (&3)
     ==> linside c s u v a (&48 / &25) (&64 / &25)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let C981R27_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cL sL uL vL aL cT sT uT vT aT.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     cT * cT + sT * sT = &1 /\ &0 < aT /\
     &1 < aC /\ &1 < aL /\ lcont cL sL uL vL aL /\
     linside cC sC uC vC aC (&33 / &20) (&47 / &20) /\
     linside cC sC uC vC aC (&87 / &50) (&2) /\
     linside cC sC uC vC aC (&8 / &5) (&3) /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&1) (&87 / &50) /\
     linside cT sT uT vT aT (&2) (&113 / &50) /\
     linside cT sT uT vT aT (&87 / &50) (&3) /\
     linside cT sT uT vT aT (&12 / &5) (&3) /\
     ldisj cC sC uC vC aC cL sL uL vL aL /\
     ldisj cC sC uC vC aC cT sT uT vT aT
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] WLR_POINT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C981R27_FIRST_POINT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C981R27_SECOND_POINT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`]
    C981R27_TOP_POINT) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
