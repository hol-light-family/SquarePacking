(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ContinuousOrigin.lean         *)
(* (N12Compact.Completion.OtherCases.C1089.ContinuousOrigin).  The corner-to-*)
(* right-origin step of C1089-CONTINUOUS-REDUCTION Theorem 3.  Squares W, B, *)
(* K, C are cW sW uW vW aW etc.  Lean's chartSquare Q (translate of opposite *)
(* of swap) is the explicit square of OC1089CO_CHART:                        *)
(* (chart Q).Inside x y <=> Q.Inside (2 - y) (2 - x).  boundary_origin is    *)
(* OCWPBO_BOUNDARY_ORIGIN; ContinuousReach.bottom_points is                  *)
(* C1089CR_BOTTOM_POINTS.  Tag OC1089CO_.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousReach.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

let OC1089CO_CHART = prove
 (`forall c s u v a x y.
     linside (--c) s (v + &2 * s - &2 * c) (u - &2 * c - &2 * s) a x y <=>
     linside c s u v a (&2 - y) (&2 - x)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: right_origin *)
let OC1089CO_RIGHT_ORIGIN = prove
 (`forall cW sW uW vW aW cB sB uB vB aB cK sK uK vK aK.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aW /\ aW = aK /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     (forall x y. linside cK sK uK vK aK x y ==> x <= &2 /\ y <= &2) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\ linside cW sW uW vW aW (&1) (&13 / &50) /\
     linside cK sK uK vK aK (&543 / &500) (&1) /\ linside cK sK uK vK aK (&1) (&1) /\
     linside cB sB uB vB aB (&1 / &2) (&1) /\
     ldisj cK sK uK vK aK cB sB uB vB aB /\
     ldisj cK sK uK vK aK cW sW uW vW aW
     ==> linside cW sW uW vW aW (&1) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aK`)) THEN
  MP_TAC(SPECL [`--cW`; `sW:real`; `vW + &2 * sW - &2 * cW`; `uW - &2 * cW - &2 * sW`; `aK:real`;
                `--cK`; `sK:real`; `vK + &2 * sK - &2 * cK`; `uK - &2 * cK - &2 * sK`; `aK:real`;
                `&457 / &500`; `&87 / &50`] OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[OC1089CO_CHART; ldisj] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&2 - y`; `&2 - x`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `cW:real`)) (concl th) &&
      is_imp(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&2 - y`; `&2 - x`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `cK:real`)) (concl th) &&
      is_imp(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `ldisj cK sK uK vK aK cB sB uB vB aB` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1 / &2`; `&1`]) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `ldisj cK sK uK vK aK cW sW uW vW aK` THEN REWRITE_TAC[ldisj] THEN
    MESON_TAC[]]);;

(* Lean: right_origin_of_points *)
let OC1089CO_RIGHT_ORIGIN_OF_POINTS = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cB sB uB vB aB cK sK uK vK aK.
     cC * cC + sC * sC = &1 /\ &0 < aC /\
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aW /\ &1 < aB /\ aW = aK /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     (forall x y. linside cB sB uB vB aB x y ==> y <= &2) /\
     (forall x y. linside cK sK uK vK aK x y ==> x <= &2 /\ y <= &2) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\ linside cW sW uW vW aW (&1) (&13 / &50) /\
     linside cB sB uB vB aB (&0) (&543 / &500) /\ linside cB sB uB vB aB (&2 / &5) (&1) /\
     ~linside cB sB uB vB aB (--(&13) / &50) (&1) /\
     linside cK sK uK vK aK (&543 / &500) (&1) /\ linside cK sK uK vK aK (&1) (&1) /\
     ldisj cB sB uB vB aB cC sC uC vC aC /\
     ldisj cK sK uK vK aK cB sB uB vB aB /\
     ldisj cK sK uK vK aK cW sW uW vW aW
     ==> linside cB sB uB vB aB (&14 / &25) (&1) /\ linside cW sW uW vW aW (&1) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aK`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1089CR_BOTTOM_POINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~linside cB sB uB vB aB (--(&13) / &50) (&1)` THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OC1089CO_RIGHT_ORIGIN THEN
  MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                        `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] THEN
  ASM_REWRITE_TAC[]);;
