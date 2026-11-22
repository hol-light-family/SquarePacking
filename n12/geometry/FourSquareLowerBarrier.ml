(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareLowerBarrier.lean                      *)
(*                                                                           *)
(* Premises (extending FourSquareHighRight.Premises with rRight and          *)
(* rMissingRow) becomes the hypothesis list.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977WallChains.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallLowerBarrier.ml";;
needs "n12/geometry/FourSquareHighRight.ml";;

(* Lean: right_point *)
let FSLB_RIGHT_POINT = prove
 (`forall c s u v a cA sA uA vA aA.
     c * c + s * s = &1 /\ &1 < a /\ cA * cA + sA * sA = &1 /\ &0 < aA /\
     lcont c s u v a /\
     lclosed c s u v a (&1543 / &500) (&2) /\
     lclosed c s u v a (&3) (&12 / &5) /\
     ~(linside c s u v a (&3) (&87 / &50)) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     ldisj c s u v a cA sA uA vA aA
     ==> linside c s u v a (&3) (&5 / &2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj; lcont] THEN STRIP_TAC THEN
  (* hD *)
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `&113 / &50`; `&2`] OUTSIDE_OF_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* r = positive frame of pullX q *)
  MP_TAC(SPECL [`--c:real`; `s:real`; `u - &4 * c:real`; `--v - a - &4 * s:real`; `a:real`]
    CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LINSIDE_PULLX; LCLOSED_PULLX; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN
  (* hwall and hvertex *)
  SUBGOAL_THEN `forall x y. linside cr sr ur vr ar x y ==> &0 <= x /\ &0 <= y` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&4 - x:real`; `y:real`] o
      check (fun th -> is_imp(snd(strip_forall(concl th))))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
    C977WC_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= cr * ur - sr * (vr + ar)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the forced point *)
  MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`]
    WLB_LEFT_POSITIVE_POINT) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;

(* Lean: impossible *)
let FSLB_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cL sL uL vL aL cR sR uR vR aR.
     lsquare cA sA uA vA aA /\ lsquare cB sB uB vB aB /\
     lsquare cL sL uL vL aL /\ lsquare cR sR uR vR aR /\
     &1 < aB /\ aB <= &1001 / &1000 /\
     aA = aB /\ aB = aL /\ aB = aR /\
     lcont cB sB uB vB aB /\ lcont cL sL uL vL aL /\ lcont cR sR uR vR aR /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     lclosed cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cB sB uB vB aB (&87 / &50) (&3) /\
     ~linside cB sB uB vB aB (&1) (&1543 / &500) /\
     ~linside cB sB uB vB aB (&2) (&1543 / &500) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     ~linside cL sL uL vL aL (&19 / &25) (&187 / &100) /\
     ~linside cL sL uL vL aL (&33 / &20) (&33 / &20) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cB sB uB vB aB cR sR uR vR aR /\
     lclosed cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&3) (&87 / &50)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aA:real = aB` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aL` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aR` o concl)) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`;
                `cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] FSLB_RIGHT_POINT) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[lsquare]) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ldisj cA sA uA vA aB cR sR uR vR aB` THEN
    REWRITE_TAC[ldisj] THEN MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] FSHR_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;
