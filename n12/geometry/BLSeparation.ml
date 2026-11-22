(* ========================================================================= *)
(* Port of Compact/Geometry/BLSeparation.lean (N12Compact.BLSeparation).     *)
(* The compulsory B/L triangles reduce the eight signed separating-axis     *)
(* alternatives to three directed alternatives.                             *)
(*                                                                           *)
(* supportRadius q nx ny = tss_support_radius cq sq aq nx ny                 *)
(* (ThreeSquareSupport.ml); pairRadius / FaceSeparation from                 *)
(* C977ChainBridge.ml.                                                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CongruentSAT.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* Lean: directed_support (private) *)
let BLS_DIRECTED_SUPPORT = prove
 (`forall cq sq uq vq aq cr sr ur vr ar x y x' y' nx ny.
     cq * cq + sq * sq = &1 /\ cr * cr + sr * sr = &1 /\
     lclosed cq sq uq vq aq x y /\ lclosed cr sr ur vr ar x' y' /\
     nx * x + ny * y < nx * x' + ny * y'
     ==> nx * (lcx cq sq uq vq aq - lcx cr sr ur vr ar) +
         ny * (lcy cq sq uq vq aq - lcy cr sr ur vr ar) <
         tss_support_radius cq sq aq nx ny + tss_support_radius cr sr ar nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`; `x:real`; `y:real`;
                `nx:real`; `ny:real`] TSS_CLOSED_SUPPORT) THEN
  MP_TAC(SPECL [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`; `x':real`; `y':real`;
                `nx:real`; `ny:real`] TSS_CLOSED_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `nx * x + ny * y < nx * x' + ny * y'` THEN
  REAL_ARITH_TAC);;

(* Lean: parallel_radius (private) *)
let BLS_PARALLEL_RADIUS = prove
 (`forall cq sq aq cr sr ar. cq * cq + sq * sq = &1
     ==> tss_support_radius cq sq aq cq sq + tss_support_radius cr sr ar cq sq =
         C977CB_pairRadius cq sq aq cr sr ar`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[tss_support_radius; C977CB_pairRadius;
    REAL_ARITH `--cq * sq + sq * cq = &0`;
    REAL_ARITH `abs(--cq * sr + sq * cr) = abs(cq * sr - sq * cr)`] THEN
  REAL_ARITH_TAC);;

(* Lean: perpendicular_radius (private) *)
let BLS_PERPENDICULAR_RADIUS = prove
 (`forall cq sq aq cr sr ar. cq * cq + sq * sq = &1
     ==> tss_support_radius cq sq aq (--sq) cq + tss_support_radius cr sr ar (--sq) cq =
         C977CB_pairRadius cq sq aq cr sr ar`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[tss_support_radius; C977CB_pairRadius;
    REAL_ARITH `--sq * cq + cq * sq = &0`;
    REAL_ARITH `abs(--sq * cr + cq * sr) = abs(cq * sr - sq * cr)`;
    REAL_ARITH `abs(-- --sq * sr + cq * cr) = abs(cq * cr + sq * sr)`;
    REAL_ARITH `-- --sq * sq + cq * cq = cq * cq + sq * sq`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: transverse_overlap *)
let BLS_TRANSVERSE_OVERLAP = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5)
     ==> abs(--sB * (lcx cB sB uB vB aB - lcx cL sL uL vL aL) +
             cB * (lcy cB sB uB vB aB - lcy cL sL uL vL aL)) <
         C977CB_pairRadius cB sB aB cL sL aL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `&457 / &500`; `&2`; `&8 / &5`; `&3`; `--sB`; `cB:real`]
    BLS_DIRECTED_SUPPORT) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&33 / &20`; `&47 / &20`; `&1`; `&12 / &5`; `--sB`; `cB:real`]
    BLS_DIRECTED_SUPPORT) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `aB:real`; `cL:real`; `sL:real`; `aL:real`]
    BLS_PERPENDICULAR_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[REAL_ARITH `abs x < d <=> --d < x /\ x < d`] THEN
  RASM_ARITH_TAC);;

(* Lean: three_directed_alternatives *)
let BLS_THREE_DIRECTED_ALTERNATIVES = prove
 (`forall cB sB uB vB aB cL sL uL vL aL.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     &0 < cL /\ abs sL <= cL /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     lclosed cL sL uL vL aL (&457 / &500) (&2) /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     aB = aL /\
     ldisj cB sB uB vB aB cL sL uL vL aL
     ==> C977CB_pairRadius cB sB aB cL sL aL <=
           cB * (lcx cB sB uB vB aB - lcx cL sL uL vL aL) +
           sB * (lcy cB sB uB vB aB - lcy cL sL uL vL aL) \/
         C977CB_pairRadius cL sL aL cB sB aB <=
           cL * (lcx cB sB uB vB aB - lcx cL sL uL vL aL) +
           sL * (lcy cB sB uB vB aB - lcy cL sL uL vL aL) \/
         (&13 * sL <= --cL /\
          C977CB_pairRadius cL sL aL cB sB aB <=
           --sL * (lcx cB sB uB vB aB - lcx cL sL uL vL aL) +
           cL * (lcy cB sB uB vB aB - lcy cL sL uL vL aL))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aB:real = aL`)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aL:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ASM_REWRITE_TAC[C977CB_faceSep] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aL:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
    BLS_TRANSVERSE_OVERLAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* bu_backward *)
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aL:real`;
                `&457 / &500`; `&2`; `&8 / &5`; `&3`; `cB:real`; `sB:real`]
    BLS_DIRECTED_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `aL:real`; `cL:real`; `sL:real`; `aL:real`]
    BLS_PARALLEL_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] th]) THEN
  DISCH_TAC THEN
  (* lu_backward *)
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aL:real`;
                `&1`; `&12 / &5`; `&33 / &20`; `&47 / &20`; `cL:real`; `sL:real`]
    BLS_DIRECTED_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `abs sL <= cL` THEN UNDISCH_TAC `&0 < cL` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `aL:real`; `cB:real`; `sB:real`; `aL:real`]
    BLS_PARALLEL_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  (* lv_backward *)
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aL:real`;
                `&457 / &500`; `&2`; `&8 / &5`; `&3`; `--sL`; `cL:real`]
    BLS_DIRECTED_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `abs sL <= cL` THEN UNDISCH_TAC `&0 < cL` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `aL:real`; `cB:real`; `sB:real`; `aL:real`]
    BLS_PERPENDICULAR_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
  (* the slope bound in the last branch *)
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aL:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&33 / &20`; `&47 / &20`; `&1`; `&12 / &5`; `--sL`; `cL:real`]
    BLS_DIRECTED_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `aL:real`; `cB:real`; `sB:real`; `aL:real`]
    BLS_PERPENDICULAR_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] th]) THEN
  DISCH_TAC THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
    filter (fun th -> not (is_forall(concl th))) o rev) THEN
  REWRITE_TAC[lclosed] THEN
  SPEC_TAC(`lcx cB sB uB vB aL`,`Bx:real`) THEN SPEC_TAC(`lcy cB sB uB vB aL`,`By:real`) THEN
  SPEC_TAC(`lcx cL sL uL vL aL`,`Lx:real`) THEN SPEC_TAC(`lcy cL sL uL vL aL`,`Ly:real`) THEN
  SPEC_TAC(`C977CB_pairRadius cB sB aL cL sL aL`,`R1:real`) THEN
  SPEC_TAC(`C977CB_pairRadius cL sL aL cB sB aL`,`R2:real`) THEN
  REAL_ARITH_TAC);;
