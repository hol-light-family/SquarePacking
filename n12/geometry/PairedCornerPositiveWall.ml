(* ========================================================================= *)
(* Port of Compact/Geometry/PairedCornerPositiveWall.lean (Jatloe,           *)
(* N12-jatloe; namespace N12Compact.PairedCornerPositiveWall).               *)
(* The positive wall's actual inward V face and its neighbouring paired      *)
(* corner suffice.  Normal is c977cc_normal; PositiveWallMarker.upper_faces: *)
(* PWM_UPPER_FACES; FourSquareBLBridge.left_wall: FSBL_LEFT_WALL;            *)
(* PositiveWallOwnedWestFaces.tilt: PWOWF_TILT;                              *)
(* PositiveWallOwnedWestCorner.impossible: PWOWC_IMPOSSIBLE.                 *)
(* W = turnFrame (turnFrame (pullX R)) is the 5-tuple                        *)
(* (cR, t, 4 cR - uR - aR, vR - 4 t, aR) when sR = --t; pullX E is           *)
(* (--cE, sE, uE - 4 cE, --vE - aE - 4 sE, aE) (LINSIDE_PULLX).              *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/PositiveWallMarker.ml";;
needs "n12/geometry/PositiveWallOwnedWestFaces.ml";;
needs "n12/geometry/PositiveWallOwnedWestCorner.ml";;

let PCPW_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PCPW_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PCPW_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: outward_margin (private) *)
let PCPW_OUTWARD_MARGIN = prove
 (`forall d t. c977cc_normal d t ==> &1 - (&1 / &5) * d pow 2 + d * t <= d + t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN PCPW_NORMAL_TAC THEN
  SUBGOAL_THEN `d + t - &1 <= (&3 / &5) * d` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCPW_PROD_TAC `(&3 / &5) * d - (d + t - &1)` `(&3 / &5) * d + (d + t - &1)` THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `d:real`]);;

(* Lean: upper_v *)
let PCPW_UPPER_V = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c s /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\ &2 * c - s <= v /\
     ~linside c s u v a (&457 / &500) (&3) /\ ~linside c s u v a (&4 / &5) (&3)
     ==> v + a <= &3 * c - (&457 / &500) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] PWM_UPPER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  PCPW_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s * (v + a) <= c * u` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME `linside c s u v a (&457 / &500) (&2)`)) THEN
  PCPW_PRODLT_TAC `a - &1` `c + s` THEN
  PCPW_PROD_TAC `s:real` `v - (&2 * c - s)` THEN
  PCPW_PROD_TAC `c:real` `(&457 / &500) * c + &3 * s - (u + a)` THEN
  SUBGOAL_THEN `(&43 / &500) * c pow 2 < (&1 - c) * (&1 - s)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPW_PROD_TAC `c:real` `&1 - c` THEN
  SUBGOAL_THEN `&1 - c <= s pow 2` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `c / &4 < s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PCPW_PROD_TAC `c / &4 - s` `c / &4 + s` THEN
   PCPW_PROD_TAC `s:real` `&1 - c` THEN
   PCPW_PRODLT_TAC `c:real` `c:real` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `u < (&4 / &5) * c + &3 * s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v < &3 * c - (&4 / &5) * s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `u + a <= (&4 / &5) * c + &3 * s` THENL
  [PCPW_PROD_TAC `c:real` `(&4 / &5) * c + &3 * s - (u + a)` THEN
   MP_TAC(SPECL [`c:real`; `s:real`] PCPW_OUTWARD_MARGIN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MATCH_MP_TAC(TAUT `false ==> p`) THEN NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= &3 * c - (&4 / &5) * s` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (&4 / &5) (&3)` THEN REWRITE_TAC[linside] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c + s / &5` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PCPW_PRODLT_TAC `c + s / &5 - &1` `c + &1` THEN
  PCPW_PROD_TAC `s:real` `&1 - c` THEN
  SUBGOAL_THEN `s < &2 / &5` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  PCPW_PRODLT_TAC `&2 / &5 - s` `&2 / &5 + s` THEN
  SUBGOAL_THEN `&21 / &25 < c pow 2` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PCPW_PRODLT_TAC `c + s / &5 - &1` `&1 - s` THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `s - &1 / &2`]);;

(* Lean: impossible *)
let PCPW_IMPOSSIBLE = prove
 (`forall c s u v a cE sE uE vE aE.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c977cc_normal c s /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     &2 * c - s <= v /\
     linside cE sE uE vE aE (&4 / &5) (&3) /\ linside cE sE uE vE aE (&1) (&3) /\
     linside cE sE uE vE aE (&457 / &500) (&3) /\
     linside cE sE uE vE aE (&1) (&1543 / &500) /\
     ldisj cE sE uE vE aE c s u v a
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside c s u v a (&457 / &500) (&3) /\ ~linside c s u v a (&4 / &5) (&3)`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cE sE uE vE aE c s u v a` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(fun th -> MP_TAC(SPECL [`&457 / &500`; `&3`] th) THEN
                        MP_TAC(SPECL [`&4 / &5`; `&3`] th)) THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] PCPW_UPPER_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `a:real`; `v:real`] PWOWF_TILT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] PWOWC_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;

(* W = turnFrame (turnFrame (pullX R)) with R.s = --t *)
let PCPW_W_INSIDE = prove
 (`forall c t u v a x y.
      linside c t (&4 * c - u - a) (v - &4 * t) a x y <=>
      linside c (--t) u v a (&4 - x) y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let PCPW_W_CONT = prove
 (`forall c t u v a. lcont c (--t) u v a ==> lcont c t (&4 * c - u - a) (v - &4 * t) a`,
  REWRITE_TAC[lcont; PCPW_W_INSIDE] THEN MESON_TAC[REAL_ARITH
   `&0 <= &4 - x /\ &4 - x <= &4 ==> &0 <= x /\ x <= &4`]);;

(* Lean: negative_right_impossible *)
let PCPW_NEGATIVE_RIGHT_IMPOSSIBLE = prove
 (`forall cR sR uR vR aR cE sE uE vE aE t.
     cR * cR + sR * sR = &1 /\ &0 < aR /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     sR = --t /\ c977cc_normal cR t /\ &1 < aR /\ lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     &3 * t + &2 * cR <= vR /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\ linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&1543 / &500) (&3) /\
     linside cE sE uE vE aE (&3) (&1543 / &500) /\
     ldisj cE sE uE vE aE cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sR = --t`)) THEN
  MATCH_MP_TAC(SPECL [`cR:real`; `t:real`; `&4 * cR - uR - aR`; `vR - &4 * t`; `aR:real`;
                `--cE`; `sE:real`; `uE - &4 * cE`; `--vE - aE - &4 * sE`; `aE:real`]
    PCPW_IMPOSSIBLE) THEN
  REWRITE_TAC[PCPW_W_INSIDE; LINSIDE_PULLX; ldisj] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_SIMP_TAC[PCPW_W_CONT] THEN
  UNDISCH_TAC `ldisj cE sE uE vE aE cR (--t) uR vR aR` THEN
  REWRITE_TAC[ldisj] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY(RASM_ARITH_TAC) THEN ASM_MESON_TAC[]);;

(* Lean: negative_right_point *)
let PCPW_NEGATIVE_RIGHT_POINT = prove
 (`forall cR sR uR vR aR cE sE uE vE aE t.
     cR * cR + sR * sR = &1 /\ &0 < aR /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     sR = --t /\ c977cc_normal cR t /\ &1 < aR /\ lcont cR sR uR vR aR /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\ linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&1543 / &500) (&3) /\
     linside cE sE uE vE aE (&3) (&1543 / &500) /\
     ldisj cE sE uE vE aE cR sR uR vR aR
     ==> linside cR sR uR vR aR (&3) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sR = --t`)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cR:real`; `--t`; `uR:real`; `vR:real`; `aR:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`]
    PCPW_NEGATIVE_RIGHT_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cR (--t) uR vR aR (&3) (&2)` THEN REWRITE_TAC[] THEN
  MP_TAC(ASSUME `linside cR (--t) uR vR aR (&1543 / &500) (&2)`) THEN
  MP_TAC(ASSUME `linside cR (--t) uR vR aR (&3) (&12 / &5)`) THEN
  PCPW_NORMAL_TAC THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;
