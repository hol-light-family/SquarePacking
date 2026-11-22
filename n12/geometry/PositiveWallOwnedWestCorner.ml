(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveWallOwnedWestCorner.lean (Jatloe,        *)
(* N12-jatloe; namespace N12Compact.PositiveWallOwnedWestCorner).            *)
(* The upper-corner triangle closes the positive-wall branch when the        *)
(* central square owns (1,2).  Normal is c977cc_normal;                      *)
(* ClosedPointExclusion.outside_of_closed is OUTSIDE_OF_CLOSED (p2_base);    *)
(* FourSquareBLBridge.left_wall: FSBL_LEFT_WALL.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;
needs "n12/geometry/PositiveWallOwnedWestFaces.ml";;

let PWOWC_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PWOWC_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PWOWC_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: weighted_lower (private) *)
let PWOWC_WEIGHTED_LOWER = prove
 (`forall a b g p q r z. &0 < a /\ &0 < b /\ &0 < g /\ a + b + g = &1 /\
     z < p /\ z < q /\ z < r ==> z < a * p + b * q + g * r`,
  REPEAT STRIP_TAC THEN
  PWOWC_PRODLT_TAC `a:real` `p - z` THEN PWOWC_PRODLT_TAC `b:real` `q - z` THEN
  PWOWC_PRODLT_TAC `g:real` `r - z` THEN
  SUBGOAL_THEN `z = (a + b + g) * z` SUBST1_TAC THENL
  [ASM_REWRITE_TAC[REAL_MUL_LID]; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: triangle *)
let PWOWC_TRIANGLE = prove
 (`forall c s u v a x y.
     linside c s u v a (&4 / &5) (&3) /\ linside c s u v a (&1) (&3) /\
     linside c s u v a (&1) (&1543 / &500) /\
     &49 / &50 < x /\ x < &1 /\ &3 < y /\ y < &151 / &50
     ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&4 / &5) (&3)`; `linside c s u v a (&1) (&3)`;
    `linside c s u v a (&1) (&1543 / &500)`] THEN
  ABBREV_TAC `wa = &5 * (&1 - x)` THEN ABBREV_TAC `wg = (&500 / &43) * (y - &3)` THEN
  ABBREV_TAC `wb = &1 - wa - wg` THEN
  SUBGOAL_THEN `&0 < wa /\ &0 < wg /\ &0 < wb /\ wa + wb + wg = &1` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["wb"; "wa"; "wg"] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
   `c * x + s * y = wa * (c * &4 / &5 + s * &3) + wb * (c * &1 + s * &3) +
                    wg * (c * &1 + s * &1543 / &500) /\
    --s * x + c * y = wa * (--s * &4 / &5 + c * &3) + wb * (--s * &1 + c * &3) +
                      wg * (--s * &1 + c * &1543 / &500)` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["wb"; "wa"; "wg"] THEN CONJ_TAC THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  REWRITE_TAC[linside] THEN ASM_REWRITE_TAC[] THEN
  let wl = MATCH_MP_TAC PWOWC_WEIGHTED_LOWER THEN ASM_REWRITE_TAC[] in
  let wu = ONCE_REWRITE_TAC[GSYM REAL_LT_NEG2] THEN
    SUBGOAL_THEN `forall P Q R. --(wa * P + wb * Q + wg * R) =
                          wa * --P + wb * --Q + wg * --R` (fun th -> REWRITE_TAC[th]) THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC PWOWC_WEIGHTED_LOWER THEN ASM_REWRITE_TAC[REAL_LT_NEG2] in
  REPEAT CONJ_TAC THENL [wl; wu; wl; wu]);;

(* Lean: upper_u *)
let PWOWC_UPPER_U = prove
 (`forall c s u v a.
     c977cc_normal c s /\ &1 < a /\ linside c s u v a (&1) (&12 / &5) /\
     &2 * c - s <= v /\ ~linside c s u v a (&1) (&3)
     ==> u + a <= c + &3 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWOWC_NORMAL_TAC THEN
  MP_TAC(ASSUME `linside c s u v a (&1) (&12 / &5)`) THEN
  MP_TAC(ASSUME `~linside c s u v a (&1) (&3)`) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: impossible *)
let PWOWC_IMPOSSIBLE = prove
 (`forall c s u v a cE sE uE vE aE.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c977cc_normal c s /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&1) (&12 / &5) /\
     &2 * c - s <= v /\ v + a <= &3 * c - (&457 / &500) * s /\
     &0 < s /\ s < &43 / &250 /\
     linside cE sE uE vE aE (&4 / &5) (&3) /\ linside cE sE uE vE aE (&1) (&3) /\
     linside cE sE uE vE aE (&1) (&1543 / &500) /\
     ldisj cE sE uE vE aE c s u v a
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside c s u v a (&1) (&3)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cE sE uE vE aE c s u v a` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&1`; `&3`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] PWOWC_UPPER_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  PWOWC_NORMAL_TAC THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s * (v + a) <= c * u` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `X = c * (u + a) - s * (v + a)` THEN
  ABBREV_TAC `Y = s * (u + a) + c * (v + a)` THEN
  SUBGOAL_THEN `c * X + s * Y = u + a /\ --s * X + c * Y = v + a` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN CONJ_TAC THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `lclosed c s u v a X Y` ASSUME_TAC THENL
  [REWRITE_TAC[lclosed] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * a <= X` ASSUME_TAC THENL
  [EXPAND_TAC "X" THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWOWC_PRODLT_TAC `&43 / &250 - s` `&43 / &250 + s` THEN
  SUBGOAL_THEN `&49 / &50 < c` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PWOWC_PROD_TAC `&49 / &50 - c` `&49 / &50 + c` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWOWC_PRODLT_TAC `c:real` `a - &1` THEN
  SUBGOAL_THEN `&49 / &50 < X` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWOWC_PROD_TAC `s:real` `v - (&2 * c - s)` THEN
  PWOWC_PROD_TAC `c:real` `(c + &3 * s) - (u + a)` THEN
  PWOWC_PRODLT_TAC `s:real` `a - c` THEN
  SUBGOAL_THEN `X < &1` ASSUME_TAC THENL
  [EXPAND_TAC "X" THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `c * Y = s * X + (v + a)` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  PWOWC_PROD_TAC `s:real` `X - c * a` THEN
  PWOWC_PROD_TAC `s:real` `c:real` THEN
  PWOWC_PRODLT_TAC `a - &1` `&1 + s * c` THEN
  PWOWC_PROD_TAC `&1 - c` `&1 - s` THEN
  SUBGOAL_THEN `&3 < Y` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   PWOWC_PROD_TAC `c:real` `&3 - Y` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWOWC_PROD_TAC `c:real` `(&3 * c - (&457 / &500) * s) - (v + a)` THEN
  PWOWC_PROD_TAC `s:real` `(c + &3 * s) - (u + a)` THEN
  SUBGOAL_THEN `Y <= &3 + (&43 / &500) * c * s` ASSUME_TAC THENL
  [EXPAND_TAC "Y" THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWOWC_PROD_TAC `s:real` `&1 - c` THEN
  SUBGOAL_THEN `Y < &151 / &50` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `X:real`; `Y:real`]
    OUTSIDE_OF_CLOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[GSYM ldisj]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC PWOWC_TRIANGLE THEN ASM_REWRITE_TAC[]);;
