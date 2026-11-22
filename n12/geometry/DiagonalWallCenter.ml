(* ========================================================================= *)
(* Port of Compact/Geometry/DiagonalWallCenter.lean (Jatloe, N12-jatloe).     *)
(* A diagonal-owning wall has only one shallow signed orientation; the       *)
(* elbow's two outer arms then rule out all separating axes.                 *)
(* turnFrame^3 (c,s,u,v,a) = (s, --c, --v - a, u, a) (see ClosedFrames.ml).  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/DiagonalWallSegment.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* turnFrame (turnFrame (turnFrame q)) has the same interior (S12.turnFrame_inside) *)
let DWC_TURN3_INSIDE = prove
 (`forall c s u v a x y. linside s (--c) (--v - a) u a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: wall_frame *)
let DWC_WALL_FRAME = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ abs s <= c /\ a <= &1001 / &1000 /\
     linside c s u v a (&1543 / &500) (&2) /\
     linside c s u v a (&3) (&12 / &5) /\
     linside c s u v a (&12 / &5) (&3) /\
     ~linside c s u v a (&3) (&3)
     ==> s < &0 /\ -- &2 * s < c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CWPA_UNFOLD_TAC `linside c s u v a (&1543 / &500) (&2)` THEN
  CWPA_UNFOLD_TAC `linside c s u v a (&3) (&12 / &5)` THEN
  CWPA_UNFOLD_TAC `linside c s u v a (&12 / &5) (&3)` THEN
  UNDISCH_TAC `abs s <= c` THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s < &0` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`c:real`; `s:real`] C977CC_NORMAL_BOUNDS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2]; STRIP_TAC] THEN
   SUBGOAL_THEN `u + a <= &3 * c + &3 * s` ASSUME_TAC THENL
   [UNDISCH_TAC `~linside c s u v a (&3) (&3)` THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&43 / &500) * c < s /\ c + (&343 / &500) * s < &1001 / &1000`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN
    `&0 <= (&1001 / &1000 - (c + (&343 / &500) * s)) *
           (&1001 / &1000 + (c + (&343 / &500) * s)) /\
     &0 < c * (s - (&43 / &500) * c) /\
     &0 <= s * (c - s) /\
     &0 <= (c - &7 / &10) * (c + &7 / &10)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL;
     MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `--s:real`] C977CC_NORMAL_BOUNDS) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(&343 / &500) * c - s < &1001 / &1000` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= (&1001 / &1000 - ((&343 / &500) * c - s)) *
          (&1001 / &1000 + ((&343 / &500) * c - s)) /\
    &0 <= (c - &7 / &10) * (c + &7 / &10) /\
    &0 <= c * (-- &2 * s - c)` MP_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC);;

(* one separating-axis case of negative_pair_impossible *)
let DWC_CASE_TAC nx ny swap radius =
  let sep = SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                   `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`; nx; ny]
                  ABT_SEPARATED in
  let sb sq (x,y) =
    let c,s,u,v = sq in
    MP_TAC(SPECL [c; s; u; v; `aA:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  let qA = (`cA:real`,`sA:real`,`uA:real`,`vA:real`)
  and qR = (`cR:real`,`sR:real`,`uR:real`,`vR:real`) in
  MP_TAC sep THEN ANTS_TAC THENL
  [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
    else ALL_TAC) THEN
   MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  sb qA (`&113 / &50`,`&2`) THEN sb qA (`&53 / &20`,`&47 / &20`) THEN
  sb qA (`&47 / &20`,`&53 / &20`) THEN
  sb qR (`&1543 / &500`,`&2`) THEN sb qR (`&12 / &5`,`&3`) THEN
  STRIP_TAC THEN RASM_ARITH_TAC;;

(* Lean: negative_pair_impossible *)
let DWC_NEGATIVE_PAIR_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &0 < cA /\ sA <= &0 /\ -- &2 * sA <= cA /\
     &0 < cR /\ sR <= &0 /\ -- &2 * sR <= cR /\
     aA = aR /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&53 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&47 / &20) (&53 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [DWC_CASE_TAC `cA:real` `sA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cR:real`; `sR:real`; `aA:real`]
       ABT_PARALLEL_RADIUS);
   DWC_CASE_TAC `--sA:real` `cA:real` false
     (SPECL [`cA:real`; `sA:real`; `aA:real`; `cR:real`; `sR:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS);
   DWC_CASE_TAC `cR:real` `sR:real` true
     (SPECL [`cR:real`; `sR:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_PARALLEL_RADIUS);
   DWC_CASE_TAC `--sR:real` `cR:real` true
     (SPECL [`cR:real`; `sR:real`; `aA:real`; `cA:real`; `sA:real`; `aA:real`]
       ABT_TRANSVERSE_RADIUS)]);;

(* Lean: point *)
let DWC_POINT = prove
 (`forall cA sA uA vA aA cR sR uR vR aR.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     &1 < aA /\ aA = aR /\ aR <= &1001 / &1000 /\ lcont cR sR uR vR aR /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cR sR uR vR aR (&12 / &5) (&3) /\
     ~linside cR sR uR vR aR (&3) (&3) /\
     ldisj cA sA uA vA aA cR sR uR vR aR
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aA:real = aR`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    CLF_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = aA`)) THEN
  SUBGOAL_THEN
   `linside c' s' u' v' aA (&2) (&113 / &50) /\
    linside c' s' u' v' aA (&113 / &50) (&2) /\
    linside c' s' u' v' aA (&47 / &20) (&47 / &20) /\
    ~linside c' s' u' v' aA (&47 / &20) (&33 / &20) /\
    ~linside c' s' u' v' aA (&33 / &20) (&47 / &20) /\
    ~linside c' s' u' v' aA (&3) (&12 / &5) /\
    ~linside c' s' u' v' aA (&12 / &5) (&3) /\
    ldisj c' s' u' v' aA cR sR uR vR aA`
  STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[ldisj] THEN
   UNDISCH_TAC `ldisj cA sA uA vA aA cR sR uR vR aA` THEN
   REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `aA:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    DWS_MISSING_TOP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
     can (find_term ((=) `linside`)) (concl th) then REWRITE_TAC[GSYM th]
     else NO_TAC) THEN
  ASM_CASES_TAC `s' <= c'` THENL
  [MATCH_MP_TAC CWC_SHALLOW THEN
   MAP_EVERY EXISTS_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`] THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  ASM_CASES_TAC `s' <= &2 * c'` THENL
  [MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `aA:real`;
                 `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
     DWS_MIDDLE_IMPOSSIBLE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
   ALL_TAC] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `aA:real`] COR_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aA:real`]
    CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cW:real` (X_CHOOSE_THEN `sW:real` (X_CHOOSE_THEN
    `uW:real` (X_CHOOSE_THEN `vW:real` (X_CHOOSE_THEN `aW:real`
    STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aA`)) THEN
  SUBGOAL_THEN
   `linside cW sW uW vW aA (&1543 / &500) (&2) /\
    linside cW sW uW vW aA (&3) (&12 / &5) /\
    linside cW sW uW vW aA (&12 / &5) (&3) /\
    ~linside cW sW uW vW aA (&3) (&3) /\
    ldisj c' s' u' v' aA cW sW uW vW aA`
  STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[ldisj] THEN
   UNDISCH_TAC `ldisj c' s' u' v' aA cR sR uR vR aA` THEN
   REWRITE_TAC[ldisj] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
    DWC_WALL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`s':real`; `--c':real`; `--v' - aA:real`; `u':real`; `aA:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aA:real`]
    DWC_NEGATIVE_PAIR_IMPOSSIBLE) THEN
  REWRITE_TAC[DWC_TURN3_INSIDE] THEN
  UNDISCH_TAC `ldisj c' s' u' v' aA cW sW uW vW aA` THEN
  REWRITE_TAC[ldisj; DWC_TURN3_INSIDE] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;
