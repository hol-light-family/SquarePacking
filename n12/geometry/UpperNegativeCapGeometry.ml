(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeCapGeometry.lean                  *)
(* (N12Compact.C868.UpperNegativeCap, Jatloe).                               *)
(* Data (extends Input) = c868cg_data; private peakX / peakY =                *)
(* c868cg_peakx / c868cg_peaky; WallProfile.vertex = OCWPVG_VERTEX;          *)
(* ClosedPointExclusion.outside_of_closed = OUTSIDE_OF_CLOSED (p2_base);     *)
(* UpperNegativeCapScalars = C868CSC_*, UpperNegativeTopFaces = C868TF_*.     *)
(* ClosedInside = lclosed.  A square H is c s u v a, the top square T is     *)
(* cT sT uT vT aT.  Tag C868CG_.                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/UpperNegativeCapFaces.ml";;
needs "n12/geometry/UpperNegativeCapScalars.ml";;
needs "n12/geometry/UpperNegativeTopFaces.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

(* Lean: Data (structure, extends Input) *)
let c868cg_data = new_definition
 `c868cg_data (c:real) s u v a <=>
    ocmpnuf_input c s u v a /\
    --(&1 / &20) * (c - s) <= v /\
    v + a <= &543 / &500 * c /\
    u + a <= &23 / &50 * c + &1 / &100 * s`;;

(* Lean: peakX, peakY (private) *)
let c868cg_peakx = new_definition
 `c868cg_peakx (c:real) (s:real) (u:real) (v:real) (a:real) = c * u - s * (v + a)`;;
let c868cg_peaky = new_definition
 `c868cg_peaky (c:real) (s:real) (u:real) (v:real) (a:real) = s * u + c * (v + a)`;;

let C868CG_DATA_TAC =
  FIRST_ASSUM(fun th ->
    if fst(strip_comb(concl th)) = `c868cg_data` then
      STRIP_ASSUME_TAC (REWRITE_RULE[c868cg_data] th) else NO_TAC) THEN
  C868UI_USE C868UI_SQ OCMPNUF_LOWER_U THEN
  C868UI_USE C868UI_SQ OCMPNUF_LOWER_V THEN
  C868UI_INPUT_TAC;;

(* Lean: scalar_inputs (private) *)
let C868CG_SCALAR_INPUTS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c868cg_data c s u v a
     ==> &1 < &18 / &25 * c - &99 / &100 * s /\
         &1 < &142 / &125 * c - &1 / &20 * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868CG_DATA_TAC THEN
  CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: peak_closed *)
let C868CG_PEAK_CLOSED = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a
     ==> lclosed c s u v a (c868cg_peakx c s u v a) (c868cg_peaky c s u v a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[c868cg_peakx; c868cg_peaky] THEN
  MATCH_MP_TAC OCWPVG_VERTEX THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < a` THEN REAL_ARITH_TAC);;

(* strict product  &0 < x * y *)
let C868CG_PPROD x y =
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` `&0` (mk_binop `(*):real->real->real` x y))
    ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC];;

let C868CG_SCALARS_TAC =
  C868UI_USE C868UI_SQ C868CG_SCALAR_INPUTS THEN
  MAP_EVERY (fun th -> C868UI_USE [`c:real`; `--s`] th)
    [C868CSC_HEIGHT; C868CSC_LEFT; C868CSC_TOP; C868CSC_CHORD; C868CSC_EDGE];;

(* the five estimates of peak_bounds, each from its own product facts
   (t = --s >= 0; floorU, floorV = OCMPNUF_LOWER_U / _V; the Data faces) *)
let C868CG_X_LOW = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 <= --s /\ &0 <= c /\ c <= &1 /\ &1 < a /\
     --(&13 / &50) * c + s <= u /\ &13 / &50 * s <= v
     ==> --(&13 / &50) <= c * u - s * (v + a)`,
  REPEAT STRIP_TAC THEN
  C868SP_PROD `c:real` `u - (--(&13 / &50) * c + s)` THEN
  C868SP_PROD `--s` `v - &13 / &50 * s` THEN
  C868SP_PROD `--s` `a - &1` THEN C868SP_PROD `--s` `&1 - c` THEN
  NLIN_TAC ~deg2:false []);;

let C868CG_X_HIGH = prove
 (`forall c s u v a. &0 <= --s /\ &0 < c /\ &1 < a /\
     u + a <= &23 / &50 * c + &1 / &100 * s /\ v + a <= &543 / &500 * c /\
     &23 / &50 * c pow 2 + &269 / &250 * c * --s - c < --(&1 / &25)
     ==> c * u - s * (v + a) < --(&1 / &25)`,
  REPEAT STRIP_TAC THEN
  C868SP_PROD `c:real` `(&23 / &50 * c + &1 / &100 * s) - (u + a)` THEN
  C868SP_PROD `--s` `&543 / &500 * c - (v + a)` THEN
  C868CG_PPROD `c:real` `a - &1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC ~deg2:false []);;

let C868CG_Y_HIGH = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 <= --s /\ &0 <= c /\
     --(&13 / &50) * c + s <= u /\ v + a <= &543 / &500 * c /\
     &1 + &43 / &500 * c pow 2 + &13 / &50 * c * --s < &59 / &50
     ==> s * u + c * (v + a) < &59 / &50`,
  REPEAT STRIP_TAC THEN
  C868SP_PROD `--s` `u - (--(&13 / &50) * c + s)` THEN
  C868SP_PROD `c:real` `&543 / &500 * c - (v + a)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC ~deg2:false []);;

let C868CG_Y_LOW = prove
 (`forall c s u v a. &0 <= --s /\ &0 < c /\ &1 < a /\
     u + a <= &23 / &50 * c + &1 / &100 * s /\ --(&1 / &20) * (c - s) <= v /\
     &53 / &50 < c + --s - &51 / &100 * c * --s + &1 / &100 * --s pow 2 - &1 / &20 * c pow 2
     ==> &53 / &50 < s * u + c * (v + a)`,
  REPEAT STRIP_TAC THEN
  C868SP_PROD `--s` `(&23 / &50 * c + &1 / &100 * s) - (u + a)` THEN
  C868SP_PROD `c:real` `v - --(&1 / &20) * (c - s)` THEN
  C868CG_PPROD `c:real` `a - &1` THEN C868SP_PROD `--s` `a - &1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC ~deg2:false []);;

let C868CG_ABOVE = prove
 (`forall c s u v a. &0 <= --s /\ &0 < c /\ --s <= c /\ &1 < a /\
     u + a <= &23 / &50 * c + &1 / &100 * s /\ --(&1 / &20) * (c - s) <= v /\
     &543 / &500 < &443 / &400 * c + &357 / &400 * --s - &10071 / &20000 * c * --s -
                   &1989 / &20000 * c pow 2 + &123 / &8000 * --s pow 2
     ==> &543 / &500 + &43 / &400 * (c * u - s * (v + a)) < s * u + c * (v + a)`,
  REPEAT STRIP_TAC THEN
  C868SP_PROD `--s + &43 / &400 * c` `(&23 / &50 * c + &1 / &100 * s) - (u + a)` THEN
  C868SP_PROD `c + &43 / &400 * s` `v - --(&1 / &20) * (c - s)` THEN
  C868CG_PPROD `(--s + &43 / &400 * c) + (c + &43 / &400 * s)` `a - &1` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC ~deg2:false []);;

(* Lean: peak_bounds *)
let C868CG_PEAK_BOUNDS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c868cg_data c s u v a
     ==> --(&13 / &50) <= c868cg_peakx c s u v a /\
         c868cg_peakx c s u v a < --(&1 / &25) /\
         &53 / &50 < c868cg_peaky c s u v a /\
         c868cg_peaky c s u v a < &59 / &50 /\
         &543 / &500 + &43 / &400 * c868cg_peakx c s u v a < c868cg_peaky c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868CG_DATA_TAC THEN C868CG_SCALARS_TAC THEN
  REWRITE_TAC[c868cg_peakx; c868cg_peaky] THEN
  C868UI_USE C868UI_SQ C868CG_X_LOW THEN C868UI_USE C868UI_SQ C868CG_X_HIGH THEN
  C868UI_USE C868UI_SQ C868CG_Y_LOW THEN C868UI_USE C868UI_SQ C868CG_Y_HIGH THEN
  C868UI_USE C868UI_SQ C868CG_ABOVE THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: edge_point *)
let C868CG_EDGE_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ c868cg_data c s u v a
     ==> exists x. --(&13 / &50) <= x /\ x <= --(&7 / &100) /\
             lclosed c s u v a x (&53 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C868UI_USE C868UI_SQ C868CG_PEAK_BOUNDS THEN
  C868CG_DATA_TAC THEN C868CG_SCALARS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2; c868cg_peaky; c868cg_peakx]) THEN
  EXISTS_TAC `(u - &53 / &50 * s) / c` THEN
  ABBREV_TAC `x = (u - &53 / &50 * s) / c` THEN
  SUBGOAL_THEN `c * x + &53 / &50 * s = u` ASSUME_TAC THENL
  [EXPAND_TAC "x" THEN SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `&7 / &10 <= c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_DIV_LMUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (--s * x + c * &53 / &50) = &53 / &50 - s * u` ASSUME_TAC THENL
  [UNDISCH_TAC `c * x + &53 / &50 * s = u` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C868SP_PROD `--s` `u - (--(&13 / &50) * c + s)` THEN
  C868CG_PPROD `c:real` `(--s * --(&7 / &20) + c * &7 / &20) - v` THEN
  C868SP_PROD `c:real` `--s` THEN
  SUBGOAL_THEN `s * u + c * v < &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false [SPEC `c:real` REAL_LE_SQUARE]; ALL_TAC] THEN
  REWRITE_TAC[lclosed] THEN REPEAT CONJ_TAC THEN
  (NLIN_TAC ~deg2:false [] ORELSE
   (fun (asl,w as g) ->
      (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
       C868CG_PPROD `c:real` (mk_binop `(-):real->real->real` (lhand w) (rand w)) THEN
       NLIN_TAC ~deg2:false []) g)));;

(* Lean: impossible *)
let C868CG_IMPOSSIBLE = prove
 (`forall c s u v a cT sT uT vT aT.
     c * c + s * s = &1 /\ &0 < a /\ cT * cT + sT * sT = &1 /\ &0 < aT /\
     c868cg_data c s u v a /\
     &1 < aT /\ &0 < cT /\ &0 <= sT /\
     linside cT sT uT vT aT (--(&4 / &5)) (&1) /\
     linside cT sT uT vT aT (&0) (&543 / &500) /\
     ldisj c s u v a cT sT uT vT aT
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c868cg_data; ocmpnuf_input] o
    check (fun th -> fst(strip_comb(concl th)) = `c868cg_data`)) THEN
  SUBGOAL_THEN `forall x y. ~(linside cT sT uT vT aT x y /\ linside c s u v a x y)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj c s u v a cT sT uT vT aT` THEN REWRITE_TAC[ldisj] THEN MESON_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `~linside cT sT uT vT aT (--(&7 / &20)) (&7 / &20)` ASSUME_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `forall x y. lclosed c s u v a x y ==> ~linside cT sT uT vT aT x y` ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`;
                 `c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`]
     OUTSIDE_OF_CLOSED) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC `sT <= &2 / &5 * cT` THENL
  [C868UI_USE C868UI_SQ C868CG_PEAK_BOUNDS THEN
   C868UI_USE C868UI_SQ C868CG_PEAK_CLOSED THEN
   C868UI_USE [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`;
               `c868cg_peakx c s u v a`; `c868cg_peaky c s u v a`]
     C868TF_SHALLOW_REGION_TIGHT THEN
   ASM_MESON_TAC[];
   C868UI_USE C868UI_SQ C868CG_EDGE_POINT THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
   C868UI_USE [`cT:real`; `sT:real`; `uT:real`; `vT:real`; `aT:real`; `x:real`]
     C868TF_STEEP_REGION THEN
   ASM_MESON_TAC[]]);;
