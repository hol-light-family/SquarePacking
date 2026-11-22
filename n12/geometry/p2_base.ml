(* ========================================================================= *)
(* Phase 2, base layer: Jatloe's OpenSquare representation and the anchors  *)
(* of the four-square template (Compact/Geometry/FourSquareAnchors).        *)
(*                                                                           *)
(* A square is given by a unit normal (c,s), lower face offsets u, v and a   *)
(* side a:  (x,y) is inside  iff  u < c x + s y < u + a  and                 *)
(*                                 v < -s x + c y < v + a.                   *)
(* ========================================================================= *)

needs "n12/phase1/auxcover.ml";;
needs "shared/tools/cover_tac.ml";;

let linside = new_definition
 `linside (c:real) s u v a x y <=>
    u < c * x + s * y /\ c * x + s * y < u + a /\
    v < --s * x + c * y /\ --s * x + c * y < v + a`;;

let lclosed = new_definition
 `lclosed (c:real) s u v a x y <=>
    u <= c * x + s * y /\ c * x + s * y <= u + a /\
    v <= --s * x + c * y /\ --s * x + c * y <= v + a`;;

(* the bridge to the centred representation used in Phase 1 *)
let OSQ_LSQ = prove
 (`forall x y c1 c2 a b l. vector[x; y] IN osq c1 c2 a b l <=>
      linside a b (a * c1 + b * c2 - l / &2) (--b * c1 + a * c2 - l / &2) l x y`,
  REWRITE_TAC[IN_OSQ; linside] THEN REAL_ARITH_TAC);;

let LINSIDE_CLOSED = prove
 (`forall c s u v a x y. linside c s u v a x y ==> lclosed c s u v a x y`,
  SIMP_TAC[linside; lclosed; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Anchors.                                                                  *)
(* ------------------------------------------------------------------------- *)

let NONCONST_PROJ = prove
 (`forall A B x0 y0 x1 y1 x2 y2.
     A * A + B * B = &1 /\
     ~((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0) = &0)
     ==> ~(A * x0 + B * y0 = A * x1 + B * y1 /\ A * x0 + B * y0 = A * x2 + B * y2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0) = &0)` THEN REWRITE_TAC[] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

let STRICT_MEAN = prove
 (`forall l u a b c. l <= a /\ a <= u /\ l <= b /\ b <= u /\ l <= c /\ c <= u /\
               ~(a = b /\ a = c)
               ==> l < (a + b + c) / &3 /\ (a + b + c) / &3 < u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(a:real = b /\ a = c)` THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CENTROID_INSIDE = prove
 (`forall c s u v a x0 y0 x1 y1 x2 y2.
      c * c + s * s = &1 /\
      lclosed c s u v a x0 y0 /\ lclosed c s u v a x1 y1 /\ lclosed c s u v a x2 y2 /\
      ~((x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0) = &0)
      ==> linside c s u v a ((x0 + x1 + x2) / &3) ((y0 + y1 + y2) / &3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`u:real`; `u + a:real`; `c * x0 + s * y0`; `c * x1 + s * y1`; `c * x2 + s * y2`]
         STRICT_MEAN) THEN
  MP_TAC(SPECL [`v:real`; `v + a:real`; `--s * x0 + c * y0`; `--s * x1 + c * y1`; `--s * x2 + c * y2`]
         STRICT_MEAN) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `x0:real`; `y0:real`; `x1:real`; `y1:real`; `x2:real`; `y2:real`]
         NONCONST_PROJ) THEN
  MP_TAC(SPECL [`--s:real`; `c:real`; `x0:real`; `y0:real`; `x1:real`; `y1:real`; `x2:real`; `y2:real`]
         NONCONST_PROJ) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_imp(concl th) then MP_TAC th THEN
           ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] else NO_TAC)) THEN
  ASM_REAL_ARITH_TAC);;

let anchor_thm (p0,p1,p2) =
  let (x0,y0) = p0 and (x1,y1) = p1 and (x2,y2) = p2 in
  let th = SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; x0; y0; x1; y1; x2; y2] CENTROID_INSIDE in
  let th = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) th in
  let th = REWRITE_RULE[] th in
  GENL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] th;;

let ANCHOR_A = anchor_thm ((q"&2",q"&113 / &50"),(q"&113 / &50",q"&2"),(q"&47 / &20",q"&47 / &20"));;
let ANCHOR_B = anchor_thm ((q"&8 / &5",q"&3"),(q"&33 / &20",q"&47 / &20"),(q"&87 / &50",q"&3"));;
let ANCHOR_L = anchor_thm ((q"&457 / &500",q"&2"),(q"&1",q"&113 / &50"),(q"&1",q"&12 / &5"));;
let ANCHOR_R = anchor_thm ((q"&3",q"&113 / &50"),(q"&1543 / &500",q"&2"),(q"&3",q"&12 / &5"));;

(* ------------------------------------------------------------------------- *)
(* Closed points of a foreign square (ClosedPointExclusion).                 *)
(* ------------------------------------------------------------------------- *)

let LCLOSED_SEGMENT = prove
 (`forall c s u v a x0 y0 x1 y1 t.
      lclosed c s u v a x0 y0 /\ lclosed c s u v a x1 y1 /\ &0 <= t /\ t <= &1
      ==> lclosed c s u v a ((&1 - t) * x0 + t * x1) ((&1 - t) * y0 + t * y1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN NLIN_TAC []);;

let POS_NEAR_ZERO = prove
 (`forall al be. &0 < al ==> exists e. &0 < e /\ forall t. &0 < t /\ t < e ==> &0 < al + be * t`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `al / (abs be + &1)` THEN
  SUBGOAL_THEN `&0 < abs be + &1` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_RDIV_EQ] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`abs be`; `t:real`] REAL_LE_MUL) THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `--(abs be * t) <= be * t` MP_TAC THENL
   [ASM_CASES_TAC `&0 <= be` THENL
     [ASM_SIMP_TAC[REAL_ARITH `&0 <= be ==> abs be = be`] THEN
      MP_TAC(SPECL [`be:real`; `t:real`] REAL_LE_MUL) THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ARITH `~(&0 <= be) ==> abs be = --be`] THEN REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

let CONVEX_STRICT = prove
 (`forall l u p m t. l <= p /\ p <= u /\ l < m /\ m < u /\ &0 < t /\ t < &1
               ==> l < (&1 - t) * p + t * m /\ (&1 - t) * p + t * m < u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN NLIN_TAC []);;

(* centre of a square in face coordinates *)
let LCENTRE = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> c * (c * (u + a / &2) - s * (v + a / &2)) + s * (s * (u + a / &2) + c * (v + a / &2)) = u + a / &2 /\
         --s * (c * (u + a / &2) - s * (v + a / &2)) + c * (s * (u + a / &2) + c * (v + a / &2)) = v + a / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

let OUTSIDE_OF_CLOSED = prove
 (`forall c s u v a c' s' u' v' a' x y.
      c' * c' + s' * s' = &1 /\ &0 < a' /\
      (forall x y. ~(linside c s u v a x y /\ linside c' s' u' v' a' x y)) /\
      lclosed c' s' u' v' a' x y
      ==> ~(linside c s u v a x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  ABBREV_TAC `X0 = c' * (u' + a' / &2) - s' * (v' + a' / &2)` THEN
  ABBREV_TAC `Y0 = s' * (u' + a' / &2) + c' * (v' + a' / &2)` THEN
  ABBREV_TAC `du = c * (X0 - x) + s * (Y0 - y)` THEN
  ABBREV_TAC `dv = --s * (X0 - x) + c * (Y0 - y)` THEN
  MP_TAC(SPECL [`c * x + s * y - u`; `du:real`] POS_NEAR_ZERO) THEN
  MP_TAC(SPECL [`u + a - (c * x + s * y)`; `--du:real`] POS_NEAR_ZERO) THEN
  MP_TAC(SPECL [`--s * x + c * y - v`; `dv:real`] POS_NEAR_ZERO) THEN
  MP_TAC(SPECL [`v + a - (--s * x + c * y)`; `--dv:real`] POS_NEAR_ZERO) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `e3:real` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC)] THEN
  ABBREV_TAC `t = min (min e0 e1) (min (min e2 e3) (&1 / &2)) / &2` THEN
  SUBGOAL_THEN `&0 < t /\ t < e0 /\ t < e1 /\ t < e2 /\ t < e3 /\ t < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(&1 - t) * x + t * X0`; `(&1 - t) * y + t * Y0`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  REWRITE_TAC[linside] THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] LCENTRE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THEN REPEAT CONJ_TAC THEN NLIN_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Shared vocabulary (Jatloe: Container, SquareFrame, SymmetryBase).         *)
(* A square is the 5-tuple c s u v a with c*c + s*s = &1 and &0 < a.         *)
(* ------------------------------------------------------------------------- *)

let lsquare = new_definition
 `lsquare (c:real) (s:real) (u:real) (v:real) (a:real) <=> c * c + s * s = &1 /\ &0 < a`;;

let lcont = new_definition
 `lcont c s u v a <=>
    forall x y. linside c s u v a x y ==> &0 <= x /\ x <= &4 /\ &0 <= y /\ y <= &4`;;

let ldisj = new_definition
 `ldisj c s u v a c' s' u' v' a' <=>
    forall x y. ~(linside c s u v a x y /\ linside c' s' u' v' a' x y)`;;

let lcx = new_definition `lcx (c:real) s u v a = c * (u + a / &2) - s * (v + a / &2)`;;
let lcy = new_definition `lcy (c:real) s u v a = s * (u + a / &2) + c * (v + a / &2)`;;

let LCENTRE_COORDS = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> c * lcx c s u v a + s * lcy c s u v a = u + a / &2 /\
         --s * lcx c s u v a + c * lcy c s u v a = v + a / &2`,
  REWRITE_TAC[lcx; lcy] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;

(* the symmetries: x -> 4 - x, y -> 4 - y, and x <-> y, as maps of the 5-tuple *)
let LINSIDE_PULLX = prove
 (`forall c s u v a x y. linside (--c) s (u - &4 * c) (--v - a - &4 * s) a x y <=>
                   linside c s u v a (&4 - x) y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let LINSIDE_PULLY = prove
 (`forall c s u v a x y. linside c (--s) (u - &4 * s) (&4 * c - v - a) a x y <=>
                   linside c s u v a x (&4 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let LINSIDE_PULLSW = prove
 (`forall c s u v a x y. linside s c u (--v - a) a x y <=> linside c s u v a y x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let LCLOSED_PULLX = prove
 (`forall c s u v a x y. lclosed (--c) s (u - &4 * c) (--v - a - &4 * s) a x y <=>
                   lclosed c s u v a (&4 - x) y`,
  REWRITE_TAC[lclosed] THEN REAL_ARITH_TAC);;
let LCLOSED_PULLY = prove
 (`forall c s u v a x y. lclosed c (--s) (u - &4 * s) (&4 * c - v - a) a x y <=>
                   lclosed c s u v a x (&4 - y)`,
  REWRITE_TAC[lclosed] THEN REAL_ARITH_TAC);;
let LCLOSED_PULLSW = prove
 (`forall c s u v a x y. lclosed s c u (--v - a) a x y <=> lclosed c s u v a y x`,
  REWRITE_TAC[lclosed] THEN REAL_ARITH_TAC);;

let LCONT_PULLX = prove
 (`forall c s u v a. lcont c s u v a ==> lcont (--c) s (u - &4 * c) (--v - a - &4 * s) a`,
  REWRITE_TAC[lcont; LINSIDE_PULLX] THEN MESON_TAC[REAL_ARITH
   `&0 <= &4 - x /\ &4 - x <= &4 ==> &0 <= x /\ x <= &4`]);;
let LCONT_PULLY = prove
 (`forall c s u v a. lcont c s u v a ==> lcont c (--s) (u - &4 * s) (&4 * c - v - a) a`,
  REWRITE_TAC[lcont; LINSIDE_PULLY] THEN MESON_TAC[REAL_ARITH
   `&0 <= &4 - x /\ &4 - x <= &4 ==> &0 <= x /\ x <= &4`]);;
let LCONT_PULLSW = prove
 (`forall c s u v a. lcont c s u v a ==> lcont s c u (--v - a) a`,
  REWRITE_TAC[lcont; LINSIDE_PULLSW] THEN MESON_TAC[]);;

let LSQUARE_PULLS = prove
 (`forall c s u v a. lsquare c s u v a
     ==> lsquare (--c) s (u - &4 * c) (--v - a - &4 * s) a /\
         lsquare c (--s) (u - &4 * s) (&4 * c - v - a) a /\
         lsquare s c u (--v - a) a`,
  REWRITE_TAC[lsquare] THEN REAL_ARITH_TAC);;
