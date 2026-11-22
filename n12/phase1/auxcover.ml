(* ========================================================================= *)
(* Port, layer 4: the auxiliary F/G covers (Jatloe: AuxCoverBase,            *)
(* AuxCoverGeometry, AuxPairCover, WideWallRow, TwoHeightWall).              *)
(* A square that avoids the ten F points owns one of six marker pairs.       *)
(* ========================================================================= *)

needs "n12/phase1/markers.ml";;
needs "shared/tools/nlin.ml";;

let ABS_LT_BANDS = REAL_ARITH `forall x h. abs x < h <=> --h < x /\ x < h`;;

(* Every direction can be turned by a multiple of 90 degrees into the first   *)
(* quadrant without changing the square.                                     *)

let OSQ_POS_FRAME = prove
 (`forall c1 c2 a b l. a * a + b * b = &1
     ==> exists c s. &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\ abs a + abs b = c + s /\
               osq c1 c2 a b l = osq c1 c2 c s l`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= a` THEN ASM_CASES_TAC `&0 <= b` THENL
   [MAP_EVERY EXISTS_TAC [`a:real`; `b:real`];
    MAP_EVERY EXISTS_TAC [`--b`; `a:real`];
    MAP_EVERY EXISTS_TAC [`b:real`; `--a`];
    MAP_EVERY EXISTS_TAC [`--a`; `--b`]] THEN
  REWRITE_TAC[OSQ_ROT; OSQ_NEG; OSQ_ROT3] THEN
  REPEAT CONJ_TAC THEN TRY(UNDISCH_TAC `a * a + b * b = &1` THEN REAL_ARITH_TAC) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Wall rows in the positive frame.                                          *)
(* ------------------------------------------------------------------------- *)

let FRAME_FACTS_TAC =
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `s - &1`; SQ_NONNEG `c - &1`]
   [`c <= &1`; `s <= &1`; `&1 <= c + s`; `&0 <= c * s`; `&0 < (l - &1) * (c + s)`;
    `&0 < &1 + s * (c + s)`; `&0 < &1 + c * (c + s)`;
    `&0 < (l - &1) * (&1 + s * (c + s))`; `&0 < (l - &1) * (&1 + c * (c + s))`];;

let WIDE_WALL_ROW = prove
 (`forall X Y c s l bb w.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= Y /\ &0 <= X /\ X <= w /\ &0 <= w /\ w <= &413 / &500 /\
        Y <= bb /\ bb <= &1
        ==> vector[&0; bb] IN osq X Y c s l \/ vector[w; bb] IN osq X Y c s l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN FRAME_FACTS_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c + s - &99 / &70`; SQ_NONNEG `s - &1`;
                  SQ_NONNEG `c - &1`]
   [`c + s <= &99 / &70`; `&0 <= (c * s) * (&413 / &500 - w)`;
    `s * (bb - Y) < l / &2`; `c * (bb - Y) < l / &2`;
    `&0 <= &1 - &413 / &1000 * (c + s + &1)`;
    `&0 <= (&1 - &413 / &1000 * (c + s + &1)) * (c + s - &1)`] THEN
  DISJ_NLIN_TAC [SQ_NONNEG `c - s`]);;

let TWO_HEIGHT_WALL = prove
 (`forall X Y c s l w bb d.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= Y /\ &0 <= X /\ X <= w /\ &0 <= w /\ w <= &4 / &5 /\
        Y <= d /\ &9 / &10 <= bb /\ bb <= d /\ d <= &1
        ==> vector[&0; bb] IN osq X Y c s l \/ vector[w; d] IN osq X Y c s l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN FRAME_FACTS_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c + s - &3 / &2`; SQ_NONNEG `s - &1`;
                  SQ_NONNEG `c - &1`; SQ_NONNEG `c:real`; SQ_NONNEG `s:real`]
   [`c + s <= &3 / &2`; `&0 <= (c * s) * (&4 / &5 - w)`;
    `s * (bb - Y) < l / &2`; `c * (d - Y) < l / &2`;
    `--(l / &2) < s * X + c * (bb - Y)`;
    `w * w + (d - bb) * (d - bb) <= &1`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `w:real`; `d - bb`] CS_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ARITH `abs x <= &1 <=> -- &1 <= x /\ x <= &1`] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c:real`; SQ_NONNEG `s:real`]
   [
    `&0 <= (s * s) * (&1 / &10 - (d - bb))`;
    `&0 <= (c * c) * (&1 - bb)`; `&0 <= (s * s) * (&1 - d)`;
    `&0 <= &3 / &5 - &2 / &5 * (c + s)`;
    `&0 <= (&3 / &5 - &2 / &5 * (c + s)) * (c + s - &1)`] THEN
  DISJ_NLIN_TAC [SQ_NONNEG `c - s`]);;

(* ------------------------------------------------------------------------- *)
(* General-direction forms, with the container walls as owalls.              *)
(* ------------------------------------------------------------------------- *)

let OWALLS_SW = prove
 (`forall c1 c2 a b l. owalls c2 c1 b a l <=> owalls c1 c2 a b l`,
  REWRITE_TAC[owalls] THEN REAL_ARITH_TAC);;

let OSQ_SWAP_PT = prove
 (`forall x y c1 c2 a b l. vector[x; y] IN osq c2 c1 b a l <=> vector[y; x] IN osq c1 c2 a b l`,
  REWRITE_TAC[IN_OSQ] THEN REAL_ARITH_TAC);;

let FRAME_INTRO_TAC =
  MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] OSQ_POS_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `owalls c1 c2 a b l` THEN ASM_REWRITE_TAC[owalls] THEN STRIP_TAC;;

let BOTTOM_SEGMENT = prove
 (`forall c1 c2 a b l x0 x1 bb.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        x0 <= c1 /\ c1 <= x1 /\ c2 <= bb /\ x1 - x0 <= &413 / &500 /\ bb <= &1
        ==> vector[x0; bb] IN osq c1 c2 a b l \/ vector[x1; bb] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FRAME_INTRO_TAC THEN
  MP_TAC(SPECL [`c1 - x0`; `c2:real`; `c:real`; `s:real`; `l:real`; `bb:real`; `x1 - x0`]
         WIDE_WALL_ROW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_OSQ] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN BINOP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let BOTTOM_TWOHEIGHT = prove
 (`forall c1 c2 a b l x0 x1 bb d.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        x0 <= c1 /\ c1 <= x1 /\ c2 <= d /\ x1 - x0 <= &4 / &5 /\
        &9 / &10 <= bb /\ bb <= d /\ d <= &1
        ==> vector[x0; bb] IN osq c1 c2 a b l \/ vector[x1; d] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FRAME_INTRO_TAC THEN
  MP_TAC(SPECL [`c1 - x0`; `c2:real`; `c:real`; `s:real`; `l:real`; `x1 - x0`;
                `bb:real`; `d:real`] TWO_HEIGHT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_OSQ] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN BINOP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let CORNER_H = prove
 (`forall c1 c2 a b l bb.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        c1 <= &1 /\ c2 <= &1 /\ &9 / &10 <= bb /\ bb <= &1
        ==> vector[bb; &1] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FRAME_INTRO_TAC THEN
  MATCH_MP_TAC CORNER_POINT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The F-avoidance chain (Jatloe: aux_avoid_walls ... avoidingF_forces_pair). *)
(* ------------------------------------------------------------------------- *)

let SQ_HYPS = `&1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l`;;

(* apply a wall lemma to the square or to its mirror image in y = x, then close
   the goal F from the negated memberships among the assumptions *)
let HIT_TAC lemma args =
  MP_TAC(SPECL ([`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] @ args) lemma) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[];;

let OSQ_SWAP_C = prove
 (`forall x y. vector[x; y] IN osq c2 c1 b a l <=> vector[y; x] IN osq c1 c2 a b l`,
  REWRITE_TAC[OSQ_SWAP_PT]);;
let SW_RULE = ONCE_REWRITE_RULE[OSQ_SWAP_PT; OWALLS_SW];;

let SWHIT_TAC lemma args =
  MP_TAC(SW_RULE (SPECL ([`c2:real`; `c1:real`; `b:real`; `a:real`; `l:real`] @ args) lemma)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[];;

let AUX_AVOID_WALLS = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        ~(vector[&1; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&1; &113 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&8 / &5; &1] IN osq c1 c2 a b l) /\
        ~(vector[&12 / &5; &1] IN osq c1 c2 a b l) /\
        (~(vector[&1; &457 / &500] IN osq c1 c2 a b l) \/
         ~(vector[&457 / &500; &1] IN osq c1 c2 a b l)) /\
        c1 <= &2 /\ c2 <= &2
        ==> &1 < c1 /\ &1 < c2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  (SUBGOAL_THEN `&1 < c1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    ASM_CASES_TAC `c2 <= &1` THENL
     [MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`; `&457 / &500`] CORNER_H) THEN
      MP_TAC(SW_RULE (SPECL [`c2:real`; `c1:real`; `b:real`; `a:real`; `l:real`; `&457 / &500`] CORNER_H)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `c2 <= &87 / &50` THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [SWHIT_TAC BOTTOM_SEGMENT [`&457 / &500`; `&87 / &50`; `&1`];
        SWHIT_TAC BOTTOM_TWOHEIGHT [`&1`; `&87 / &50`; `&457 / &500`; `&1`]];
      SWHIT_TAC BOTTOM_SEGMENT [`&87 / &50`; `&113 / &50`; `&1`]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ASM_CASES_TAC `c1 <= &8 / &5` THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [HIT_TAC BOTTOM_TWOHEIGHT [`&1`; `&8 / &5`; `&457 / &500`; `&1`];
      HIT_TAC BOTTOM_SEGMENT [`&457 / &500`; `&8 / &5`; `&1`]];
    HIT_TAC BOTTOM_SEGMENT [`&8 / &5`; `&12 / &5`; `&1`]]));;

(* Triangle covers with barycentric weights affine in the centre.           *)

let tri_lemma (p0,p1,p2) (w0,w1,w2) =
  let pt (x,y) = mk_comb(`vector:(real)list->real^2`, mk_list([x;y],`:real`)) in
  let mem p = mk_comb(mk_comb(`(IN):real^2->(real^2->bool)->bool`, pt p), `osq c1 c2 a b l`) in
  let ge0 w = mk_binop `(<=):real->real->bool` `&0` w in
  let tm = list_mk_forall([`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`],
    mk_imp(list_mk_conj [`&1 < l`; `a * a + b * b = &1`; ge0 w0; ge0 w1; ge0 w2],
           list_mk_disj [mem p0; mem p1; mem p2])) in
  let (x0,y0) = p0 and (x1,y1) = p1 and (x2,y2) = p2 in
  prove(tm,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`;
                  x0;y0;x1;y1;x2;y2;w0;w1;w2] TRIANGLE_NONAVOID) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN REAL_ARITH_TAC);;

let q x = parse_term x;;
let AUX0A_HIT = tri_lemma ((q"&1",q"&457 / &500"),(q"&8 / &5",q"&1"),(q"&1",q"&87 / &50"))
  (q"(-- &1850 / &1239) * c1 + (-- &500 / &413) * c2 + &4460 / &1239",
   q"(&5 / &3) * c1 - &5 / &3",
   q"(-- &215 / &1239) * c1 + (&500 / &413) * c2 + (-- &1156 / &1239)");;
let AUX0B_HIT = tri_lemma ((q"&457 / &500",q"&1"),(q"&8 / &5",q"&1"),(q"&1",q"&87 / &50"))
  (q"(-- &500 / &343) * c1 + (-- &15000 / &12691) * c2 + &44600 / &12691",
   q"(&500 / &343) * c1 + (-- &2150 / &12691) * c2 + (-- &14759 / &12691)",
   q"(&50 / &37) * c2 - &50 / &37");;
let AUX1_HIT = tri_lemma ((q"&1",q"&87 / &50"),(q"&8 / &5",q"&1"),(q"&2",q"&87 / &50"))
  (q"-- c1 + (&20 / &37) * c2 + &196 / &185",
   q"(-- &50 / &37) * c2 + &87 / &37",
   q"c1 + (&30 / &37) * c2 + (-- &446 / &185)");;
let AUX2_HIT = tri_lemma ((q"&8 / &5",q"&1"),(q"&12 / &5",q"&1"),(q"&2",q"&87 / &50"))
  (q"(-- &5 / &4) * c1 + (-- &25 / &37) * c2 + &136 / &37",
   q"(&5 / &4) * c1 + (-- &25 / &37) * c2 + (-- &49 / &37)",
   q"(&50 / &37) * c2 - &50 / &37");;
let FANL_HIT = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&1",q"&87 / &50"),(q"&1",q"&113 / &50"))
  (q"(&20 / &13) * c1 - &20 / &13",
   q"(-- &305 / &169) * c1 + (-- &25 / &13) * c2 + &2079 / &338",
   q"(&45 / &169) * c1 + (&25 / &13) * c2 + (-- &1221 / &338)");;
let FANT_HIT = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&1",q"&113 / &50"),(q"&2",q"&113 / &50"))
  (q"(-- &100 / &61) * c2 + &226 / &61",
   q"-- c1 + (&35 / &61) * c2 + &429 / &610",
   q"c1 + (&65 / &61) * c2 + (-- &2079 / &610)");;
let FANR_HIT = tri_lemma ((q"&33 / &20",q"&33 / &20"),(q"&2",q"&87 / &50"),(q"&2",q"&113 / &50"))
  (q"(-- &20 / &7) * c1 + &40 / &7",
   q"(&305 / &91) * c1 + (-- &25 / &13) * c2 + (-- &33 / &14)",
   q"(-- &45 / &91) * c1 + (&25 / &13) * c2 + (-- &33 / &14)");;

let TRIHIT_TAC th =
  MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];;

let AUX_LOWER_INTERIOR = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\
        ~(vector[&1; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&8 / &5; &1] IN osq c1 c2 a b l) /\
        ~(vector[&2; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&12 / &5; &1] IN osq c1 c2 a b l) /\
        (~(vector[&1; &457 / &500] IN osq c1 c2 a b l) \/
         ~(vector[&457 / &500; &1] IN osq c1 c2 a b l)) /\
        &1 <= c1 /\ c1 <= &2 /\ &1 <= c2 /\ c2 <= &87 / &50
        ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= c1 + (&30 / &37) * c2 + (-- &446 / &185)` THENL
   [ASM_CASES_TAC `&0 <= -- c1 + (&20 / &37) * c2 + &196 / &185` THENL
     [TRIHIT_TAC AUX1_HIT; TRIHIT_TAC AUX2_HIT];
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [TRIHIT_TAC AUX0A_HIT; TRIHIT_TAC AUX0B_HIT]]);;

let AUX_LOWER_LOC = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        ~(vector[&1; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&1; &113 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&8 / &5; &1] IN osq c1 c2 a b l) /\
        ~(vector[&2; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&12 / &5; &1] IN osq c1 c2 a b l) /\
        (~(vector[&1; &457 / &500] IN osq c1 c2 a b l) \/
         ~(vector[&457 / &500; &1] IN osq c1 c2 a b l)) /\
        c1 <= &2 /\ c2 <= &2
        ==> &1 < c1 /\ &87 / &50 < c2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] AUX_AVOID_WALLS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] AUX_LOWER_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let AUX_CENTRAL_FAN = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\
        ~(vector[&1; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&1; &113 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&2; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&2; &113 / &50] IN osq c1 c2 a b l) /\
        &1 <= c1 /\ c1 <= &2 /\ &87 / &50 <= c2 /\ c2 <= &113 / &50
        ==> vector[&33 / &20; &33 / &20] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `&0 <= -- c1 + (&35 / &61) * c2 + &429 / &610` THENL
   [ASM_CASES_TAC `&0 <= c1 + (&65 / &61) * c2 + (-- &2079 / &610)` THENL
     [TRIHIT_TAC FANT_HIT; TRIHIT_TAC FANL_HIT];
    TRIHIT_TAC FANR_HIT]);;

(* Reflections y -> 4 - y and x -> 4 - x of the square. *)

let OSQ_RY_PT = prove
 (`forall x y c1 c2 a b l. vector[x; y] IN osq c1 (&4 - c2) b a l <=>
                     vector[x; &4 - y] IN osq c1 c2 a b l`,
  REWRITE_TAC[IN_OSQ] THEN REAL_ARITH_TAC);;
let OSQ_RX_PT = prove
 (`forall x y c1 c2 a b l. vector[x; y] IN osq (&4 - c1) c2 b a l <=>
                     vector[&4 - x; y] IN osq c1 c2 a b l`,
  REWRITE_TAC[IN_OSQ] THEN REAL_ARITH_TAC);;
let OWALLS_RY = prove
 (`forall c1 c2 a b l. owalls c1 (&4 - c2) b a l <=> owalls c1 c2 a b l`,
  REWRITE_TAC[owalls] THEN REAL_ARITH_TAC);;
let OWALLS_RX = prove
 (`forall c1 c2 a b l. owalls (&4 - c1) c2 b a l <=> owalls c1 c2 a b l`,
  REWRITE_TAC[owalls] THEN REAL_ARITH_TAC);;

let RY_RULE th =
  CONV_RULE (REAL_RAT_REDUCE_CONV) (ONCE_REWRITE_RULE[OSQ_RY_PT; OWALLS_RY]
    (SPECL [`c1:real`; `&4 - c2`; `b:real`; `a:real`; `l:real`] th));;
let RX_RULE th =
  CONV_RULE (REAL_RAT_REDUCE_CONV) (ONCE_REWRITE_RULE[OSQ_RX_PT; OWALLS_RX]
    (SPECL [`&4 - c1`; `c2:real`; `b:real`; `a:real`; `l:real`] th));;

let USE_TAC th =
  MP_TAC th THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN TRY(UNDISCH_TAC `a * a + b * b = &1` THEN REAL_ARITH_TAC) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC];;

let AUX_LEFT_PAIR = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        ~(vector[&1; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&1; &113 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&8 / &5; &1] IN osq c1 c2 a b l) /\
        ~(vector[&8 / &5; &3] IN osq c1 c2 a b l) /\
        ~(vector[&2; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&2; &113 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&12 / &5; &1] IN osq c1 c2 a b l) /\
        ~(vector[&12 / &5; &3] IN osq c1 c2 a b l) /\
        (~(vector[&1; &457 / &500] IN osq c1 c2 a b l) \/
         ~(vector[&457 / &500; &1] IN osq c1 c2 a b l)) /\
        (~(vector[&1; &1543 / &500] IN osq c1 c2 a b l) \/
         ~(vector[&457 / &500; &3] IN osq c1 c2 a b l)) /\
        c1 <= &2
        ==> vector[&33 / &20; &33 / &20] IN osq c1 c2 a b l /\
            vector[&33 / &20; &47 / &20] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= c1 /\ &87 / &50 <= c2 /\ c2 <= &113 / &50` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `c2 <= &2` THENL
     [USE_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] AUX_LOWER_LOC) THEN
      ASM_REAL_ARITH_TAC;
      USE_TAC(RY_RULE AUX_LOWER_LOC) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] AUX_CENTRAL_FAN) THEN
    REWRITE_TAC[];
    USE_TAC(RY_RULE AUX_CENTRAL_FAN) THEN REWRITE_TAC[]]);;

let AVOIDF_FORCES_PAIR = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        ~(vector[&1; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&1; &113 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&8 / &5; &1] IN osq c1 c2 a b l) /\
        ~(vector[&8 / &5; &3] IN osq c1 c2 a b l) /\
        ~(vector[&2; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&2; &113 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&12 / &5; &1] IN osq c1 c2 a b l) /\
        ~(vector[&12 / &5; &3] IN osq c1 c2 a b l) /\
        ~(vector[&3; &87 / &50] IN osq c1 c2 a b l) /\
        ~(vector[&3; &113 / &50] IN osq c1 c2 a b l)
        ==> (vector[&1; &457 / &500] IN osq c1 c2 a b l /\
             vector[&457 / &500; &1] IN osq c1 c2 a b l) \/
            (vector[&3; &457 / &500] IN osq c1 c2 a b l /\
             vector[&1543 / &500; &1] IN osq c1 c2 a b l) \/
            (vector[&3; &1543 / &500] IN osq c1 c2 a b l /\
             vector[&1543 / &500; &3] IN osq c1 c2 a b l) \/
            (vector[&1; &1543 / &500] IN osq c1 c2 a b l /\
             vector[&457 / &500; &3] IN osq c1 c2 a b l) \/
            (vector[&33 / &20; &33 / &20] IN osq c1 c2 a b l /\
             vector[&33 / &20; &47 / &20] IN osq c1 c2 a b l) \/
            (vector[&47 / &20; &33 / &20] IN osq c1 c2 a b l /\
             vector[&47 / &20; &47 / &20] IN osq c1 c2 a b l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p0 /\ ~p1 /\ ~p2 /\ ~p3 ==> p4 \/ p5)
                     ==> p0 \/ p1 \/ p2 \/ p3 \/ p4 \/ p5`) THEN
  REWRITE_TAC[DE_MORGAN_THM; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `c1 <= &2` THENL
   [DISJ1_TAC THEN
    USE_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`] AUX_LEFT_PAIR) THEN
    REWRITE_TAC[];
    DISJ2_TAC THEN USE_TAC(RX_RULE AUX_LEFT_PAIR) THEN REWRITE_TAC[]]);;

let AVOIDG_FORCES_PAIR = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        ~(vector[&87 / &50; &1] IN osq c1 c2 a b l) /\
        ~(vector[&113 / &50; &1] IN osq c1 c2 a b l) /\
        ~(vector[&1; &8 / &5] IN osq c1 c2 a b l) /\
        ~(vector[&3; &8 / &5] IN osq c1 c2 a b l) /\
        ~(vector[&87 / &50; &2] IN osq c1 c2 a b l) /\
        ~(vector[&113 / &50; &2] IN osq c1 c2 a b l) /\
        ~(vector[&1; &12 / &5] IN osq c1 c2 a b l) /\
        ~(vector[&3; &12 / &5] IN osq c1 c2 a b l) /\
        ~(vector[&87 / &50; &3] IN osq c1 c2 a b l) /\
        ~(vector[&113 / &50; &3] IN osq c1 c2 a b l)
        ==> (vector[&457 / &500; &1] IN osq c1 c2 a b l /\
             vector[&1; &457 / &500] IN osq c1 c2 a b l) \/
            (vector[&457 / &500; &3] IN osq c1 c2 a b l /\
             vector[&1; &1543 / &500] IN osq c1 c2 a b l) \/
            (vector[&1543 / &500; &3] IN osq c1 c2 a b l /\
             vector[&3; &1543 / &500] IN osq c1 c2 a b l) \/
            (vector[&1543 / &500; &1] IN osq c1 c2 a b l /\
             vector[&3; &457 / &500] IN osq c1 c2 a b l) \/
            (vector[&33 / &20; &33 / &20] IN osq c1 c2 a b l /\
             vector[&47 / &20; &33 / &20] IN osq c1 c2 a b l) \/
            (vector[&33 / &20; &47 / &20] IN osq c1 c2 a b l /\
             vector[&47 / &20; &47 / &20] IN osq c1 c2 a b l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SW_RULE (SPECL [`c2:real`; `c1:real`; `b:real`; `a:real`; `l:real`] AVOIDF_FORCES_PAIR)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `a * a + b * b = &1` THEN REAL_ARITH_TAC;
    REWRITE_TAC[]]);;
let GENERAL_WALL = prove
 (`forall X Y c s l w bb d.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= Y /\ &0 <= X /\ X <= w /\ &0 <= w /\ w <= &1 /\
        Y <= d /\ &3 / &4 <= bb /\ bb <= d /\ d <= &1 /\
        w * w + (d - bb) * (d - bb) <= &1 /\
        c * c * bb + s * s * d + w * c * s <= c + s
        ==> vector[&0; bb] IN osq X Y c s l \/ vector[w; d] IN osq X Y c s l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN FRAME_FACTS_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c + s - &3 / &2`; SQ_NONNEG `s - &1`;
                  SQ_NONNEG `c - &1`; SQ_NONNEG `c:real`; SQ_NONNEG `s:real`]
   [`c + s <= &3 / &2`; `&0 <= (c * s) * (&1 - w)`;
    `s * (bb - Y) < l / &2`; `c * (d - Y) < l / &2`;
    `--(l / &2) < s * X + c * (bb - Y)`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `w:real`; `d - bb`] CS_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ARITH `abs x <= &1 <=> -- &1 <= x /\ x <= &1`] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c:real`; SQ_NONNEG `s:real`;
                  SQ_NONNEG `c - &3 / &5 * s`]
   [`&0 <= (s * s) * (&1 / &4 - (d - bb))`;
    `&0 <= (&3 / &2 - (c + s)) * (c + s - &1)`;
    `c * s + &1 / &4 * s * s <= (c + s) / &2`] THEN
  DISJ_NLIN_TAC [SQ_NONNEG `c - s`]);;
let NB_SMALL = prove
 (`forall w bb d c s. w <= &413 / &500 /\ bb <= &1 /\ d <= &1 /\
               &0 <= c /\ &0 <= s /\ c * c + s * s = &1
               ==> c * c * bb + s * s * d + w * c * s <= c + s`,
  REPEAT STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s`; SQ_NONNEG `c + s - &99 / &70`; SQ_NONNEG `c + s - &1`;
                  SQ_NONNEG `c:real`; SQ_NONNEG `s:real`]
   [`&1 <= c + s`; `c + s <= &99 / &70`; `&0 <= c * s`; `&0 <= (c * s) * (&413 / &500 - w)`;
    `&0 <= (c * c) * (&1 - bb)`; `&0 <= (s * s) * (&1 - d)`;
    `&0 <= &1 - &413 / &1000 * (c + s + &1)`;
    `&0 <= (&1 - &413 / &1000 * (c + s + &1)) * (c + s - &1)`] THEN
  NLIN_TAC []);;

let GEN_SEGMENT_HIT = prove
 (`forall c1 c2 a b l x0 x1 bb d.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        x0 <= c1 /\ c1 <= x1 /\ c2 <= d /\ x1 - x0 <= &1 /\
        &3 / &4 <= bb /\ bb <= d /\ d <= &1 /\
        (x1 - x0) * (x1 - x0) + (d - bb) * (d - bb) <= &1 /\
        (forall c s. &0 <= c /\ &0 <= s /\ c * c + s * s = &1
               ==> c * c * bb + s * s * d + (x1 - x0) * c * s <= c + s)
        ==> vector[x0; bb] IN osq c1 c2 a b l \/ vector[x1; d] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FRAME_INTRO_TAC THEN
  MP_TAC(SPECL [`c1 - x0`; `c2:real`; `c:real`; `s:real`; `l:real`; `x1 - x0`;
                `bb:real`; `d:real`] GENERAL_WALL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_OSQ] THEN
  MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
  MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN BINOP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let GEN_SEGMENT_DESC = prove
 (`forall c1 c2 a b l x0 x1 bb d.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l /\
        x0 <= c1 /\ c1 <= x1 /\ c2 <= bb /\ x1 - x0 <= &1 /\
        &3 / &4 <= d /\ d <= bb /\ bb <= &1 /\
        (x1 - x0) * (x1 - x0) + (bb - d) * (bb - d) <= &1 /\
        (forall c s. &0 <= c /\ &0 <= s /\ c * c + s * s = &1
               ==> c * c * d + s * s * bb + (x1 - x0) * c * s <= c + s)
        ==> vector[x0; bb] IN osq c1 c2 a b l \/ vector[x1; d] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&4 - c1`; `c2:real`; `b:real`; `a:real`; `l:real`;
                `&4 - x1`; `&4 - x0`; `d:real`; `bb:real`] GEN_SEGMENT_HIT) THEN
  ONCE_REWRITE_TAC[OSQ_RX_PT; OWALLS_RX] THEN
  REWRITE_TAC[REAL_ARITH `&4 - (&4 - x) = x`] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(UNDISCH_TAC `a * a + b * b = &1` THEN REAL_ARITH_TAC) THEN
    TRY ASM_REAL_ARITH_TAC THEN
    REWRITE_TAC[REAL_ARITH `(&4 - x0) - (&4 - x1) = x1 - x0`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_ARITH `(x:real) * x = (--x) * (--x)`];
    MESON_TAC[]]);;

let OSQ_CENTER_DIST = prove
 (`forall x y c1 c2 a b l. a * a + b * b = &1 /\ vector[x; y] IN osq c1 c2 a b l
     ==> (x - c1) * (x - c1) + (y - c2) * (y - c2) < l * l / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_OSQ; ABS_LT_BANDS] THEN STRIP_TAC THEN
  ABBREV_TAC `u = (x - c1) * a + (y - c2) * b` THEN
  ABBREV_TAC `v = (y - c2) * a - (x - c1) * b` THEN
  SUBGOAL_THEN `(x - c1) * (x - c1) + (y - c2) * (y - c2) = u * u + v * v` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN UNDISCH_TAC `a * a + b * b = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC []);;

let CORNER_OWNER_CENTER = prove
 (`forall c1 c2 a b l. &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\
     vector[&1; &457 / &500] IN osq c1 c2 a b l ==> c1 <= &2 /\ c2 <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1`; `&457 / &500`; `c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`]
         OSQ_CENTER_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `&457 / &500 - c2`; SQ_NONNEG `&1 - c1`]);;
