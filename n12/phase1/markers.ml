(* ========================================================================= *)
(* Port of Jatloe et al.'s s(12) proof, layer 1: open squares and the 16     *)
(* markers.  Every open square of side > 1 whose closure lies in [0,4]^2     *)
(* contains one of the 16 marker points (Jatloe's marker_nonavoidance).      *)
(* ========================================================================= *)

needs "n12/bounds/cover_lib.ml";;

(* An open square: centre (c1,c2), unit direction (a,b), side l.             *)

let osq = new_definition
 `osq c1 c2 a b l =
    {z:real^2 | abs((z$1 - c1) * a + (z$2 - c2) * b) < l / &2 /\
                abs((z$2 - c2) * a - (z$1 - c1) * b) < l / &2}`;;

(* The centre constraints for the closure to lie in [0,4]^2.               *)

let owalls = new_definition
 `owalls c1 c2 a b l <=>
    (abs a + abs b) * l / &2 <= c1 /\ c1 <= &4 - (abs a + abs b) * l / &2 /\
    (abs a + abs b) * l / &2 <= c2 /\ c2 <= &4 - (abs a + abs b) * l / &2`;;

let OSQ_ROT = prove
 (`forall c1 c2 a b l. osq c1 c2 (--b) a l = osq c1 c2 a b l`,
  REWRITE_TAC[osq; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let OSQ_NEG = prove
 (`forall c1 c2 a b l. osq c1 c2 (--a) (--b) l = osq c1 c2 a b l`,
  REWRITE_TAC[osq; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The markers.                                                              *)
(* ------------------------------------------------------------------------- *)

let marker = new_definition
 `marker k =
    if k = 0 then vector[&1; &457 / &500]:real^2
    else if k = 1 then vector[&457 / &500; &1]
    else if k = 2 then vector[&3; &457 / &500]
    else if k = 3 then vector[&1543 / &500; &1]
    else if k = 4 then vector[&3; &1543 / &500]
    else if k = 5 then vector[&1543 / &500; &3]
    else if k = 6 then vector[&1; &1543 / &500]
    else if k = 7 then vector[&457 / &500; &3]
    else if k = 8 then vector[&33 / &20; &33 / &20]
    else if k = 9 then vector[&47 / &20; &33 / &20]
    else if k = 10 then vector[&47 / &20; &47 / &20]
    else if k = 11 then vector[&33 / &20; &47 / &20]
    else if k = 12 then vector[&457 / &500; &2]
    else if k = 13 then vector[&2; &457 / &500]
    else if k = 14 then vector[&1543 / &500; &2]
    else vector[&2; &1543 / &500]`;;

let MARKER_CONV =
  REWRITE_CONV[marker] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[];;

(* ------------------------------------------------------------------------- *)
(* Basic facts about a unit direction with nonnegative components.           *)
(* ------------------------------------------------------------------------- *)

let DIR_FACTS = prove
 (`forall a b. &0 <= a /\ &0 <= b /\ a * a + b * b = &1
         ==> a <= &1 /\ b <= &1 /\ &1 <= a + b /\ a + b <= &99 / &70 /\
             a * b = ((a + b) * (a + b) - &1) / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= a * b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SQ_LE_IMP_LIB THEN MP_TAC(SPEC `b:real` REAL_LE_SQUARE) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SQ_LE_IMP_LIB THEN MP_TAC(SPEC `a:real` REAL_LE_SQUARE) THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SQ_LE_IMP_LIB THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SQ_LE_IMP_LIB THEN MP_TAC(SPEC `a - b:real` REAL_LE_SQUARE) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The triangle lemma (Jatloe: centered_triangle_cover).                     *)
(* ------------------------------------------------------------------------- *)

let WPOS3 = prove
 (`forall w0 w1 w2 x0 x1 x2.
        &0 <= w0 /\ &0 <= w1 /\ &0 <= w2 /\ w0 + w1 + w2 = &1 /\
        &0 < x0 /\ &0 < x1 /\ &0 < x2
        ==> &0 < w0 * x0 + w1 * x1 + w2 * x2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`w0:real`; `x0:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`w1:real`; `x1:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`w2:real`; `x2:real`] REAL_LE_MUL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `&0 < w0` THENL
   [MP_TAC(SPECL [`w0:real`; `x0:real`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < w1` THENL
   [MP_TAC(SPECL [`w1:real`; `x1:real`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`w2:real`; `x2:real`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC);;

let SEP_DIR = prove
 (`forall w0 w1 w2 u0 u1 u2 v0 v1 v2 c s.
        &0 <= w0 /\ &0 <= w1 /\ &0 <= w2 /\ w0 + w1 + w2 = &1 /\
        w0 * u0 + w1 * u1 + w2 * u2 = &0 /\ w0 * v0 + w1 * v1 + w2 * v2 = &0
        ==> ~(&0 < c * u0 + s * v0 /\ &0 < c * u1 + s * v1 /\ &0 < c * u2 + s * v2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w0:real`; `w1:real`; `w2:real`; `c * u0 + s * v0`;
                `c * u1 + s * v1`; `c * u2 + s * v2`] WPOS3) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH
   `w0 * (c * u0 + s * v0) + w1 * (c * u1 + s * v1) + w2 * (c * u2 + s * v2) =
    c * (w0 * u0 + w1 * u1 + w2 * u2) + s * (w0 * v0 + w1 * v1 + w2 * v2)`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CENTERED_TRIANGLE = prove
 (`forall l u0 v0 u1 v1 u2 v2 w0 w1 w2.
        &1 < l /\ &0 <= w0 /\ &0 <= w1 /\ &0 <= w2 /\ w0 + w1 + w2 = &1 /\
        w0 * u0 + w1 * u1 + w2 * u2 = &0 /\ w0 * v0 + w1 * v1 + w2 * v2 = &0 /\
        abs(u0 - u1) <= &1 /\ abs(u0 - u2) <= &1 /\ abs(u1 - u2) <= &1 /\
        abs(v0 - v1) <= &1 /\ abs(v0 - v2) <= &1 /\ abs(v1 - v2) <= &1
        ==> (abs u0 < l / &2 /\ abs v0 < l / &2) \/
            (abs u1 < l / &2 /\ abs v1 < l / &2) \/
            (abs u2 < l / &2 /\ abs v2 < l / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let seps = map (fun (c,s) ->
    SPECL [`w0:real`; `w1:real`; `w2:real`; `u0:real`; `u1:real`; `u2:real`;
           `v0:real`; `v1:real`; `v2:real`; c; s] SEP_DIR)
   [`&1`,`&0`; `-- &1`,`&0`; `&0`,`&1`; `&0`,`-- &1`;
    `&1`,`&1`; `&1`,`-- &1`; `-- &1`,`&1`; `-- &1`,`-- &1`] in
  MAP_EVERY (fun th -> MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) seps THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    exists (fun v -> free_in v (concl th)) [`w0:real`; `w1:real`; `w2:real`]))) THEN
  GEN_REWRITE_TAC I [TAUT `a \/ b \/ c <=> ~a ==> ~b ==> ~c ==> false`] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o
    REWRITE_RULE[DE_MORGAN_THM; REAL_NOT_LT;
                 REAL_ARITH `h <= abs x <=> h <= x \/ x <= --h`])) THEN
  POP_ASSUM_LIST(fun ths ->
    let seps' = filter (fun th -> is_neg(concl th)) ths
    and rest = filter (fun th -> not(is_neg(concl th))) ths in
    MAP_EVERY ASSUME_TAC rest THEN
    FIRST (ASM_REAL_ARITH_TAC ::
           map (fun th -> MP_TAC th THEN ASM_REAL_ARITH_TAC) seps')));;

let CS_BOUND = prove
 (`forall a b dx dy. a * a + b * b = &1 /\ dx * dx + dy * dy <= &1
               ==> abs(dx * a + dy * b) <= &1 /\ abs(dy * a - dx * b) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(dx * a + dy * b) * (dx * a + dy * b) +
                (dy * a - dx * b) * (dy * a - dx * b) <= &1` MP_TAC THENL
   [SUBGOAL_THEN `(dx * a + dy * b) * (dx * a + dy * b) +
                  (dy * a - dx * b) * (dy * a - dx * b) =
                  (dx * dx + dy * dy) * (a * a + b * b)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_REWRITE_TAC[REAL_MUL_RID]];
    ALL_TAC] THEN
  MP_TAC(SPEC `dx * a + dy * b` REAL_LE_SQUARE) THEN
  MP_TAC(SPEC `dy * a - dx * b` REAL_LE_SQUARE) THEN
  REPEAT DISCH_TAC THEN CONJ_TAC THEN
  REWRITE_TAC[REAL_ARITH `abs x <= &1 <=> abs x <= abs(&1)`; REAL_LE_SQUARE_ABS] THEN
  ASM_REAL_ARITH_TAC);;

let TRIANGLE_NONAVOID = prove
 (`forall c1 c2 a b l x0 y0 x1 y1 x2 y2 w0 w1 w2.
        &1 < l /\ a * a + b * b = &1 /\
        &0 <= w0 /\ &0 <= w1 /\ &0 <= w2 /\ w0 + w1 + w2 = &1 /\
        w0 * x0 + w1 * x1 + w2 * x2 = c1 /\ w0 * y0 + w1 * y1 + w2 * y2 = c2 /\
        (x0 - x1) * (x0 - x1) + (y0 - y1) * (y0 - y1) <= &1 /\
        (x0 - x2) * (x0 - x2) + (y0 - y2) * (y0 - y2) <= &1 /\
        (x1 - x2) * (x1 - x2) + (y1 - y2) * (y1 - y2) <= &1
        ==> vector[x0; y0] IN osq c1 c2 a b l \/
            vector[x1; y1] IN osq c1 c2 a b l \/
            vector[x2; y2] IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN
  MATCH_MP_TAC CENTERED_TRIANGLE THEN
  MAP_EVERY EXISTS_TAC [`w0:real`; `w1:real`; `w2:real`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `w0 * x0 + w1 * x1 + w2 * x2 = c1` THEN
    UNDISCH_TAC `w0 * y0 + w1 * y1 + w2 * y2 = c2` THEN
    UNDISCH_TAC `w0 + w1 + w2 = &1` THEN CONV_TAC REAL_RING;
    UNDISCH_TAC `w0 * x0 + w1 * x1 + w2 * x2 = c1` THEN
    UNDISCH_TAC `w0 * y0 + w1 * y1 + w2 * y2 = c2` THEN
    UNDISCH_TAC `w0 + w1 + w2 = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  FIRST (map (fun (p,q) ->
    let dx = mk_binop `(-):real->real->real` (mk_var("x"^p,`:real`)) (mk_var("x"^q,`:real`))
    and dy = mk_binop `(-):real->real->real` (mk_var("y"^p,`:real`)) (mk_var("y"^q,`:real`)) in
    MP_TAC(SPECL [`a:real`; `b:real`; dx; dy] CS_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC) ["0","1"; "0","2"; "1","2"]));;

(* ------------------------------------------------------------------------- *)
(* The corner lemma and the wall-row lemma (Jatloe: corner_frame_point,      *)
(* wall_row_frame), for a direction (c,s) with c,s >= 0.                     *)
(* ------------------------------------------------------------------------- *)

let CORNER_POINT = prove
 (`forall X Y c s l bb.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= X /\ l * (c + s) / &2 <= Y /\ X <= &1 /\ Y <= &1 /\
        &9 / &10 <= bb /\ bb <= &1
        ==> vector[bb; &1] IN osq X Y c s l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] DIR_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN
  SUBGOAL_THEN `&0 < (l - &1) * (&1 + (c + s) * (c + s)) /\
                &0 <= (l - &1) * c * (c + s) /\ &0 <= (l - &1) * s * (c + s)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LT_MUL) THEN
    TRY(MP_TAC(SPEC `c + s:real` REAL_LE_SQUARE)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun (p,x,lo,hi) ->
    MP_TAC(SPECL [p; x; lo; hi] BILIN) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC])
   [`c:real`, `bb - X`, `bb - &1`, `&1 - l * (c + s) / &2`;
    `s:real`, `bb - X`, `bb - &1`, `&1 - l * (c + s) / &2`;
    `c:real`, `&1 - Y`, `&0`, `&1 - l * (c + s) / &2`;
    `s:real`, `&1 - Y`, `&0`, `&1 - l * (c + s) / &2`;
    `c:real`, `bb:real`, `&9 / &10`, `&1`;
    `s:real`, `bb:real`, `&9 / &10`, `&1`] THEN
  SUBGOAL_THEN `&0 <= (&1 - c) * (&1 - c) + s * (c - &1 / &5)` ASSUME_TAC THENL
   [ASM_CASES_TAC `&1 / &5 <= c` THENL
     [MP_TAC(SPECL [`s:real`; `c - &1 / &5`] REAL_LE_MUL) THEN
      MP_TAC(SPEC `&1 - c` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`s:real`; `&1`; `&1 / &5 - c`; `&1 / &5 - c`] REAL_LE_MUL2) THEN
      MP_TAC(SPECL [`&4 / &5`; `&1 - c`; `&4 / &5`; `&1 - c`] REAL_LE_MUL2) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - s) * (&1 - s) + s * c` ASSUME_TAC THENL
   [MP_TAC(SPECL [`s:real`; `c:real`] REAL_LE_MUL) THEN
    MP_TAC(SPEC `&1 - s` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `c + s - &1` REAL_LE_SQUARE) THEN
  ASM_REAL_ARITH_TAC);;

let HAS_ASM t = FIRST_ASSUM(fun th -> if aconv (concl th) t then ALL_TAC else NO_TAC);;

let WALL_ROW_POINT = prove
 (`forall X Y c s l bb.
        &1 < l /\ &0 <= c /\ &0 <= s /\ c * c + s * s = &1 /\
        l * (c + s) / &2 <= Y /\ &0 <= X /\ X <= &1 /\ Y <= bb /\ bb <= &457 / &500
        ==> vector[&0; bb] IN osq X Y c s l \/ vector[&1; bb] IN osq X Y c s l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] DIR_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN
  ABBREV_TAC `d = bb - Y` THEN
  SUBGOAL_THEN `&0 <= d /\ d <= &457 / &500 - l * (c + s) / &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (l - &1) * (c + s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d * c * c + d * s * s = d` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `d * c * c + d * s * s = d * (c * c + s * s)`] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&99 / &70 - (c + s)) * ((c + s) + &29 / &70) /\
                &0 <= (&99 / &70 - (c + s)) * ((c + s) - &41 / &70)` STRIP_ASSUME_TAC
  THENL [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (p,x,lo,hi) ->
    MP_TAC(SPECL [p; x; lo; hi] BILIN) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; STRIP_TAC])
   [`c:real`, `X:real`, `&0`, `&1`; `s:real`, `X:real`, `&0`, `&1`;
    `d:real`, `c:real`, `&0`, `&1`; `d:real`, `s:real`, `&0`, `&1`] THEN
  ABBREV_TAC `U0 = (&0 - X) * c + d * s` THEN
  ABBREV_TAC `V0 = d * c - (&0 - X) * s` THEN
  ABBREV_TAC `U1 = (&1 - X) * c + d * s` THEN
  ABBREV_TAC `V1 = d * c - (&1 - X) * s` THEN
  SUBGOAL_THEN `U0 < l / &2 /\ --(l / &2) < V0 /\ --(l / &2) < U1 /\ V1 < l / &2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U0"; "V0"; "U1"; "V1"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `U0 < h /\ --h < V0 /\ --h < U1 /\ V1 < h /\
    ((--h < U0 /\ V0 < h) \/ (U1 < h /\ --h < V1))
    ==> (abs U0 < h /\ abs V0 < h) \/ (abs U1 < h /\ abs V1 < h)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISJ_CASES_TAC(REAL_ARITH `U0 <= --(l / &2) \/ --(l / &2) < U0`) THEN
  DISJ_CASES_TAC(REAL_ARITH `l / &2 <= V0 \/ V0 < l / &2`) THEN
  DISJ_CASES_TAC(REAL_ARITH `l / &2 <= U1 \/ U1 < l / &2`) THEN
  DISJ_CASES_TAC(REAL_ARITH `V1 <= --(l / &2) \/ --(l / &2) < V1`) THEN
  TRY(DISJ1_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  TRY(DISJ2_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC THEN NO_TAC) THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN
  FIRST
   [(* U0 <= -h, U1 >= h *)
    HAS_ASM `U0 <= --(l / &2)` THEN HAS_ASM `l / &2 <= U1` THEN
    SUBGOAL_THEN `U1 - U0 = c` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["U0"; "U1"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `U0 <= --(l / &2)` THEN UNDISCH_TAC `l / &2 <= U1` THEN
    UNDISCH_TAC `c <= &1` THEN UNDISCH_TAC `&1 < l` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC;
    (* V0 >= h, V1 <= -h *)
    HAS_ASM `l / &2 <= V0` THEN HAS_ASM `V1 <= --(l / &2)` THEN
    SUBGOAL_THEN `V0 - V1 = s` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["V0"; "V1"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `l / &2 <= V0` THEN UNDISCH_TAC `V1 <= --(l / &2)` THEN
    UNDISCH_TAC `s <= &1` THEN UNDISCH_TAC `&1 < l` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC;
    (* U0 <= -h, V1 <= -h *)
    HAS_ASM `U0 <= --(l / &2)` THEN HAS_ASM `V1 <= --(l / &2)` THEN
    MP_TAC(SPECL [`s:real`; `--(l / &2) - U0`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`c:real`; `--(l / &2) - V1`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `s * U0 + c * V1 = d - c * s` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["U0"; "V1"] THEN
      UNDISCH_TAC `d * c * c + d * s * s = d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c * s = ((c + s) * (c + s) - &1) / &2` THEN
    UNDISCH_TAC `&0 <= (&99 / &70 - (c + s)) * ((c + s) + &29 / &70)` THEN
    UNDISCH_TAC `&0 < (l - &1) * (c + s)` THEN UNDISCH_TAC `&0 <= d` THEN
    UNDISCH_TAC `&0 <= s * (--(l / &2) - U0)` THEN
    UNDISCH_TAC `&0 <= c * (--(l / &2) - V1)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC;
    (* V0 >= h, U1 >= h *)
    HAS_ASM `l / &2 <= V0` THEN HAS_ASM `l / &2 <= U1` THEN
    MP_TAC(SPECL [`c:real`; `V0 - l / &2`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`s:real`; `U1 - l / &2`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `c * V0 + s * U1 = d + c * s` MP_TAC THENL
     [MAP_EVERY EXPAND_TAC ["V0"; "U1"] THEN
      UNDISCH_TAC `d * c * c + d * s * s = d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `c * s = ((c + s) * (c + s) - &1) / &2` THEN
    UNDISCH_TAC `&0 <= (&99 / &70 - (c + s)) * ((c + s) - &41 / &70)` THEN
    UNDISCH_TAC `&0 < (l - &1) * (c + s)` THEN
    UNDISCH_TAC `d <= &457 / &500 - l * (c + s) / &2` THEN
    UNDISCH_TAC `&0 <= c * (V0 - l / &2)` THEN
    UNDISCH_TAC `&0 <= s * (U1 - l / &2)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Non-avoidance on the fundamental region c1 <= c2 <= 2.                    *)
(* ------------------------------------------------------------------------- *)

let IN_OSQ = prove
 (`forall x y c1 c2 a b l. vector[x; y] IN osq c1 c2 a b l <=>
        abs((x - c1) * a + (y - c2) * b) < l / &2 /\
        abs((y - c2) * a - (x - c1) * b) < l / &2`,
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2]);;

let MARKER_EXPLICIT = prove
 (`marker 0 = vector[&1; &457 / &500] /\ marker 1 = vector[&457 / &500; &1] /\
   marker 2 = vector[&3; &457 / &500] /\ marker 3 = vector[&1543 / &500; &1] /\
   marker 4 = vector[&3; &1543 / &500] /\ marker 5 = vector[&1543 / &500; &3] /\
   marker 6 = vector[&1; &1543 / &500] /\ marker 7 = vector[&457 / &500; &3] /\
   marker 8 = vector[&33 / &20; &33 / &20] /\ marker 9 = vector[&47 / &20; &33 / &20] /\
   marker 10 = vector[&47 / &20; &47 / &20] /\ marker 11 = vector[&33 / &20; &47 / &20] /\
   marker 12 = vector[&457 / &500; &2] /\ marker 13 = vector[&2; &457 / &500] /\
   marker 14 = vector[&1543 / &500; &2] /\ marker 15 = vector[&2; &1543 / &500]`,
  REWRITE_TAC[marker] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let marker_xy i =
  let v = rhs(concl(REWRITE_CONV[MARKER_EXPLICIT] (mk_comb(`marker`, mk_small_numeral i)))) in
  match dest_list(rand v) with [x;y] -> x,y | _ -> failwith "marker_xy";;

let TRI_TAC (i0,i1,i2) (w0,w1,w2) =
  let (x0,y0) = marker_xy i0 and (x1,y1) = marker_xy i1 and (x2,y2) = marker_xy i2 in
  MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`;
                x0;y0;x1;y1;x2;y2;w0;w1;w2] TRIANGLE_NONAVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC (mk_small_numeral i0); EXISTS_TAC (mk_small_numeral i1);
    EXISTS_TAC (mk_small_numeral i2)] THEN
  ASM_REWRITE_TAC[MARKER_EXPLICIT] THEN CONV_TAC NUM_REDUCE_CONV;;

let FUNDAMENTAL_NONAVOID = prove
 (`forall c1 c2 a b l.
        &1 < l /\ &0 <= a /\ &0 <= b /\ a * a + b * b = &1 /\
        l * (a + b) / &2 <= c1 /\ l * (a + b) / &2 <= c2 /\
        c1 <= c2 /\ c2 <= &2
        ==> exists k. k < 16 /\ marker k IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `c2 <= &1` THENL
   [EXISTS_TAC `1` THEN REWRITE_TAC[MARKER_EXPLICIT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC CORNER_POINT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `c1 <= &457 / &500` THENL
   [MP_TAC(SPECL [`c2 - &1`; `c1:real`; `b:real`; `a:real`; `l:real`; `&457 / &500`]
                 WALL_ROW_POINT) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_OSQ] THEN STRIP_TAC THENL
     [EXISTS_TAC `1`; EXISTS_TAC `12`] THEN
    REWRITE_TAC[MARKER_EXPLICIT; IN_OSQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&33 / &20 <= c1` THENL
   [TRI_TAC (8,9,11) (`(-- &10 / &7) * c1 + (-- &10 / &7) * c2 + &40 / &7`,
                      `(&10 / &7) * c1 - &33 / &14`, `(&10 / &7) * c2 - &33 / &14`);
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (&125 / &184) * c1 + (&10 / &7) * c2 + (-- &17919 / &5152)` THENL
   [TRI_TAC (12,8,11) (`(-- &125 / &92) * c1 + &825 / &368`,
                       `(&125 / &184) * c1 + (-- &10 / &7) * c2 + &11521 / &5152`,
                       `(&125 / &184) * c1 + (&10 / &7) * c2 + (-- &17919 / &5152)`);
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (-- &325 / &368) * c1 + c2 + (-- &1419 / &7360)` THENL
   [TRI_TAC (1,12,8) (`(-- &175 / &368) * c1 - c2 + &17919 / &7360`,
                      `(-- &325 / &368) * c1 + c2 + (-- &1419 / &7360)`,
                      `(&125 / &92) * c1 + (-- &457 / &368)`);
    TRI_TAC (0,1,8) (`(&162500 / &29799) * c1 + (-- &184000 / &29799) * c2 + &25 / &21`,
                     `(-- &184000 / &29799) * c1 + (&162500 / &29799) * c2 + &25 / &21`,
                     `(&500 / &693) * c1 + (&500 / &693) * c2 + (-- &29 / &21)`)]);;

(* ------------------------------------------------------------------------- *)
(* Symmetries of the container permute the markers.                          *)
(* ------------------------------------------------------------------------- *)

let LT16_CASES = prove
 (`forall k. k < 16 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/
                  k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/
                  k = 14 \/ k = 15`,
  ARITH_TAC);;

let VEC2_EQ_LOCAL = prove
 (`forall x1 x2 y1 y2. (vector[x1; x2]:real^2) = vector[y1; y2] <=> x1 = y1 /\ x2 = y2`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let MARKER_PERM_TAC perm =
  REWRITE_TAC[LT16_CASES] THEN GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
  (map (fun j -> EXISTS_TAC (mk_small_numeral j) THEN
      REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2; VEC2_EQ_LOCAL] THEN
      CONV_TAC(DEPTH_CONV NUM_LT_CONV THENC REAL_RAT_REDUCE_CONV))
    perm);;

let MARKER_RX = prove
 (`forall k. k < 16 ==> exists j. j < 16 /\ marker j = vector[&4 - marker k$1; marker k$2]`,
  MARKER_PERM_TAC [2;3;0;1;6;7;4;5;9;8;11;10;14;13;12;15]);;

let MARKER_RY = prove
 (`forall k. k < 16 ==> exists j. j < 16 /\ marker j = vector[marker k$1; &4 - marker k$2]`,
  MARKER_PERM_TAC [6;7;4;5;2;3;0;1;11;10;9;8;12;15;14;13]);;

let MARKER_SW = prove
 (`forall k. k < 16 ==> exists j. j < 16 /\ marker j = vector[marker k$2; marker k$1]`,
  MARKER_PERM_TAC [1;0;7;6;5;4;3;2;8;11;10;9;13;12;15;14]);;

let OSQ_RX = prove
 (`forall z c1 c2 a b l. z IN osq c1 c2 a b l <=>
                   vector[&4 - z$1; z$2] IN osq (&4 - c1) c2 b a l`,
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC);;

let OSQ_RY = prove
 (`forall z c1 c2 a b l. z IN osq c1 c2 a b l <=>
                   vector[z$1; &4 - z$2] IN osq c1 (&4 - c2) b a l`,
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC);;

let OSQ_SW = prove
 (`forall z c1 c2 a b l. z IN osq c1 c2 a b l <=>
                   vector[z$2; z$1] IN osq c2 c1 b a l`,
  REWRITE_TAC[osq; IN_ELIM_THM; VECTOR_2] THEN REAL_ARITH_TAC);;

let VEC2_ETA = prove
 (`forall z:real^2. vector[z$1; z$2] = z`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let REFLECT_STEP_TAC lemma mlemma (cx,cy) =
  FIRST_X_ASSUM(MP_TAC o SPECL [cx; cy; `b:real`; `a:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `k:num` mlemma) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [lemma] THEN ASM_REWRITE_TAC[VECTOR_2] THEN
  REWRITE_TAC[REAL_ARITH `&4 - (&4 - x) = x`; VEC2_ETA] THEN
  ASM_REWRITE_TAC[];;

let NONNEG_NONAVOID = prove
 (`forall c1 c2 a b l.
        &1 < l /\ &0 <= a /\ &0 <= b /\ a * a + b * b = &1 /\
        l * (a + b) / &2 <= c1 /\ c1 <= &4 - l * (a + b) / &2 /\
        l * (a + b) / &2 <= c2 /\ c2 <= &4 - l * (a + b) / &2
        ==> exists k. k < 16 /\ marker k IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    SUBGOAL_THEN
     `forall c1 c2 a b. &0 <= a /\ &0 <= b /\ a * a + b * b = &1 /\
                  l * (a + b) / &2 <= c1 /\ c1 <= &4 - l * (a + b) / &2 /\
                  l * (a + b) / &2 <= c2 /\ c2 <= &4 - l * (a + b) / &2 /\
                  c1 <= c2 /\ c2 <= &2
                  ==> exists k. k < 16 /\ marker k IN osq c1 c2 a b l`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNDAMENTAL_NONAVOID THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC th) THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `forall c1 c2 a b. &0 <= a /\ &0 <= b /\ a * a + b * b = &1 /\
                l * (a + b) / &2 <= c1 /\ c1 <= &4 - l * (a + b) / &2 /\
                l * (a + b) / &2 <= c2 /\ c2 <= &4 - l * (a + b) / &2 /\
                c1 <= &2 /\ c2 <= &2
                ==> exists k. k < 16 /\ marker k IN osq c1 c2 a b l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `c1 <= c2` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REFLECT_STEP_TAC OSQ_SW MARKER_SW (`c2:real`, `c1:real`);
    POP_ASSUM_LIST(MP_TAC o el 0) THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `forall c1 c2 a b. &0 <= a /\ &0 <= b /\ a * a + b * b = &1 /\
                l * (a + b) / &2 <= c1 /\ c1 <= &4 - l * (a + b) / &2 /\
                l * (a + b) / &2 <= c2 /\ c2 <= &4 - l * (a + b) / &2 /\
                c2 <= &2
                ==> exists k. k < 16 /\ marker k IN osq c1 c2 a b l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `c1 <= &2` THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REFLECT_STEP_TAC OSQ_RX MARKER_RX (`&4 - c1`, `c2:real`);
    POP_ASSUM_LIST(MP_TAC o el 0) THEN DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c2 <= &2` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REFLECT_STEP_TAC OSQ_RY MARKER_RY (`c1:real`, `&4 - c2`));;

(* Jatloe's marker_nonavoidance, for any orientation.                        *)

let OSQ_ROT3 = prove
 (`forall c1 c2 a b l. osq c1 c2 b (--a) l = osq c1 c2 a b l`,
  REWRITE_TAC[osq; EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let NORM_CASE_TAC (ea,eb) (a',b') =
  SUBGOAL_THEN (mk_conj(mk_eq(`abs a`,ea), mk_eq(`abs b`,eb)))
   (CONJUNCTS_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `c2:real`; a'; b'; `l:real`] NONNEG_NONAVOID) THEN
  REWRITE_TAC[OSQ_ROT; OSQ_NEG; OSQ_ROT3] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `a * a + b * b = &1` THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];;

let MARKER_NONAVOID = prove
 (`forall c1 c2 a b l.
        &1 < l /\ a * a + b * b = &1 /\ owalls c1 c2 a b l
        ==> exists k. k < 16 /\ marker k IN osq c1 c2 a b l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[owalls] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= a` THEN ASM_CASES_TAC `&0 <= b` THENL
   [NORM_CASE_TAC (`a:real`,`b:real`) (`a:real`,`b:real`);
    NORM_CASE_TAC (`a:real`,`--b`) (`--b`,`a:real`);
    NORM_CASE_TAC (`--a`,`b:real`) (`b:real`,`--a`);
    NORM_CASE_TAC (`--a`,`--b`) (`--a`,`--b`)]);;
