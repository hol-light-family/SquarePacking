(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/SingletonMissingFan.lean           *)
(* (N12Compact.CommonCases.SingletonMissing).  The seven-triangle missing-   *)
(* corner fan: the fixed triangles rep0tri0..3 of S12.SingletonTriangles     *)
(* plus the excluded vertex (1,1).                                           *)
(*                                                                           *)
(* Translation: centerX q / centerY q are lcx / lcy; Marker = Fin 16 is      *)
(* i < 16 with the Phase-1 table `marker` (n12/phase1/markers.ml), and         *)
(* Owns q i is linside c s u v a (marker i$1) (marker i$2).                  *)
(* S12.triangle_nonavoidance is re-derived locally from the Phase-1          *)
(* TRIANGLE_NONAVOID (as in C1092WallCenterCover.ml).  The weight functions  *)
(* rep0triKwJ are written out as explicit linear forms.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

let CCSMF_OSQ_CENTRE = prove
 (`forall c s u v a x y. c * c + s * s = &1
     ==> (vector[x; y] IN osq (lcx c s u v a) (lcy c s u v a) c s a <=>
          linside c s u v a x y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[OSQ_LSQ] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c * lcx c s u v a + s * lcy c s u v a - a / &2 = u /\
                --s * lcx c s u v a + c * lcy c s u v a - a / &2 = v`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: S12.triangle_nonavoidance (source/S12/TriangleCover) *)
let CCSMF_TRIANGLE_NONAVOIDANCE = prove
 (`forall c s u v a x0 y0 x1 y1 x2 y2 w0 w1 w2.
     c * c + s * s = &1 /\ &1 < a /\
     &0 <= w0 /\ &0 <= w1 /\ &0 <= w2 /\ w0 + w1 + w2 = &1 /\
     w0 * x0 + w1 * x1 + w2 * x2 = lcx c s u v a /\
     w0 * y0 + w1 * y1 + w2 * y2 = lcy c s u v a /\
     (x0 - x1) pow 2 + (y0 - y1) pow 2 <= &1 /\
     (x0 - x2) pow 2 + (y0 - y2) pow 2 <= &1 /\
     (x1 - x2) pow 2 + (y1 - y2) pow 2 <= &1
     ==> linside c s u v a x0 y0 \/ linside c s u v a x1 y1 \/
         linside c s u v a x2 y2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lcx c s u v a`; `lcy c s u v a`; `c:real`; `s:real`; `a:real`;
                `x0:real`; `y0:real`; `x1:real`; `y1:real`; `x2:real`; `y2:real`;
                `w0:real`; `w1:real`; `w2:real`] TRIANGLE_NONAVOID) THEN
  ASM_SIMP_TAC[CCSMF_OSQ_CENTRE] THEN DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REWRITE_TAC[]);;

(* the foreign-marker hypothesis, instantiated at all markers i <> 0 *)
let CCSMF_HOUT =
  `forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)`;;

let CCSMF_MARKERS_TAC =
  FIRST_ASSUM(fun th ->
    if not (aconv (concl th) CCSMF_HOUT) then failwith "CCSMF_MARKERS_TAC" else
    MAP_EVERY (fun i ->
      let th1 = SPEC (mk_small_numeral i) th in
      let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
      ASSUME_TAC(REWRITE_RULE[MARKER_EXPLICIT; VECTOR_2] th2)) (1--15));;

(* apply triangle_nonavoidance with vertices / weights in the centre X Y *)
let CCSMF_TRI_TAC (x0,y0,x1,y1,x2,y2,w0,w1,w2) =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                x0; y0; x1; y1; x2; y2; w0; w1; w2] CCSMF_TRIANGLE_NONAVOIDANCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
    ASM_REWRITE_TAC[]];;

let CCSMF_ABBREV_TAC =
  CCSMF_MARKERS_TAC THEN
  ABBREV_TAC `X = lcx c s u v a` THEN ABBREV_TAC `Y = lcy c s u v a`;;

let CCSMF_INTRO_TAC = REPEAT GEN_TAC THEN STRIP_TAC THEN CCSMF_ABBREV_TAC;;

let ccsmf_tri0 w0 w1 w2 = (q"&33 / &20",q"&33 / &20",q"&457 / &500",q"&1",q"&457 / &500",q"&2",w0,w1,w2);;
let ccsmf_tri1 w0 w1 w2 = (q"&33 / &20",q"&33 / &20",q"&457 / &500",q"&2",q"&33 / &20",q"&47 / &20",w0,w1,w2);;
let ccsmf_tri2 w0 w1 w2 = (q"&33 / &20",q"&33 / &20",q"&33 / &20",q"&47 / &20",q"&47 / &20",q"&33 / &20",w0,w1,w2);;
let ccsmf_tri3 w0 w1 w2 = (q"&33 / &20",q"&33 / &20",q"&47 / &20",q"&33 / &20",q"&2",q"&457 / &500",w0,w1,w2);;
let ccsmf_rep0tri0 = ccsmf_tri0 `(&125 / &92) * X + &0 * Y + (-- &457 / &368)`
                    `(-- &175 / &368) * X + -- &1 * Y + (&17919 / &7360)`
                    `(-- &325 / &368) * X + &1 * Y + (-- &1419 / &7360)`;;
let ccsmf_rep0tri1 = ccsmf_tri1 `(&125 / &184) * X + (-- &10 / &7) * Y + (&11521 / &5152)`
                    `(-- &125 / &92) * X + &0 * Y + (&825 / &368)`
                    `(&125 / &184) * X + (&10 / &7) * Y + (-- &17919 / &5152)`;;
let ccsmf_rep0tri2 = ccsmf_tri2 `(-- &10 / &7) * X + (-- &10 / &7) * Y + (&40 / &7)`
                    `&0 * X + (&10 / &7) * Y + (-- &33 / &14)`
                    `(&10 / &7) * X + &0 * Y + (-- &33 / &14)`;;
let ccsmf_rep0tri3 = ccsmf_tri3 `(-- &10 / &7) * X + (&125 / &184) * Y + (&11521 / &5152)`
                    `(&10 / &7) * X + (&125 / &184) * Y + (-- &17919 / &5152)`
                    `&0 * X + (-- &125 / &92) * Y + (&825 / &368)`;;

(* Lean: lower_fan (private); the conclusions are rep0tri0w2 < 0 and       *)
(* rep0tri3w1 < 0 at the centre                                            *)
let CCSMF_LOWER_FAN = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      &457 / &500 <= lcx c s u v a /\ lcx c s u v a <= &2 /\
      &457 / &500 <= lcy c s u v a /\ lcy c s u v a <= &2 /\
      (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2))
      ==> (-- &325 / &368) * lcx c s u v a + &1 * lcy c s u v a + (-- &1419 / &7360) < &0 /\
          (&10 / &7) * lcx c s u v a + (&125 / &184) * lcy c s u v a + (-- &17919 / &5152) < &0`,
  CCSMF_INTRO_TAC THEN CONJ_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
   [ASM_CASES_TAC `X <= &33 / &20` THENL
     [ASM_CASES_TAC `&0 <= (-- &175 / &368) * X - Y + &17919 / &7360` THENL
       [CCSMF_TRI_TAC ccsmf_rep0tri0; CCSMF_TRI_TAC ccsmf_rep0tri1];
      CCSMF_TRI_TAC ccsmf_rep0tri2];
    ASM_CASES_TAC `Y <= &33 / &20` THENL
     [CCSMF_TRI_TAC ccsmf_rep0tri3;
      ASM_CASES_TAC `&33 / &20 <= X` THENL
       [CCSMF_TRI_TAC ccsmf_rep0tri2; CCSMF_TRI_TAC ccsmf_rep0tri1]]]);;

(* Lean: below_diagonal (private) *)
let CCSMF_BELOW_DIAGONAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &1 <= lcy c s u v a /\
      (-- &325 / &368) * lcx c s u v a + &1 * lcy c s u v a + (-- &1419 / &7360) < &0 /\
      (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)) /\
      ~linside c s u v a (&1) (&1)
      ==> lcy c s u v a < lcx c s u v a`,
  CCSMF_INTRO_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  CCSMF_TRI_TAC (`&1`,`&1`,`&457 / &500`,`&1`,`&33 / &20`,`&33 / &20`,
    `&1 - &20 / &13 * (Y - &1) - &500 / &43 * (Y - X)`,
    `&500 / &43 * (Y - X)`, `&20 / &13 * (Y - &1)`));;

(* Lean: target182_right_triangle (private) *)
let CCSMF_TARGET182_RIGHT_TRIANGLE = prove
 (`forall c s u v a wF wM.
      c * c + s * s = &1 /\ &1 < a /\
      (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)) /\
      &0 <= wF /\ &0 <= wM /\ &0 <= &1 - wF - wM /\
      (&1 - wF - wM) * (&91 / &50) + wF * &2 + wM * (&33 / &20) = lcx c s u v a /\
      (&1 - wF - wM) + wF * (&457 / &500) + wM * (&33 / &20) = lcy c s u v a
      ==> linside c s u v a (&91 / &50) (&1)`,
  CCSMF_INTRO_TAC THEN
  CCSMF_TRI_TAC (`&91 / &50`,`&1`,`&2`,`&457 / &500`,`&33 / &20`,`&33 / &20`,
    `&1 - wF - wM`,`wF:real`,`wM:real`));;

(* Lean: target196_right_triangle (private) *)
let CCSMF_TARGET196_RIGHT_TRIANGLE = prove
 (`forall c s u v a wF wM.
      c * c + s * s = &1 /\ &1 < a /\
      (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)) /\
      &0 <= wF /\ &0 <= wM /\ &0 <= &1 - wF - wM /\
      (&1 - wF - wM) * (&49 / &25) + wF * &2 + wM * (&33 / &20) = lcx c s u v a /\
      (&1 - wF - wM) * (&19 / &25) + wF * (&457 / &500) + wM * (&33 / &20) = lcy c s u v a
      ==> linside c s u v a (&49 / &25) (&19 / &25)`,
  CCSMF_INTRO_TAC THEN
  CCSMF_TRI_TAC (`&49 / &25`,`&19 / &25`,`&2`,`&457 / &500`,`&33 / &20`,`&33 / &20`,
    `&1 - wF - wM`,`wF:real`,`wM:real`));;

let CCSMF_TARGET_TAC th wf wm =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; wf; wm] th) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN RASM_ARITH_TAC;;

(* Lean: replacement182_left *)
let CCSMF_REPLACEMENT182_LEFT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      &457 / &500 <= lcx c s u v a /\ lcx c s u v a <= &91 / &50 /\
      &1 <= lcy c s u v a /\ lcy c s u v a <= &2 /\
      (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)) /\
      ~linside c s u v a (&1) (&1)
      ==> linside c s u v a (&91 / &50) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCSMF_LOWER_FAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCSMF_BELOW_DIAGONAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `&0 <= &1 - &50 / &41 * (lcx c s u v a - lcy c s u v a) -
                         &20 / &13 * (lcy c s u v a - &1)` THENL
   [CCSMF_ABBREV_TAC THEN
    CCSMF_TRI_TAC (`&91 / &50`,`&1`,`&33 / &20`,`&33 / &20`,`&1`,`&1`,
      `&50 / &41 * (X - Y)`, `&20 / &13 * (Y - &1)`,
      `&1 - &50 / &41 * (X - Y) - &20 / &13 * (Y - &1)`);
    CCSMF_TARGET_TAC CCSMF_TARGET182_RIGHT_TRIANGLE
      `&50000 / &5119 * (&13 / &20 * (lcx c s u v a - &91 / &50) + &17 / &100 * (lcy c s u v a - &1))`
      `&50000 / &5119 * (&9 / &50 * (lcy c s u v a - &1) + &43 / &500 * (lcx c s u v a - &91 / &50))`]);;

(* Lean: replacement182_right *)
let CCSMF_REPLACEMENT182_RIGHT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      &91 / &50 <= lcx c s u v a /\ lcx c s u v a <= &2 /\
      &1 <= lcy c s u v a /\ lcy c s u v a <= &2 /\
      (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2))
      ==> linside c s u v a (&91 / &50) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCSMF_LOWER_FAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  CCSMF_TARGET_TAC CCSMF_TARGET182_RIGHT_TRIANGLE
    `&50000 / &5119 * (&13 / &20 * (lcx c s u v a - &91 / &50) + &17 / &100 * (lcy c s u v a - &1))`
    `&50000 / &5119 * (&9 / &50 * (lcy c s u v a - &1) + &43 / &500 * (lcx c s u v a - &91 / &50))`);;

(* Lean: replacement196_left *)
let CCSMF_REPLACEMENT196_LEFT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      &457 / &500 <= lcx c s u v a /\ lcx c s u v a <= &49 / &25 /\
      &1 <= lcy c s u v a /\ lcy c s u v a <= &2 /\
      (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2)) /\
      ~linside c s u v a (&1) (&1)
      ==> linside c s u v a (&49 / &25) (&19 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCSMF_LOWER_FAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCSMF_BELOW_DIAGONAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `&0 <= &1 - &5 / &6 * (lcx c s u v a - lcy c s u v a) -
       &20 / &13 * (lcy c s u v a - &1 + &6 / &25 * (&5 / &6 * (lcx c s u v a - lcy c s u v a)))` THENL
   [CCSMF_ABBREV_TAC THEN
    CCSMF_TRI_TAC (`&49 / &25`,`&19 / &25`,`&33 / &20`,`&33 / &20`,`&1`,`&1`,
      `&5 / &6 * (X - Y)`, `&20 / &13 * (Y - &1 + &6 / &25 * (&5 / &6 * (X - Y)))`,
      `&1 - &5 / &6 * (X - Y) - &20 / &13 * (Y - &1 + &6 / &25 * (&5 / &6 * (X - Y)))`);
    CCSMF_TARGET_TAC CCSMF_TARGET196_RIGHT_TRIANGLE
      `&50000 / &4167 * (&89 / &100 * (lcx c s u v a - &49 / &25) + &31 / &100 * (lcy c s u v a - &19 / &25))`
      `&50000 / &4167 * (&1 / &25 * (lcy c s u v a - &19 / &25) - &77 / &500 * (lcx c s u v a - &49 / &25))`]);;

(* Lean: replacement196_right *)
let CCSMF_REPLACEMENT196_RIGHT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      &49 / &25 <= lcx c s u v a /\ lcx c s u v a <= &2 /\
      &457 / &500 <= lcy c s u v a /\ lcy c s u v a <= &2 /\
      (forall i. i < 16 /\ ~(i = 0) ==> ~linside c s u v a (marker i$1) (marker i$2))
      ==> linside c s u v a (&49 / &25) (&19 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CCSMF_LOWER_FAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  CCSMF_TARGET_TAC CCSMF_TARGET196_RIGHT_TRIANGLE
    `&50000 / &4167 * (&89 / &100 * (lcx c s u v a - &49 / &25) + &31 / &100 * (lcy c s u v a - &19 / &25))`
    `&50000 / &4167 * (&1 / &25 * (lcy c s u v a - &19 / &25) - &77 / &500 * (lcx c s u v a - &49 / &25))`);;
