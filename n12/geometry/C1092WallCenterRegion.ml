(* ========================================================================= *)
(* Port of Compact/Geometry/C1092WallCenterRegion.lean (Jatloe, N12-jatloe).  *)
(* Geometric entrance to the centerX >= 1 branch of the C1092 wall point.    *)
(* Also ports S12.inside_center_distance (source/S12/CenterLocalization)     *)
(* and S12.tri0w0..2, S12.triangle0_hit (source/S12/MarkerCoverGeometryBase);*)
(* marker 0 = (1,457/500), marker 1 = (457/500,1), marker 8 = (33/20,33/20). *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* bridge: the centred representation of Phase 1 at the centre of the square *)
let C1092WCR_OSQ_CENTRE = prove
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

(* Lean: S12.inside_center_distance *)
let C1092WCR_INSIDE_CENTER_DISTANCE = prove
 (`forall c s u v a x y. c * c + s * s = &1 /\ linside c s u v a x y
     ==> (x - lcx c s u v a) pow 2 + (y - lcy c s u v a) pow 2 < a pow 2 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `linside c s u v a x y` THEN REWRITE_TAC[linside] THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x - X) pow 2 + (y - Y) pow 2 =
                (c * (x - X) + s * (y - Y)) pow 2 + (--s * (x - X) + c * (y - Y)) pow 2`
  SUBST1_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `--(a / &2) < c * (x - X) + s * (y - Y) /\
                c * (x - X) + s * (y - Y) < a / &2 /\
                --(a / &2) < --s * (x - X) + c * (y - Y) /\
                --s * (x - X) + c * (y - Y) < a / &2` MP_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`c * (x - X) + s * (y - Y)`,`p:real`) THEN
  SPEC_TAC(`--s * (x - X) + c * (y - Y)`,`q:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN NLIN_TAC []);;

(* Lean: S12.tri0w0, tri0w1, tri0w2 (definitions) *)
let c1092wcr_tri0w0 = new_definition
 `c1092wcr_tri0w0 (X:real) (Y:real) =
    (&162500 / &29799) * X + (-- &184000 / &29799) * Y + &25 / &21`;;
let c1092wcr_tri0w1 = new_definition
 `c1092wcr_tri0w1 (X:real) (Y:real) =
    (-- &184000 / &29799) * X + (&162500 / &29799) * Y + &25 / &21`;;
let c1092wcr_tri0w2 = new_definition
 `c1092wcr_tri0w2 (X:real) (Y:real) =
    (&500 / &693) * X + (&500 / &693) * Y + -- &29 / &21`;;

let C1092WCR_TRI0_OSQ = tri_lemma
  ((q"&1",q"&457 / &500"),(q"&457 / &500",q"&1"),(q"&33 / &20",q"&33 / &20"))
  (q"(&162500 / &29799) * c1 + (-- &184000 / &29799) * c2 + &25 / &21",
   q"(-- &184000 / &29799) * c1 + (&162500 / &29799) * c2 + &25 / &21",
   q"(&500 / &693) * c1 + (&500 / &693) * c2 + -- &29 / &21");;

(* Lean: S12.triangle0_hit *)
let C1092WCR_TRIANGLE0_HIT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     &0 <= c1092wcr_tri0w0 (lcx c s u v a) (lcy c s u v a) /\
     &0 <= c1092wcr_tri0w1 (lcx c s u v a) (lcy c s u v a) /\
     &0 <= c1092wcr_tri0w2 (lcx c s u v a) (lcy c s u v a)
     ==> linside c s u v a (&1) (&457 / &500) \/
         linside c s u v a (&457 / &500) (&1) \/
         linside c s u v a (&33 / &20) (&33 / &20)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c1092wcr_tri0w0; c1092wcr_tri0w1; c1092wcr_tri0w2] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lcx c s u v a`; `lcy c s u v a`; `c:real`; `s:real`; `a:real`]
    C1092WCR_TRI0_OSQ) THEN
  ASM_SIMP_TAC[C1092WCR_OSQ_CENTRE]);;

(* Lean: coarse_bounds *)
let C1092WCR_COARSE_BOUNDS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ a <= &1001 / &1000 /\
     linside c s u v a (&457 / &500) (&2)
     ==> lcx c s u v a < &33 / &20 /\ lcx c s u v a < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `&457 / &500`; `&2`] C1092WCR_INSIDE_CENTER_DISTANCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a pow 2 <= (&1001 / &1000) pow 2` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `(&457 / &500 - lcx c s u v a) pow 2 + (&2 - lcy c s u v a) pow 2 <
               a pow 2 / &2` THEN
  UNDISCH_TAC `a pow 2 <= (&1001 / &1000) pow 2` THEN
  SPEC_TAC(`a pow 2`,`A:real`) THEN
  SPEC_TAC(`lcx c s u v a`,`X:real`) THEN SPEC_TAC(`lcy c s u v a`,`Y:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THENL
  [NLIN_TAC [SQ_NONNEG `&2 - Y`];
   NLIN_TAC [SQ_NONNEG `(X - &457 / &500) - (&2 - Y)`]]);;

(* Lean: original_marker_entrance *)
let C1092WCR_ORIGINAL_MARKER_ENTRANCE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\
     linside c s u v a (&457 / &500) (&2) /\
     ~linside c s u v a (&1) (&457 / &500) /\
     ~linside c s u v a (&457 / &500) (&1) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     &1 <= lcx c s u v a /\ lcy c s u v a <= &2
     ==> lcx c s u v a <= &33 / &20 /\
         (&325 / &368) * lcx c s u v a + &1419 / &7360 <= lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092WCR_COARSE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C1092WCR_TRIANGLE0_HIT) THEN
  ASM_REWRITE_TAC[c1092wcr_tri0w0; c1092wcr_tri0w1; c1092wcr_tri0w2] THEN
  ASM_REAL_ARITH_TAC);;
