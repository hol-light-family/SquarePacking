(* ========================================================================= *)
(* Port of source/S12/OverlapCertificate.lean (Jatloe, N12-jatloe).          *)
(* ReferenceSquare <c,s,side> : Q^3 is RefSq c s side.  r.toSquare hr is the *)
(* 5-tuple (c, s, --side/2, --side/2, side); its squareSet is rs_sqset r.    *)
(* ratPoint is the identity (rational data are real literals).              *)
(* Lean subtypes {q // q.Check} inside OverlapCertificate become conjuncts   *)
(* rs_check of ovcert_check.                                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/ConvexOverlap.ml";;

(* Lean: structure ReferenceSquare *)
let refsq_INDUCT,refsq_RECURSION = define_type "refsq = RefSq real real real";;

let rs_c = define `rs_c (RefSq c s a) = c`;;
let rs_s = define `rs_s (RefSq c s a) = s`;;
let rs_side = define `rs_side (RefSq c s a) = a`;;
let RS_ACCESSORS = [rs_c; rs_s; rs_side];;

(* Lean: ReferenceSquare.Check *)
let rs_check = new_definition
 `rs_check r <=> rs_c r pow 2 + rs_s r pow 2 = &1 /\ &0 < rs_side r`;;

(* Lean: ReferenceSquare.toSquare: the open square (c,s,-side/2,-side/2,side) *)
let rs_sqset = new_definition
 `rs_sqset r = sqset (rs_c r) (rs_s r) (--(rs_side r) / &2) (--(rs_side r) / &2) (rs_side r)`;;

(* the OpenSquare invariants of r.toSquare hr *)
let OC_TOSQUARE_INVARIANTS = prove
 (`forall r. rs_check r ==> rs_c r * rs_c r + rs_s r * rs_s r = &1 /\ &0 < rs_side r`,
  REWRITE_TAC[rs_check; REAL_POW_2] THEN MESON_TAC[]);;

(* Lean: ReferenceSquare.InsideAt *)
let rs_inside_at = new_definition
 `rs_inside_at r (A:real#real) (P:real#real) <=>
    --(rs_side r) / &2 < rs_c r * (FST P - FST A) + rs_s r * (SND P - SND A) /\
    rs_c r * (FST P - FST A) + rs_s r * (SND P - SND A) < rs_side r / &2 /\
    --(rs_side r) / &2 < --(rs_s r) * (FST P - FST A) + rs_c r * (SND P - SND A) /\
    --(rs_s r) * (FST P - FST A) + rs_c r * (SND P - SND A) < rs_side r / &2`;;

(* Lean: ReferenceSquare.insideAt_sound *)
let OC_INSIDEAT_SOUND = prove
 (`forall r A P. rs_check r /\ rs_inside_at r A P ==> psub P A IN rs_sqset r`,
  REWRITE_TAC[rs_inside_at; rs_sqset; IN_SQSET; psub; linside] THEN REAL_ARITH_TAC);;

(* Lean: structure VertexWitness *)
let vwitness_INDUCT,vwitness_RECURSION =
  define_type "vwitness = VWitness (real#real) (real#real) (real#real)";;
let vw_centerA = define `vw_centerA (VWitness a b p) = a`;;
let vw_centerB = define `vw_centerB (VWitness a b p) = b`;;
let vw_point = define `vw_point (VWitness a b p) = p`;;

(* Lean: structure OverlapCertificate *)
let ovcert_INDUCT,ovcert_RECURSION =
  define_type "ovcert = OvCert refsq refsq ((real#real)list) ((real#real)list) (vwitness list)";;
let oc_first = define `oc_first (OvCert f s va vb ws) = f`;;
let oc_second = define `oc_second (OvCert f s va vb ws) = s`;;
let oc_verticesA = define `oc_verticesA (OvCert f s va vb ws) = va`;;
let oc_verticesB = define `oc_verticesB (OvCert f s va vb ws) = vb`;;
let oc_witnesses = define `oc_witnesses (OvCert f s va vb ws) = ws`;;

(* Lean: OverlapCertificate.Check, together with the subtype checks of
   first and second *)
let ovcert_check = new_definition
 `ovcert_check w <=>
    rs_check (oc_first w) /\ rs_check (oc_second w) /\
    forall A. MEM A (oc_verticesA w) ==> forall B. MEM B (oc_verticesB w) ==>
      exists v. MEM v (oc_witnesses w) /\ vw_centerA v = A /\ vw_centerB v = B /\
          rs_inside_at (oc_first w) A (vw_point v) /\
          rs_inside_at (oc_second w) B (vw_point v)`;;

(* Lean: vertexHull *)
let vertex_hull = new_definition
 `vertex_hull (V:(real#real)list) = pconvex_hull (set_of_list V)`;;

let OC_RSSQSET = prove
 (`forall r. rs_sqset r = sqset (rs_c r) (rs_s r) (--(rs_side r) / &2) (--(rs_side r) / &2) (rs_side r)`,
  REWRITE_TAC[rs_sqset]);;

(* Lean: OverlapCertificate.sound *)
let OC_SOUND = prove
 (`forall w A B. ovcert_check w /\ A IN vertex_hull (oc_verticesA w) /\ B IN vertex_hull (oc_verticesB w)
     ==> overlaps_at (rs_sqset (oc_first w)) (rs_sqset (oc_second w)) A B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vertex_hull] THEN STRIP_TAC THEN
  REWRITE_TAC[OC_RSSQSET] THEN
  MP_TAC(ISPECL [`rs_c(oc_first w)`; `rs_s(oc_first w)`; `--(rs_side(oc_first w)) / &2`;
    `--(rs_side(oc_first w)) / &2`; `rs_side(oc_first w)`;
    `rs_c(oc_second w)`; `rs_s(oc_second w)`; `--(rs_side(oc_second w)) / &2`;
    `--(rs_side(oc_second w)) / &2`; `rs_side(oc_second w)`;
    `set_of_list(oc_verticesA w)`; `set_of_list(oc_verticesB w)`] CO_VERTEX_OVERLAP_EXTENDS) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[IN_SET_OF_LIST; GSYM OC_RSSQSET] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ovcert_check w` THEN REWRITE_TAC[ovcert_check] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `A':real#real`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `B':real#real`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[overlaps_at] THEN
  EXISTS_TAC `vw_point v` THEN CONJ_TAC THEN MATCH_MP_TAC OC_INSIDEAT_SOUND THEN
  ASM_REWRITE_TAC[]);;

(* Lean: OverlapCertificate.excludes *)
let OC_EXCLUDES = prove
 (`forall w cq sq uq vq aq cr sr ur vr ar A B.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ cr * cr + sr * sr = &1 /\ &0 < ar /\
     ovcert_check w /\ A IN vertex_hull (oc_verticesA w) /\ B IN vertex_hull (oc_verticesB w) /\
     (forall P. psub P A IN rs_sqset (oc_first w) ==> P IN sqset cq sq uq vq aq) /\
     (forall P. psub P B IN rs_sqset (oc_second w) ==> P IN sqset cr sr ur vr ar) /\
     ldisj cq sq uq vq aq cr sr ur vr ar
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:ovcert`; `A:real#real`; `B:real#real`] OC_SOUND) THEN
  ASM_REWRITE_TAC[overlaps_at] THEN STRIP_TAC THEN
  UNDISCH_TAC `ldisj cq sq uq vq aq cr sr ur vr ar` THEN REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(P:real#real)`; `SND(P:real#real)`]) THEN
  REWRITE_TAC[GSYM IN_SQSET] THEN ASM_MESON_TAC[]);;
