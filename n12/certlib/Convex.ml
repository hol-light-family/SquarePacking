(* ========================================================================= *)
(* Port of source/S12/Convex.lean (Jatloe, N12-jatloe).                      *)
(* inside_segment is CES_INSIDE_SEGMENT (geometry/CentralEscapeSegment.ml).        *)
(* A TriangleCertificate <p0,p1,p2,target,s,t> is the HOL value              *)
(* TriCert p0 p1 p2 target s t (points real#real, rational data as reals).   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: interval_segment *)
let CVX_INTERVAL_SEGMENT = prove
 (`forall l a x y t. l < x /\ x < l + a /\ l < y /\ y < l + a /\ &0 <= t /\ t <= &1
     ==> l < (&1 - t) * x + t * y /\ (&1 - t) * x + t * y < l + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  (MATCH_MP_TAC REAL_CONVEX_BOUND_LT ORELSE MATCH_MP_TAC REAL_CONVEX_BOUND_GT) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: inside_segment *)
let CVX_INSIDE_SEGMENT = CES_INSIDE_SEGMENT;;

(* Lean: structure TriangleCertificate *)
let tri_cert_INDUCT,tri_cert_RECURSION =
  define_type "tri_cert = TriCert (real#real) (real#real) (real#real) (real#real) real real";;

(* Lean: TriangleCertificate.Check *)
let tri_cert_check = define
 `tri_cert_check (TriCert p0 p1 p2 target s t) <=>
    &0 <= s /\ s <= &1 /\ &0 <= t /\ t <= &1 /\
    FST target = (&1 - t) * ((&1 - s) * FST p0 + s * FST p1) + t * FST p2 /\
    SND target = (&1 - t) * ((&1 - s) * SND p0 + s * SND p1) + t * SND p2`;;

(* Lean: triangle_certificate_sound *)
let CVX_TRIANGLE_CERTIFICATE_SOUND = prove
 (`forall p0 p1 p2 target s t c sn u v a.
     tri_cert_check (TriCert p0 p1 p2 target s t) /\
     linside c sn u v a (FST p0) (SND p0) /\ linside c sn u v a (FST p1) (SND p1) /\
     linside c sn u v a (FST p2) (SND p2)
     ==> linside c sn u v a (FST target) (SND target)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tri_cert_check] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CES_INSIDE_SEGMENT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CES_INSIDE_SEGMENT THEN ASM_REWRITE_TAC[]);;
