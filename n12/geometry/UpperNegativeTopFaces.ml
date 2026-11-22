(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeTopFaces.lean (Jatloe, N12-jatloe)*)
(* (N12Compact.C868.UpperNegativeTopFaces).  A compact whole-square region  *)
(* for the surviving top owner.  Pure geometry; tag C868TF_.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: shallow_lower_v *)
let C868TF_SHALLOW_LOWER_V = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ &0 <= s /\ s <= (&2 / &5) * c /\
     linside c s u v a (--(&4 / &5)) (&1) /\
     linside c s u v a (&0) (&543 / &500) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20)
     ==> (&7 / &20) * (c + s) <= v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  RASM_ARITH_TAC);;

(* Lean: above_chord_lower_v *)
let C868TF_ABOVE_CHORD_LOWER_V = prove
 (`forall c s u v a x y.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ &0 <= s /\
     linside c s u v a (--(&4 / &5)) (&1) /\
     linside c s u v a (&0) (&543 / &500) /\
     --(&4 / &5) <= x /\ x <= &0 /\
     &543 / &500 + (&43 / &400) * x < y
     ==> v < --s * x + c * y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < c * (y - &543 / &500 - (&43 / &400) * x)`] THEN
  ASM_CASES_TAC `s <= (&43 / &400) * c` THENL
  [NLIN_FACTS_TAC [] [`&0 <= ((&43 / &400) * c - s) * (x + &4 / &5)`] THEN
   NLIN_TAC ~deg2:false [];
   NLIN_FACTS_TAC [] [`&0 <= (s - (&43 / &400) * c) * --x`] THEN
   NLIN_TAC ~deg2:false []]);;

let C868TF_REGION_TAC xr yt =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    C868TF_SHALLOW_LOWER_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`]
    C868TF_ABOVE_CHORD_LOWER_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c:real`]
    [`c <= &1`; `s <= &1`] THEN
  UNDISCH_TAC `linside c s u v a (--(&4 / &5)) (&1)` THEN
  UNDISCH_TAC `linside c s u v a (&0) (&543 / &500)` THEN
  UNDISCH_TAC `~linside c s u v a (--(&7 / &20)) (&7 / &20)` THEN
  REWRITE_TAC[linside] THEN REPEAT DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 < c * (x + &4 / &5)`; `&0 <= s * (y - &1)`;
    parse_term ("&0 <= c * (" ^ xr ^ " - x)");
    parse_term ("&0 <= s * (" ^ yt ^ " - y)");
    `&0 <= s * (x + &2 / &5)`;
    parse_term ("&0 <= c * (" ^ yt ^ " - y)")] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* Lean: shallow_region *)
let C868TF_SHALLOW_REGION = prove
 (`forall c s u v a x y.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= (&2 / &5) * c /\
     linside c s u v a (--(&4 / &5)) (&1) /\
     linside c s u v a (&0) (&543 / &500) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     --(&2 / &5) <= x /\ x <= --(&7 / &100) /\
     &1 <= y /\ y <= &61 / &50 /\
     &543 / &500 + (&43 / &400) * x < y
     ==> linside c s u v a x y`,
  C868TF_REGION_TAC "--(&7 / &100)" "&61 / &50");;

(* Lean: shallow_region_tight *)
let C868TF_SHALLOW_REGION_TIGHT = prove
 (`forall c s u v a x y.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= (&2 / &5) * c /\
     linside c s u v a (--(&4 / &5)) (&1) /\
     linside c s u v a (&0) (&543 / &500) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     --(&2 / &5) <= x /\ x <= --(&1 / &25) /\
     &1 <= y /\ y <= &59 / &50 /\
     &543 / &500 + (&43 / &400) * x < y
     ==> linside c s u v a x y`,
  C868TF_REGION_TAC "--(&1 / &25)" "&59 / &50");;

(* Lean: steep_region *)
let C868TF_STEEP_REGION = prove
 (`forall c s u v a x.
     c * c + s * s = &1 /\ &0 < a /\
     &0 < c /\ &0 <= s /\ (&2 / &5) * c <= s /\
     linside c s u v a (--(&4 / &5)) (&1) /\
     linside c s u v a (&0) (&543 / &500) /\
     --(&13 / &50) <= x /\ x <= --(&7 / &100)
     ==> linside c s u v a x (&53 / &50)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= c * (x + &13 / &50)`; `&0 <= c * (--(&7 / &100) - x)`;
    `&0 <= s * (x + &13 / &50)`; `&0 <= s * (--(&7 / &100) - x)`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;
