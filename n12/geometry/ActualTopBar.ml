(* ========================================================================= *)
(* Port of Compact/Cases/C868/ActualTopBar.lean (N12Compact.C868).           *)
(* The actual top wall owner 32768 reaches left: ContinuousBottom.reach_of_far*)
(* (C1089CB_REACH_OF_FAR) on W = pullX (pullY (owner 32768)) (LINSIDE_PULLX, *)
(* LINSIDE_PULLY, LCONT_PULLX, LCONT_PULLY).  Tag C868TB_.                   *)
(* ========================================================================= *)

needs "n12/geometry/ActualBars.ml";;

(* Lean: top_bar *)
let C868TB_TOP_BAR = c868_check
 `forall c1 c2 a b l x. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     &6 / &5 <= x /\ x <= &87 / &50
     ==> linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
                 (oov c1 c2 a b l 32768) l x (&3)`
 (let ow = c868_own 32768 in
  let w = c868_pullx (c868_pully ow) in
  let box = MATCH_MP LCONT_PULLX (MATCH_MP LCONT_PULLY (c868_box 32768)) in
  let th = C868_PULL_RULE (SPECL w C1089CB_REACH_OF_FAR) in
  let facts = [box; c868_seed_f 32768 (`&2`, `&1543 / &500`); c868_mp C868AO_ADDITIONAL_INSIDE.(6);
               c868_excl_f 32768 16 (c868_mp C868AO_ADDITIONAL_INSIDE.(1));
               c868_excl_f 32768 16 (c868_seed_f 16 (`&213 / &100`, `&81 / &25`));
               c868_excl_f 32768 3072 (c868_seed_f 3072 (`&33 / &20`, `&47 / &20`))] in
  let r = CONJUNCT2 (CONJUNCT2 (c868_discharge facts th)) in
  let h = `&6 / &5 <= x /\ x <= &87 / &50` in
  let r1 = SPEC `&4 - x` r in
  let r2 = MP r1 (MP (REAL_ARITH (mk_imp(h, lhand (concl r1)))) (ASSUME h)) in
  let r3 = REWRITE_RULE[REAL_ARITH `&4 - (&4 - x) = x`] r2 in
  c868_genx [`x:real`] [h] r3);;
