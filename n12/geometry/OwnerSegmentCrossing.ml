(* ========================================================================= *)
(* Port of Compact/Bridge/OwnerSegmentCrossing.lean                          *)
(* (N12Compact.OwnerSegmentCrossing).  Two actual owners whose interior      *)
(* segments cross cannot coexist.                                            *)
(*                                                                           *)
(* Lean  d : Data  is the OCaml tuple                                        *)
(*   (firstMask, secondMask, firstOwned, secondOwned, firstStart, firstEnd,  *)
(*    secondStart, secondEnd, firstWeight, secondWeight)                     *)
(* (owned sets as int lists, points / weights as rational strings).         *)
(* Lean impossible quantifies over all d with d.InputCheck, d.CrossCheck;    *)
(* in HOL it is the producer  osc_impossible fam d  that re-checks both      *)
(* (failure = the Lean decide would fail) and returns                        *)
(*   |- !c1 c2 a b l. NPACK c1 c2 a b l /\                                  *)
(*        IMAGE binarysum (FFP c1 c2 a b l) = fam /\                        *)
(*        ooaux c1 c2 a b l firstMask = firstOwned /\                        *)
(*        ooaux c1 c2 a b l secondMask = secondOwned ==> F                   *)
(* (hm, hn : masks in family are checked by in_fam; ooaux .. m is            *)
(* natCombinedOwners p (ownerIndex p m) by definition).  Tag OSC_.          *)
(* ========================================================================= *)

needs "n12/geometry/owner_bridge.ml";;

(* Lean: Data.InputCheck, Data.CrossCheck (decided on the OCaml data) *)
let osc_cross_check (_, _, _, _, p0, p1, q0, q1, t, w) =
  let r = nlin_rat and one = num 1 and zero = num 0 in
  let t = r t and w = r w in
  let comb (x0, y0) (x1, y1) s =
    ((one -/ s) */ r x0 +/ s */ r x1, (one -/ s) */ r y0 +/ s */ r y1) in
  zero <=/ t && t <=/ one && zero <=/ w && w <=/ one &&
  qeq (comb p0 p1 t) (comb q0 q1 w);;

(* Lean: impossible *)
let osc_impossible fam d =
  let (m1, m2, o1, o2, p0, p1, q0, q1, t, w) = d in
  if m1 = m2 then failwith "osc_impossible: equal masks" else
  if not (osc_cross_check d) then failwith "osc_impossible: CrossCheck" else
  let ctx = ob_ctx fam (false, false, false) [(m1, mk_numset o1); (m2, mk_numset o2)] in
  let fs = ref [] in
  ob_inside ctx fs m1 p0; ob_inside ctx fs m1 p1;
  ob_inside ctx fs m2 q0; ob_inside ctx fs m2 q1;
  ob_segment ctx fs m1 p0 p1 t;
  ob_segment ctx fs m2 q0 q1 w;
  let (_, _, th2) = hd !fs and (_, _, th1) = hd (tl !fs) in
  let args = snd (strip_comb (concl th1)) in
  let th2 = ob_align th2 (el 5 args, el 6 args) in
  let dj = SPECL [el 5 args; el 6 args] (REWRITE_RULE[ldisj] (ob_ldisj ctx m1 m2)) in
  ob_close ctx (MP (NOT_ELIM dj) (CONJ th1 th2));;

(* a check of the producer: crossing 0 of Cases/FourSquareHighRight/Crossings.lean
   in the family of case 678 *)
let OSC_CHECK_678 = osc_impossible (mk_numset [1; 2; 12; 16; 32; 192; 256; 512; 2048; 4096; 8192; 17408])
  (512, 17408, [8;16], [5;18], ("47/20","33/20"), ("3","87/50"), ("47/20","47/20"), ("3","8/5"), "5/6", "5/6");;
