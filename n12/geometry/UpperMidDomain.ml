(* ========================================================================= *)
(* Port of Compact/Bridge/UpperMidDomain.lean (N12Compact.UpperMidDomain).   *)
(* The top-middle/inner marker pair (mask 33792) is the half-turn of the     *)
(* bottom-middle pair; a second auxiliary point is forced by one exact       *)
(* triangle whenever F3 is owned, excluding three singleton assignments.     *)
(*   halfTurnF        : umd_halfturnf (= RO_HALFTURN, the list ![9,..,0])    *)
(*   mismatch33792 j  : umd_mismatch33792 j, the local-query data            *)
(*                      (mask, kind, owned, inside (hull) points, outside)   *)
(*   mismatch33792_checked j hne : umd_mismatch33792_checked j  (fails for   *)
(*                      j = 4, as the Lean hypothesis j <> 4 requires; the   *)
(*                      query is re-proved by slq_new)                       *)
(*   domain33792 family hc0 hc1 : umd_domain33792 fam  |- cdom fam 33792 al  *)
(*                      for a literal family; the card hypotheses hc0, hc1   *)
(*                      are checked by the budget producers                  *)
(*                      (tob_transformed_singleton, ro_single).              *)
(* Tag umd_ / UMD_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/TransformedOwnerBudget.ml";;
needs "n12/geometry/SharedLocalQueries.ml";;

(* Lean: halfTurnF *)
let umd_halfturnf = RO_HALFTURN;;
let () = if umd_halfturnf <> [9;8;7;6;5;4;3;2;1;0] then failwith "umd_halfturnf";;

(* Lean: mismatch33792 *)
let umd_mismatch33792 j =
  if j < 0 || j > 9 then failwith "umd_mismatch33792: j is a Fin 10" else
  let q x = rat_of_term (parse_term x) in
  (33792, 2, [3; j + 10],
   [(q "&8 / &5", q "&3"); (q "&2", q "&1543 / &500"); (q "&47 / &20", q "&47 / &20")],
   [(q "&87 / &50", q "&3")]);;

(* Lean: mismatch33792_checked *)
let umd_mismatch33792_checked j =
  if j = 4 then failwith "umd_mismatch33792_checked: j = 4 is excluded" else
  slq_new (umd_mismatch33792 j);;

(* Lean: domain33792 *)
let umd_domain33792 fam =
  let first = tob_transformed_singleton fam 33792 0 0 (false, true, true) 72 umd_halfturnf
                `[{7}; {5}; {3}]` in
  let second = ro_single fam 101 in
  let d0 = pk_product first second in
  let rm d j =
    let (_, _, ow, _, _) = umd_mismatch33792 j in
    ignore (umd_mismatch33792_checked j);
    pk_remove d (mk_numset ow) in
  rm (rm (rm d0 6) 7) 9;;

(* check: the domain for Lean's family864 (Cases/FourSquareConvex/Case864) *)
let UMD_CHECK_864 = umd_domain33792 `{1,2,12,16,192,256,512,2048,4096,8192,16416,33792}`;;
