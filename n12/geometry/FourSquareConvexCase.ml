(* ========================================================================= *)
(* Port of Compact/Bridge/FourSquareConvexCase.lean                          *)
(* (N12Compact.FourSquareConvexCase): original-packing bridge for the       *)
(* lower-barrier reduction (FourSquareLowerBarrier.impossible =             *)
(* FSLB_IMPOSSIBLE, FourSquareLowerBarrier.ml) with exact convex point      *)
(* certificates.                                                             *)
(*                                                                           *)
(* Lean  d : Data = <transform, masks, owned, leftBarrier, hulls>  is the    *)
(* OCaml tuple (trf, [m0..m4], [S0..S4], leftBarrier, [hulls0..hulls4]),     *)
(* trf = (swap, reflectX, reflectY), owned sets as int lists, a Lean         *)
(* TriangleCertificate <p0, p1, p2, target, s, t> the tuple                  *)
(* (p0, p1, p2, target, s, t) of rational strings.  impossible quantifies    *)
(* over all d with d.Check family; in HOL it is the producer                 *)
(*   fscc_impossible fam d                                                   *)
(*     |- (!c1 c2 a b l. NPACK c1 c2 a b l /\                               *)
(*           IMAGE binarysum (FFP c1 c2 a b l) = fam                        *)
(*           ==> ooaux c1 c2 a b l m0 = S0 /\ .. /\ ooaux c1 c2 a b l m4 = S4) *)
(*        ==> !c1 c2 a b l. NPACK .. /\ IMAGE .. = fam ==> F                 *)
(* which re-checks every condition of d.Check (owner_bridge.ml; a failure =  *)
(* the Lean decide would fail).  fscc_impossible_of_owned fam d is the same  *)
(* with the owned sets as hypotheses (the core of the Lean proof).           *)
(* (ooaux c1 c2 a b l m = natCombinedOwners p (ownerIndex p m)).  Tag FSCC_. *)
(* ========================================================================= *)

needs "n12/geometry/owner_bridge.ml";;
needs "n12/geometry/FourSquareLowerBarrier.ml";;

(* Lean: insidePoints *)
let FSCC_INSIDE = [|[("2","113/50"); ("113/50","2"); ("47/20","47/20")];
                    [("33/20","47/20"); ("8/5","3"); ("87/50","3")];
                    [("457/500","2"); ("1","12/5")];
                    [("3","12/5"); ("1543/500","2")];
                    [("3","87/50")]|];;

(* Lean: outsidePoints *)
let FSCC_OUTSIDE = [|[("33/20","33/20"); ("47/20","33/20")];
                     [("1","1543/500"); ("2","1543/500")];
                     [("33/20","33/20")];
                     [];
                     []|];;

(* Lean: Data.Check (checked while the proof is built: masks and leftBarrier
   in family by in_fam, distinct pairs 01, 03, 12, 13, 34 and
   masks 2 <> leftBarrier by oo_apart, each inside point in queryInsidePoints
   or the target of a checked triangle certificate over queryInsidePoints,
   outside points in queryOutsidePoints, the barrier point in
   seedPoints (maskSupport leftBarrier)) *)

(* the core of Lean impossible with the forced owner sets as hypotheses *)
let fscc_impossible_of_owned fam (trf, masks, owned, lb, hulls) =
  if List.length masks <> 5 || List.length owned <> 5 || List.length hulls <> 5
  then failwith "fscc: data" else
  let ctx = ob_ctx fam trf (zip masks (map mk_numset owned)) in
  List.iter (fun m -> ignore (ob_inf ctx m)) (masks @ [lb]);
  let fs = ref [] in
  List.iteri (fun i m -> List.iter (ob_inside_or_hull ctx fs m (el i hulls)) FSCC_INSIDE.(i)) masks;
  List.iteri (fun i m -> List.iter (ob_outside ctx fs m) FSCC_OUTSIDE.(i)) masks;
  ob_barrier ctx fs (el 2 masks) lb ("19/25", "187/100");
  (* rMissingRow: the point (3, 87/50) of owner 4 is outside owner 3 (apart 3 4) *)
  ob_foreign ctx fs (el 3 masks) (el 4 masks) ("3", "87/50");
  ob_close ctx (ob_apply ctx fs FSLB_IMPOSSIBLE (fst (chop_list 4 masks)) []);;

(* Lean: impossible *)
let fscc_impossible fam d = ob_forced (fscc_impossible_of_owned fam d);;

(* checks of the producer: cases 445 and 864 (Cases/FourSquareConvex/Case445.lean,
   Case864.lean; 864 uses a triangle certificate for owner 3) *)
let FSCC_CHECK_445 = fscc_impossible
  (mk_numset [1; 2; 4; 48; 192; 512; 1024; 2048; 4096; 8448; 16384; 32768])
  ((false, false, false), [1024; 2048; 4096; 16384; 512],
   [[5; 16]; [3; 14]; [1; 11]; [9; 19]; [8; 18]], 2, [[]; []; []; []; []]);;
let FSCC_CHECK_864 = fscc_impossible
  (mk_numset [1; 2; 12; 16; 192; 256; 512; 2048; 4096; 8192; 16416; 33792])
  ((false, false, false), [33792; 2048; 4096; 16416; 512],
   [[5; 16]; [3; 14]; [1; 11]; [9; 19]; [8; 18]], 2,
   [[]; []; []; [(("3","9/4"), ("3","11/4"), ("3","9/4"), ("3","12/5"), "3/10", "0")]; []]);;
