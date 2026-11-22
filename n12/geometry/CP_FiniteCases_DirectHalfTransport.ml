(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/DirectHalfTransport.lean.         *)
(* A typed local-query domain (S12 DirectSingleDomain) reused as local       *)
(* geometry for a transformed mask, as a half domain of the target family.  *)
(*                                                                           *)
(* A Lean  w : DirectSingleDomain  is the OCaml record dht_dom below: mask,  *)
(* lower, upper, allowed, and its local queries as kernel-checkable hints    *)
(* (mask, kind, owned, inside points, outside points), the same hint format *)
(* as LOCAL_QUERIES / cert/EN_Entry.ml (a Lean .hull/.four/.short query      *)
(* contributes its inside and outside points).  Every query is re-proved by  *)
(* the HOL kernel (localq.ml query_theorem); nothing is trusted.             *)
(*                                                                           *)
(*   dht_check w fam k        Lean  w.Check fam k  (OCaml check; fails if    *)
(*                            the Lean decide would fail)                    *)
(*   dht_local_sound w k      Lean  local_sound:                             *)
(*     |- !c1 c2 a b l. &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\ *)
(*          owalls c1 c2 a b l /\ owned c1 c2 a b l = bitset w.mask /\       *)
(*          lo <= CARD (auxown k c1 c2 a b l) /\ CARD (..) <= hi             *)
(*          ==> MEM (auxown k c1 c2 a b l) [w.allowed]                      *)
(*   dht_transported fam mask w oldfam k l trf perm                         *)
(*                            Lean  transported family mask w oldFamily k l  *)
(*                            checked t _ _ targetMask perm points budget:  *)
(*     |- hdom fam mask l [pushOwners perm s | s in w.allowed]               *)
(*   DHT_QUARTERFG, dht_check_points: Lean quarterFG / quarterFG_points.     *)
(* The side conditions (Check, target mask = t.maskAction w.mask, the point *)
(* permutation, and the budget  w.lower <= lower mask l /\ upper family mask *)
(* l <= w.upper) are all checked; the budget by the kernel in pk_hdom_local. *)
(* Tested (session p1b) on Lean C975Domains.rawTopG = transported family     *)
(* 34816 C715.mergedF C715.family 0 1 .. quarterFG: the 45 mergedF queries   *)
(* (hull and four-point) were re-proved for mask 34816 kind 1 and the result *)
(* was hdom .. 34816 1 [{3};{1};{4};{3,6};{4,6};{1,3};{3,7};{3,4};{1,4};    *)
(* {4,7}] = Lean topGAllowed (42 s).                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_TransposeOwnerDomain.ml";;

(* Lean: S12.DirectSingleDomain (data) *)
type dht_dom = { dht_mask : int; dht_lower : int; dht_upper : int; dht_allowed : int list list;
                 dht_queries : (int * int * int list * (num * num) list * (num * num) list) list };;

let dht_sorted s = List.sort compare (setify s);;

(* re-prove (m, k, owned) from the first hint that the kernel accepts *)
let dht_prove_query (m, k, owned) hints =
  if Hashtbl.mem LQ_TABLE (m, k, owned) then () else
  let rec go l = match l with
      [] -> failwith (Printf.sprintf "dht: no checkable query for (%d, %d, {%s})" m k
                        (String.concat "," (map string_of_int owned)))
    | (uin, uout) :: r ->
        (try Hashtbl.add LQ_TABLE (m, k, owned) (query_theorem (-1, m, k, owned, uin, uout))
         with Failure _ -> go r) in
  go hints;;

let dht_hints w m k owned =
  map (fun (_, _, _, uin, uout) -> (uin, uout))
    (filter (fun (m', k', o', _, _) -> m' = m && k' = k && dht_sorted o' = owned) w.dht_queries);;

(* sorted subsets of l with lo <= size <= hi *)
let dht_subsets lo hi l =
  let rec all n l = if n = 0 then [[]] else match l with
      [] -> [] | h :: t -> map (fun s -> h :: s) (all (n - 1) t) @ all n t in
  List.concat (map (fun n -> all n l) (lo -- hi));;

(* Lean: DirectSingleDomain.Check family k *)
let dht_check w fam k =
  if w.dht_lower <> pk_num (pklow_thm w.dht_mask k) then failwith "dht_check: lower" else
  if w.dht_upper <> pk_num (pkup_thm fam w.dht_mask k) then failwith "dht_check: upper" else
  List.iter (fun x ->
      if not (mem x (map dht_sorted w.dht_allowed)) &&
         not (exists (fun (m', k', o', _, _) -> m' = w.dht_mask && k' = k && dht_sorted o' = x) w.dht_queries)
      then failwith (Printf.sprintf "dht_check: subset {%s} neither allowed nor refuted"
                       (String.concat "," (map string_of_int x))))
    (dht_subsets w.dht_lower (min w.dht_upper 10) (0 -- 9));;

(* Lean: local_sound *)
let dht_local_sound w k =
  let m = w.dht_mask in
  let al = map dht_sorted w.dht_allowed in
  List.iter (fun x -> if not (mem x al) then dht_prove_query (m, k, x) (dht_hints w m k x))
    (dht_subsets w.dht_lower (min w.dht_upper 10) (0 -- 9));
  let th = spec_theorem m k w.dht_lower w.dht_upper al in
  let ownp = mk_eq(`owned c1 c2 a b l`, set_tm (bits m)) in
  let (hl, hh) = bound_tms k w.dht_lower w.dht_upper in
  let hyps = LQ_HYPS @ [ownp; hl; hh] in
  let th = List.fold_left MP (SPECL SPEC5 th) (map ASSUME hyps) in
  local_to_mem m (auxown_tm k) hyps th (mk_list(map mk_numset al, `:num->bool`));;

(* Lean: points premise of transported (t maps auxPoints k j to auxPoints l (perm j)),
   with perm a permutation of 0..9 (Equiv) *)
let dht_check_points trf k l perm =
  if List.sort compare perm <> (0 -- 9) then failwith "dht: not a permutation" else
  tod_check_points trf k l perm;;

(* Lean: transported *)
let dht_transported fam mask w oldfam k l trf perm =
  dht_check w oldfam k;
  if mask_action trf w.dht_mask <> mask then failwith "dht_transported: target mask" else
  dht_check_points trf k l perm;
  let tp (x, y) = let (x1, y1) = tr_point trf (term_of_rat x, term_of_rat y) in
                  (rat_of_term x1, rat_of_term y1) in
  let push s = List.sort compare (map (fun j -> el j perm) s) in
  let al = map dht_sorted w.dht_allowed in
  List.iter (fun x ->
      if not (mem x al) then
        dht_prove_query (mask, l, push x)
          (map (fun (uin, uout) -> (map tp uin, map tp uout)) (dht_hints w w.dht_mask k x)))
    (dht_subsets w.dht_lower (min w.dht_upper 10) (0 -- 9));
  let id = ro_fresh_id () in
  EXTRA_SINGLE := (id, mask, l, w.dht_lower, w.dht_upper, map push w.dht_allowed) :: !EXTRA_SINGLE;
  pk_single fam id;;

(* Lean: quarterFG *)
let DHT_QUARTERFG = [5;2;8;0;6;3;9;1;7;4];;

(* Lean: quarterFG_points *)
let () = dht_check_points (true, true, false) 0 1 DHT_QUARTERFG;;
