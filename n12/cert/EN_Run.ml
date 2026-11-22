(* ========================================================================= *)
(* W-ENTRY driver: proves the ownership domains, certified points and point   *)
(* premises of all historical entries (and C898), then checks the shapes.     *)
(* Load after the Phase-1 chain:                                             *)
(*   loadt "n12/cases/cs_load.ml";;  loadt "n12/cert/EN_Run.ml";;        *)
(* ========================================================================= *)

needs "n12/cert/EN_Entry.ml";;

let EN_T0 = Unix.gettimeofday ();;
List.iter en_run_case (EN_CASE_IDS @ ["898"]);;

(* every entry theorem is hypothesis-free and stated under the row hypothesis *)
let EN_CHECKED =
  Hashtbl.fold (fun (c, k) th n ->
    let (_, fam) = en_family c in
    if hyp th <> [] || lhand (snd (strip_forall (concl th))) <> en_hyp fam
    then failwith (Printf.sprintf "EN check C%s owner %d" c k) else n + 1) EN_ENTRY 0;;

Printf.printf "W-ENTRY: %d entry theorems, %d domains, %d half domains, %d certified points, %d local queries in LQ_TABLE, %.0fs\n%!"
  EN_CHECKED (Hashtbl.length EN_DOM) (Hashtbl.length EN_HDOM) (Hashtbl.length EN_POINT)
  (Hashtbl.length LQ_TABLE) (Unix.gettimeofday () -. EN_T0);;
