(* ========================================================================= *)
(* Builds the theorems of all 113 historical pair stages (design §4.1):      *)
(*   ck_stage_thm (case, step), e.g. ck_stage_thm ("713", "03").             *)
(* cr_hist_domains (default 12) OCaml domains evaluate the plan checks.      *)
(* ========================================================================= *)

needs "n12/cert/CR_HistStages.ml";;

let cr_hist_domains = ref 12;;
let ck_t0 = Unix.gettimeofday ();;
let CK_STAGES = List.map (fun ((c,st,_,_,_,_) as s) ->
   ((c, st), if Hashtbl.mem ck_stage_tbl (c,st) then Hashtbl.find ck_stage_tbl (c,st)
             else ck_build_stage !cr_hist_domains s)) hist_stages;;
Printf.printf "ALL STAGES: %d theorems, %.1fs\n%!" (List.length CK_STAGES) (Unix.gettimeofday () -. ck_t0);;
