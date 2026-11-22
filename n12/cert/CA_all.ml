(* ========================================================================= *)
(* W-ASM loader (after the Phase-1 chain n12/cases/cs_load.ml and            *)
(* n12/certlib/p3_all.ml): the certificate layers needed by the case         *)
(* composition, with at most 8 OCaml domains, then CA_Assembly.ml.           *)
(*   core + 113 historical pair stages (as CR_HistRun.ml, 8 domains),        *)
(*   W-CHORD (CH_all.ml), W-C898 (C8_all.ml), W-ENTRY (EN_Run.ml).           *)
(* ========================================================================= *)

needs "n12/cert/CR_Row.ml";;
needs "n12/cert/CR_Farkas.ml";;
needs "n12/cert/CR_Plan.ml";;
needs "n12/cert/CR_Eval.ml";;
needs "n12/cert/CR_HistData.ml";;
needs "n12/cert/CR_HistStages.ml";;

let ca_load_t0 = Unix.gettimeofday ();;
let CK_STAGES = List.map (fun ((c,st,_,_,_,_) as s) ->
   ((c, st), if Hashtbl.mem ck_stage_tbl (c,st) then Hashtbl.find ck_stage_tbl (c,st)
             else ck_build_stage 8 s)) hist_stages;;
Printf.printf "CA: %d pair stages, %.0fs\n%!" (List.length CK_STAGES) (Unix.gettimeofday () -. ca_load_t0);;

needs "n12/cert/CH_all.ml";;
Printf.printf "CA: chords done, %.0fs\n%!" (Unix.gettimeofday () -. ca_load_t0);;
needs "n12/cert/C8_all.ml";;
Printf.printf "CA: C898 done, %.0fs\n%!" (Unix.gettimeofday () -. ca_load_t0);;
needs "n12/cert/EN_Run.ml";;
Printf.printf "CA: entries done, %.0fs\n%!" (Unix.gettimeofday () -. ca_load_t0);;
needs "n12/cert/CA_Assembly.ml";;
