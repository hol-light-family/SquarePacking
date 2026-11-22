(* ========================================================================= *)
(* W-F345: builds the block-overlap theorems of all 113 historical pair     *)
(* stages and the corresponding transitions (design §4.2, §12.1):            *)
(*   ov_overlap_thm (case, step) : |- cr_block_overlap hdrs (MAP cr_leaf N)  *)
(*   ov_step_thm (case, step)    : |- cr_pair_transition S N T  (no hyps)   *)
(* OV_STAGES lists ((case, step), step theorem).                             *)
(* ========================================================================= *)

needs "n12/cert/OV_HistRun.ml";;

let ov_t0 = Unix.gettimeofday ();;
let OV_STAGES = List.map (fun ((c, st, _, _, _, _) as s) ->
   if not (Hashtbl.mem ov_step_tbl (c, st)) then ignore (ov_build_stage s);
   ((c, st), ov_step_thm (c, st))) hist_stages;;

let () =
  let tot = ref (0, 0, 0, 0, 0.0, 0.0) in
  Hashtbl.iter (fun _ (p, e, pt, ax, t1, t2) ->
      let (p0, e0, pt0, ax0, a0, b0) = !tot in
      tot := (p0 + p, e0 + e, pt0 + pt, ax0 + ax, a0 +. t1, b0 +. t2)) ov_stage_stats;
  let (p, e, pt, ax, t1, t2) = !tot in
  if List.exists (fun (_, th) -> hyp th <> []) OV_STAGES then failwith "OV_STAGES: hypotheses";
  Printf.printf "OV ALL STAGES: %d stage theorems, %d pairs, %d support entries, %d point tests, %d axis tests; eval %.0fs, assemble %.0fs, total %.0fs\n%!"
    (List.length OV_STAGES) p e pt ax t1 t2 (Unix.gettimeofday () -. ov_t0);;
