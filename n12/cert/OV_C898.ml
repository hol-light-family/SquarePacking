(* ========================================================================= *)
(* W-F345 for C898 (design §4.6): the block overlaps of the 13 C898 pair    *)
(* steps (00..08, 11..14; step 14 = whole source poses, SOME [] headers)    *)
(* with the checkers of OV_Overlap.ml, and the hypothesis-free steps:       *)
(*   ov8_overlap_thm "NN" : |- cr_block_overlap c898_sNN_hdrs (MAP cr_leaf c898_dN) *)
(*   ov8_step_thm "NN"    : |- cr_pair_transition (MAP cr_leaf c898_dS)      *)
(*                             (MAP cr_leaf c898_dN) (MAP cr_leaf c898_dT)   *)
(* Data (untrusted): `python3 n12/scripts/ov_oracle.py c898` ->                 *)
(* n12/data/cert/ov898_ctx.txt, ov898_pairs.txt.  Context keys are prefixed     *)
(* "c898 " in the shared OV_HistRun tables (separate dictionary).            *)
(* Needs C8_all.ml (c8_step_thm, c8_hdrs_tbl, c8dom_def) and OV_HistRun.ml. *)
(* ========================================================================= *)

needs "n12/cert/C8_all.ml";;
needs "n12/cert/OV_HistRun.ml";;

let () =
  List.iter (fun l -> match String.index_opt l '|' with
      Some i -> Hashtbl.replace ov_ctx_raw ("c898 " ^ String.trim (String.sub l 0 i))
                  (String.trim (String.sub l (i + 1) (String.length l - i - 1)))
    | None -> ()) (cr_read_lines "n12/data/cert/ov898_ctx.txt");;

let ov8_pairs_raw : (string, string list) Hashtbl.t = Hashtbl.create 20;;
let () =
  let cur = ref None and acc = ref [] in
  let flush () = match !cur with
      Some k -> Hashtbl.replace ov8_pairs_raw k (List.rev !acc) | None -> () in
  List.iter (fun l ->
      if String.length l > 1 && l.[0] = 'S' && l.[1] = ' ' then
        (flush (); acc := [];
         match cr_split ' ' l with
           [_; _; st; _; _] -> cur := Some st
         | _ -> failwith "ov898_pairs")
      else if l <> "" then acc := l :: !acc) (cr_read_lines "n12/data/cert/ov898_pairs.txt");
  flush ();;

let ov8_overlap_tbl : (string, thm) Hashtbl.t = Hashtbl.create 20;;
let ov8_step_tbl : (string, thm) Hashtbl.t = Hashtbl.create 20;;
let ov8_stage_stats : (string, int * int * int * int * float * float) Hashtbl.t = Hashtbl.create 20;;

let ov8_build_step (st, sdom, ndom, tdom, _) =
  let c = "898" in
  let t0 = Unix.gettimeofday () in
  let hdef = Hashtbl.find c8_hdrs_tbl st in
  let ndef = c8dom_def ndom in
  let nconst = lhs (concl ndef) in
  let nids = Hashtbl.find c898_domain_ids ndom in
  let nposes = dest_list (rhs (concl ndef)) in
  let hdrs = dest_list (rhs (concl hdef)) in
  let plan_lines = List.filter (fun l -> l <> "" && l.[0] = 'P')
      (cr_read_lines (Printf.sprintf "n12/data/cert/c898_plans/S%s.txt" st)) in
  let meth_lines = ref (try Hashtbl.find ov8_pairs_raw st with Not_found -> []) in
  (* headers: (header, None | Some (src, blk, key, rows, src angle, methods)) *)
  let hinfo = List.map2 (fun h pl ->
      let src, blko = dest_pair h in
      match cr_split ' ' (String.sub pl 0 (String.index pl '|')) with
        ["P"; sid; b] when b <> "-" ->
          let b = "B=" ^ String.sub b 2 (String.length b - 2) in
          let ml = (match !meth_lines with x :: r -> meth_lines := r; x
                                         | [] -> failwith "ov: missing method line") in
          let blk = rand blko in
          let rows = mk_comb (mk_comb (ov_append_c, mk_comb (`cp_rows`, src)), blk) in
          let a = fst (Hashtbl.find c898_poses_raw (int_of_string sid)) in
          h, Some (src, blk, "c898 " ^ sid ^ " " ^ b, rows, a, cr_split ' ' ml)
      | _ -> h, None) hdrs plan_lines in
  if !meth_lines <> [] then failwith "ov: extra method lines";
  let nkeys = List.map (fun i -> "c898 " ^ string_of_int i ^ " B-") nids in
  let nangs = List.map (fun i -> fst (Hashtbl.find c898_poses_raw i)) nids in
  let nrows = List.map (fun p -> mk_comb (`cp_rows`, p)) nposes in
  let nbrs = zip nkeys (zip nangs (zip nrows nposes)) in
  (* 1. the support entries and point tests needed *)
  let need_sem = Hashtbl.create 1000 in
  let add_sem key a rows pose =
    if not (Hashtbl.mem ov_sem_tbl (key, a)) && not (Hashtbl.mem need_sem (key, a)) then
      Hashtbl.add need_sem (key, a) (rows, pose) in
  let need_pt = Hashtbl.create 1000 in
  let add_pt key a m =
    if not (Hashtbl.mem ov_pt_tbl (key, a, m)) && not (Hashtbl.mem need_pt (key, a, m)) then
      Hashtbl.add need_pt (key, a, m) () in
  List.iter (fun (h, inf) -> match inf with
      Some (src, blk, key, rows, a, ms) when ms <> ["E"] ->
        add_sem key a rows src;
        List.iter2 (fun (nk, (b, (rn, np))) m ->
            add_sem nk b rn np;
            if m = "A" then (add_sem key b rows src; add_sem nk a rn np)
            else (add_pt key a m; add_pt nk b m)) nbrs ms
    | _ -> ()) hinfo;
  let sem_jobs = Hashtbl.fold (fun (key, a) (rows, pose) acc ->
      let e, cert = List.assoc a (ov_entries key) in
      (((key, a), e, pose), list_mk_comb (`ov_ang_check`, [rows; e; cert])) :: acc) need_sem [] in
  let nsem = List.length sem_jobs in
  ov_run_jobs sem_jobs (fun (k, e, pose) th ->
      Hashtbl.replace ov_sem_tbl k (MATCH_MP OV_ANG_CHECK_SOUND th, e));
  let pt_jobs = Hashtbl.fold (fun (key, a, m) () acc ->
      let e = ov_entry key a in
      let (x, y, w) = ov_pt_tm m in
      ((key, a, m), list_mk_comb (`ov_pt_ok`, [e; x; y; w])) :: acc) need_pt [] in
  let npt = List.length pt_jobs in
  ov_run_jobs pt_jobs (fun k th -> Hashtbl.replace ov_pt_tbl k th);
  (* 2. axis tests: one evaluation per pair *)
  let axis_jobs = ref [] in
  List.iter (fun (h, inf) -> match inf with
      Some (src, blk, key, rows, a, ms) when ms <> ["E"] ->
        List.iter2 (fun (nk, (b, _)) m ->
            if m = "A" then begin
              let e1 = ov_entry key a and e2 = ov_entry key b
              and e3 = ov_entry nk a and e4 = ov_entry nk b in
              let r1 = mk_comb (`ova_ref`, e1) and r4 = mk_comb (`ova_ref`, e4) in
              let tm = mk_conj (list_mk_comb (`ov_axes`, [r1; r4; e1; e3]),
                                list_mk_comb (`ov_axes`, [r1; r4; e2; e4])) in
              axis_jobs := ((key, nk), tm) :: !axis_jobs
            end) nbrs ms
    | _ -> ()) hinfo;
  let axis_jobs = List.rev !axis_jobs in
  let nax = List.length axis_jobs in
  let ax_tbl = Hashtbl.create 1000 in
  ov_run_jobs axis_jobs (fun k th -> Hashtbl.replace ax_tbl k th);
  let t1 = Unix.gettimeofday () in
  (* 3. pair, header and stage theorems *)
  let sem k = Hashtbl.find ov_sem_tbl k in
  let empty_thm (src, blk, key, rows) =
        (match cr_split ' ' (Hashtbl.find ov_ctx_raw key) with
           [_; ins; terms] ->
             let ins_tm = mk_list (List.map (fun i -> mk_small_numeral (int_of_string i))
                                     (cr_split ',' ins), `:num`) in
             let terms_tm = ov_terms_tm terms in
             let ev = ov_eval (list_mk_comb (`cr_empty_check`, [rows; ins_tm; terms_tm])) in
             let n = `n:cpose` in
             let th = MP (ISPECL [src; blk; ins_tm; terms_tm; n] OV_EMPTY_SOUND) ev in
             let th = GEN n (DISCH (mk_comb (mk_comb (`MEM:cpose->cpose list->bool`, n), nconst)) th) in
             MP (ISPECL [nconst; src; blk] OV_HDR_SOME) th
         | _ -> failwith "ov empty") in
  let empties = Hashtbl.create 3 in
  List.iter (fun (h, inf) -> match inf with
      Some (src, blk, key, rows, _, ["E"]) ->
        Hashtbl.replace empties key (empty_thm (src, blk, key, rows))
    | _ -> ()) hinfo;
  let hdr_thm (h, inf) = match inf with
      None -> let src, _ = dest_pair h in ISPECL [nconst; src] OV_HDR_NONE
    | Some (_, _, key, _, _, ["E"]) -> Hashtbl.find empties key
    | Some (src, blk, key, rows, a, ms) ->
        let pred = mk_comb (mk_comb (ov_cpo_c, src), blk) in
        let (semA, eA) = sem (key, a) in
        let angA = ov_angle_eq eA src in
        let pair (nk, (b, (_, np))) m =
          let (semB, eB) = sem (nk, b) in
          let angB = ov_angle_eq eB np in
          if m <> "A" then
            let (x, y, w) = ov_pt_tm m in
            MP (ISPECL [src; blk; np; eA; eB; x; y; w] OV_PAIR_PT)
               (end_itlist CONJ [semA; angA; semB; angB;
                                 Hashtbl.find ov_pt_tbl (key, a, m); Hashtbl.find ov_pt_tbl (nk, b, m)])
          else
            let (sem2, e2) = sem (key, b) and (sem3, e3) = sem (nk, a) in
            let ang2 = ov_angle_eq e2 np and ang3 = ov_angle_eq e3 src in
            MP (ISPECL [src; blk; np; eA; e2; e3; eB] OV_PAIR_AX)
               (end_itlist CONJ [semA; angA; sem2; ang2; sem3; ang3; semB; angB;
                                 Hashtbl.find ax_tbl (key, nk)]) in
        let pths = List.map2 pair nbrs ms in
        let all_th = itlist2 (fun np th acc ->
            MP (ISPECL [pred; np; rand (concl acc)] CR_ALL_CONS) (CONJ th acc))
          nposes pths (ISPEC pred CR_ALL_NIL) in
        let all_th = EQ_MP (AP_TERM (mk_comb (ov_all_cpose_c, pred)) (SYM ndef)) all_th in
        MP (ISPECL [nconst; src; blk] OV_HDR_SOME) (MATCH_MP OV_ALL_MEM all_th) in
  let hths = cr_parallel_map !ov_domains hdr_thm hinfo in
  let hpred = mk_comb (`ov_hdr_ok`, nconst) in
  let all_th = itlist2 (fun h th acc ->
      MP (ISPECL [hpred; h; rand (concl acc)] CR_ALL_CONS) (CONJ th acc))
    hdrs hths (ISPEC hpred CR_ALL_NIL) in
  let all_th = EQ_MP (AP_TERM (mk_comb (`ALL:(cpose#(crow list)option->bool)->(cpose#(crow list)option)list->bool`, hpred)) (SYM hdef)) all_th in
  let ov = MATCH_MP OV_BLOCK_OVERLAP all_th in
  let step = MP (c8_step_thm st) ov in
  let t2 = Unix.gettimeofday () in
  let nh = List.length (List.filter (fun (_, i) -> i <> None) hinfo) in
  Hashtbl.replace ov8_overlap_tbl st ov;
  Hashtbl.replace ov8_step_tbl st step;
  Hashtbl.replace ov8_stage_stats st (nh * List.length nids, nsem, npt, nax, t1 -. t0, t2 -. t1);
  Printf.printf "overlap C%s S%s: %d x %d pairs, %d entries, %d point and %d axis tests; eval %.1fs, assemble %.1fs\n%!"
    c st nh (List.length nids) nsem npt nax (t1 -. t0) (t2 -. t1);
  ov;;

let ov8_overlap_thm st = Hashtbl.find ov8_overlap_tbl st;;
let ov8_step_thm st = Hashtbl.find ov8_step_tbl st;;

let ov8_t0 = Unix.gettimeofday ();;
let OV8_STEPS = List.map (fun ((st, _, _, _, _) as s) ->
   if not (Hashtbl.mem ov8_step_tbl st) then ignore (ov8_build_step s);
   (st, ov8_step_thm st)) c8_steps;;

let () =
  let tot = ref (0, 0, 0, 0) in
  Hashtbl.iter (fun _ (p, e, pt, ax, _, _) ->
      let (p0, e0, pt0, ax0) = !tot in tot := (p0 + p, e0 + e, pt0 + pt, ax0 + ax)) ov8_stage_stats;
  let (p, e, pt, ax) = !tot in
  if List.exists (fun (_, th) -> hyp th <> []) OV8_STEPS then failwith "OV8_STEPS: hypotheses";
  Printf.printf "OV C898 STEPS: %d step theorems, %d pairs, %d support entries, %d point tests, %d axis tests, %.0fs\n%!"
    (List.length OV8_STEPS) p e pt ax (Unix.gettimeofday () -. ov8_t0);;
