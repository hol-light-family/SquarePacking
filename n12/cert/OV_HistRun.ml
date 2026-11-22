(* ========================================================================= *)
(* W-F345: the block-overlap theorems of all 113 historical pair stages     *)
(* (design §4.2) and the resulting Lean step_sound transitions:             *)
(*   ov_overlap_thm (case, step) :                                           *)
(*     |- cr_block_overlap hCK_sNN_hdrs (MAP cr_leaf hCK_dB_v)               *)
(*   ov_step_thm (case, step) :                                              *)
(*     |- cr_pair_transition (MAP cr_leaf hCK_dA_v) (MAP cr_leaf hCK_dB_v)   *)
(*                           (MAP cr_leaf hCK_dA_w)                          *)
(* Data (untrusted, n12/scripts/ov_oracle.py): n12/data/cert/ov_ctx.txt (support    *)
(* entries per context and angle), n12/data/cert/ov_pairs.txt (common point or  *)
(* axis test per pair).  Every support entry, point test and axis test is   *)
(* checked by evaluation (CR_EVAL_CONV) of the checkers of OV_Overlap.ml;   *)
(* the per-pair, per-header and per-stage theorems are assembled by MP.     *)
(* Compute's cost grows with the size of its input term, so every           *)
(* evaluation only sees one context's rows and one or a few entries.        *)
(* ========================================================================= *)

needs "n12/cert/OV_Overlap.ml";;
needs "n12/cert/CR_HistStages.ml";;

let ov_domains = ref 12;;

(* ---- raw data ---- *)
let ov_ctx_raw : (string, string) Hashtbl.t = Hashtbl.create 20000;;
let () =
  List.iter (fun l -> match String.index_opt l '|' with
      Some i -> Hashtbl.replace ov_ctx_raw (String.trim (String.sub l 0 i))
                  (String.trim (String.sub l (i + 1) (String.length l - i - 1)))
    | None -> ()) (cr_read_lines "n12/data/cert/ov_ctx.txt");;

(* stage -> method lines (one per header with a block, plan order) *)
let ov_pairs_raw : (string * string, string list) Hashtbl.t = Hashtbl.create 200;;
let () =
  let cur = ref None and acc = ref [] in
  let flush () = match !cur with
      Some k -> Hashtbl.replace ov_pairs_raw k (List.rev !acc) | None -> () in
  List.iter (fun l ->
      if String.length l > 1 && l.[0] = 'S' && l.[1] = ' ' then
        (flush (); acc := [];
         match cr_split ' ' l with
           [_; c; st; _; _] -> cur := Some (c, st)
         | _ -> failwith "ov_pairs")
      else if l <> "" then acc := l :: !acc) (cr_read_lines "n12/data/cert/ov_pairs.txt");
  flush ();;

(* ---- term builders (main domain only) ---- *)
let ov_terms_tm s =
  mk_list (List.map (fun t -> match String.split_on_char '@' t with
      [w; i] -> mk_pair (cr_int_tm w, mk_small_numeral (int_of_string i))
    | _ -> failwith "ov term") (cr_split '+' s), `:int#num`);;

let ov_sup_c = `OvSup` and ov_ang_c = `OvAng`;;
(* k,kr,er,sr,terms -> (OvSup kr er sr, (k, terms)) *)
let ov_sup_tm s =
  match String.split_on_char ',' s with
    [k; kr; er; sr; terms] ->
      list_mk_comb (ov_sup_c, [cr_int_tm kr; cr_int_tm er; if sr = "1" then `true` else `false`]),
      mk_pair (cr_int_tm k, ov_terms_tm terms)
  | _ -> failwith ("ov sup " ^ s);;

(* the entries of a context line: angle -> (entry term, cert term) *)
let ov_entries_of_string s =
  List.map (fun part ->
      match String.index_opt part ':' with
        Some i ->
          let a = int_of_string (String.sub part 0 i) in
          let sups = List.map ov_sup_tm
              (String.split_on_char '/' (String.sub part (i + 1) (String.length part - i - 1))) in
          (match sups with
             [(s0, c0); (s1, c1); (s2, c2); (s3, c3)] ->
               a, (list_mk_comb (ov_ang_c, [mk_small_numeral a; ov_ref_tms.(a); s0; s1; s2; s3]),
                   mk_pair (c0, mk_pair (c1, mk_pair (c2, c3))))
           | _ -> failwith "ov 4 sups")
      | None -> failwith "ov ang") (cr_split ';' s);;

let ov_entries_tbl : (string, (int * (term * term)) list) Hashtbl.t = Hashtbl.create 20000;;
let ov_entries key =
  try Hashtbl.find ov_entries_tbl key with Not_found ->
    let l = ov_entries_of_string (Hashtbl.find ov_ctx_raw key) in
    Hashtbl.add ov_entries_tbl key l; l;;
let ov_entry key a = fst (List.assoc a (ov_entries key));;

let ov_pt_tm =
  let tbl = Hashtbl.create 10000 in
  fun s -> try Hashtbl.find tbl s with Not_found ->
    let t = match String.split_on_char ',' s with
        [x; y; w] -> (cr_int_tm x, cr_int_tm y, cr_int_tm w)
      | _ -> failwith "ov point" in
    Hashtbl.add tbl s t; t;;

(* ---- caches of checked facts ---- *)
(* (key, angle) -> |- ov_ang_sem rws e, e *)
let ov_sem_tbl : (string * int, thm * term) Hashtbl.t = Hashtbl.create 200000;;
(* (key, angle, point) -> |- ov_pt_ok e X Y W *)
let ov_pt_tbl : (string * int * string, thm) Hashtbl.t = Hashtbl.create 400000;;

(* constants used inside worker domains (no parsing there) *)
let ov_ova_angle_c = `ova_angle` and ov_cp_angle_c = `cp_angle`;;
let ov_cpo_c = `cr_pair_overlaps`;;
let ov_all_cpose_c = `ALL:(cpose->bool)->cpose list->bool`;;

let ov_angle_eq e pose =
  TRANS (PURE_ONCE_REWRITE_CONV [ova_angle] (mk_comb (ov_ova_angle_c, e)))
        (SYM (PURE_ONCE_REWRITE_CONV [cp_angle] (mk_comb (ov_cp_angle_c, pose))));;

let ov_eval tm = cr_prove_by_eval [] tm;;

(* evaluate (key, term) jobs in parallel, store the theorems (main domain) *)
let ov_run_jobs jobs store =
  let ths = cr_parallel_map !ov_domains (fun (_, tm) -> ov_eval tm) jobs in
  List.iter2 (fun (k, _) th -> store k th) jobs ths;;

(* ---- one stage ---- *)
let ov_overlap_tbl : (string * string, thm) Hashtbl.t = Hashtbl.create 200;;
let ov_step_tbl : (string * string, thm) Hashtbl.t = Hashtbl.create 200;;
let ov_stage_stats : (string * string, int * int * int * int * float * float) Hashtbl.t =
  Hashtbl.create 200;;

let ov_append_c = `APPEND:crow list->crow list->crow list`;;

let ov_build_stage (c, st, sdom, ndom, tdom, _) =
  let t0 = Unix.gettimeofday () in
  let hdef = Hashtbl.find ck_hdrs_tbl (c, st) in
  let ndef = hdom_def (c, ndom) in
  let nconst = lhs (concl ndef) in
  let nids = Hashtbl.find hist_domain_ids (c, ndom) in
  let nposes = dest_list (rhs (concl ndef)) in
  let hdrs = dest_list (rhs (concl hdef)) in
  let plan_lines = cr_read_lines (Printf.sprintf "n12/data/cert/hist_plans/C%s_S%s.txt" c st) in
  let meth_lines = ref (try Hashtbl.find ov_pairs_raw (c, st) with Not_found -> []) in
  (* headers: (header, None | Some (src, blk, key, rows, src angle, methods)) *)
  let hinfo = List.map2 (fun h pl ->
      let src, blko = dest_pair h in
      match cr_split ' ' (String.sub pl 0 (String.index pl '|')) with
        [sid; b; _] when b <> "B-" ->
          let ml = (match !meth_lines with x :: r -> meth_lines := r; x
                                         | [] -> failwith "ov: missing method line") in
          let blk = rand blko in
          let rows = mk_comb (mk_comb (ov_append_c, mk_comb (`cp_rows`, src)), blk) in
          let a = fst (Hashtbl.find hist_poses_raw (int_of_string sid)) in
          h, Some (src, blk, sid ^ " " ^ b, rows, a, cr_split ' ' ml)
      | _ -> h, None) hdrs plan_lines in
  if !meth_lines <> [] then failwith "ov: extra method lines";
  let nkeys = List.map (fun i -> string_of_int i ^ " B-") nids in
  let nangs = List.map (fun i -> fst (Hashtbl.find hist_poses_raw i)) nids in
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
  let step = MP (ck_stage_thm (c, st)) ov in
  let t2 = Unix.gettimeofday () in
  let nh = List.length (List.filter (fun (_, i) -> i <> None) hinfo) in
  Hashtbl.replace ov_overlap_tbl (c, st) ov;
  Hashtbl.replace ov_step_tbl (c, st) step;
  Hashtbl.replace ov_stage_stats (c, st) (nh * List.length nids, nsem, npt, nax, t1 -. t0, t2 -. t1);
  Printf.printf "overlap C%s S%s: %d x %d pairs, %d entries, %d point and %d axis tests; eval %.1fs, assemble %.1fs\n%!"
    c st nh (List.length nids) nsem npt nax (t1 -. t0) (t2 -. t1);
  ov;;

let ov_overlap_thm (c, st) = Hashtbl.find ov_overlap_tbl (c, st);;
let ov_step_thm (c, st) = Hashtbl.find ov_step_tbl (c, st);;
