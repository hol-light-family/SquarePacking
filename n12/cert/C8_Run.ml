(* ========================================================================= *)
(* W-C898, part 4: builds the 13 C898 pair-step theorems (§4.1 shape, block   *)
(* overlap premise left to W-F345) and the fused chord theorem C8_FUSED.     *)
(*   c8_step_thm "NN" : |- cr_block_overlap c898_sNN_hdrs (MAP cr_leaf c898_dN) *)
(*        ==> cr_pair_transition (MAP cr_leaf c898_dS) (MAP cr_leaf c898_dN)  *)
(*                               (MAP cr_leaf c898_dT)                       *)
(*   C8_FUSED : |- c8_fused_transition (MAP cr_leaf c898_d5_0)                *)
(*        (MAP cr_leaf c898_d0_9) (MAP cr_leaf c898_d7_7) (MAP cr_leaf c898_d11_0) *)
(*        (MAP cr_leaf c898_d3_3) (MAP cr_leaf c898_d6_5) (MAP cr_leaf c898_d9_8)  *)
(*        (MAP cr_leaf c898_d5_11)                                           *)
(* ========================================================================= *)

needs "n12/cert/C8_Fused.ml";;

let c8_domains = ref 8;;
let c8_t0 = Unix.gettimeofday ();;
let C8_STEPS = List.map (fun ((st,_,_,_,_) as s) ->
   (st, if Hashtbl.mem c8_step_tbl st then Hashtbl.find c8_step_tbl st
        else c8_build_step !c8_domains s)) c8_steps;;
Printf.printf "C898 STEPS: %d theorems, %d links, %.1fs\n%!" (List.length C8_STEPS)
  (Hashtbl.length c8_link_thm_tbl) (Unix.gettimeofday () -. c8_t0);;

(* ---- fused chord ---- *)
let c8_fused_lines = cr_read_lines "n12/data/cert/c898_fused.txt";;
let c8_win side = match List.find (fun l -> match cr_split ' ' l with
      "W" :: s :: _ -> s = side | _ -> false) c8_fused_lines |> cr_split ' ' with
    [_; _; ln; ld; hn; hd] -> ch_win_tm false (ln, ld, hn, hd)
  | _ -> failwith "c8_win";;
let c8_wl = c8_win "left" and c8_wr = c8_win "right";;

let c8_fused_nbrs side c =
  List.concat (List.map (fun l -> match String.split_on_char '|' l with
      [lhs_s; hs] -> (match cr_split ' ' lhs_s with
         ["N"; sd; cc; src; k; rl; rh] when sd = side && int_of_string cc = c ->
           [list_mk_comb (`ChNbr`, [c8p_tm (int_of_string src); ch_num k; ch_row_tm rl;
                                    ch_row_tm rh; ch_hints_tm hs])]
       | _ -> [])
    | _ -> []) c8_fused_lines);;

let c8_fused_plans =
  List.concat (List.map (fun l -> match String.split_on_char '|' l with
      [lhs_s; hs] -> (match cr_split ' ' lhs_s with
         ["F"; src; k; lc; uc; cl; tg] ->
           let tgt = if tg = "-" then `NONE:cpose option`
                     else mk_comb (`SOME:cpose->cpose option`, c8p_tm (int_of_string tg)) in
           [list_mk_comb (`C8FPlan`, [c8p_tm (int_of_string src); ch_num k; ch_row_tm lc;
              ch_row_tm uc; ch_row_tm cl; tgt; ch_hints_tm hs])]
       | _ -> [])
    | _ -> []) c8_fused_lines);;

let c8_fused_doms = match List.find (fun l -> l.[0] = 'D') c8_fused_lines |> cr_split ' ' with
    "D" :: ds -> ds | _ -> failwith "D";;

let C8_FUSED =
  let t0 = Unix.gettimeofday () in
  let [sd; d1; d2; d3; e1; e2; e3; td] = c8_fused_doms in
  let nl = List.map (c8_fused_nbrs "left") [0; 1; 2] and nr = List.map (c8_fused_nbrs "right") [0; 1; 2] in
  let lchk = mk_comb (`ch_nbr_check`, c8_wl) and rchk = mk_comb (`ch_nbr_check`, c8_wr) in
  let pchk = list_mk_comb (`c8f_plan_check`, [c8_wl; c8_wr]) in
  let items = List.map (fun t -> mk_comb (lchk, t)) (List.concat nl) @
              List.map (fun t -> mk_comb (rchk, t)) (List.concat nr) @
              List.map (fun t -> mk_comb (pchk, t)) c8_fused_plans in
  let ths = cr_parallel_map !c8_domains (cr_prove_by_eval []) items in
  let t1 = Unix.gettimeofday () in
  let rec take k l = if k = 0 then [], l else match l with
      h :: t -> let a, b = take (k - 1) t in h :: a, b | [] -> failwith "take" in
  let rest = ref ths in
  let next l = let a, b = take (List.length l) !rest in rest := b; a in
  let allsl = List.map (fun l -> ch_all_rule lchk (next l)) nl in
  let allsr = List.map (fun l -> ch_all_rule rchk (next l)) nr in
  let pths = !rest in
  let sdef = c8dom_def sd and tdef = c8dom_def td in
  let tconst = lhs (concl tdef) in
  let okpred = list_mk_comb (`c8f_plan_ok`, [c8_wl; c8_wr; tconst]) in
  let ok_thm p chk =
    let tl = PURE_REWRITE_CONV [c8f_targets; ch_opt_list] (mk_comb (`c8f_targets`, p)) in
    let allm, pred = ch_all_mem tdef (rhs (concl tl)) in
    let allm = EQ_MP (SYM (AP_TERM (mk_comb (`ALL:(cpose->bool)->cpose list->bool`, pred)) tl)) allm in
    EQ_MP (SYM (REWRITE_CONV [c8f_plan_ok] (mk_comb (okpred, p)))) (CONJ chk allm) in
  let allp = ch_all_rule okpred (List.map2 ok_thm c8_fused_plans pths) in
  let plist = mk_list (c8_fused_plans, `:c8fplan`) in
  let msrc = ch_map_eq `c8f_src` [c8f_src] sdef plist in
  let num_fact tm = prove (tm, REWRITE_TAC[chw_hz; chw_lo; chw_hi; ch_q; int_of_num_th] THEN
                               CONV_TAC REAL_RAT_REDUCE_CONV) in
  let wl = c8_wl and wr = c8_wr in
  let side = List.map num_fact
    [mk_neg (mk_comb (`chw_hz`, wl)); mk_neg (mk_comb (`chw_hz`, wr));
     mk_binop `(<=):real->real->bool` (mk_comb (`chw_lo`, wl)) (mk_comb (`chw_hi`, wl));
     mk_binop `(<=):real->real->bool` (mk_comb (`chw_lo`, wr)) (mk_comb (`chw_hi`, wr));
     mk_binop `(<=):real->real->bool` (mk_comb (`chw_lo`, wl)) `&6397 / &4000`;
     mk_binop `(<=):real->real->bool` `&9603 / &4000` (mk_comb (`chw_hi`, wr))] in
  let lists = List.map (fun l -> mk_list (l, `:chnbr`)) (nl @ nr) in
  let th = MP (ISPECL ([wl; wr] @ lists @ [plist; lhs (concl sdef); tconst]) C8_FUSED_SOUND)
              (end_itlist CONJ (side @ allsl @ allsr @ [allp; msrc])) in
  let meqs = List.map2 (fun l d -> ch_map_eq `chn_src` [chn_src] (c8dom_def d) l)
               lists [d1; d2; d3; e1; e2; e3] in
  let th = PURE_REWRITE_RULE meqs th in
  Printf.printf "C898 fused chord: %d plans, %d neighbours, eval %.1fs, assemble %.1fs\n%!"
    (List.length c8_fused_plans) (List.length (List.concat (nl @ nr))) (t1 -. t0)
    (Unix.gettimeofday () -. t1);
  th;;
Printf.printf "W-C898 (independent parts) done: %.1fs\n%!" (Unix.gettimeofday () -. c8_t0);;

(* the links not used by any step (Lean checks all 927 entries; so do we) *)
let () =
  let rest = List.filter (fun i -> not (Hashtbl.mem c8_link_thm_tbl i)) (0--926) in
  let goals = List.map (fun i -> let a, b = dest_pair (c8_link_tm i) in let t, h = dest_pair b in
      list_mk_comb (`cr_relax_check`, [a; t; h])) rest in
  let ths = cr_parallel_map !c8_domains (cr_prove_by_eval []) goals in
  List.iter2 (fun i th -> Hashtbl.replace c8_link_thm_tbl i th) rest ths;
  Printf.printf "C898 links checked: %d (%d not used by a step)\n%!"
    (Hashtbl.length c8_link_thm_tbl) (List.length rest);;
let c8_link_thm i = Hashtbl.find c8_link_thm_tbl i;;
Printf.printf "W-C898 total: %.1fs\n%!" (Unix.gettimeofday () -. c8_t0);;
