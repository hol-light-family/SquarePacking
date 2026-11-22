(* ========================================================================= *)
(* The historical pair stages (Lean Cases/C{701,713,717,973,978,979}/        *)
(* DirectPruning/StepNN.lean, Stage.step_sound), design §4.1:               *)
(*   ck_stage_thm (case, step) :                                             *)
(*     |- cr_block_overlap hCK_sNN_hdrs (MAP cr_leaf hCK_dB_v)               *)
(*        ==> cr_pair_transition (MAP cr_leaf hCK_dA_v) (MAP cr_leaf hCK_dB_v) *)
(*                               (MAP cr_leaf hCK_dA_w)                      *)
(* Every plan is checked by evaluating cr_plan_check (CR_EVAL_CONV).         *)
(* ========================================================================= *)

needs "n12/cert/CR_HistData.ml";;

let cr_cplan_c = `CPlan` and cr_bhint_ty = `:cbhint` and cr_rlist_ty = `:crow list`;;
let cr_none_blk = `NONE:(crow list)option` and cr_some_blk = `SOME:crow list->(crow list)option`;;
let cr_none_tgt = `NONE:cpose option` and cr_some_tgt = `SOME:cpose->cpose option`;;

let cr_rh_tm s =
  let n i = mk_small_numeral (int_of_string i) in
  match s.[0] with
    'k' -> `RhConst`
  | 'c' -> mk_comb (`RhCopy`, n (String.sub s 1 (String.length s - 1)))
  | 's' -> mk_comb (`RhSingle`, n (String.sub s 1 (String.length s - 1)))
  | 'p' -> (match String.split_on_char '.' (String.sub s 1 (String.length s - 1)) with
              [i; j] -> mk_comb (mk_comb (`RhPair`, n i), n j)
            | _ -> failwith "cr_rh_tm")
  | _ -> failwith ("cr_rh_tm " ^ s);;

let cr_bh_tm s =
  match String.sub s 0 2 with
    "d:" -> mk_comb (`BhDirect`, cr_rh_tm (String.sub s 2 (String.length s - 2)))
  | "b:" -> mk_comb (`BhBlock`, mk_list (List.map cr_rh_tm
                (cr_split ',' (String.sub s 2 (String.length s - 2))), `:crhint`))
  | _ -> failwith ("cr_bh_tm " ^ s);;

(* one line of n12/data/cert/hist_plans/*.txt -> (plan term, src id, tgt id option) *)
let cr_plan_of_line l =
  let lhs_s, rhs_s = match String.index_opt l '|' with
      Some i -> String.sub l 0 i, String.sub l (i + 1) (String.length l - i - 1)
    | None -> failwith "plan line" in
  match cr_split ' ' lhs_s with
    [src; blk; tgt] ->
      let src = int_of_string src in
      let blk_tm =
        if blk = "B-" then cr_none_blk
        else mk_comb (cr_some_blk, cr_rows_tm (List.map int_of_string
                        (cr_split ',' (String.sub blk 2 (String.length blk - 2))))) in
      let tgt_tm, tgt = if tgt = "-" then cr_none_tgt, None
                        else let t = int_of_string tgt in mk_comb (cr_some_tgt, hp_tm t), Some t in
      let hints = List.map cr_bh_tm (cr_split ';' (String.trim rhs_s)) in
      (list_mk_comb (cr_cplan_c, [hp_tm src; blk_tm; tgt_tm; mk_list (hints, cr_bhint_ty)]),
       src, tgt)
  | _ -> failwith ("plan line: " ^ l);;

let cr_stage_plans (c, st) =
  List.map cr_plan_of_line (cr_read_lines (Printf.sprintf "n12/data/cert/hist_plans/C%s_S%s.txt" c st));;

(* |- MEM x l   for a literal list l containing x (structural, no evaluation) *)
let cr_mem_rule x l =
  let ty = type_of x in
  let rec go l =
    let h, t = dest_cons l in
    if h == x || aconv h x then ISPECL [x; t] CR_MEM_HEAD
    else MP (ISPECL [x; h; t] CR_MEM_TAIL) (go t) in
  ignore ty; go l;;

(* per-plan theorem  |- cr_plan_check plan  (evaluation) *)
let cr_plan_check_thm plan = cr_prove_by_eval [] (mk_comb (`cr_plan_check`, plan));;

let ck_stage_tbl : (string * string, thm) Hashtbl.t = Hashtbl.create 200;;
let ck_hdrs_tbl : (string * string, thm) Hashtbl.t = Hashtbl.create 200;;
let ck_stage_time : (string * string, float) Hashtbl.t = Hashtbl.create 200;;

(* evaluate the plan checks of a stage (nd domains), then assemble *)
let ck_build_stage nd (c, st, sdom, ndom, tdom, _) =
  let t0 = Unix.gettimeofday () in
  let plans = cr_stage_plans (c, st) in
  let sdef = hdom_def (c, sdom) and ndef = hdom_def (c, ndom) and tdef = hdom_def (c, tdom) in
  let pterms = List.map (fun (p, _, _) -> p) plans in
  let checks = cr_parallel_map nd cr_plan_check_thm pterms in
  let t1 = Unix.gettimeofday () in
  let tconst = lhs (concl tdef) and tlist = rhs (concl tdef) in
  let mem_t = AP_TERM `MEM:cpose->cpose list->bool` in
  let ok_thm (p, _, tgt) chk =
    let [src; blk; tg; hs] = snd (strip_comb p) in
    let tth = match tgt with
        None -> ISPECL [tconst; src; blk; hs] CR_TGT_NONE
      | Some _ ->
          let tgp = rand tg in
          let m = cr_mem_rule tgp tlist in
          let m' = EQ_MP (AP_TERM (mk_comb (`MEM:cpose->cpose list->bool`, tgp)) (SYM tdef)) m in
          MP (ISPECL [tconst; src; blk; tgp; hs] CR_TGT_SOME) m' in
    ignore mem_t;
    MP (ISPECL [tconst; p] CR_PLAN_OK_INTRO) (CONJ chk tth) in
  let oks = List.map2 ok_thm plans checks in
  let pred = mk_comb (`cr_plan_ok`, tconst) in
  let plist = mk_list (pterms, `:cplan`) in
  let all_th = itlist2 (fun p ok acc ->
      let t = rand (concl acc) in
      MP (ISPECL [pred; p; t] CR_ALL_CONS) (CONJ ok acc))
    pterms oks (ISPEC pred CR_ALL_NIL) in
  (* MAP cpl_source plans = Sd *)
  let msrc = PURE_REWRITE_CONV [MAP; cpl_source] (mk_icomb (mk_icomb (`MAP:(cplan->cpose)->cplan list->cpose list`, `cpl_source`), plist)) in
  let msrc = TRANS msrc (SYM sdef) in
  let stage_ok = MP (ISPECL [lhs (concl sdef); tconst; plist] CR_STAGE_OK_INTRO) (CONJ msrc all_th) in
  (* MAP cpl_header plans = hdrs *)
  let mh = PURE_REWRITE_CONV [MAP; cpl_header; cpl_source; cpl_block]
             (mk_icomb (mk_icomb (`MAP:(cplan->cpose#(crow list)option)->cplan list->(cpose#(crow list)option)list`, `cpl_header`), plist)) in
  let hname = Printf.sprintf "h%s_s%s_hdrs" c st in
  let hdef = cr_get_or_define hname (rhs (concl mh)) in
  let mh = TRANS mh (SYM hdef) in
  let nlist = mk_icomb (mk_icomb (`MAP:(cpose->pose_leaf)->cpose list->pose_leaf list`, `cr_leaf`), lhs (concl ndef)) in
  let th = MP (ISPECL [lhs (concl sdef); nlist; tconst; plist; lhs (concl hdef)] CR_STAGE_THM)
              (CONJ stage_ok mh) in
  let t2 = Unix.gettimeofday () in
  Hashtbl.replace ck_stage_tbl (c, st) th;
  Hashtbl.replace ck_hdrs_tbl (c, st) hdef;
  Hashtbl.replace ck_stage_time (c, st) (t1 -. t0);
  Printf.printf "stage C%s S%s: %d plans, eval %.1fs, assemble %.1fs\n%!" c st
    (List.length plans) (t1 -. t0) (t2 -. t1);
  th;;

let ck_stage_thm (c, st) = Hashtbl.find ck_stage_tbl (c, st);;
