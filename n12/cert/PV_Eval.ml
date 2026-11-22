(* ========================================================================= *)
(* W-F6, part 3: evaluation of the initial-cover roots and the owner         *)
(* theorems CK_INITIAL (design §4.3).                                        *)
(* Data: n12/data/cert/pv_owners.txt, pv_roots.txt (n12/scripts/pv_extract.py,        *)
(*       n12/scripts/pv_oracle.py; untrusted, everything is re-checked here).    *)
(* OCaml API:                                                                *)
(*   pv_root_tm (case, owner, angle)  : term  PvRoot ...                     *)
(*   pv_owner_thm nd (case, owner)    : thm   (CK_INITIAL of that owner)     *)
(*   pv_initial_tbl                   : (case, owner) -> thm                 *)
(* ========================================================================= *)

needs "n12/cert/PV_Root.ml";;
needs "n12/cert/PV_Fast.ml";;
needs "n12/cert/CR_HistData.ml";;

(* ------------------------------------------------------------------------- *)
(* Compset extension: the PV_ checker equations, the explicit pose-input     *)
(* rows, and rational real arithmetic (for comparing Lean's forms).          *)
(* ------------------------------------------------------------------------- *)

let PV_NIL_EQ = prove (`(([]:A list) = []) <=> true`, REWRITE_TAC[]);;

let pv_nochange conv tm =
  let th = conv tm in
  if aconv (rhs (concl th)) tm then failwith "pv_nochange" else th;;

let pv_eval_thms =
  [pvr_wxcheck; pv_wfast; pv_filter2; pv_active2; pv_lx2_check; pv_xtri; pv_xrow; pv_wpc; pv_wit_x;
   pvr_xcheck; pv_box; EX; pv_fast; pv_filter; pv_active; pv_lx_check; pv_tri; pv_row; pv_pc;
   pv_det; pv_vtx; pv_base_ok; pv_blk_pos; pv_blks_ok; pv_veval; pv_target_rows;
   pv_strict_ok; pv_res_angle; pv_inputs; pv_forbidden; pv_point_rows; pv_wall_rows;
   pv_decode; cr_normalized; outer_ref; ae_reference; lflat;
   ae_lower; ae_upper; ae_c; ae_s; ae_outer; ae_inner; ae_wall;
   injectivity "lincon"; injectivity "affine"; int_of_num_th; int_neg_th; PV_NIL_EQ];;

let pv_eval_convs =
  [`(+):real->real->real`,2,pv_nochange REAL_RAT_ADD_CONV;
   `(-):real->real->real`,2,pv_nochange REAL_RAT_SUB_CONV;
   `( * ):real->real->real`,2,pv_nochange REAL_RAT_MUL_CONV;
   `(/):real->real->real`,2,pv_nochange REAL_RAT_DIV_CONV;
   `(--):real->real`,1,pv_nochange REAL_RAT_NEG_CONV;
   `(=):real->real->bool`,2,REAL_RAT_EQ_CONV];;

let () =
  let new_thms = List.filter (fun th -> not (List.exists (fun t -> concl t = concl th) !cr_extra_thms))
                   pv_eval_thms in
  let new_convs = List.filter (fun (c, n, _) ->
                    not (List.exists (fun (c', n', _) -> c' = c && n' = n) !cr_extra_convs)) pv_eval_convs in
  if new_thms <> [] || new_convs <> [] then begin
    cr_extra_thms := !cr_extra_thms @ new_thms;
    cr_extra_convs := !cr_extra_convs @ new_convs;
    cr_cs_reset ()
  end;;

(* ------------------------------------------------------------------------- *)
(* Data                                                                       *)
(* ------------------------------------------------------------------------- *)

let pv_rat_tm s =
  match String.split_on_char ':' s with
    [p; q] -> term_of_rat (Num.num_of_string p // Num.num_of_string q)
  | _ -> failwith ("pv_rat_tm " ^ s);;

let pv_pts_tm s =
  let pts = if s = "-" then [] else cr_split ';' s in
  mk_list (List.map (fun p -> match cr_split ',' p with
      [x; y] -> mk_pair (pv_rat_tm x, pv_rat_tm y)
    | _ -> failwith "pv_pts_tm") pts, `:real#real`);;

(* owners: (case, owner) -> (grid, inside term, outside term) *)
let pv_owners : (string * int, int * term * term) Hashtbl.t = Hashtbl.create 100;;
let pv_owner_list = ref ([] : (string * int) list);;
let pv_load_owners file =
  List.fold_left (fun acc l -> match cr_split ' ' l with
      [c; k; g; ins; outs] ->
        let key = (c, int_of_string k) in
        Hashtbl.replace pv_owners key (int_of_string g, pv_pts_tm ins, pv_pts_tm outs);
        acc @ [key]
    | _ -> acc) [] (cr_read_lines file);;
let () = pv_owner_list := pv_load_owners "n12/data/cert/pv_owners.txt";;

let pv_rd_tm s =
  match cr_split ',' s with
    [x; y; c; st; d] ->
      mk_pair (cr_row_of_strings (x, y, c, st = "1"), mk_numeral (Num.num_of_string d))
  | _ -> failwith ("pv_rd_tm " ^ s);;

let pv_rd_ty = `:crow#num`;;
let pv_plan_ty = `:(num#int#int)option`;;
let pv_some_plan = `SOME:num#int#int->(num#int#int)option`;;
let pv_none_plan = `NONE:(num#int#int)option`;;
let pv_some_pose = `SOME:cpose->cpose option`;;
let pv_none_pose = `NONE:cpose option`;;
let pv_root_c = `PvRoot`;;

let pv_plan_item s =
  if s = "." then pv_none_plan else
  match cr_split ':' s with
    [i; sc; m] -> mk_comb (pv_some_plan,
                    mk_pair (mk_small_numeral (int_of_string i), mk_pair (cr_int_tm sc, cr_int_tm m)))
  | _ -> failwith "pv_plan_item";;

let pv_lx_ty = `:pvlx option` and pv_wit_ty = `:pvwit` and pv_wits_ty = `:pvwit list`;;
let pv_some_lx = `SOME:pvlx->pvlx option` and pv_none_lx = `NONE:pvlx option`;;
let pv_lx_c = `PvLx` and pv_wbase_c = `PwBase` and pv_wblock_c = `PwBlock` and pv_wtargets = `PwTargets`;;

let pv_plan2_item s =
  if s = "." then pv_none_lx else
  match cr_split ':' s with
    [i; j; li; lj; mu] -> mk_comb (pv_some_lx, list_mk_comb (pv_lx_c,
        [mk_small_numeral (int_of_string i); mk_small_numeral (int_of_string j);
         cr_int_tm li; cr_int_tm lj; cr_int_tm mu]))
  | _ -> failwith "pv_plan2_item";;

let pv_wit_item s =
  if s = "t" then pv_wtargets
  else let n = mk_small_numeral (int_of_string (String.sub s 1 (String.length s - 1))) in
       if s.[0] = 'b' then mk_comb (pv_wbase_c, n)
       else if s.[0] = 'k' then mk_comb (pv_wblock_c, n) else failwith "pv_wit_item";;

let pv_wits_tm s =
  mk_list (List.map (fun row -> mk_list (List.map pv_wit_item (cr_split ',' row), pv_wit_ty))
             (String.split_on_char '/' s), pv_wits_ty);;

(* roots: (case, owner) -> list of (angle, root term, fast-route data) in Lean order *)
let pv_roots : (string * int, (int * term * (term * term) option) list) Hashtbl.t = Hashtbl.create 100;;
let pv_load_roots file pose_tm =
  let keys = ref [] in
  List.iter (fun l ->
    let fields = List.map String.trim (String.split_on_char '|' l) in
    let fields, fast = match fields with
        [hd; base; forb; plan; tgt; plan2; wits] ->
          [hd; base; forb; plan; tgt],
          Some (mk_list (List.map pv_plan2_item (cr_split ';' plan2), pv_lx_ty),
                (if wits = "" then mk_list ([], pv_wits_ty) else pv_wits_tm wits))
      | _ -> fields, None in
    match fields with
      [hd; base; forb; plan; tgt] ->
        (match cr_split ' ' hd with
           [c; k; a] ->
             let a = int_of_string a in
             let base_tm = mk_list (List.map pv_rd_tm (cr_split ';' base), pv_rd_ty) in
             let forb_tm =
               mk_list ((if forb = "-" then [] else
                          List.map (fun b -> mk_list (List.map pv_rd_tm (cr_split ';' b), pv_rd_ty))
                            (cr_split '/' forb)), `:(crow#num)list`) in
             let plan_tm = mk_list (List.map pv_plan_item (cr_split ';' plan), pv_plan_ty) in
             let res_tm = if tgt = "-" then pv_none_pose
                          else mk_comb (pv_some_pose, pose_tm (int_of_string tgt)) in
             let r = list_mk_comb (pv_root_c, [mk_small_numeral a; base_tm; forb_tm; res_tm; plan_tm]) in
             let key = (c, int_of_string k) in
             let old = try Hashtbl.find pv_roots key with Not_found -> (keys := key :: !keys; []) in
             Hashtbl.replace pv_roots key ((a, r, fast) :: old)
         | _ -> failwith "pv_roots header")
    | _ -> ()) (cr_read_lines file);
  List.iter (fun key -> Hashtbl.replace pv_roots key (List.rev (Hashtbl.find pv_roots key))) !keys;;
let () = pv_load_roots "n12/data/cert/pv_roots.txt" hp_tm;;

(* initial domain definition of an owner (|- hCASE_dK_0 = [..]); other dictionaries
   (C898) register their own function here *)
let pv_dom_defs : (string, int -> thm) Hashtbl.t = Hashtbl.create 10;;
let pv_dom_def (c, k) =
  try Hashtbl.find pv_dom_defs c k with Not_found -> hdom_def (c, string_of_int k ^ "_0");;

let pv_root_tm (c, k, a) =
  let (_, r, _) = List.find (fun (b, _, _) -> b = a) (Hashtbl.find pv_roots (c, k)) in r;;

(* |- s12_angles a = AngleEnc ... *)
let pv_angle_th =
  let conv = REWRITE_CONV[s12_angles] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[AD64_EL; AD128_EL] in
  Array.init 192 (fun a ->
    let th = conv (mk_comb (`s12_angles`, mk_small_numeral a)) in
    if can (find_term ((=) `EL:num->angle_enc list->angle_enc`)) (rhs (concl th))
    then failwith "pv_angle_th" else th);;

(* ------------------------------------------------------------------------- *)
(* One root: |- pvr_check R I O   (evaluation; may run in a worker domain)    *)
(* ------------------------------------------------------------------------- *)

let pv_xcheck_c = `pvr_xcheck`;;
let pv_lt_c = `(<):num->num->bool` and pv_192 = `192` and pv_T = `true`;;

let pv_wxcheck_c = `pvr_wxcheck`;;

let pv_root_thm ins outs (a, r, fast) =
  let ath = pv_angle_th.(a) in
  let w = rhs (concl ath) in
  let tm = match fast with
      None -> list_mk_comb (pv_xcheck_c, [w; r; ins; outs])
    | Some (plan2, wits) -> list_mk_comb (pv_wxcheck_c, [w; r; ins; outs; plan2; wits]) in
  let th = CR_EVAL_CONV tm in
  if rhs (concl th) <> pv_T then failwith (Printf.sprintf "pv_root_thm: angle %d does not evaluate to T" a) else
  let xth = MATCH_MP (if fast = None then PVR_XCHECK_SOUND else PVR_WXCHECK_SOUND) (EQT_ELIM th) in
  let lt = EQT_ELIM (NUM_LT_CONV (mk_binop pv_lt_c (mk_small_numeral a) pv_192)) in
  MATCH_MP PVR_CHECK_INTRO (CONJ lt (CONJ ath xth));;

(* ------------------------------------------------------------------------- *)
(* One owner: CK_INITIAL (design §4.3)                                       *)
(*  |- !c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\                 *)
(*        a <= &1001 / &1000 /\ lcont c s u v a /\                          *)
(*        linside c s u v a x1 y1 /\ ... /\ ~linside c s u v a x1' y1' /\ ...*)
(*        ==> oriented_pose_covered (MAP cr_leaf hCASE_dK_0) c s u v a       *)
(* Lean: CK_Entry.ownerK_cover's geometric part, i.e.                        *)
(*   DirectPoseCover.Owner.oriented_sound ownerK ownerK_checked              *)
(*   + ownerK_leaves_shared  (OrientedPoseCovered continuousScoutCKDomainK_0)*)
(* ------------------------------------------------------------------------- *)

let pv_all_nil = CONJUNCT1 pv_all_check and pv_all_cons = CONJUNCT2 pv_all_check;;

let pv_all_c = `pv_all_check`;;
let pv_all_rule ins outs ths =
  let nilt = list_mk_comb (pv_all_c, [ins; outs; mk_list ([], `:pvroot`)]) in
  let nil_th = EQT_ELIM (PART_MATCH lhs pv_all_nil nilt) in
  List.fold_right (fun th acc ->
      let r = rand (rator (rator (concl th))) in
      let rs = rand (concl acc) in
      let eq = PART_MATCH lhs pv_all_cons
                 (list_mk_comb (pv_all_c, [ins; outs; mk_cons r rs])) in
      EQ_MP (SYM eq) (CONJ th acc)) ths nil_th;;

(* |- MAP (\r. s12_angles (pvr_angle r)) roots = angles64 / angles128
   (spine conversions: never traverse the root data) *)
let pv_angle_nil, pv_angle_cons = CONJ_PAIR PV_MAP_ANGLE_CONS;;
let rec pv_angle_spine tm =
  (REWR_CONV pv_angle_nil ORELSEC
   (REWR_CONV pv_angle_cons THENC
    COMB2_CONV (RAND_CONV (fun t -> pv_angle_th.(dest_small_numeral (rand t)))) pv_angle_spine)) tm;;

let pv_map_angle_c = `MAP:(pvroot->angle_enc)->pvroot list->angle_enc list`;;
let pv_angle_lam = `\r. s12_angles (pvr_angle r)`;;
let pv_cov_c = `covers_interval (&0) (&1)`;;

let pv_cover_th grid roots_tm =
  let tm = mk_comb (mk_comb (pv_map_angle_c, pv_angle_lam), roots_tm) in
  let th1 = pv_angle_spine tm in
  let def = if grid = 64 then angles64 else angles128 in
  let cov = if grid = 64 then ANGLES64_COVER else ANGLES128_COVER in
  if not (aconv (rhs (concl th1)) (rhs (concl def))) then failwith "pv_cover_th: angle list" else
  let eq = TRANS th1 (SYM def) in
  EQ_MP (SYM (AP_TERM pv_cov_c eq)) cov;;

(* |- lflat (MAP (\r. pv_leaves (pvr_result r)) roots) = hCASE_dK_0 *)
let pv_flat_nil, pv_flat_some, pv_flat_none =
  let a, b = CONJ_PAIR PV_FLAT_CONS in let b, c = CONJ_PAIR b in a, b, c;;
let rec pv_flat_spine tm =
  (REWR_CONV pv_flat_nil ORELSEC
   (REWR_CONV pv_flat_some THENC RAND_CONV pv_flat_spine) ORELSEC
   (REWR_CONV pv_flat_none THENC pv_flat_spine)) tm;;

let pv_lflat_c = `lflat:(cpose list)list->cpose list`;;
let pv_map_leaves_c = `MAP:(pvroot->cpose list)->pvroot list->(cpose list)list`;;
let pv_leaves_lam = `\r. pv_leaves (pvr_result r)`;;

let pv_flat_th (c, k) roots_tm =
  let tm = mk_comb (pv_lflat_c, mk_comb (mk_comb (pv_map_leaves_c, pv_leaves_lam), roots_tm)) in
  let th1 = pv_flat_spine tm in
  let def = pv_dom_def (c, k) in
  if not (aconv (rhs (concl th1)) (rhs (concl def))) then failwith "pv_flat_th: domain mismatch" else
  TRANS th1 (SYM def);;

let pv_mem_conv = REWRITE_CONV[ALL_MEM; ALL; FST; SND] THENC REWRITE_CONV[];;

let pv_initial_tbl : (string * int, thm) Hashtbl.t = Hashtbl.create 100;;

(* number of OCaml domains for the root evaluation (memory: keep <= 8) *)
let pv_hist_domains = ref 8;;

let pv_owner_assemble (c, k) ths =
  let t1 = Unix.gettimeofday () in
  let (grid, ins, outs) = Hashtbl.find pv_owners (c, k) in
  let roots = Hashtbl.find pv_roots (c, k) in
  let roots_tm = mk_list (List.map (fun (_, r, _) -> r) roots, `:pvroot`) in
  let all_th = pv_all_rule ins outs ths in
  let cov_th = pv_cover_th grid roots_tm in
  let flat = pv_flat_th (c, k) roots_tm in
  (* (no rewriting with flat: a net over its huge left-hand side overflows the stack) *)
  let th = MP (ISPECL [roots_tm; ins; outs; rhs (concl flat)] PV_OWNER_THM_D)
              (CONJ cov_th (CONJ all_th flat)) in
  let insv = `ins:(real#real)list` and outsv = `outs:(real#real)list` in
  let pin = `forall P. MEM P ins ==> linside c s u v a (FST P) (SND P)` in
  let pout = `forall P. MEM P outs ==> ~linside c s u v a (FST P) (SND P)` in
  let ein = pv_mem_conv (subst [ins, insv] pin) and eout = pv_mem_conv (subst [outs, outsv] pout) in
  let th = PURE_REWRITE_RULE[ein; eout] th in
  let th = PURE_REWRITE_RULE[GSYM CONJ_ASSOC] th in
  Printf.printf "CK_INITIAL %s owner %d: %d roots, assembly %.1fs\n%!" c k
    (List.length roots) (Unix.gettimeofday () -. t1);
  Hashtbl.replace pv_initial_tbl (c, k) th; th;;

let pv_owner_thm nd (c, k) =
  let t0 = Unix.gettimeofday () in
  let (_, ins, outs) = Hashtbl.find pv_owners (c, k) in
  let roots = Hashtbl.find pv_roots (c, k) in
  ignore (CR_EVAL_CONV `pv_det (CRow (&1) (&2) (&3) false) (CRow (&3) (&4) (&5) true)`);
  let ths = cr_parallel_map nd (pv_root_thm ins outs) roots in
  Printf.printf "roots of %s owner %d: eval %.1fs\n%!" c k (Unix.gettimeofday () -. t0);
  pv_owner_assemble (c, k) ths;;

(* all owners at once: one Domain pool over all roots (longest first), then assembly *)
let pv_all_owners nd keys =
  let t0 = Unix.gettimeofday () in
  let items = List.concat_map (fun key ->
      let (_, ins, outs) = Hashtbl.find pv_owners key in
      List.mapi (fun i root -> (key, i, ins, outs, root)) (Hashtbl.find pv_roots key)) keys in
  let size (_, _, _, _, (_, r, f)) = match f with
      Some (_, w) -> List.fold_left (fun n l -> n + List.length (dest_list l)) 0 (dest_list w)
    | None -> 0 in
  let sorted = List.map snd (List.sort (fun (a, _) (b, _) -> compare b a)
                                (List.map (fun it -> (size it, it)) items)) in
  ignore (CR_EVAL_CONV `pv_det (CRow (&1) (&2) (&3) false) (CRow (&3) (&4) (&5) true)`);
  let ths = cr_parallel_map nd (fun (_, _, ins, outs, root) -> pv_root_thm ins outs root) sorted in
  Printf.printf "all %d roots evaluated: %.1fs\n%!" (List.length items) (Unix.gettimeofday () -. t0);
  let tbl = Hashtbl.create 10000 in
  List.iter2 (fun (key, i, _, _, _) th -> Hashtbl.replace tbl (key, i) th) sorted ths;
  List.map (fun key ->
      let n = List.length (Hashtbl.find pv_roots key) in
      (key, pv_owner_assemble key (List.init n (fun i -> Hashtbl.find tbl (key, i))))) keys;;
