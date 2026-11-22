(* ========================================================================= *)
(* Historical dictionary (Lean C713Shared.dictionary = HistoricalBank) as    *)
(* OCaml tables and HOL terms (design §2.1).                                 *)
(* Data: n12/data/cert/hist_{rows,poses,domains,stages}.txt (n12/scripts/cert_extract.py) *)
(* - cr_row_tm id   : term  `CRow x y c s`  (memoized, physically shared)     *)
(* - hp_tm id       : term  `CPose a [rows]` (memoized)                        *)
(* - hdom_def (case, "A_B") : |- hCASE_dA_B = [poses]  (constants of type     *)
(*   cpose list, Lean continuousScoutCASEDomainA_BIds)                       *)
(* All terms must be built here (main domain) before parallel evaluation.   *)
(* ========================================================================= *)

needs "n12/cert/CR_Eval.ml";;

let cr_read_lines fn =
  let ic = Stdlib.open_in fn in
  let rec loop acc = match In_channel.input_line ic with
      Some l -> loop (l :: acc) | None -> close_in ic; List.rev acc in
  loop [];;

let cr_split c s = List.filter (fun x -> x <> "") (String.split_on_char c s);;

let cr_int_tm =
  let tbl = Hashtbl.create 100000 in
  fun (s : string) ->
    try Hashtbl.find tbl s with Not_found ->
      let t = mk_intconst (Num.num_of_string s) in Hashtbl.add tbl s t; t;;

let cr_crow_c = `CRow` and cr_cpose_c = `CPose`;;
let cr_crow_ty = `:crow` and cr_cpose_ty = `:cpose`;;

(* raw table: id -> (x, y, c, strict, denPred) as strings *)
let hist_rows_raw : (int, string * string * string * bool * string) Hashtbl.t = Hashtbl.create 120000;;
let hist_poses_raw : (int, int * int list) Hashtbl.t = Hashtbl.create 30000;;

let () =
  List.iter (fun l -> match cr_split ' ' l with
      [k; x; y; c; s; d] -> Hashtbl.replace hist_rows_raw (int_of_string k) (x, y, c, s = "1", d)
    | _ -> ()) (cr_read_lines "n12/data/cert/hist_rows.txt");
  List.iter (fun l -> match cr_split ' ' l with
      [k; a; rs] -> Hashtbl.replace hist_poses_raw (int_of_string k)
                      (int_of_string a, List.map int_of_string (cr_split ',' rs))
    | [k; a] -> Hashtbl.replace hist_poses_raw (int_of_string k) (int_of_string a, [])
    | _ -> ()) (cr_read_lines "n12/data/cert/hist_poses.txt");;

(* Lean SharedRows: missing ids give the fallback row (0,0,0,false) *)
let cr_row_of_strings (x, y, c, s) =
  list_mk_comb (cr_crow_c, [cr_int_tm x; cr_int_tm y; cr_int_tm c; if s then `true` else `false`]);;

let cr_row_tm =
  let tbl = Hashtbl.create 120000 in
  fun id ->
    try Hashtbl.find tbl id with Not_found ->
      let (x, y, c, s, _) = try Hashtbl.find hist_rows_raw id
                            with Not_found -> ("0", "0", "0", false, "0") in
      let t = cr_row_of_strings (x, y, c, s) in Hashtbl.add tbl id t; t;;

let cr_rows_tm ids = mk_list (List.map cr_row_tm ids, cr_crow_ty);;

(* Lean SharedPoses: missing ids give the fallback pose (0, []) *)
let hp_tm =
  let tbl = Hashtbl.create 30000 in
  fun id ->
    try Hashtbl.find tbl id with Not_found ->
      let (a, rs) = try Hashtbl.find hist_poses_raw id with Not_found -> (0, []) in
      let t = mk_comb (mk_comb (cr_cpose_c, mk_small_numeral a), cr_rows_tm rs) in
      Hashtbl.add tbl id t; t;;

(* domains *)
let hist_domain_ids : (string * string, int list) Hashtbl.t = Hashtbl.create 300;;
let () =
  List.iter (fun l -> match cr_split ' ' l with
      [c; n; ids] -> Hashtbl.replace hist_domain_ids (c, n) (List.map int_of_string (cr_split ',' ids))
    | [c; n] -> Hashtbl.replace hist_domain_ids (c, n) []
    | _ -> ()) (cr_read_lines "n12/data/cert/hist_domains.txt");;

(* define  name = tm, or (on reload) recover the existing identical definition *)
let cr_get_or_define name tm =
  if can get_const_type name then
    let th = find (fun th -> try fst (dest_const (lhs (concl th))) = name with Failure _ -> false)
               (definitions ()) in
    if aconv (rhs (concl th)) tm then th
    else failwith ("cr_get_or_define: " ^ name ^ " already defined differently")
  else new_basic_definition (mk_eq (mk_var (name, type_of tm), tm));;

let hdom_tbl : (string * string, thm) Hashtbl.t = Hashtbl.create 300;;
let hdom_name (c, n) = "h" ^ c ^ "_d" ^ n;;
let hdom_def (c, n) =
  try Hashtbl.find hdom_tbl (c, n) with Not_found ->
    let ids = Hashtbl.find hist_domain_ids (c, n) in
    let tm = mk_list (List.map hp_tm ids, cr_cpose_ty) in
    let th = cr_get_or_define (hdom_name (c, n)) tm in
    Hashtbl.add hdom_tbl (c, n) th; th;;
let hdom_const cn = lhs (concl (hdom_def cn));;

(* stages: case step srcDom nbrDom tgtDom nplans *)
let hist_stages =
  List.map (fun l -> match cr_split ' ' l with
      [c; st; s; n; t; k] -> (c, st, s, n, t, int_of_string k)
    | _ -> failwith "hist_stages") (cr_read_lines "n12/data/cert/hist_stages.txt");;
