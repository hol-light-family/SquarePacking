(* ========================================================================= *)
(* W-C898, part 1: the C898 dictionary (Lean Cases/C898/{SharedRows,         *)
(* SharedPoses,SharedDictionary,SharedDomains}.lean) as OCaml tables and HOL *)
(* terms in the CR_ representation (design §2, §2.1).                        *)
(* Data: n12/data/cert/c898_{rows,poses,domains}.txt (n12/scripts/cert_extract_c898.py) *)
(* - c8_row_tm id : `CRow x y c s` (memoized; missing ids: Lean's fallback   *)
(*   row (0,0,0,false)); c8p_tm id : `CPose a [rows]` (missing: (0, [])).    *)
(*   Every C898 angle index is < 64, and s12_angles a = EL a angles64 for     *)
(*   a < 64, which is Lean's C898 dictionary angle (angles64[a]).             *)
(* - c8dom_def "A_B" : |- c898_dA_B = [poses]   (continuousScout898DomainA_BIds) *)
(* Build all terms in the main domain (memo tables are not domain-safe).    *)
(* ========================================================================= *)

needs "n12/cert/CR_HistData.ml";;

let c898_rows_raw : (int, string * string * string * bool * string) Hashtbl.t = Hashtbl.create 12000;;
let c898_poses_raw : (int, int * int list) Hashtbl.t = Hashtbl.create 3000;;

let () =
  List.iter (fun l -> match cr_split ' ' l with
      [k; x; y; c; s; d] -> Hashtbl.replace c898_rows_raw (int_of_string k) (x, y, c, s = "1", d)
    | _ -> ()) (cr_read_lines "n12/data/cert/c898_rows.txt");
  List.iter (fun l -> match cr_split ' ' l with
      [k; a; rs] -> Hashtbl.replace c898_poses_raw (int_of_string k)
                      (int_of_string a, List.map int_of_string (cr_split ',' rs))
    | [k; a] -> Hashtbl.replace c898_poses_raw (int_of_string k) (int_of_string a, [])
    | _ -> ()) (cr_read_lines "n12/data/cert/c898_poses.txt");;

let c8_row_tm =
  let tbl = Hashtbl.create 12000 in
  fun id ->
    try Hashtbl.find tbl id with Not_found ->
      let (x, y, c, s, _) = try Hashtbl.find c898_rows_raw id
                            with Not_found -> ("0", "0", "0", false, "0") in
      let t = cr_row_of_strings (x, y, c, s) in Hashtbl.add tbl id t; t;;

let c8_rows_tm ids = mk_list (List.map c8_row_tm ids, cr_crow_ty);;

let c8p_tm =
  let tbl = Hashtbl.create 3000 in
  fun id ->
    try Hashtbl.find tbl id with Not_found ->
      let (a, rs) = try Hashtbl.find c898_poses_raw id with Not_found -> (0, []) in
      if a >= 64 then failwith "c8p_tm: angle >= 64";
      let t = mk_comb (mk_comb (cr_cpose_c, mk_small_numeral a), c8_rows_tm rs) in
      Hashtbl.add tbl id t; t;;

let c898_domain_ids : (string, int list) Hashtbl.t = Hashtbl.create 40;;
let () =
  List.iter (fun l -> match cr_split ' ' l with
      [n; ids] -> Hashtbl.replace c898_domain_ids n (List.map int_of_string (cr_split ',' ids))
    | [n] -> Hashtbl.replace c898_domain_ids n []
    | _ -> ()) (cr_read_lines "n12/data/cert/c898_domains.txt");;

let c8dom_tbl : (string, thm) Hashtbl.t = Hashtbl.create 40;;
let c8dom_def n =
  try Hashtbl.find c8dom_tbl n with Not_found ->
    let ids = Hashtbl.find c898_domain_ids n in
    let tm = mk_list (List.map c8p_tm ids, cr_cpose_ty) in
    let th = cr_get_or_define ("c898_d" ^ n) tm in
    Hashtbl.add c8dom_tbl n th; th;;
let c8dom_const n = lhs (concl (c8dom_def n));;
