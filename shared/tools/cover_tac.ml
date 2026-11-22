(* ========================================================================= *)
(* COVER_TAC: cover a polygon of square centres by triangle lemmas.          *)
(* The case tree is found by an untrusted search (shared/tools/cover_search.py);  *)
(* HOL replays it with case splits and REAL_ARITH.                           *)
(* ========================================================================= *)

needs "shared/tools/nlin.ml";;

let cover_vars = ref (`c1:real`, `c2:real`);;

(* coefficients (a,b,c) of a*X + b*Y + c, failing if not affine in X,Y *)
let lin_coeffs t =
  let (x,y) = !cover_vars in
  nlin_atoms := [x; y];
  let p = poly_of_term t in
  if length !nlin_atoms > 2 then failwith "lin_coeffs: other atoms" else
  let get m = try assoc m p with Failure _ -> num 0 in
  if exists (fun (m,_) -> not (mem m [[]; [0,1]; [1,1]])) p then failwith "lin_coeffs: nonlinear"
  else (get [0,1], get [1,1], get []);;

let region_of_asl asl =
  mapfilter (fun (_,th) ->
    let (k,th') = fact_of_thm th in
    if k = Neq then failwith "" else
    let (a,b,c) = lin_coeffs (rand(concl th')) in
    (a,b,c,k = Ngt)) asl;;

let tri_weights th =
  let ants = conjuncts(lhand(snd(strip_forall(concl th)))) in
  let ws = map rand (filter (fun t -> is_comb t && is_comb (rator t) &&
              rand(rator t) = `&0` && fst(dest_const(fst(strip_comb t))) = "real_le") ants) in
  let (x,y) = !cover_vars in
  map (fun w -> lin_coeffs w) ws;;

let json_num n = "\"" ^ string_of_num n ^ "\"";;

let cover_counter = ref 0;;

let run_cover_search region tris depth =
  incr cover_counter;
  (* oracle input/output: fresh files in the system temporary directory ($TMPDIR) *)
  let fin = Filename.temp_file "sq_cover" ".json" in
  let fout = fin ^ ".out" in
  let oc = Stdlib.open_out fin in
  let lin (a,b,c) = "[" ^ String.concat "," (map json_num [a;b;c]) ^ "]" in
  Printf.fprintf oc "{\"depth\": %d, \"region\": [%s], \"tris\": [%s]}\n" depth
    (String.concat "," (map (fun (a,b,c,s) -> "[" ^ String.concat "," (map json_num [a;b;c]) ^
                                              "," ^ (if s then "true" else "false") ^ "]") region))
    (String.concat "," (map (fun ws -> "[" ^ String.concat "," (map lin ws) ^ "]") tris));
  Stdlib.close_out oc;
  let cmd = Printf.sprintf
    "%s shared/tools/cover_search.py %s %s" (sq_python ()) fin fout in
  if Sys.command cmd <> 0 then failwith "cover_search failed";
  let ic = Stdlib.open_in fout in
  let s = input_line ic in Stdlib.close_in ic;
  (try Sys.remove fin; Sys.remove fout with Sys_error _ -> ()); s;;

(* a tiny parser for the JSON tree *)
type ctree = Cempty | Ctri of int | Csplit of (num * num * num) * ctree * ctree;;

let parse_ctree s =
  let toks = ref [] in
  let buf = Buffer.create 16 in
  let flush () = if Buffer.length buf > 0 then (toks := Buffer.contents buf :: !toks; Buffer.clear buf) in
  String.iter (fun ch -> match ch with
      '[' | ']' | ',' -> flush (); toks := String.make 1 ch :: !toks
    | ' ' | '"' -> flush ()
    | c -> Buffer.add_char buf c) s;
  flush ();
  let toks = ref (List.rev !toks) in
  let next () = match !toks with t::r -> toks := r; t | [] -> failwith "parse_ctree" in
  let expect t = if next () <> t then failwith ("parse_ctree: expected " ^ t) in
  let rat s = nlin_rat s in
  let rec tree () =
    expect "[";
    let tag = next () in
    let r =
      if tag = "empty" then Cempty
      else if tag = "tri" then (expect ","; Ctri (int_of_string (next ())))
      else if tag = "split" then
        (expect ","; expect "["; let a = rat(next()) in expect ","; let b = rat(next()) in
         expect ","; let c = rat(next()) in expect "]"; expect ",";
         let t1 = tree () in expect ","; let t2 = tree () in Csplit((a,b,c),t1,t2))
      else failwith ("parse_ctree: " ^ tag) in
    expect "]"; r in
  tree ();;

let lin_term (a,b,c) =
  let (x,y) = !cover_vars in
  mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (term_of_rat a) x)
   (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (term_of_rat b) y)
     (term_of_rat c));;

(* tris: theorems !c1 c2 a b l. ... ==> P0 \/ P1 \/ P2, already usable *)
let COVER_TAC ?(depth=14) spec tris (asl,w as g) =
  let region = region_of_asl asl in
  let tws = map tri_weights tris in
  let tree = parse_ctree (run_cover_search region tws depth) in
  let rec replay t =
    match t with
      Cempty -> RASM_ARITH_TAC
    | Ctri k ->
        MP_TAC(SPECL spec (el k tris)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ASM_REWRITE_TAC[]]
    | Csplit(abc,t1,t2) ->
        ASM_CASES_TAC (mk_binop `(<=):real->real->bool` `&0` (lin_term abc)) THENL
         [replay t1; replay t2] in
  replay tree g;;
