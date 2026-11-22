(* shared helpers for the case drivers *)
let case_timer f c cid =
  let t1 = Sys.time() in
  let r = try Some (f c) with Failure m -> (Printf.printf "case %d FAIL: %s\n%!" cid m; None)
                            | e -> (Printf.printf "case %d EXN: %s\n%!" cid (Printexc.to_string e); None) in
  Printf.printf "case %d %s %.0fs\n%!" cid (if r = None then "failed" else "done") (Sys.time() -. t1);
  r;;
let run_cases name f cid_of cases =
  let res = mapfilter (fun c -> match case_timer f c (cid_of c) with Some x -> x | None -> failwith "") cases in
  Printf.printf "%s: %d of %d cases proved\n%!" name (length res) (length cases);
  res;;
let check_case_thm (ri, th) =
  if hyp th <> [] || not (aconv (concl th) (EXCLUDED_ROW ri)) then failwith "check_case_thm" else (ri, th);;
