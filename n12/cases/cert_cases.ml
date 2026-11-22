(* ========================================================================= *)
(* W-ASM driver: the case theorems of the seven certificate cases            *)
(*   CA_EXCLUDED : (case, ri, thm) list,  thm : H1, .., Hn |- EXCLUDED_ROW ri *)
(* (hypotheses = the premises still missing from other work packages, named  *)
(* by ca_missing; none when all providers are registered).                  *)
(* Session: n12/cases/cs_load.ml chain, p3_all, the cert stage layers and    *)
(* W-ENTRY (see n12/cert/CA_all.ml), optionally OV_/PV_ results and    *)
(* CA_ProvideOV.ml / CA_ProvidePV.ml before this file.                      *)
(* ========================================================================= *)

needs "n12/cert/CA_Assembly.ml";;

let ca_t0 = Unix.gettimeofday ();;
let CA_EXCLUDED = map (fun c ->
    let th = ca_discharge (ca_case c) in
    let (ri, _) = Hashtbl.find CA_CASES c in
    Hashtbl.replace CA_CASES c (ri, th);
    (c, ri, th)) CA_CASE_IDS;;

let () =
  List.iter (fun (c, ri, th) ->
      if concl th <> EXCLUDED_ROW ri then failwith ("cert_cases: C" ^ c ^ " conclusion");
      let named = ca_missing c in
      let no = length (filter (fun (n, _) -> String.length n > 5 && n.[5] = 'o') named) in
      Printf.printf "C%s: |- EXCLUDED_ROW %d with %d hypotheses (%d block overlaps, %d initial covers)\n%!"
        c ri (length (hyp th)) no (length named - no)) CA_EXCLUDED;
  Printf.printf "cert_cases: %.0fs\n%!" (Unix.gettimeofday () -. ca_t0);;
