(* ========================================================================= *)
(* Parallelism cap.  Some proof steps run kernel computations on several     *)
(* OCaml 5 domains (the HOL kernel is purely functional, so this does not    *)
(* affect soundness or the theorems proved; it only changes the speed).      *)
(* Each such step asks for n domains through sq_ndomains n, which caps n by  *)
(* the environment variable SQ_DOMAINS (default: the number of cores OCaml   *)
(* recommends, Domain.recommended_domain_count ()).                         *)
(* ========================================================================= *)

let sq_domain_cap =
  match Sys.getenv_opt "SQ_DOMAINS" with
    Some s when s <> "" ->
      (try max 1 (int_of_string s) with _ -> failwith "SQ_DOMAINS: not a number")
  | _ -> max 1 (Domain.recommended_domain_count ());;

let sq_ndomains n = max 1 (min n sq_domain_cap);;

Printf.printf "parallel steps use at most %d domains (SQ_DOMAINS)\n%!" sq_domain_cap;;
