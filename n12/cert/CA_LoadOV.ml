(* W-ASM: load W-F345 (block overlaps of the 113 historical stages) with at most
   8 OCaml domains, then register them for CA_Assembly (CA_ProvideOV.ml).
   The overlap layer with ov_domains := 8. *)
needs "n12/cert/cert_all.ml";;
needs "n12/cert/OV_Overlap.ml";;
needs "n12/cert/OV_HistRun.ml";;
ov_domains := 8;;
needs "n12/cert/OV_Run.ml";;
needs "n12/cert/CA_ProvideOV.ml";;
needs "n12/cert/OV_C898.ml";;
let () = Hashtbl.iter (fun st th -> ca_provide_overlap ("898", st) th) ov8_overlap_tbl;;
