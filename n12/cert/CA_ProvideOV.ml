(* W-ASM: register all W-F345 block-overlap theorems present in ov_overlap_tbl
   (OV_HistRun.ml) as providers of the "C<case> overlap S<step>" premises.
   Load after OV_HistRun.ml / OV_Run.ml and CA_Assembly.ml. *)
let () = Hashtbl.iter (fun key th -> ca_provide_overlap key th) ov_overlap_tbl;;
