(* W-ASM: register all W-F6 CK_INITIAL theorems present in pv_initial_tbl
   (PV_Eval.ml, filled by PV_HistRun.ml / PV_C898.ml) as providers of the
   "C<case> initial owner <k>" premises.  Load after those and CA_Assembly.ml. *)
let () = Hashtbl.iter (fun key th -> ca_provide_initial key th) pv_initial_tbl;;
