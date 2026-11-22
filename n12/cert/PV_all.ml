(* ========================================================================= *)
(* W-F6 (n12/docs/cert_design.md §4.3, §9): planar vertex enumeration, initial   *)
(* cover roots/owners, and CK_INITIAL for all 64 historical (case, owner)    *)
(* entries.  Needs p2_base + p3; loads only CR_Row/Farkas/Plan/Eval/HistData *)
(* of the core (not the 113 pair stages).                                    *)
(* ========================================================================= *)

needs "n12/cert/CR_HistData.ml";;
needs "n12/cert/PV_Vertex.ml";;
needs "n12/cert/PV_Root.ml";;
needs "n12/cert/PV_Eval.ml";;
needs "n12/cert/PV_HistRun.ml";;
needs "n12/cert/PV_C898.ml";;
