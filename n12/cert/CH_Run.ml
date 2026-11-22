(* ========================================================================= *)
(* W-CHORD, part 4: builds all 20 historical chord stage theorems and the   *)
(* C713 height theorem (design §4.4).                                        *)
(*   ck_chord_thm (case, step), e.g. ck_chord_thm ("701", "06")              *)
(*     |- ch_chord_transition (MAP cr_leaf hC_dSRC) (MAP cr_leaf hC_dN1)     *)
(*          (MAP cr_leaf hC_dN2) (MAP cr_leaf hC_dN3) (MAP cr_leaf hC_dTGT)  *)
(*     (q0 = owner masks.(0), q1..q3 = masks.(1..3): ck_chord_masks)        *)
(*   C713_HEIGHT : square-level C713ChordDirect.source_to_after_height       *)
(* ch_domains (default 8) OCaml domains evaluate the checks.                *)
(* ========================================================================= *)

needs "n12/cert/CH_Stages.ml";;

let ch_domains = ref 8;;
let ch_t0 = Unix.gettimeofday ();;
let CK_CHORDS = List.map (fun ((c,st,_,_,_,_,_,_,_,_) as s) ->
   ((c, st), if Hashtbl.mem ck_chord_tbl (c,st) then Hashtbl.find ck_chord_tbl (c,st)
             else ck_build_chord !ch_domains s)) ch_stages;;
Printf.printf "ALL CHORD STAGES: %d theorems, %.1fs\n%!" (List.length CK_CHORDS) (Unix.gettimeofday () -. ch_t0);;

let C713_HEIGHT_STAGE = ch_build_height !ch_domains;;

(* Lean: C713ChordDirect.source_to_after_height (square level; q = owner 2304,
   q1 q2 q3 = owners of masks 2, 512, 16384, with the occupied-row points of
   C713OccupiedRow.above_radius: commonPoint713_27 / _7 / _22 / _36) *)
let C713_HEIGHT = MATCH_MP CH_HEIGHT_EXPLICIT C713_HEIGHT_STAGE;;
Printf.printf "W-CHORD done: %.1fs\n%!" (Unix.gettimeofday () -. ch_t0);;
