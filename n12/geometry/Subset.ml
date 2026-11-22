(* ========================================================================= *)
(* Port of Compact/Bridge/C981DomainReuse/Subset.lean                        *)
(* (N12Compact.C981DomainSubset): the unchanged direct domains selected by   *)
(* C981.  The queries query976_N are C981DSQ_QUERY976_N (Queries00..08.ml,   *)
(* registered in LQ_TABLE by slq_new).  A Lean DirectSingleDomain is the     *)
(* dsd record of SmallOwnerDomainThree.ml (dqueries = [] since the queries   *)
(* are new, not entries of S12.localQueries; the Lean query list is kept as  *)
(* the signature list, whose agreement with the queries' (mask, kind,        *)
(* owned) -- Lean's `rfl` -- was checked when this file was generated and is *)
(* re-checked against LQ_TABLE at load time).                                *)
(* Lean single976_i_j_checked (via SmallOwnerDomain.checked) is              *)
(*   C981DSUB_SINGLE976_I_J_CHECKED : |- hdom c981dsub_case976_family m k al *)
(* c981dsub_small_checked performs SmallOwnerDomain.Check (budget            *)
(* equalities, upper <= 2, every small subset of the budget interval allowed *)
(* or refuted by a query of the signature list) before the kernel proof.     *)
(* ========================================================================= *)

needs "n12/geometry/SharedLocalQueries.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Queries00.ml";;
needs "n12/geometry/Queries01.ml";;
needs "n12/geometry/Queries02.ml";;
needs "n12/geometry/Queries03.ml";;
needs "n12/geometry/Queries04.ml";;
needs "n12/geometry/Queries05.ml";;
needs "n12/geometry/Queries06.ml";;
needs "n12/geometry/Queries07.ml";;
needs "n12/geometry/Queries08.ml";;

(* Lean: case976Family *)
let c981dsub_case976_family = new_definition
 `c981dsub_case976_family = {1,2,12,48,192,256,512,1024,6144,8192,16384,32768}`;;

(* Lean: SmallOwnerDomain.checked (+ Check); sigs = the query signatures *)
let c981dsub_small_checked fam k w sigs =
  let lo = pk_num (pklow_thm w.dmask k) and hi = pk_num (pkup_thm fam w.dmask k) in
  if w.dlower <> lo || w.dupper <> hi then failwith "c981dsub_small_checked: budget" else
  if hi > 2 then failwith "c981dsub_small_checked: upper > 2" else
  let sigs = map (fun (m, kq, ow) -> (m, kq, List.sort compare ow)) sigs in
  List.iter (fun (m, kq, ow) ->
      if m <> w.dmask || kq <> k then failwith "c981dsub_small_checked: signature mask / kind";
      if not (Hashtbl.mem LQ_TABLE (m, kq, ow)) then failwith "c981dsub_small_checked: unchecked query")
    sigs;
  let al = map (List.sort compare) w.dallowed in
  List.iter (fun s ->
      let c = List.length s in
      if lo <= c && c <= hi && not (mem s al) && not (mem (w.dmask, k, s) sigs)
      then failwith "c981dsub_small_checked: subset neither allowed nor refuted") RO_SMALL;
  dsd_actual fam k { w with dqueries = [] };;

(* Lean: single976_2_0 (queries query976_214, query976_215, query976_216, query976_217, query976_218, query976_219, query976_220, query976_221) *)
let c981dsub_single976_2_0 = { dmask = 12; dlower = 0; dupper = 1;
  dallowed = [[]; [6]; [8]]; dqueries = [] };;

(* Lean: single976_2_0_signatures *)
let c981dsub_single976_2_0_signatures = [(12, 0, [0]); (12, 0, [1]); (12, 0, [2]); (12, 0, [3]); (12, 0, [4]); (12, 0, [5]); (12, 0, [7]); (12, 0, [9])];;

(* Lean: single976_2_0_checked *)
let C981DSUB_SINGLE976_2_0_CHECKED =
  c981dsub_small_checked `c981dsub_case976_family` 0 c981dsub_single976_2_0 c981dsub_single976_2_0_signatures;;

(* Lean: single976_2_1 (queries query976_222, query976_223, query976_224, query976_225, query976_226, query976_227, query976_228, query976_229) *)
let c981dsub_single976_2_1 = { dmask = 12; dlower = 0; dupper = 1;
  dallowed = [[]; [5]; [8]]; dqueries = [] };;

(* Lean: single976_2_1_signatures *)
let c981dsub_single976_2_1_signatures = [(12, 1, [0]); (12, 1, [1]); (12, 1, [2]); (12, 1, [3]); (12, 1, [4]); (12, 1, [6]); (12, 1, [7]); (12, 1, [9])];;

(* Lean: single976_2_1_checked *)
let C981DSUB_SINGLE976_2_1_CHECKED =
  c981dsub_small_checked `c981dsub_case976_family` 1 c981dsub_single976_2_1 c981dsub_single976_2_1_signatures;;

(* Lean: single976_3_0 (queries query976_233, query976_234, query976_235, query976_236, query976_237, query976_238, query976_239, query976_240) *)
let c981dsub_single976_3_0 = { dmask = 48; dlower = 0; dupper = 1;
  dallowed = [[]; [7]; [9]]; dqueries = [] };;

(* Lean: single976_3_0_signatures *)
let c981dsub_single976_3_0_signatures = [(48, 0, [0]); (48, 0, [1]); (48, 0, [2]); (48, 0, [3]); (48, 0, [4]); (48, 0, [5]); (48, 0, [6]); (48, 0, [8])];;

(* Lean: single976_3_0_checked *)
let C981DSUB_SINGLE976_3_0_CHECKED =
  c981dsub_small_checked `c981dsub_case976_family` 0 c981dsub_single976_3_0 c981dsub_single976_3_0_signatures;;

(* Lean: single976_3_1 (queries query976_241, query976_242, query976_243, query976_244, query976_245, query976_246, query976_247, query976_248) *)
let c981dsub_single976_3_1 = { dmask = 48; dlower = 0; dupper = 1;
  dallowed = [[]; [7]; [9]]; dqueries = [] };;

(* Lean: single976_3_1_signatures *)
let c981dsub_single976_3_1_signatures = [(48, 1, [0]); (48, 1, [1]); (48, 1, [2]); (48, 1, [3]); (48, 1, [4]); (48, 1, [5]); (48, 1, [6]); (48, 1, [8])];;

(* Lean: single976_3_1_checked *)
let C981DSUB_SINGLE976_3_1_CHECKED =
  c981dsub_small_checked `c981dsub_case976_family` 1 c981dsub_single976_3_1 c981dsub_single976_3_1_signatures;;

(* Lean: single976_4_0 (queries query976_252, query976_253, query976_254, query976_255, query976_256, query976_257, query976_258, query976_259) *)
let c981dsub_single976_4_0 = { dmask = 192; dlower = 0; dupper = 1;
  dallowed = [[]; [1]; [3]]; dqueries = [] };;

(* Lean: single976_4_0_signatures *)
let c981dsub_single976_4_0_signatures = [(192, 0, [0]); (192, 0, [2]); (192, 0, [4]); (192, 0, [5]); (192, 0, [6]); (192, 0, [7]); (192, 0, [8]); (192, 0, [9])];;

(* Lean: single976_4_0_checked *)
let C981DSUB_SINGLE976_4_0_CHECKED =
  c981dsub_small_checked `c981dsub_case976_family` 0 c981dsub_single976_4_0 c981dsub_single976_4_0_signatures;;

(* Lean: single976_4_1 (queries query976_260, query976_261, query976_262, query976_263, query976_264, query976_265, query976_266, query976_267) *)
let c981dsub_single976_4_1 = { dmask = 192; dlower = 0; dupper = 1;
  dallowed = [[]; [1]; [4]]; dqueries = [] };;

(* Lean: single976_4_1_signatures *)
let c981dsub_single976_4_1_signatures = [(192, 1, [0]); (192, 1, [2]); (192, 1, [3]); (192, 1, [5]); (192, 1, [6]); (192, 1, [7]); (192, 1, [8]); (192, 1, [9])];;

(* Lean: single976_4_1_checked *)
let C981DSUB_SINGLE976_4_1_CHECKED =
  c981dsub_small_checked `c981dsub_case976_family` 1 c981dsub_single976_4_1 c981dsub_single976_4_1_signatures;;

(* Lean: single976_7_0 (queries query976_561, query976_562, query976_563, query976_564, query976_565, query976_566, query976_567, query976_568, query976_569, query976_570, query976_571, query976_572, query976_573, query976_574, query976_575, query976_576, query976_577, query976_578, query976_579, query976_580, query976_581, query976_582, query976_583, query976_584, query976_585, query976_586, query976_587, query976_588, query976_589, query976_590, query976_591, query976_592, query976_593, query976_594, query976_595, query976_596, query976_597, query976_598, query976_599, query976_600, query976_601, query976_602, query976_603, query976_604) *)
let c981dsub_single976_7_0 = { dmask = 1024; dlower = 1; dupper = 2;
  dallowed = [[5]; [3; 5]; [4; 5]; [7]; [5; 7]; [5; 8]; [9]; [4; 9]; [5; 9]; [7; 9]; [8; 9]]; dqueries = [] };;

(* Lean: single976_7_0_signatures *)
let c981dsub_single976_7_0_signatures = [(1024, 0, [0]); (1024, 0, [1]); (1024, 0, [0; 1]); (1024, 0, [2]); (1024, 0, [0; 2]); (1024, 0, [1; 2]); (1024, 0, [3]); (1024, 0, [0; 3]); (1024, 0, [1; 3]); (1024, 0, [2; 3]); (1024, 0, [4]); (1024, 0, [0; 4]); (1024, 0, [1; 4]); (1024, 0, [2; 4]); (1024, 0, [3; 4]); (1024, 0, [0; 5]); (1024, 0, [1; 5]); (1024, 0, [2; 5]); (1024, 0, [6]); (1024, 0, [0; 6]); (1024, 0, [1; 6]); (1024, 0, [2; 6]); (1024, 0, [3; 6]); (1024, 0, [4; 6]); (1024, 0, [5; 6]); (1024, 0, [0; 7]); (1024, 0, [1; 7]); (1024, 0, [2; 7]); (1024, 0, [3; 7]); (1024, 0, [4; 7]); (1024, 0, [6; 7]); (1024, 0, [8]); (1024, 0, [0; 8]); (1024, 0, [1; 8]); (1024, 0, [2; 8]); (1024, 0, [3; 8]); (1024, 0, [4; 8]); (1024, 0, [6; 8]); (1024, 0, [7; 8]); (1024, 0, [0; 9]); (1024, 0, [1; 9]); (1024, 0, [2; 9]); (1024, 0, [3; 9]); (1024, 0, [6; 9])];;

(* Lean: single976_7_0_checked *)
let C981DSUB_SINGLE976_7_0_CHECKED =
  c981dsub_small_checked `c981dsub_case976_family` 0 c981dsub_single976_7_0 c981dsub_single976_7_0_signatures;;

(* Lean: single976_7_1 (queries query976_605, query976_606, query976_607, query976_608, query976_609, query976_610, query976_611, query976_612, query976_613, query976_614, query976_615, query976_616, query976_617, query976_618, query976_619, query976_620, query976_621, query976_622, query976_623, query976_624, query976_625, query976_626, query976_627, query976_628, query976_629, query976_630, query976_631, query976_632, query976_633, query976_634, query976_635, query976_636, query976_637, query976_638, query976_639, query976_640, query976_641, query976_642, query976_643, query976_644, query976_645, query976_646, query976_647, query976_648) *)
let c981dsub_single976_7_1 = { dmask = 1024; dlower = 1; dupper = 2;
  dallowed = [[6]; [3; 6]; [4; 6]; [7]; [3; 7]; [4; 7]; [6; 7]; [6; 8]; [9]; [6; 9]; [7; 9]]; dqueries = [] };;

(* Lean: single976_7_1_signatures *)
let c981dsub_single976_7_1_signatures = [(1024, 1, [0]); (1024, 1, [1]); (1024, 1, [0; 1]); (1024, 1, [2]); (1024, 1, [0; 2]); (1024, 1, [1; 2]); (1024, 1, [3]); (1024, 1, [0; 3]); (1024, 1, [1; 3]); (1024, 1, [2; 3]); (1024, 1, [4]); (1024, 1, [0; 4]); (1024, 1, [1; 4]); (1024, 1, [2; 4]); (1024, 1, [3; 4]); (1024, 1, [5]); (1024, 1, [0; 5]); (1024, 1, [1; 5]); (1024, 1, [2; 5]); (1024, 1, [3; 5]); (1024, 1, [4; 5]); (1024, 1, [0; 6]); (1024, 1, [1; 6]); (1024, 1, [2; 6]); (1024, 1, [5; 6]); (1024, 1, [0; 7]); (1024, 1, [1; 7]); (1024, 1, [2; 7]); (1024, 1, [5; 7]); (1024, 1, [8]); (1024, 1, [0; 8]); (1024, 1, [1; 8]); (1024, 1, [2; 8]); (1024, 1, [3; 8]); (1024, 1, [4; 8]); (1024, 1, [5; 8]); (1024, 1, [7; 8]); (1024, 1, [0; 9]); (1024, 1, [1; 9]); (1024, 1, [2; 9]); (1024, 1, [3; 9]); (1024, 1, [4; 9]); (1024, 1, [5; 9]); (1024, 1, [8; 9])];;

(* Lean: single976_7_1_checked *)
let C981DSUB_SINGLE976_7_1_CHECKED =
  c981dsub_small_checked `c981dsub_case976_family` 1 c981dsub_single976_7_1 c981dsub_single976_7_1_signatures;;
