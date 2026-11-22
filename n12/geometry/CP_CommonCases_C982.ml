(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C982.lean                          *)
(* (N12Compact.CommonCases.C982).  The complete original C982 contract:     *)
(* original marker seeds, C982Merged.reaches_original (C982M_REACHES_ORIGINAL)*)
(* and C982Obstruction.impossible_original (CCC982_IMPOSSIBLE_ORIGINAL).     *)
(* Private owner / owner_code / side / seed / apart are the OriginalOwners  *)
(* toolkit (ooc .. , OO_SIDE, oo_seed, oo_apart); S12.inside_segment is      *)
(* CES_INSIDE_SEGMENT.  row_checked / excludes via RowIdentity (row 513).    *)
(* Tag CCC982C_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/C982Merged.ml";;
needs "n12/geometry/CP_CommonCases_C982Obstruction.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: family *)
let ccc982c_family = new_definition
 `ccc982c_family = {1,2,12,48,192,512,1024,2048,4096,8448,16384,32768}`;;
let CCC982C_F = `ccc982c_family`;;

let CCC982C_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let CCC982C_H = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc982c_family`;;
let ccc982c_mp th = MP (SPECL CCC982C_VARS th) (ASSUME CCC982C_H);;
let ccc982c_own m =
  map (fun f -> list_mk_comb(f, CCC982C_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let CCC982C_NP = CONJUNCT1 (ASSUME CCC982C_H);;

(* Lean: seed (private) *)
let ccc982c_seed m p = ccc982c_mp (oo_inst CCC982C_F (oo_seed m p));;
(* Lean: apart (private) *)
let ccc982c_apart m n = REWRITE_RULE[ldisj] (ccc982c_mp (oo_apart CCC982C_F m n));;
(* Lean: side (private) *)
let CCC982C_SIDE = MP (SPECL CCC982C_VARS OO_SIDE) CCC982C_NP;;
let ccc982c_unit m = MP (SPECL (CCC982C_VARS @ [mk_small_numeral m]) OO_UNIT) CCC982C_NP;;

(* ~ owner m at the point of a theorem  |- linside (owner n) x y *)
let ccc982c_foreign m n thn =
  let args = snd (strip_comb (concl thn)) in
  let d = SPECL [el 5 args; el 6 args] (ccc982c_apart m n) in
  let a = lhand (rand (concl d)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d) (CONJ (ASSUME a) thn)));;

let CCC982C_BOTTOM = ccc982c_seed 8448 (`&2`, `&457 / &500`);;
let CCC982C_SOUTHWEST = ccc982c_seed 8448 (`&33 / &20`, `&33 / &20`);;
let CCC982C_SINGLETON = ccc982c_seed 1 (`&87 / &50`, `&1`);;
let CCC982C_SOUTHEAST = ccc982c_seed 512 (`&47 / &20`, `&33 / &20`);;
let CCC982C_CORNER = ccc982c_seed 12 (`&3`, `&1`);;
let CCC982C_CORNER_MARKER = ccc982c_seed 12 (`&1543 / &500`, `&1`);;
let CCC982C_WALL_MARKER = ccc982c_seed 16384 (`&1543 / &500`, `&2`);;

(* Lean: endpoint (C982Merged.reaches_original on owner 8448) *)
let CCC982C_ENDPOINT =
  MP (SPECL (ccc982c_own 8448) C982M_REACHES_ORIGINAL)
     (end_itlist CONJ [ccc982c_unit 8448; CCC982C_SIDE; CCC982C_BOTTOM; CCC982C_SOUTHWEST;
                       ccc982c_foreign 8448 1 CCC982C_SINGLETON;
                       ccc982c_foreign 8448 512 CCC982C_SOUTHEAST]);;

(* the segment from (2, 457/500) to (23/10, 46/25) lies in owner 8448, hence not in owner 512 *)
let CCC982C_SEGMENT_FOREIGN =
  let seg = MP (SPECL (ccc982c_own 8448 @ [`&2`; `&457 / &500`; `&23 / &10`; `&46 / &25`; `w:real`])
                  CES_INSIDE_SEGMENT)
               (end_itlist CONJ [CCC982C_BOTTOM; CCC982C_ENDPOINT;
                                 ASSUME `&0 <= w`; ASSUME `w <= &1`]) in
  GEN `w:real` (DISCH `&0 <= w` (DISCH `w <= &1` (ccc982c_foreign 512 8448 seg)));;

(* Lean: family_impossible *)
let CCC982C_FAMILY_IMPOSSIBLE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc982c_family ==> false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ACCEPT_TAC (MP (SPECL (ccc982c_own 512) CCC982_IMPOSSIBLE_ORIGINAL)
    (end_itlist CONJ [ccc982c_unit 512; CCC982C_SIDE; CCC982C_SOUTHEAST;
                      ccc982c_foreign 512 12 CCC982C_CORNER;
                      ccc982c_foreign 512 12 CCC982C_CORNER_MARKER;
                      ccc982c_foreign 512 16384 CCC982C_WALL_MARKER;
                      CCC982C_SEGMENT_FOREIGN])));;

(* Lean: row_checked (private) / excludes *)
let CCC982C_EXCLUDES = prove
 (`excl_case 982`,
  REWRITE_TAC[ri_excludes_case_iff 513 `ccc982c_family`; excl_fam] THEN
  MESON_TAC[CCC982C_FAMILY_IMPOSSIBLE]);;

(* for the assembly: |- EXCLUDED_ROW 513 *)
let CCC982C_EXCLUDED_ROW = ri_excluded_row 513 CCC982C_EXCLUDES;;
