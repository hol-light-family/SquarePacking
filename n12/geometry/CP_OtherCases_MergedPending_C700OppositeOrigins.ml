(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/C700OppositeOrigins  *)
(* .lean (namespace N12Compact.MergedPending).  The paired northwest corner  *)
(* (owner 192) supplies the left and top boundary origins of C700.           *)
(* family .c700 is mpf_family_c700; owner p m is the OriginalOwners tuple    *)
(* (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l.  WallProfile.boundary_     *)
(* origin is OCWPBO_BOUNDARY_ORIGIN; left_reach / top_reach are the c700     *)
(* entries of MPWR_LEFT_REACH / MPWR_TOP_REACH (WallReach.ml).  The pulled   *)
(* squares pullSwap (pullY W) and pullY W are handled by the local lemmas    *)
(* MPCOO_RAW_LEFT / MPCOO_RAW_TOP on arbitrary squares B (the wall owner)    *)
(* and K (the corner owner).  Tag MPCOO_.                                    *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_WallReach.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

let MPCOO_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         RASM_ARITH_TAC;
         UNDISCH_TAC `cB * cB + sB * sB = &1` THEN REAL_ARITH_TAC;
         UNDISCH_TAC `cK * cK + sK * sK = &1` THEN REAL_ARITH_TAC;
         REPEAT GEN_TAC THEN FIRST_ASSUM(fun th ->
           if not (is_forall (concl th)) then failwith "" else
           (fun (asl, w) ->
              let lin = lhand (snd (strip_forall w)) in
              let x = rand (rator lin) and y = rand lin in
              (DISCH_TAC THEN MP_TAC(SPECL [x; y] th) THEN
               ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REAL_ARITH_TAC]) (asl, w)));
         REPEAT GEN_TAC THEN FIRST_ASSUM(fun th ->
           if not (is_forall (concl th)) then failwith "" else
           (fun (asl, w) ->
              let lin = lhand (rand w) in
              let x = rand (rator lin) and y = rand lin in
              ACCEPT_TAC (SPECL [x; y] th) (asl, w)))];;

(* the pulled step of c700_left_origin: boundary_origin on pullSwap (pullY B), pullSwap (pullY K) *)
let MPCOO_RAW_LEFT = prove
 (`forall cB sB uB vB aB cK sK uK vK aK.
     cB * cB + sB * sB = &1 /\ cK * cK + sK * sK = &1 /\ &1 < aB /\ aB = aK /\
     lcont cB sB uB vB aB /\ lcont cK sK uK vK aK /\
     linside cB sB uB vB aB (&457 / &500) (&2) /\ linside cB sB uB vB aB (&1) (&12 / &5) /\
     linside cK sK uK vK aK (&457 / &500) (&3) /\ linside cK sK uK vK aK (&1) (&3) /\
     ~linside cK sK uK vK aK (&3 / &2) (&3) /\
     ldisj cK sK uK vK aK cB sB uB vB aB
     ==> linside cB sB uB vB aB (&1) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--sB:real`; `cB:real`; `uB - &4 * sB`; `--(&4 * cB - vB - aB) - aB`; `aB:real`;
                `--sK:real`; `cK:real`; `uK - &4 * sK`; `--(&4 * cK - vK - aK) - aK`; `aK:real`;
                `&457 / &500`; `&8 / &5`] OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[LINSIDE_PULLSW; LINSIDE_PULLY; ldisj] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN
  ANTS_TAC THENL [MPCOO_ANTS_TAC; REWRITE_TAC[]]);;

(* the pulled step of c700_top_origin: boundary_origin on pullY B, pullY K *)
let MPCOO_RAW_TOP = prove
 (`forall cB sB uB vB aB cK sK uK vK aK.
     cB * cB + sB * sB = &1 /\ cK * cK + sK * sK = &1 /\ &1 < aB /\ aB = aK /\
     lcont cB sB uB vB aB /\ lcont cK sK uK vK aK /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\ linside cB sB uB vB aB (&8 / &5) (&3) /\
     linside cK sK uK vK aK (&1) (&1543 / &500) /\ linside cK sK uK vK aK (&1) (&3) /\
     ~linside cK sK uK vK aK (&1) (&5 / &2) /\
     ldisj cK sK uK vK aK cB sB uB vB aB
     ==> linside cB sB uB vB aB (&2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `--sB:real`; `uB - &4 * sB`; `&4 * cB - vB - aB`; `aB:real`;
                `cK:real`; `--sK:real`; `uK - &4 * sK`; `&4 * cK - vK - aK`; `aK:real`;
                `&457 / &500`; `&8 / &5`] OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[LINSIDE_PULLY; ldisj] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN
  ANTS_TAC THENL [MPCOO_ANTS_TAC; REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Packing level.                                                            *)
(* ------------------------------------------------------------------------- *)

let MPCOO_FAM = `mpf_family_c700`;;

let mpcoo_apply lemma mB mK ths =
  let fam = MPCOO_FAM in
  let np = mpwr_np fam in
  let th = SPECL (butlast (mpwr_tuple mB) @ [`l:real`] @ butlast (mpwr_tuple mK) @ [`l:real`]) lemma in
  let unit m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let box m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_BOX) np in
  let side = MP (SPECL MPWR_VARS OO_SIDE) np in
  MP th (TAC_PROOF(([], lhand (concl th)),
    REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC ([unit mB; unit mK; box mB; box mK; side; REFL `l:real`] @ ths))));;

(* Lean: c700_left_origin *)
let MPCOO_C700_LEFT_ORIGIN =
  let fam = MPCOO_FAM in
  let left = el 1 MPWR_LEFT_REACH and top = el 1 MPWR_TOP_REACH in
  let marker = mpwr_seed fam 4096 (`&457 / &500`, `&2`) in
  let corner_marker = mpwr_seed fam 192 (`&457 / &500`, `&3`) in
  let corner = mpwr_seed fam 192 (`&1`, `&3`) in
  let reach = mpwr_bar (CONJUNCT2 (mpwr_inst fam left)) `&12 / &5` in
  let original = mpwr_excl fam 192 32768 (mpwr_bar (CONJUNCT2 (mpwr_inst fam top)) `&3 / &2`) in
  let apart = mpwr_inst fam (oo_apart fam 192 4096) in
  let res = mpcoo_apply MPCOO_RAW_LEFT 4096 192 [marker; reach; corner_marker; corner; original; apart] in
  mpwr_prove fam (mpwr_inside 4096 `&1` `&2`) res;;

(* Lean: c700_top_origin *)
let MPCOO_C700_TOP_ORIGIN =
  let fam = MPCOO_FAM in
  let left = el 1 MPWR_LEFT_REACH and top = el 1 MPWR_TOP_REACH in
  let marker = mpwr_seed fam 32768 (`&2`, `&1543 / &500`) in
  let corner_marker = mpwr_seed fam 192 (`&1`, `&1543 / &500`) in
  let corner = mpwr_seed fam 192 (`&1`, `&3`) in
  let reach = mpwr_bar (CONJUNCT2 (mpwr_inst fam top)) `&8 / &5` in
  let original = mpwr_excl fam 192 4096 (mpwr_bar (CONJUNCT2 (mpwr_inst fam left)) `&5 / &2`) in
  let apart = mpwr_inst fam (oo_apart fam 192 32768) in
  let res = mpcoo_apply MPCOO_RAW_TOP 32768 192 [marker; reach; corner_marker; corner; original; apart] in
  mpwr_prove fam (mpwr_inside 32768 `&2` `&3`) res;;
