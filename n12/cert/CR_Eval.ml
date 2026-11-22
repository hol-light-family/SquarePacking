(* ========================================================================= *)
(* Certificate layer: evaluation of the reflective checkers (design §5).     *)
(* CR_EVAL_CONV tm proves |- tm = value by call-by-value evaluation          *)
(* (hol-light compute.ml) with the cr_ checker equations and integer/num    *)
(* literal arithmetic externs.  Compsets are built per OCaml Domain.         *)
(* ========================================================================= *)

needs "n12/cert/CR_Plan.ml";;
needs "shared/tools/domains.ml";;

(* executable forms of library functions on numerals *)
let CR_EL_NUM = prove
 (`forall n (l:A list). EL n l = if n = 0 then HD l else EL (n - 1) (TL l)`,
  INDUCT_TAC THEN REWRITE_TAC[EL; NOT_SUC; SUC_SUB1]);;

let CR_LENGTH_NUM = prove
 (`(LENGTH ([]:A list) = 0) /\ (forall h:A t. LENGTH (CONS h t) = LENGTH t + 1)`,
  REWRITE_TAC[LENGTH; ADD1]);;

let cr_extra_thms = ref ([] : thm list);;
let cr_extra_convs = ref ([] : (term * int * conv) list);;

let cr_base_thms () =
  [CR_EL_NUM; CR_LENGTH_NUM; HD; TL; MEM; ALL; MAP; APPEND; NULL; FST; SND; LET_END_DEF;
   cr_x; cr_y; cr_c; cr_s; cp_angle; cp_rows; cr_zero; cr_one; cr_opposite;
   cr_rowat; cr_tworow_check; cr_sum; cr_nonneg; cr_cert_check; cr_cramer; cr_rs_check;
   cr_single_check; cr_const_check; cr_hint_check; cr_hints_check; cr_empty_check;
   cr_bhint_check; cr_bhint_indep; cr_bt_check; cr_blk_rows; cr_blk_none; cr_blk_empty;
   cr_plan_check; cpl_source; cpl_block; cpl_target; cpl_hints; cpl_header;
   injectivity "crow"; injectivity "cpose"; injectivity "option"; distinctness "option";
   CONS_11; NOT_CONS_NIL; PAIR_EQ] @ !cr_extra_thms;;

let cr_base_convs () =
  [`(+):int->int->int`,2,INT_ADD_CONV; `(-):int->int->int`,2,INT_SUB_CONV;
   `( * ):int->int->int`,2,INT_MUL_CONV; `(--):int->int`,1,INT_NEG_CONV;
   `(<=):int->int->bool`,2,INT_LE_CONV; `(<):int->int->bool`,2,INT_LT_CONV;
   `(=):int->int->bool`,2,INT_EQ_CONV; `abs:int->int`,1,INT_ABS_CONV;
   `(+):num->num->num`,2,NUM_ADD_CONV; `(-):num->num->num`,2,NUM_SUB_CONV;
   `( * ):num->num->num`,2,NUM_MULT_CONV;
   `(<):num->num->bool`,2,NUM_LT_CONV; `(<=):num->num->bool`,2,NUM_LE_CONV;
   `(=):num->num->bool`,2,NUM_EQ_CONV; `SUC`,1,NUM_SUC_CONV] @ !cr_extra_convs;;

(* compsets must be built in the main domain (parser / compute state) *)
let make_cr_cs () =
  let cs = Compute.bool_compset () in
  Compute.add_thms (cr_base_thms ()) cs;
  List.iter (fun c -> Compute.add_conv c cs) (cr_base_convs ());
  cs;;
let cr_cs_pool = ref ([] : Compute.compset list);;

(* one compset per OCaml domain (compute.ml state is not domain safe) *)
let cr_cs_tbl = Array.make 4096 None;;
let cr_cs_gen = ref 0;;
let cr_cs () =
  let i = (Domain.self () :> int) land 4095 in
  match cr_cs_tbl.(i) with
    Some (g, cs) when g = !cr_cs_gen -> cs
  | _ -> let cs = make_cr_cs () in cr_cs_tbl.(i) <- Some (!cr_cs_gen, cs); cs;;
(* call after extending cr_extra_thms / cr_extra_convs *)
let cr_cs_reset () = incr cr_cs_gen; cr_cs_pool := [];;

let CR_EVAL_CONV tm = Compute.CBV_CONV (cr_cs ()) tm;;

(* prove a closed boolean term by evaluation, unfolding the given data definitions first *)
let cr_prove_by_eval defs tm =
  let th1 = if defs = [] then REFL tm else PURE_REWRITE_CONV defs tm in
  let th2 = CR_EVAL_CONV (rhs (concl th1)) in
  let th = TRANS th1 th2 in
  if rhs (concl th) = `true` then EQT_ELIM th
  else failwith ("cr_prove_by_eval: evaluates to " ^ string_of_term (rhs (concl th)));;

(* ------------------------------------------------------------------------- *)
(* A small Domain pool: map f over items with nd domains (results in order). *)
(* f must not touch shared mutable state (other than read-only data).        *)
(* ------------------------------------------------------------------------- *)
let cr_parallel_map nd (f : 'a -> 'b) (items : 'a list) : 'b list =
  let nd = sq_ndomains nd in
  let arr = Array.of_list items in
  let n = Array.length arr in
  let res = Array.make n None in
  let next = Atomic.make 0 in
  let worker () =
    let rec loop () =
      let i = Atomic.fetch_and_add next 1 in
      if i < n then begin
        res.(i) <- Some (try Ok (f arr.(i)) with e -> Error (Printexc.to_string e));
        loop ()
      end in
    loop () in
  (* compsets for the workers, built here in the main domain *)
  let k = max 0 (nd - 1) in
  while List.length !cr_cs_pool < k do cr_cs_pool := make_cr_cs () :: !cr_cs_pool done;
  let pool = Array.of_list !cr_cs_pool in
  let gen = !cr_cs_gen in
  let ds = List.init k (fun j -> Domain.spawn (fun () ->
      cr_cs_tbl.((Domain.self () :> int) land 4095) <- Some (gen, pool.(j));
      worker ())) in
  worker ();
  List.iter Domain.join ds;
  Array.to_list (Array.mapi (fun i r -> match r with
      Some (Ok x) -> x
    | Some (Error m) -> failwith (Printf.sprintf "cr_parallel_map item %d: %s" i m)
    | None -> failwith "cr_parallel_map: missing") res);;
