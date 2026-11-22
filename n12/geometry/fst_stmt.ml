(* The statement of Jatloe's FourSquareTemplate.impossible, as a HOL term.
   The ported template (n12/geometry/FourSquareTemplate.ml) must prove exactly
   this term:   let FST_IMPOSSIBLE = prove(FST_STMT, ...)                   *)

needs "n12/geometry/p2_base.ml";;

(* the template statement (Jatloe: FourSquareTemplate.impossible) *)
let FST_STMT =
  let sq n = map (fun v -> mk_var(v ^ n, `:real`)) ["c"; "s"; "u"; "v"; "a"] in
  let A = sq "A" and B = sq "B" and L = sq "L" and R = sq "R" in
  let app f q args = list_mk_icomb (fst(dest_const f)) (q @ args) in
  let pt (x,y) = [parse_term x; parse_term y] in
  let cl q p = app `lclosed` q (pt p) and op q p = mk_neg(app `linside` q (pt p)) in
  let side q = el 4 q in
  let hyps =
    [app `lsquare` A []; app `lsquare` B []; app `lsquare` L []; app `lsquare` R [];
     mk_binop `(<):real->real->bool` `&1` (side B); mk_binop `(<=):real->real->bool` (side B) `&1001 / &1000`;
     mk_eq(side A, side B); mk_eq(side B, side L); mk_eq(side B, side R);
     app `lcont` B []; app `lcont` L []; app `lcont` R [];
     cl A ("&2","&113 / &50"); cl A ("&113 / &50","&2"); cl A ("&47 / &20","&47 / &20");
     op A ("&33 / &20","&33 / &20"); op A ("&47 / &20","&33 / &20");
     cl B ("&33 / &20","&47 / &20"); cl B ("&8 / &5","&3"); cl B ("&87 / &50","&3");
     op B ("&1","&1543 / &500"); op B ("&2","&1543 / &500");
     cl L ("&457 / &500","&2"); cl L ("&1","&12 / &5"); op L ("&19 / &25","&187 / &100");
     op L ("&33 / &20","&33 / &20");
     cl R ("&3","&12 / &5"); cl R ("&1543 / &500","&2"); op R ("&81 / &25","&187 / &100");
     app `ldisj` A B; app `ldisj` A R; app `ldisj` B L; app `ldisj` B R] in
  list_mk_forall(A @ B @ L @ R, mk_imp(list_mk_conj hyps, `false`));;

