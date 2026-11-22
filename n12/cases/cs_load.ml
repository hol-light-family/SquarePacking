needs "n12/upper.ml";;
needs "n12/phase1/normalize.ml";;
needs "n12/phase1/groups.ml";;
needs "shared/tools/domains.ml";;
let SQ_PORT_DOMAINS = sq_ndomains 16;;
loadt "n12/phase1/families_check.ml";;
let FAMILIES_CLASSIFIED = families_theorem SQ_PORT_DOMAINS 6;;
loadt "n12/phase1/bridge.ml";;
loadt "n12/phase1/hull.ml";;
let S12_REDUCED_577 = prove
 (`forall t. packs 12 t /\ t < &4
       ==> exists c1 c2 a b l. NPACK c1 c2 a b l /\ GOALF (FFP c1 c2 a b l)`,
  MESON_TAC[PACKS12_NORMALIZE; PACKING_REDUCED]);;
needs "n12/phase1/step6.ml";;
print_string "CS step6\n";;
needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/fs_bridge.ml";;
needs "n12/geometry/gen_bridge.ml";;
needs "n12/geometry/cornerpair.ml";;
needs "n12/geometry/var_data.ml";;
needs "n12/geometry/hr_data.ml";;
needs "n12/geometry/promote.ml";;
print_string "CS bridges\n";;
