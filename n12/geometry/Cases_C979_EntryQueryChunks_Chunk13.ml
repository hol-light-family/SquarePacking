(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk13.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC13_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;

needs "n12/geometry/Chunk49.ml";;
needs "n12/geometry/Queries059.ml";;
needs "n12/geometry/Queries060.ml";;
needs "n12/geometry/Queries061.ml";;
needs "n12/geometry/Queries062.ml";;
needs "n12/geometry/Queries063.ml";;

(* Lean: single979_6_1 *)
let c979eqc13_single979_6_1 = { dmask = 512; dlower = 1; dupper = 3;
  dallowed = [[5]; [2; 5]; [3; 5]; [2; 3; 5]; [6]; [2; 6]; [3; 6]; [2; 3; 6]; [5; 6]; [2; 5; 6]; [3; 5; 6]; [8]; [5; 8]; [2; 5; 8]; [3; 5; 8]; [6; 8]; [2; 6; 8]; [3; 6; 8]; [5; 6; 8]; [6; 9]; [6; 8; 9]];
  dqueries = [626; 627; 628; 629; 630; 631; slq_hist_idx 1910; 632; 633; 634; slq_hist_idx 1911; 635; slq_hist_idx 1912; slq_hist_idx 1913; 636; 637; 638; slq_hist_idx 1914; 639; slq_hist_idx 1915; slq_hist_idx 1916; 640; slq_hist_idx 1917; slq_hist_idx 1918; slq_hist_idx 1919; 641; 642; slq_hist_idx 1920; slq_hist_idx 1921; slq_hist_idx 1922; slq_hist_idx 1923; slq_hist_idx 1924; 643; slq_hist_idx 1925; slq_hist_idx 1926; slq_hist_idx 1927; slq_hist_idx 1928; 644; 645; slq_hist_idx 1929; slq_hist_idx 1930; slq_hist_idx 1931; slq_hist_idx 1932; slq_hist_idx 1933; 646; slq_hist_idx 1934; slq_hist_idx 1935; slq_hist_idx 1936; slq_hist_idx 1937; slq_hist_idx 1938; slq_hist_idx 1939; slq_hist_idx 1940; 647; 648; 649; slq_hist_idx 1941; 650; slq_hist_idx 1942; slq_hist_idx 1943; 651; slq_hist_idx 1944; slq_hist_idx 1945; slq_hist_idx 1946; 652; slq_hist_idx 1947; slq_hist_idx 1948; slq_hist_idx 1949; slq_hist_idx 1950; 653; slq_hist_idx 1951; slq_hist_idx 1952; slq_hist_idx 1953; slq_hist_idx 1954; slq_hist_idx 1955; 654; slq_hist_idx 1956; slq_hist_idx 1957; slq_hist_idx 1958; slq_hist_idx 1959; slq_hist_idx 1960; slq_hist_idx 1961; 655; 656; slq_hist_idx 1962; 657; slq_hist_idx 1963; slq_hist_idx 1964; 658; slq_hist_idx 1965; slq_hist_idx 1966; slq_hist_idx 1967; 659; slq_hist_idx 1968; slq_hist_idx 1969; slq_hist_idx 1970; slq_hist_idx 1971; slq_hist_idx 1972; slq_hist_idx 1973; slq_hist_idx 1974; slq_hist_idx 1975; slq_hist_idx 1976; slq_hist_idx 1977; 660; slq_hist_idx 1978; slq_hist_idx 1979; slq_hist_idx 1980; slq_hist_idx 1981; slq_hist_idx 1982; slq_hist_idx 1983; slq_hist_idx 1984; 661; 662; 663; slq_hist_idx 1985; 664; slq_hist_idx 1986; slq_hist_idx 1987; 665; slq_hist_idx 1988; slq_hist_idx 1989; slq_hist_idx 1990; 666; slq_hist_idx 1991; slq_hist_idx 1992; slq_hist_idx 1993; slq_hist_idx 1994; 667; slq_hist_idx 1995; slq_hist_idx 1996; slq_hist_idx 1997; slq_hist_idx 1998; slq_hist_idx 1999; slq_hist_idx 2000; slq_hist_idx 2001; slq_hist_idx 2002; slq_hist_idx 2003; slq_hist_idx 2004; slq_hist_idx 2005; 668; slq_hist_idx 2006; slq_hist_idx 2007; slq_hist_idx 2008; slq_hist_idx 2009; slq_hist_idx 2010; slq_hist_idx 2011; slq_hist_idx 2012; 669; slq_hist_idx 2013; slq_hist_idx 2014; slq_hist_idx 2015; slq_hist_idx 2016; slq_hist_idx 2017; slq_hist_idx 2018; slq_hist_idx 2019] };;
(* Lean: single979_6_1_checked *)
let C979EQC13_SINGLE979_6_1_CHECKED = sodt_checked `c979eqb_family` 1 c979eqc13_single979_6_1;;
