(* ========================================================================= *)
(* Port of Compact/Cases/C979/EntryQueryChunks/Chunk11.lean (namespace S12):*)
(* direct single-owner domains of the C979 entry.  A Lean DirectSingleDomain  *)
(* <mask, lower, upper, allowed, queries> is the dsd record of               *)
(* SmallOwnerDomainThree.ml; its queries are indices: (certified_query% n)    *)
(* is n (S12.localQueries; C979SharedSelections.selectedN = query N), HistoricalOwnership.Queries.queryN_certified is   *)
(* slq_hist_idx N (registered by QueriesNNN.ml).  Lean  w_checked : w.Check   *)
(* case979Family k  (SmallOwnerDomain.checked / SmallOwnerDomainThree.checked,*)
(* whose private signature lists are just the query signatures) is           *)
(*   dsd_actual / sodt_checked `c979eqb_family` k w : |- hdom fam mask k allowed*)
(* (budget equalities lower / upper, every subset in the interval allowed or *)
(* refuted by a kernel-checked exact query).  Tag C979EQC11_.                     *)
(* ========================================================================= *)

needs "n12/geometry/Cases_C979_EntryQueryBase.ml";;
needs "n12/geometry/SmallOwnerDomainThree.ml";;
needs "n12/geometry/Chunk49.ml";;

needs "n12/geometry/Queries054.ml";;
needs "n12/geometry/Queries055.ml";;
needs "n12/geometry/Queries056.ml";;
needs "n12/geometry/Queries057.ml";;

(* Lean: single979_5_1 *)
let c979eqc11_single979_5_1 = { dmask = 256; dlower = 1; dupper = 3;
  dallowed = [[0]; [2]; [0; 2]; [3]; [0; 3]; [1; 3]; [0; 1; 3]; [2; 3]; [0; 2; 3]; [2; 5]; [0; 2; 5]; [3; 5]; [0; 3; 5]; [2; 3; 5]; [2; 6]; [0; 2; 6]; [3; 6]; [0; 3; 6]; [2; 3; 6]; [2; 5; 6]; [3; 5; 6]];
  dqueries = [473; 474; 475; slq_hist_idx 1730; slq_hist_idx 1731; 476; 477; 478; slq_hist_idx 1732; 479; slq_hist_idx 1733; slq_hist_idx 1734; 480; slq_hist_idx 1735; slq_hist_idx 1736; slq_hist_idx 1737; 481; 482; 483; slq_hist_idx 1738; slq_hist_idx 1739; slq_hist_idx 1740; 484; slq_hist_idx 1741; slq_hist_idx 1742; slq_hist_idx 1743; slq_hist_idx 1744; 485; 486; 487; slq_hist_idx 1745; slq_hist_idx 1746; slq_hist_idx 1747; 488; slq_hist_idx 1748; slq_hist_idx 1749; slq_hist_idx 1750; slq_hist_idx 1751; 489; slq_hist_idx 1752; slq_hist_idx 1753; slq_hist_idx 1754; 490; 491; 492; slq_hist_idx 1755; 493; slq_hist_idx 1756; slq_hist_idx 1757; 494; slq_hist_idx 1758; slq_hist_idx 1759; slq_hist_idx 1760; 495; slq_hist_idx 1761; slq_hist_idx 1762; slq_hist_idx 1763; slq_hist_idx 1764; 496; slq_hist_idx 1765; slq_hist_idx 1766; slq_hist_idx 1767; slq_hist_idx 1768; slq_hist_idx 1769; 497; slq_hist_idx 1770; slq_hist_idx 1771; slq_hist_idx 1772; slq_hist_idx 1773; slq_hist_idx 1774; slq_hist_idx 1775; 498; 499; 500; slq_hist_idx 1776; 501; slq_hist_idx 1777; slq_hist_idx 1778; 502; slq_hist_idx 1779; slq_hist_idx 1780; slq_hist_idx 1781; 503; slq_hist_idx 1782; slq_hist_idx 1783; slq_hist_idx 1784; slq_hist_idx 1785; 504; slq_hist_idx 1786; slq_hist_idx 1787; slq_hist_idx 1788; slq_hist_idx 1789; slq_hist_idx 1790; 505; slq_hist_idx 1791; slq_hist_idx 1792; slq_hist_idx 1793; slq_hist_idx 1794; slq_hist_idx 1795; slq_hist_idx 1796; 506; slq_hist_idx 1797; slq_hist_idx 1798; slq_hist_idx 1799; slq_hist_idx 1800; slq_hist_idx 1801; slq_hist_idx 1802; slq_hist_idx 1803; 507; 508; 509; slq_hist_idx 1804; 510; slq_hist_idx 1805; slq_hist_idx 1806; 511; slq_hist_idx 1807; slq_hist_idx 1808; slq_hist_idx 1809; 512; slq_hist_idx 1810; slq_hist_idx 1811; slq_hist_idx 1812; slq_hist_idx 1813; 513; slq_hist_idx 1814; slq_hist_idx 1815; slq_hist_idx 1816; slq_hist_idx 1817; slq_hist_idx 1818; 514; slq_hist_idx 1819; slq_hist_idx 1820; slq_hist_idx 1821; slq_hist_idx 1822; slq_hist_idx 1823; slq_hist_idx 1824; 515; slq_hist_idx 1825; slq_hist_idx 1826; slq_hist_idx 1827; slq_hist_idx 1828; slq_hist_idx 1829; slq_hist_idx 1830; slq_hist_idx 1831; 516; slq_hist_idx 1832; slq_hist_idx 1833; slq_hist_idx 1834; slq_hist_idx 1835; slq_hist_idx 1836; slq_hist_idx 1837; slq_hist_idx 1838; slq_hist_idx 1839] };;
(* Lean: single979_5_1_checked *)
let C979EQC11_SINGLE979_5_1_CHECKED = sodt_checked `c979eqb_family` 1 c979eqc11_single979_5_1;;
