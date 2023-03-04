open HolKernel Parse boolLib bossLib;

val _ = new_theory "wfap";


Inductive wfap:
wfap [] [] ∧
wfap sl tl ⇒ wfab     



val _ = export_theory();

