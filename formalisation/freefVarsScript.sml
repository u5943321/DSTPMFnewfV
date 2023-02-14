open HolKernel Parse boolLib bossLib;

val _ = new_theory "freefVars";



Definition freefVars_def:
  freefVars False = {} ∧
  freefVars (IMP f1 f2) = freefVars f1 ∪ freefVars f2 ∧
  freefVars (Pred _ _) = {} ∧
  (freefVars (fVar P sl tl) =
  if ok_abs sl then {(P,sl)} else {}) ∧
  freefVars (FALL s b) = freefVars b
End




Theorem freefVars_abs:
∀f i. freefVars (abs (n,s) i f) =
    freefVars f DIFF {(P,sl) | (P,sl) ∈ freefVars f ∧
    ∃st. MEM st sl ∧ (n,s) ∈ sfv st}
Proof
Induct_on ‘f’ (* 5 *)
>- rw[Once EXTENSION,freefVars_def,abs_def]
>- rw[Once EXTENSION,freefVars_def,abs_def]
>- (gs[EXTENSION,freefVars_def,abs_def] >> metis_tac[])
>- rw[Once EXTENSION,freefVars_def,abs_def] >>
rw[Once EXTENSION,freefVars_def,abs_def] (* 3 *)
>- (Cases_on ‘x’ >> gs[] >> rw[EQ_IMP_THM] (* 3 *)
   >>  metis_tac[slabs_id,NOT_ok_abs])
>- metis_tac[slabs_id,NOT_ok_abs] >>
metis_tac[slabs_id,NOT_ok_abs]
QED


Theorem freefVars_abs_SUBSET:
  freefVars (abs (n,s) i f) ⊆ freefVars f
Proof
  simp[freefVars_abs] >> rw[SUBSET_DEF]
QED


Theorem freefVars_fabs_SUBSET:
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
  freefVars (fabs (n,s) i f) ⊆ freefVars f
Proof
 metis_tac[freefVars_abs_SUBSET,fabs_abs]
QED


Theorem NOTIN_freefVars_frename:
∀f P sl n s nn.
        (∀st. MEM st sl ⇒ (nn,s) ∉ sfv st)  ∧
        (nn,s) ∉ ffv f ∧
        (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
        ok_abs sl ∧
        (P,sl) ∉ freefVars f ⇒
        (P,sl) ∉ freefVars (frename (n,s) nn f)
Proof
  reverse (Induct_on ‘f’) (* 5 *)
  >- (rw[]
      >> gs[freefVars_def,frename_def,finst_def] >>
      gs[GSYM srename_def,GSYM trename_def,GSYM frename_def] >>
      rw[] >>
      gs[ok_abs_rename] (* 2 *) >>
      (Cases_on ‘∃s. MEM s l ∧ (n,s') ∈ sfv s’ (* 2 *)
      >- (gs[] >> CCONTR_TAC >> gs[MEM_MAP] >>
         drule_at_then Any assume_tac $ cj 2 tfv_trename >>
         ‘sfv (srename (n,s') nn s) = sfv s DELETE (n,s') ∪ {(nn,s')}’ by metis_tac[] >> gs[PULL_EXISTS] >>
         ‘(nn,s') ∈ sfv (srename (n,s') nn s)’
          suffices_by metis_tac[] >>
         pop_assum SUBST_ALL_TAC >> simp[]) >>
      Cases_on ‘∃s. MEM s l ∧ (nn,s') ∈ sfv s’
      >- (gs[] >> CCONTR_TAC >> gs[] >>
          gs[MAP_fix] >>
          ‘(n,s') ∈ sfv s’
            by metis_tac[trename_fix] >>
          metis_tac[]) >>
      ‘ MAP (srename (n,s') nn) l = l’
        by (rw[MAP_fix] >> metis_tac[trename_fix]) >> gs[]))>>
 (gs[freefVars_def,frename_def,finst_def] >>
gs[GSYM srename_def,GSYM trename_def,GSYM frename_def] >>
rw[] >> metis_tac[])
QED        


 
Theorem freefVars_ok_abs:
∀f P sl. (P,sl) ∈ freefVars f ⇒ ok_abs sl
Proof
Induct_on ‘f’ >> simp[freefVars_def]
>- metis_tac[] >- metis_tac[] >> rw[]
QED

         

val _ = export_theory();

