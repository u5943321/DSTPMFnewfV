open HolKernel Parse boolLib bossLib;
open finite_setTheory tmTheory fm1Theory listTheory;
open finite_mapTheory;
open pred_setTheory;
val _ = new_theory "fVinst1";


Theorem slprpl_id:
∀l.slbounds l = {} ⇒ ∀bmap. slprpl bmap l = l
Proof
rw[] >> irule LIST_EQ >> gs[LENGTH_slprpl] >>
rw[] >> drule_then assume_tac slprpl_EL >> simp[] >>
irule $ cj 2 tprpl_id >>
rw[FDOM_shift_bmap] >> rw[Once EXTENSION] >>
Cases_on ‘x' ∈ sbounds (EL x l)’ >> gs[] >>
gs[Once EXTENSION] >>
gs[IN_slbounds] >> rw[] >> metis_tac[] 
QED



Theorem ok_abs_slprpl_fix:
ok_abs l ⇒ slbounds l = {}
Proof
rw[Once EXTENSION] >> rw[IN_slbounds] >>
Cases_on ‘m < LENGTH l’ >> gs[] >>
gs[ok_abs_def] >>
first_x_assum $ drule_then assume_tac >>
gs[SUBSET_DEF] >>
CCONTR_TAC >>
gs[] >>
first_x_assum $ drule_then assume_tac >>
gs[]
QED        




Theorem tprpl_FMAP_MAP_tprpl:
(∀tm bmap0 bmap.
tbounds tm ⊆ FDOM bmap0 ⇒
tprpl (FMAP_MAP (tprpl bmap) bmap0) tm =
tprpl bmap (tprpl bmap0 tm)) ∧
(∀st bmap0 bmap.
sbounds st ⊆ FDOM bmap0 ⇒
sprpl (FMAP_MAP (tprpl bmap) bmap0) st =
sprpl bmap (sprpl bmap0 st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,tprpl_def,MAP_MAP_o,MAP_EQ_f] >>
rw[] (* 4 *)
>- (first_x_assum irule >> gs[SUBSET_DEF] >>
   metis_tac[])
>- (irule FAPPLY_FMAP_MAP >> simp[])
>- gs[FDOM_FMAP_MAP] >>
first_x_assum irule >> gs[SUBSET_DEF] >>
metis_tac[]
QED

        

Definition shift_bmap'_def:
  shift_bmap' i bmap =
  FUN_FMAP (λn. if i ≤ n then tshift i (bmap ' (n − i)) else Bound n) (count i ∪ (IMAGE ($+ i) (FDOM bmap)))
End  

         


Theorem FDOM_shift_bmap':
FDOM (shift_bmap' i bmap) = count i ∪ (IMAGE ($+i) (FDOM bmap))
Proof
rw[shift_bmap'_def]
QED



Theorem FAPPLY_shift_bmap':
 ∀x.(x ∈ FDOM bmap ⇒
 (shift_bmap' i bmap) ' (i + x) = tshift i (bmap ' x)) ∧
 ∀x. x < i ⇒ (shift_bmap' i bmap) ' x = Bound x
Proof
rw[shift_bmap'_def,FUN_FMAP_DEF]
QED
                  
Theorem tprpl_shift_bmap_shift_bmap':
(∀tm i bmap. tprpl (shift_bmap i bmap) tm =
tprpl (shift_bmap' i bmap) tm) ∧
(∀st i bmap. sprpl (shift_bmap i bmap) st =
sprpl (shift_bmap' i bmap) st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tprpl_def,MAP_EQ_f,FDOM_shift_bmap',FAPPLY_shift_bmap',FDOM_shift_bmap,FAPPLY_shift_bmap] >> rw[]  (* 5 *)
>- (drule_then assume_tac FAPPLY_shift_bmap >>
    gs[] >>
    drule_then assume_tac
               $ cj 1 FAPPLY_shift_bmap' >>
    gs[])
>- gs[] >>
gs[] >> drule_then assume_tac $ cj 2 FAPPLY_shift_bmap' >> gs[]
QED



Theorem tprpl_shift_bmap'_tshift:
(∀tm n bmap.
tprpl (shift_bmap' n bmap) (tshift n tm) =
tshift n (tprpl bmap tm)) ∧
(∀st n bmap.
sprpl (shift_bmap' n bmap) (sshift n st) =
sshift n (sprpl bmap st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,tprpl_def,tshift_def,MAP_MAP_o,MAP_EQ_f,FDOM_shift_bmap'] >> rw[] (* 4 *) >> gs[] >>
gs[tshift_def]
>- (drule_then assume_tac $ cj 1 FAPPLY_shift_bmap' >>
   simp[] >>
   ‘n = x’ by simp[] >> gs[]) >>
‘n = x’ by simp[] >> gs[] 
QED

                     
Theorem shift_bmap'_FMAP_MAP:
∀n bmap bmap0.
(FMAP_MAP (tprpl (shift_bmap' n bmap)) (shift_bmap' n bmap0)) =
(shift_bmap' n (FMAP_MAP (tprpl bmap) bmap0))
Proof
rw[fmap_EXT,FDOM_FMAP_MAP,FDOM_shift_bmap'] (* 2 *)
>- (drule_then assume_tac $ cj 2 FAPPLY_shift_bmap'>>
   simp[] >>
   ‘x ∈ FDOM (shift_bmap' n bmap)’
     by rw[FDOM_shift_bmap'] >>
  drule_then assume_tac FAPPLY_FMAP_MAP >>
  ‘FMAP_MAP (tprpl (shift_bmap' n bmap)) (shift_bmap' n bmap0) ' x =
  (tprpl (shift_bmap' n bmap))
  ((shift_bmap' n bmap0) ' x)’
   by (irule FAPPLY_FMAP_MAP >>
      simp[FDOM_shift_bmap']) >>
  simp[] >> rw[tprpl_def,FAPPLY_shift_bmap']) >>
rename [‘x ∈ FDOM bmap0’] >>
‘x ∈ FDOM (FMAP_MAP (tprpl bmap) bmap0)’
 by rw[FDOM_FMAP_MAP] >>
drule_then assume_tac $ cj 1 FAPPLY_shift_bmap' >>
simp[] >>
‘FMAP_MAP (tprpl (shift_bmap' n bmap)) (shift_bmap' n bmap0) ' (n + x) =
 (tprpl (shift_bmap' n bmap))
 ((shift_bmap' n bmap0) ' (n + x))’
 by (irule FAPPLY_FMAP_MAP >>
    simp[FDOM_shift_bmap'])>>
simp[] >>
rev_drule_then assume_tac $ cj 1 FAPPLY_shift_bmap'>>
simp[] >>
‘(FMAP_MAP (tprpl bmap) bmap0 ' x) =
 tprpl bmap (bmap0 ' x)’
 by (irule FAPPLY_FMAP_MAP >> simp[]) >>
simp[] >> 
rw[tprpl_shift_bmap'_tshift]
QED    

Definition bmap_eff_def:
bmap_eff bmap i = if i ∈ FDOM bmap then bmap ' i else Bound i
End

Theorem shift_bmap_shift_bmap'_bmap_eff:
∀n i bmap. bmap_eff (shift_bmap n bmap) i =
bmap_eff (shift_bmap' n bmap) i
Proof
rw[bmap_eff_def,
   FAPPLY_shift_bmap',FAPPLY_shift_bmap,
   FDOM_shift_bmap',FDOM_shift_bmap](* 3 *)
>> gs[] (* 2 *)
>- (drule_then assume_tac FAPPLY_shift_bmap >>
   drule_then assume_tac $ cj 1 FAPPLY_shift_bmap' >>
   simp[]) >>
drule_then assume_tac $ cj 2 FAPPLY_shift_bmap'>>
gs[]
QED


        
Definition bmap_equiv_def:
bmap_equiv bmap1 bmap2 ⇔
(∀i. bmap_eff bmap1 i = bmap_eff bmap2 i)
End
        
Theorem bmap_eff_tprpl:
(∀tm bmap1 bmap2.
  bmap_equiv bmap1 bmap2 ⇒
  tprpl bmap1 tm = tprpl bmap2 tm) ∧
(∀st bmap1 bmap2.
  bmap_equiv bmap1 bmap2 ⇒
  sprpl bmap1 st = sprpl bmap2 st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[bmap_equiv_def,tprpl_def,MAP_EQ_f,bmap_eff_def] >>
rw[]
QED


Theorem bmap_eff_shift_bmap:
bmap_eff (shift_bmap n bmap) i =
if ∃a. i = n + a ∧ a ∈ FDOM bmap then tshift n (bmap ' (i-n)) else Bound i
Proof
rw[bmap_eff_def] (* 3 *)
>- (drule_then assume_tac FAPPLY_shift_bmap >>
   simp[] >>
   ‘a + n = n + a’ by simp[] >>
   pop_assum SUBST_ALL_TAC >>
   gs[])
>- gs[FDOM_shift_bmap] >>
gs[FDOM_shift_bmap]
QED



                         
Theorem shift_bmap_equiv:
bmap_equiv bmap1 bmap2 ⇒
∀n. bmap_equiv (shift_bmap n bmap1) (shift_bmap n bmap2)
Proof
rw[shift_bmap_def,bmap_equiv_def,bmap_eff_shift_bmap] >>
Cases_on ‘∃a. i = a + n’ (* 2 *)
>- (gs[] >>
   Cases_on ‘a ∈ FDOM bmap1’ >> gs[] >>
   Cases_on ‘a ∈ FDOM bmap2’ >> gs[] (* 3 *)
   >- (gs[bmap_eff_def] >>
      first_x_assum (qspecl_then [‘a’] assume_tac)>>
      gs[])
   >- (gs[bmap_eff_def] >>
      first_x_assum (qspecl_then [‘a’] assume_tac) >>
      gs[] >>
      rw[tshift_def])
   >- (gs[bmap_eff_def] >>
      first_x_assum (qspecl_then [‘a’] assume_tac) >>
      gs[] >>
      rw[tshift_def] >>
      pop_assum (assume_tac o GSYM) >>
      gs[tshift_def])) >>
gs[]
QED      

         
        
Theorem bmap_eff_slprpl:
∀sl bmap1 bmap2.
  bmap_equiv bmap1 bmap2 ⇒
  slprpl bmap1 sl = slprpl bmap2 sl
Proof
rw[] >> irule LIST_EQ >>
simp[LENGTH_slprpl] >> rw[] >>
drule_then assume_tac slprpl_EL >>
simp[] >> irule $ cj 2 bmap_eff_tprpl >>
irule shift_bmap_equiv >> simp[]
QED


Theorem bmap_eff_fprpl:
∀f bmap1 bmap2.
  bmap_equiv bmap1 bmap2 ⇒
  fprpl bmap1 f = fprpl bmap2 f
Proof 
Induct_on ‘f’ >> gs[fprpl_def,MAP_EQ_f] >>
rw[] (* 5 *)
>- metis_tac[bmap_eff_tprpl]
>- metis_tac[bmap_eff_tprpl]
>- (first_x_assum irule >>
   irule shift_bmap_equiv >> simp[]) >>
metis_tac[bmap_eff_tprpl]
QED   



       
Theorem shift_bmap_shift_bmap'_equiv:
bmap_equiv (shift_bmap' n bmap) (shift_bmap n bmap)
Proof
rw[bmap_equiv_def,shift_bmap_shift_bmap'_bmap_eff]
QED 

Theorem fprpl_FMAP_MAP:
∀f bmap bmap0.
fbounds f ⊆ FDOM bmap0 ⇒ 
fprpl (FMAP_MAP (tprpl bmap) bmap0) f =
fprpl bmap (fprpl bmap0 f)
Proof
Induct_on ‘f’ >>
gs[fprpl_def,fbounds_thm,MAP_MAP_o,MAP_EQ_f] (* 3 *)
>- (rw[] >> irule $ cj 1 tprpl_FMAP_MAP_tprpl >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (rw[] (* 2 *)
   >- (irule $ cj 2 tprpl_FMAP_MAP_tprpl >>
       simp[]) >>
   ‘fbounds f ⊆ {0} ∪ IMAGE SUC (FDOM bmap0)’
    by (rw[SUBSET_DEF] >> gs[SUBSET_DEF,PULL_EXISTS]>>
       Cases_on ‘x = 0’ >> gs[] >>
       qspecl_then [‘x’] assume_tac arithmeticTheory.num_CASES >> gs[] >>
       first_x_assum $ drule_then assume_tac >>
       gs[]) >>
   first_assum (qspecl_then [‘shift_bmap' 1 bmap’,‘shift_bmap' 1 bmap0’] assume_tac) >>
   ‘fbounds f ⊆ FDOM (shift_bmap' 1 bmap0)’
    by (simp[FDOM_shift_bmap'] >>
        ‘{0} ∪ IMAGE SUC (FDOM bmap0) =
        count 1 ∪ IMAGE ($+ 1) (FDOM bmap0)’
         suffices_by (rw[] >> gs[]) >>
        rw[count_def,Once EXTENSION,arithmeticTheory.ADD1] >> ‘x = 0 ⇔ x < 1’ suffices_by metis_tac[] >>
        simp[]) >> 
   first_x_assum $ drule_then assume_tac >>
   ‘fprpl (shift_bmap' 1 (FMAP_MAP (tprpl bmap) bmap0)) f =
        fprpl (shift_bmap' 1 bmap) (fprpl (shift_bmap' 1 bmap0) f)’
   suffices_by
    (rw[] >>
     ‘fprpl (shift_bmap' 1 (FMAP_MAP (tprpl bmap) bmap0)) f = fprpl (shift_bmap 1 (FMAP_MAP (tprpl bmap) bmap0)) f’
      by (irule bmap_eff_fprpl >>
         rw[shift_bmap_shift_bmap'_equiv]) >>
     ‘fprpl (shift_bmap' 1 bmap0) f =
      fprpl (shift_bmap 1 bmap0) f’
      by (irule bmap_eff_fprpl >>
         rw[shift_bmap_shift_bmap'_equiv]) >>
     gs[] >> irule bmap_eff_fprpl >>
     rw[shift_bmap_shift_bmap'_equiv]) >>
   pop_assum (assume_tac o GSYM) >>
   pop_assum SUBST_ALL_TAC >>
   first_x_assum (qspecl_then [‘shift_bmap' 1 bmap’,‘shift_bmap' 1 bmap0’] assume_tac) >>
   gs[shift_bmap'_FMAP_MAP]) >>
reverse (rw[]) (* 2 *)
>- (irule $ cj 1 tprpl_FMAP_MAP_tprpl >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
irule LIST_EQ >> simp[LENGTH_slprpl] >>
rw[] >>
drule_then assume_tac slprpl_EL >>
simp[] >>
‘x < LENGTH (slprpl bmap0 l)’
  by simp[LENGTH_slprpl] >>
drule_then assume_tac slprpl_EL >>
simp[] >>
‘sprpl (shift_bmap' x (FMAP_MAP (tprpl bmap) bmap0)) (EL x l) =
        sprpl (shift_bmap' x bmap) (sprpl (shift_bmap' x bmap0) (EL x l))’
 suffices_by
  (rw[] >>
  ‘sprpl (shift_bmap' x (FMAP_MAP (tprpl bmap) bmap0)) (EL x l) =
  sprpl (shift_bmap x (FMAP_MAP (tprpl bmap) bmap0)) (EL x l)’
   by (irule $ cj 2 bmap_eff_tprpl >>
      rw[shift_bmap_shift_bmap'_equiv]) >>
  ‘(sprpl (shift_bmap' x bmap0) (EL x l)) =
   (sprpl (shift_bmap x bmap0) (EL x l))’
   by (irule $ cj 2 bmap_eff_tprpl >>
      rw[shift_bmap_shift_bmap'_equiv]) >>
  gs[] >>
  irule $ cj 2 bmap_eff_tprpl >>
  rw[shift_bmap_shift_bmap'_equiv]) >>
rw[GSYM shift_bmap'_FMAP_MAP] >>
irule $ cj 2 tprpl_FMAP_MAP_tprpl >>
simp[FDOM_shift_bmap'] >>
rw[SUBSET_DEF] >> Cases_on ‘x' < x’ >> gs[] >>
qexists ‘x' - x’ >> simp[] >>
‘x ≤ x'’ by simp[] >>
gs[SUBSET_DEF] >> last_x_assum irule >>
simp[IN_slbounds] >>
qexists ‘x’ >> simp[] 
QED


        

Definition fVmap_rename_def:
fVmap_rename (n,s) nn σ =
FUN_FMAP (λ(P,sl). frename (n,s) nn (σ ' (P,sl)))
(FDOM σ)
End

        
        
Theorem fVinst_id:
∀f ε. FDOM ε ∩ fVars f = {} ⇒
 fVinst ε f = f
Proof
Induct_on ‘f’ >> gs[fVinst_def,fVars_def] (* 2 *)
>- (rw[] (* 2 *) >>
    (first_x_assum irule >> gs[EXTENSION] >> metis_tac[]))>>
rw[] >> gs[EXTENSION]    
QED
        



Theorem FDOM_fVmap_rename:
FDOM (fVmap_rename (n,s) nn σ) = FDOM σ
Proof
rw[fVmap_rename_def]
QED 

Theorem FAPPLY_fVmap_rename:
(P,sl) ∈ FDOM σ ⇒
(fVmap_rename (n,s) nn σ) ' (P,sl) =
frename (n,s) nn (σ ' (P,sl))
Proof
rw[fVmap_rename_def,FUN_FMAP_DEF]  
QED

Theorem fVinst_fabs:
∀f i.
 (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
 (n,s) ∉ fVslfv f ∧
 (∀P sl.
    (P,sl) ∈ fVars f ∩ FDOM σ ⇒
    (nn,s) ∉ ffv (σ ' (P,sl)) ∧
    (∀st. MEM st sl ⇒ (n,s) ∉ sfv st ∧ (nn,s) ∉ sfv st)) ∧
 (nn,s) ∉ ffv f ∧
 nn ≠ n ⇒
(fVinst σ (fabs (n,s) i f)) =
       frename (nn,s) n
       (fabs (n,s) i (fVinst (fVmap_rename (n,s) nn σ)
                   f))
Proof
Induct_on ‘f’ >>
simp[fVinst_def,fabs_def,frename_alt,PULL_EXISTS,fVslfv_alt](* 4 *)
>- (rw[MAP_EQ_f,MAP_MAP_o] >>
    rw[Once EQ_SYM_EQ] >>
    irule $ cj 1 trename_fix >>
    ‘tfv (tabs (n,s) i e) ⊆ tfv e DELETE (n,s)’
     by (irule $ cj 1 tfv_tabs_SUBSET >> metis_tac[]) >>
    CCONTR_TAC >> gs[] >>
    ‘(nn,s) ∈ tfv e DELETE (n,s)’ by metis_tac[SUBSET_DEF]>>
    gs[] >> metis_tac[])
>- (rw[fVars_def] (* 2 *) >>
   (first_x_assum irule >> simp[] >> rw[] (* 3 *)
   >- metis_tac[]
   >- metis_tac[]
   >- metis_tac[])) 
>- (rw[] (* 2 *)
   >- (rw[Once EQ_SYM_EQ] >>
      irule $ cj 2 trename_fix >>
      ‘(nn,s) ∉ sfv s' DELETE (n,s)’
        suffices_by metis_tac[tfv_tabs_SUBSET,SUBSET_DEF] >>
      gs[]) >>
   ‘fVinst σ (fabs (n,s) (i +1) f) =
            frename (nn,s) n
              (fabs (n,s) (i+1) (fVinst (fVmap_rename (n,s) nn σ) f))’
    by (first_x_assum irule >> gs[fVars_def] >>
       metis_tac[])) >>
rw[] (* 4 *)
>- (rw[GSYM rich_listTheory.MAP_REVERSE,mk_bmap_MAP] >>
    ‘(fVmap_rename (n,s) nn σ ' (s',l)) =
     frename (n,s) nn (σ ' (s',l))’
     by (irule FAPPLY_fVmap_rename >> gs[FDOM_fVmap_rename])
     >> gs[] >>
    (*‘abssl (n,s) i l = l’
    by (irule abssl_id >>
       drule_at_then Any assume_tac $ iffLR abssl_ok_abs >>
    metis_tac[]) >>*) gs[] >> 
   irule fprpl_FMAP_MAP_fabs_IN >> simp[FDOM_mk_bmap] >>
   rw[] (* 3 *)
   >- (‘b < LENGTH (REVERSE l0)’ by simp[] >>
      drule_then assume_tac FAPPLY_mk_bmap >>
      gs[] >> ‘MEM (EL b (REVERSE l0)) l0’
      suffices_by metis_tac[] >>
      drule_then assume_tac EL_REVERSE >> simp[] >>
      simp[MEM_EL] >>
      irule_at Any EQ_REFL >> simp[]) 
   >- (‘b < LENGTH (REVERSE l0)’ by simp[] >>
drule_then assume_tac FAPPLY_mk_bmap >>
      gs[] >> ‘MEM (EL b (REVERSE l0)) l0’
      suffices_by metis_tac[] >>
      drule_then assume_tac EL_REVERSE >> simp[] >>
      simp[MEM_EL] >>
      irule_at Any EQ_REFL >> simp[])
   >- gs[fVars_def])
>- gs[FDOM_fVmap_rename]
>- gs[FDOM_fVmap_rename] >>
rw[fabs_def,frename_alt] (* 2 *)
>- (rw[Once EQ_SYM_EQ,MAP_fix] >>
   rw[Once EQ_SYM_EQ] >> irule $ cj 2 trename_fix >>
   pop_assum mp_tac >> simp[MEM_EL] >> rw[LENGTH_abssl] >>
   drule_then assume_tac abssl_EL >> simp[] >>
   ‘(nn,s) ∉ sfv (EL n' l)’ by metis_tac[MEM_EL] >>
   ‘sfv (sabs (n,s) (i+n') (EL n' l)) ⊆
     sfv (EL n' l) DELETE (n,s)’
     by (irule $ cj 2 tfv_tabs_SUBSET >>
         metis_tac[MEM_EL]) >>
  pop_assum mp_tac >> rw[SUBSET_DEF] >> metis_tac[]) >>
rw[Once EQ_SYM_EQ,MAP_fix] >>
pop_assum mp_tac >> simp[MEM_MAP] >>
rw[] >> rw[Once EQ_SYM_EQ] >> irule $ cj 1 trename_fix >>
‘(nn,s) ∉ tfv y’ by metis_tac[] >>
‘tfv (tabs (n,s) i y) ⊆ tfv y DELETE (n,s)’
 by (irule $ cj 1 tfv_tabs_SUBSET >>
    metis_tac[]) >>
pop_assum mp_tac >> rw[SUBSET_DEF] >> metis_tac[]    
QED


Definition fVmap_eff_def:
fVmap_eff σ (P,sl) = if (P,sl) ∈ FDOM σ then σ ' (P,sl) else
 fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
End



Theorem ok_abs_slprpl:
∀l bmap. ok_abs l ⇒ slprpl bmap l = l
Proof
rw[] >> irule LIST_EQ >> simp[LENGTH_slprpl] >>
rw[] >> drule_then assume_tac slprpl_EL >>
simp[] >>
irule $ cj 2 tprpl_id >>
simp[FDOM_shift_bmap] >>
gs[ok_abs_def] >>
first_x_assum $ drule_then assume_tac >>
rw[Once EXTENSION] >>
CCONTR_TAC >> gs[] >>
gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >> gs[]
QED


Theorem fVar_prpl_eq_lemma:
MAP (tprpl (mk_bmap (REVERSE l0)) ∘ Bound)
          (REVERSE (COUNT_LIST (LENGTH l0))) =
        l0
Proof        
 irule LIST_EQ >> simp[] >>
    simp[rich_listTheory.LENGTH_COUNT_LIST] >>
 rw[] >>
 ‘x < LENGTH (REVERSE (COUNT_LIST (LENGTH l0)))’
  by simp[rich_listTheory.LENGTH_COUNT_LIST] >>
  drule_then assume_tac $ INST_TYPE [alpha |-> “:num”,beta |-> “:term” ] EL_MAP >> simp[] >>
  simp[tprpl_def,FDOM_mk_bmap] >>
  ‘EL x (REVERSE (COUNT_LIST (LENGTH l0))) < LENGTH l0’
   by (irule $ iffLR rich_listTheory.MEM_COUNT_LIST >>
      simp[MEM_EL] >> qexists ‘PRE (LENGTH l0 - x)’ >>
      simp[] >> rw[] (* 2 *)
      >- gs[rich_listTheory.LENGTH_COUNT_LIST] >>
      ‘ EL x (REVERSE (COUNT_LIST (LENGTH l0))) =
        EL (PRE (LENGTH (COUNT_LIST (LENGTH l0)) − x)) (COUNT_LIST (LENGTH l0))’ suffices_by gs[rich_listTheory.LENGTH_COUNT_LIST] >>
      irule EL_REVERSE >> simp[rich_listTheory.LENGTH_COUNT_LIST]) >>
  simp[] >>
  ‘(EL x (REVERSE (COUNT_LIST (LENGTH l0)))) < LENGTH (REVERSE l0)’
   by gs[LENGTH_REVERSE] >>
  drule_then assume_tac FAPPLY_mk_bmap >> gs[] >>
   drule_then assume_tac EL_REVERSE >> simp[] >>
   ‘(PRE (LENGTH l0 − EL x (REVERSE (COUNT_LIST (LENGTH l0))))) = x’ suffices_by metis_tac[] >>
    qpat_x_assum ‘x < LENGTH (COUNT_LIST (LENGTH l0))’
  assume_tac >>
 drule_then assume_tac EL_REVERSE >> simp[] >>
 simp[rich_listTheory.LENGTH_COUNT_LIST] >>
 ‘(PRE (LENGTH l0 − x)) < LENGTH l0’
  by gs[] >>
  drule_then assume_tac rich_listTheory.EL_COUNT_LIST >>
  simp[]
QED

(*

Theorem fprpl_mk_bmap_REVERSE_plainfV:
LENGTH l = LENGTH l0 ⇒
fprpl (mk_bmap (REVERSE l0)) (plainfV (s,l)) = fVar s l l0
Proof
simp[plainfV_def,fprpl_def,MAP_MAP_o,fVar_prpl_eq_lemma]
QED
*)                

Theorem fVar_prpl_fabs1:
∀f i σ.
       (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
       (n,s) ∉ fVslfv f ∧
       (∀P sl. (P,sl) ∈ FDOM σ ∩ fVars f⇒
        (n,s) ∉ ffv (σ ' (P,sl))) ⇒
       fVinst σ (fabs (n,s) i f) =
       fabs (n,s) i (fVinst σ f)
Proof
Induct_on ‘f’ >> rw[] (* 5 *)
>- rw[fabs_def,fVinst_def]
>- gs[fabs_def,fVinst_def,fVars_def]
>- (gs[fabs_def,fVinst_def,fVars_def,fVslfv_alt] (* 2 *) >>
   rw[] (* 2 *)
   >>first_x_assum irule >> metis_tac[])
>- (gs[fabs_def,fVinst_def,fVars_def,fVslfv_alt] >>
   metis_tac[]) >>
gs[fabs_def,fVinst_def,fVars_def] >> rw[] (* 2 *)
>- (rw[mk_bmap_MAP,GSYM rich_listTheory.MAP_REVERSE] >>
   gs[] >>
    metis_tac[fprpl_mk_bmap_abs]) >>
rw[fabs_def]
QED
        

Theorem ofFMAP_EMPTY:
ofFMAP f1 f2 {} = {}
Proof
rw[ofFMAP_def]
QED
        


Theorem ofFMAP_UNION:
ofFMAP f σ (s1 ∪ s2) = ofFMAP f σ s1 ∪ ofFMAP f σ s2
Proof
rw[ofFMAP_def,EXTENSION] >> metis_tac[]
QED        



Theorem ofFMAP_Sing:
x ∈ FDOM σ ⇒ ofFMAP f σ {x} =  f (σ ' x)
Proof
rw[ofFMAP_def,Once EXTENSION,PULL_EXISTS] >> metis_tac[]
QED                           


Theorem ofFMAP_FDOM:
ofFMAP f σ (FDOM σ ∩ A) = ofFMAP f σ A
Proof
rw[ofFMAP_def,Once EXTENSION,PULL_EXISTS] >> metis_tac[]
QED                           

Theorem ofFMAP_Sing_EMPTY:
x ∉ FDOM σ ⇒ ofFMAP f σ {x} =  {}
Proof
rw[ofFMAP_def,Once EXTENSION,PULL_EXISTS] >> metis_tac[]
QED                           

                              


Theorem ffv_fVinst:
∀f σ. 
(∀P sl n s.(P,sl) ∈ FDOM σ ∩ fVars f ⇒
             (n,s) ∈ ffv (σ ' (P,sl)) ⇒ sbounds s = ∅) ⇒
ffv f ∪ ffv (fVinst σ f) =
ffv f ∪ ofFMAP ffv σ (FDOM σ ∩ fVars f)
Proof
Induct_on ‘f’ >>
gs[fVars_def,fVinst_def,ffv_thm,ofFMAP_EMPTY,fVslfv_alt]
(* 3 *)
>- (rw[] >>
   ‘ffv f ∪ ffv f' ∪ (ffv (fVinst σ f) ∪ ffv (fVinst σ f')) =
    (ffv f ∪ ffv (fVinst σ f)) ∪ (ffv f' ∪ ffv (fVinst σ f'))’  by (gs[EXTENSION] >> metis_tac[]) >>
   ‘ffv f' ∪ ffv (fVinst σ f') =
            ffv f' ∪ ofFMAP ffv σ (FDOM σ ∩ fVars f')’
    by metis_tac[] >>
   ‘ffv f ∪ ffv (fVinst σ f) =
            ffv f ∪ ofFMAP ffv σ (FDOM σ ∩ fVars f)’
    by metis_tac[] >>
    gs[] >> gs[UNION_OVER_INTER,ofFMAP_UNION] >>
    gs[EXTENSION] >> metis_tac[])
>- (rw[] >>
   ‘ffv f ∪ ffv (fVinst σ f) =
            ffv f ∪ ofFMAP ffv σ (FDOM σ ∩ fVars f)’
    by metis_tac[] >>
   gs[EXTENSION] >> metis_tac[]) >>
rw[] (* 2 *)
>- (‘FDOM σ ∩ {(s,l)} = {(s,l)}’
    by (gs[EXTENSION] >> metis_tac[]) >>
   gs[ofFMAP_Sing] >>
   drule_then assume_tac ffv_fprpl >>
   gs[] >> gs[FDOM_mk_bmap] >> 
   ‘  {tfv (mk_bmap (REVERSE l0) ' i) |
            i |
            i ∈ FDOM (mk_bmap (REVERSE l0)) ∧ i ∈ fbounds (σ ' (s,l))} ⊆  {tfv t | MEM t l0}’
     by (gs[FDOM_mk_bmap] >> rw[SUBSET_DEF] >>
        irule_at Any EQ_REFL >>
        ‘i < LENGTH (REVERSE l0)’ by simp[] >>
        drule_then assume_tac FAPPLY_mk_bmap >>
        gs[] >> gs[MEM_EL] >>
        drule_then assume_tac EL_REVERSE >> simp[] >>
        irule_at Any EQ_REFL >>
        gs[])>> gs[FDOM_mk_bmap] >>
   drule_then assume_tac SUBSET_BIGUNION >>
   gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
gs[ofFMAP_FDOM,ofFMAP_Sing_EMPTY]
QED     



        



Theorem sbounds_frename_EMPTY:
(∀n s. (n,s) ∈ ffv f ⇒ sbounds s = {}) ⇒
(∀n s. (n,s) ∈ ffv (frename (n0,s0) nn f) ⇒ sbounds s = {})
Proof
  rw[] >> CCONTR_TAC >>
  ‘∃i. i ∈ sbounds s’
    by metis_tac[MEMBER_NOT_EMPTY] >>
  ‘i ∈ BIGUNION (IMAGE (sbounds o SND)
                 (ffv (frename (n0,s0) nn f)))’
              by (rw[IMAGE_DEF,PULL_EXISTS] >>
                  qexists ‘(n,s)’ >> simp[]) >>
   ‘BIGUNION (IMAGE (sbounds ∘ SND) (ffv (frename (n0,s0) nn f))) = BIGUNION (IMAGE (sbounds ∘ SND) (ffv f))’
            by metis_tac[BIGUNION_IMAGE_sbounds_ffv] >>         ‘BIGUNION (IMAGE (sbounds ∘ SND) (ffv f)) = {}’
            suffices_by (strip_tac >> gs[] >> gs[EXTENSION]>>
             metis_tac[])  >>
  rw[Once EXTENSION] >>
  Cases_on ‘ (∀x. x ∉ ffv f)’ >> simp[] >>
  simp[Once EXTENSION,IMAGE_DEF] >> 
  rw[] >>
  rw[EQ_IMP_THM] (* 2 *)
  >- (Cases_on ‘x'’ >> simp[] >> metis_tac[]) >>
  gs[] >> qexists ‘x'’ >> simp[] >>
  Cases_on ‘x'’ >> simp[] >> metis_tac[]          
QED 


Theorem fVars_fabs:
 ∀f v i. fVars (fabs v i f) = fVars f
Proof 
 Induct_on ‘f’ >>
 gs[fVslfv_def,fabs_def,fVars_def,Uof_UNION]
QED



   
Theorem fVars_DRESTRICT_fVinst_eq0:
∀f σ1 σ2.
 FDOM σ1 ∩ fVars f = FDOM σ2 ∩ fVars f ∧
 (∀fv. fv ∈ FDOM σ1 ∩ fVars f ⇒ σ1 ' fv = σ2 ' fv) ⇒
 fVinst σ1 f = fVinst σ2 f
Proof
  Induct_on ‘f’ >> gs[fVinst_def,fVars_def,DRESTRICT_DEF] >>
  rw[] (* 4 *)
  >>(gs[EXTENSION] >> metis_tac[])
QED  


Theorem fVars_DRESTRICT_fVinst_eq1:
∀f σ s.
 fVars f ⊆ s ⇒ 
 fVinst σ f = fVinst (DRESTRICT σ s) f
Proof
  rw[] >>
  irule fVars_DRESTRICT_fVinst_eq0 >> simp[DRESTRICT_DEF] >>
  gs[EXTENSION] >> rw[] >> gs[SUBSET_DEF] >>
  metis_tac[]
QED  
  
       

Theorem fVars_DRESTRICT_fVinst_eq:
∀f σ.
  fVinst (DRESTRICT σ (fVars f)) f =  fVinst σ f
Proof
  rw[] >>
  irule fVars_DRESTRICT_fVinst_eq0 >> simp[DRESTRICT_DEF] >>
  gs[EXTENSION] >> metis_tac[]
QED  

(*because the new ver of fprpl does not touch fVars*)
Theorem fVars_fprpl:
∀f bmap. 
fVars (fprpl bmap f) = fVars f
Proof
Induct_on ‘f’ >> gs[fVars_def,fprpl_def]
QED
 
     
Theorem fVars_fVinst:
∀f σ. fVars f ∪ fVars (fVinst σ f) =
      fVars f ∪ ofFMAP fVars σ (fVars f)
Proof      
Induct_on ‘f’ >> gs[fVars_def,ofFMAP_UNION,fVinst_def,ofFMAP_EMPTY] (* 2 *)
>- (gs[EXTENSION] >> metis_tac[]) >>
reverse
(rw[] >> gs[ofFMAP_Sing_EMPTY,ofFMAP_Sing] (* 2 *))
>- gs[fVars_def] >>
rw[fVars_fprpl]
QED

     

Theorem fVinst_EQ:
(fVinst σ (EQ t1 t2)) = EQ t1 t2
Proof
rw[EQ_def,fVinst_def]
QED



        




val _ = export_theory();

