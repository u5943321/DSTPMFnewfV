open HolKernel Parse boolLib bossLib;

val _ = new_theory "wff";


Inductive wff:
[~False:]
(wff (Σf,Σp,Σe) False) ∧
[~EQ:]
  (wft Σf t1 ∧ wft Σf t2 ∧ sort_of t1 = sort_of t2 ∧
  has_eq Σe (tsname t2) ⇒ wff (Σf,Σp,Σe) (EQ t1 t2)) ∧
[~Pred:]
  ((∀t. MEM t tl ⇒ wft Σf t) ∧
ispsym Σp p ∧
IS_SOME
(tlmatch {} (MAP (UNCURRY Var) (Σp ' p)) tl FEMPTY) ⇒
wff (Σf,Σp,Σe) (Pred p tl)) ∧
[~IMP:]
  (wff (Σf,Σp,Σe) f1 ∧ wff (Σf,Σp,Σe) f2 ⇒
  wff (Σf,Σp,Σe) (IMP f1 f2)) ∧
[~fVar:]
  (wffstl Σf sl tl ⇒
  wff (Σf,Σp,Σe) (fVar P sl tl)) ∧
[~FALL:]
 (∀f n s.
  wff (Σf,Σp,Σe) f ∧ wfs Σf s ∧
  (n,s) ∉ fVslfv f ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
  wff (Σf,Σp,Σe) (mk_FALL n s f))
End




 
Definition wffVmap_def:
  wffVmap Σ ε ⇔
  ∀P:string sl.
    (P,sl) ∈ FDOM ε ⇒ wff Σ (FALLL sl (ε ' (P,sl)))
End
        
        

       
Theorem wff_EQ:
  wfsig (Σf,Σp,Σe) ⇒
  (wff (Σf,Σp,Σe) (EQ t1 t2) ⇔
     wft Σf t1 ∧ wft Σf t2 ∧ sort_of t1 = sort_of t2 ∧
     has_eq Σe (tsname t2))
Proof
 rw[Once wff_cases,EQ_def,mk_FALL_def] >> gs[wfsig_def]
QED 



Theorem wff_finst:
  ∀f. wff (Σf,Σp,Σe) f ⇒
  (∀fsym. isfsym Σf fsym ⇒ sfv (fsymout Σf fsym) ⊆ BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
  ∀σ. cstt σ ∧ wfcod Σf σ ∧ ffv f ⊆ FDOM σ ∧ presname σ ⇒
  wff (Σf,Σp,Σe) (finst σ f)
Proof
  Induct_on ‘wff’ >> simp[] >> rw[] (* 6 *)
  >- metis_tac[wff_rules]
  >- (rw[finst_EQ] >> irule $ cj 2 wff_rules >>
     rw[] (* 4 *)
     >- (‘sort_of (tinst σ t1) = sinst σ (sort_of t1) ∧
         sort_of (tinst σ t2) = sinst σ (sort_of t2)’
         suffices_by metis_tac[] >> strip_tac (* 2 *)
        >> (irule cstt_sort_of_tinst >> simp[] >>
           metis_tac[wfcod_no_bound,wft_no_bound]))
     >- (‘(tsname (tinst σ t2)) = tsname t2’ suffices_by metis_tac[] >>
         irule $ cj 1 tsname_tinst >> metis_tac[wft_not_bound])
     >> (irule $ cj 1 wft_tinst >> gs[ffv_EQ]))
  >- (irule $ cj 3 wff_rules >> simp[MEM_MAP] >>
     rw[] (* 2 *)
     >- (first_x_assum drule >>
        rw[] >> irule $ cj 1 wft_tinst >>
        rw[] >> gs[SUBSET_DEF,MEM_MAP] >>
        metis_tac[]) >>
     irule IS_SOME_tlmatch_inst >> simp[] >>
     metis_tac[])
  >- (irule $ cj 4 wff_rules >> rw[])
  >- (irule $ cj 5 wff_rules >> irule tinst_wffstl >> simp[] >>
      gs[tlfv_def]) >>
  first_x_assum drule >> rw[] >>
  rw[mk_FALL_def] >>
  ‘∃σ1. cstt σ1 ∧ wfcod Σf σ1 ∧ ffv (mk_FALL n s f) = FDOM σ1 ∧
        presname σ1 ∧
  (wff (Σf,Σp,Σe) (FALL (sinst σ1 s) (finst σ1 (abst (n,s) f))) ⇒ wff (Σf,Σp,Σe) (FALL (sinst σ s) (finst σ (abst (n,s) f))))’
  by (qabbrev_tac ‘σ1 = DRESTRICT σ (ffv (mk_FALL n s f))’ >>
     qexists ‘σ1’ >>
     ‘cstt σ1’
       by (drule DRESTRICT_cstt >>
          rw[Abbr‘σ1’] >> first_x_assum irule >> simp[] >>
          rw[ffv_is_cont]) >> simp[] >>
     ‘wfcod Σf σ1’ by metis_tac[DRESTRICT_wfcod] >>
     simp[] >>
     ‘ffv (mk_FALL n s f) = FDOM σ1’
       by (rw[Abbr‘σ1’,DRESTRICT_DEF]  >>
          gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
     simp[] >>
     ‘(sinst σ1 s) = (sinst σ s)’
       by (irule $ cj 2 fmap_fv_inst_eq_alt >>
          gs[mk_FALL_def,ffv_def] >>
          ‘sfv s ⊆ FDOM σ1 ∧ sfv s ⊆ FDOM σ’
          by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
          simp[] >> rw[] >>
          ‘x ∈ FDOM σ1 ∧ x ∈ FDOM σ’
           by metis_tac[SUBSET_DEF] >>
          gs[Abbr‘σ1’,DRESTRICT_DEF]) >>
     ‘finst σ1 (abst (n,s) f) =
      finst σ (abst (n,s) f)’
      by (irule $ fmap_ffv_finst_eq >>
      gs[mk_FALL_def,ffv_def] >>
      ‘ffv (abst (n,s) f) ⊆ FDOM σ1 ∧ ffv (abst (n,s) f) ⊆ FDOM σ’
          by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
      simp[] >> rw[] >>
     ‘x ∈ FDOM σ1 ∧ x ∈ FDOM σ’
           by metis_tac[SUBSET_DEF] >>
      gs[Abbr‘σ1’,DRESTRICT_DEF]) >> simp[] >>
      simp[Abbr‘σ1’] >>
      metis_tac[presname_DRESTRICT]) >>
  first_x_assum irule>>
  qpat_x_assum ‘ffv (mk_FALL n s f) ⊆ FDOM σ’ (K all_tac) >>
  qpat_x_assum ‘ cstt σ’ (K all_tac) >>
  qpat_x_assum ‘wfcod Σf σ’ (K all_tac) >>
  qpat_x_assum ‘presname σ’ (K all_tac) >>
  rename [‘ cstt σ’]>>
  rw[abst_def] >>(*need lemma ffv_mk_FALL*)
  drule ffv_mk_FALL >>
  ‘(∀P sl s0. (P,sl) ∈ fVars f ∧ MEM s0 sl ⇒ (n,s) ∉ sfv s0)’ by (gs[IN_fVslfv] >> metis_tac[]) >>
  rw[] >> 
  first_x_assum $ drule_then assume_tac >> 
  rw[] >> gs[] >>
  ‘sfv s ⊆ FDOM σ’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[tm_tree_WF]) >>
  ‘(n,s) ∉ FDOM σ’ by gs[EXTENSION] >>
  ‘ffv f DELETE (n,s) ⊆ FDOM σ’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[tm_tree_WF]) >>
  ‘∃nn.
   (∀x s1. x ∈ ffv f ∪ sfv s ∧ x ≠ (n,s) ⇒ (nn,s1) ∉ tfv (σ ' x))’
   by
   (qabbrev_tac
   ‘names = BIGUNION {tfv (σ ' x) | x | x ∈ FDOM σ}’ >>
   qexists ‘variant (fromSet (IMAGE FST names)) "a"’ >>
   rw[] >>
   ‘x ∈ FDOM σ’ by simp[] >>
   ‘FINITE names’
    by (qpat_x_assum ‘FDOM _ = _’ (assume_tac o GSYM) >>
       rw[Abbr‘names’] (* 2 *)
       >- (‘{tfv (σ ' x) | x | x ∈ FDOM σ} =
           IMAGE (tfv o (λx. σ ' x)) (FDOM σ)’
           by rw[Once EXTENSION] >> simp[])
       >- simp[]) >>
   drule_then assume_tac variant_var_NOTIN >>
   gs[Abbr‘names’] >>
   metis_tac[]) >>
  drule_at_then Any assume_tac finst_fabs >>
  ‘finst σ (fabs (n,s) 0 f) =
   fabs (nn,sinst σ s) 0 (finst (σ |+ ((n,s),Var nn (sinst σ s))) f)’
    by (rw[Once EQ_SYM_EQ] >> irule finst_fabs >>
       simp[] >> metis_tac[]) >>
  simp[] >> rw[GSYM mk_FALL_def,GSYM abst_def] >>
  irule $ cj 6 wff_rules >>
  ‘wfs Σf (sinst σ s)’
    by (irule $ cj 2 wft_tinst >> simp[]) >> simp[] >>
  ‘wff (Σf,Σp,Σe) (finst (σ |+ ((n,s),Var nn (sinst σ s))) f)’
    by
     (first_x_assum irule >>
     simp[FDOM_FUPDATE,SUBSET_INSERT_DELETE ] >> gs[] >>
     ‘wfcod Σf (σ |+ ((n,s),Var nn (sinst σ s)))’
      by (irule FUPDATE_wfcod >> simp[wft_def]) >> simp[]>> rw[] (* 2 *)
      >- (irule FUPDATE_cstt >>
     simp[complete_FDOM_is_cont,sort_of_def] >>
     ‘is_cont (ffv f ∪ sfv s DELETE (n,s))’
       by metis_tac[ffv_is_cont] >> simp[] >>       
     metis_tac[tm_tree_WF,vsort_tfv_closed]) >>
      irule presname_FUPDATE >>
      simp[tsname_def,sname_def,sort_of_def,vsname_def] >>
      gs[is_bound_alt] >>
      rw[Once EQ_SYM_EQ] >> irule $ cj 2 tsname_tinst >> simp[]) >> simp[] >>
  ‘cstt (σ |+ ((n,s),Var nn (sinst σ s)))’
   by ( irule FUPDATE_cstt >>
     simp[complete_FDOM_is_cont,sort_of_def] >>
     ‘is_cont (ffv f ∪ sfv s DELETE (n,s))’
       by metis_tac[ffv_is_cont] >> simp[] >>       
     metis_tac[tm_tree_WF,vsort_tfv_closed]) >>
  drule ffv_finst >> rw[FDOM_FUPDATE,SUBSET_INSERT_DELETE]>>
  first_x_assum $ qspecl_then [‘f’,‘n1’,‘s1’] assume_tac >>
  gs[] >>
  ‘wfcod Σf (σ |+ ((n,s),Var nn (sinst σ s)))’
      by (irule FUPDATE_wfcod >> simp[wft_def]) >> simp[]>>
  drule wfcod_no_bound >> rw[] >> gs[] (* 2 *)
  >- (Cases_on ‘(n,s) = (n0,st0)’ (* 2 *)
      >- (gs[FAPPLY_FUPDATE_THM] (* 2 *)
          >- metis_tac[tm_tree_WF] >>
          rev_drule $ cj 2 tfv_sinst >> rw[] >>
          first_x_assum (qspecl_then [‘s’,‘n1’,‘s1’] assume_tac)>>
          gs[] >>
          rev_drule wfcod_no_bound >> rw[] >> gs[] >>
          ‘(n0,st0) ≠ (n,s)’ by metis_tac[tm_tree_WF] >>
          first_x_assum (qspecl_then [‘(n0,st0)’,‘sinst σ s’] assume_tac) >> gs[] >> metis_tac[vsort_tfv_closed]) >>
      gs[FAPPLY_FUPDATE_THM] >>
      first_x_assum (qspecl_then [‘(n0,st0)’,‘sinst σ s’] assume_tac) >> gs[] >> metis_tac[vsort_tfv_closed]) >>
  simp[NOTIN_fVslfv,fVars_finst,PULL_EXISTS,
       vinst_fVar_def] >>
  Cases_on ‘x’ >> simp[vinst_fVar_def,MEM_MAP,PULL_EXISTS]>>
  drule_then assume_tac $ cj 2 tfv_sinst >> gs[]>>
  rw[] >> 
  first_x_assum (qspecl_then [‘y’] assume_tac) >> gs[] >>
  ‘sfv y ⊆ fVslfv f’
    by metis_tac[MEM_fVsl_SUBSET_fVslfv] >>
  ‘fVslfv f ⊆ ffv f’
      by metis_tac[fVslfv_SUBSET_ffv] >>
  ‘sfv y ⊆ ffv f’ by metis_tac[SUBSET_TRANS] >> 
  ‘sfv y ⊆ (n,s) INSERT ffv f ∪ sfv s DELETE (n,s)’
   by (gs[SUBSET_DEF] >> metis_tac[]) >> gs[] >>
  rw[] >> Cases_on ‘(n0,st0) ∉ sfv y ’ >> gs[] >>
  ‘(n0,st0) ∈ ffv f’
    by (gs[SUBSET_DEF] >> metis_tac[]) >>
  ‘(n0,st0) ≠ (n,s)’ suffices_by
   (simp[FAPPLY_FUPDATE_THM] >> rw[] >>
   first_x_assum irule >> simp[]) >>
  ‘(n0,st0) ∈ fVslfv f’ suffices_by metis_tac[] >>
  simp[IN_fVslfv] >> metis_tac[]
QED          


Theorem wff_FALL:
 ∀s b. wff (Σf,Σp,Σe) (FALL s b) ⇔
 (∃f n. wff (Σf,Σp,Σe) f ∧
          wfs Σf s ∧
          (n,s) ∉ fVslfv f ∧
          (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
          FALL s b = mk_FALL n s f)
Proof
 rw[Once wff_cases,EQ_IMP_THM,EQ_def] (* 2 *)
 >- (gs[mk_FALL_def] >> metis_tac[]) >>
 simp[] >> irule $ cj 6 wff_rules >> simp[] >> metis_tac[]
QED 

      
Theorem wff_wfs:
(∀f. wff (Σf,Σp,Σe) f ⇒ ∀n s. (n,s) ∈ ffv f ⇒ wfs Σf s)
Proof
Induct_on ‘wff’ >> simp[ffv_thm,PULL_EXISTS] >> rw[] (* 7 *)
>- (gs[ffv_EQ] >> metis_tac[wft_wfs])
>- metis_tac[wft_wfs]
>- metis_tac[wft_wfs]
>- metis_tac[wft_wfs]
>- metis_tac[wffstl_def,wfabsap_wfs]
>- metis_tac[wffstl_def,wfabsap_wfs,wfabsap_wft,wft_wfs] >>
gs[mk_FALL_def] (* 2 *)
>- metis_tac[wft_wfs] >>
Cases_on ‘(n,s) ∈ ffv f’ (* 2 *)
>- (drule_all_then assume_tac ffv_fabs_fVslfv >>
   first_x_assum (qspecl_then [‘0’] assume_tac) >>
   gs[abst_def] >> gs[EXTENSION] >>
   metis_tac[wft_wfs]) >>
metis_tac[abst_def,fabs_id]
QED


                


Theorem wff_fbounds:
∀f. wff Σf f ⇒ fbounds f = {}
Proof
Induct_on ‘wff’ >> rw[fbounds_thm,EQ_def] (* 4 *)
>- (disj2_tac >> rw[Once EXTENSION] >>
   metis_tac[wft_no_bound])
>- (Cases_on ‘tl’ >> simp[] >>
   disj2_tac >> rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
   >> (gs[] >> metis_tac[wft_no_bound]))
>- (gs[wffstl_def] >> Cases_on ‘tl’ >> simp[] >>
   disj2_tac >> drule_then assume_tac wfabsap_wft >>
   rw[Once EXTENSION] >> gs[] >>
   metis_tac[wft_no_bound]) >>
rw[mk_FALL_def,fbounds_thm] (* 2 *)
>- metis_tac[wft_no_bound] >>
rw[abst_def] >>
Cases_on ‘(n,s) ∈ ffv f’ (* 2 *)
>- (‘fbounds (fabs (n,s) 0 f) = {0} ∪ fbounds f’
    by (irule fbounds_fabs >>
        metis_tac[wff_wfs,wft_no_bound]) >>
   simp[EXTENSION]) >>
‘(fabs (n,s) 0 f)= f’ by metis_tac[fabs_id] >>
simp[]
QED

        

Theorem wff_no_vbound:
(∀f. wff Σf f ⇒ ∀n s. (n,s) ∈ ffv f ⇒ sbounds s = {})
Proof           
Induct_on ‘wff’ >> rw[wff_fbounds,tbounds_thm,EQ_def](* 6 *)
>- metis_tac[wft_no_vbound]
>- metis_tac[wft_no_vbound]
>- (first_x_assum drule >>
   rw[] >> drule $ cj 1 wft_tbounds >>
   rw[] >> CCONTR_TAC>> gs[GSYM MEMBER_NOT_EMPTY] >>
   drule_then assume_tac $ cj 1 sbounds_tbounds>>
   gs[SUBSET_DEF])
>- metis_tac[]
>- metis_tac[]
>- metis_tac[wffstl_def,wfabsap_sfv_sbounds]
>- (gs[wffstl_def] >> drule_then assume_tac wfabsap_wft >>
   first_x_assum $ drule_then assume_tac >>
   drule_then assume_tac $ cj 1 wft_tbounds >>
   CCONTR_TAC>> gs[GSYM MEMBER_NOT_EMPTY] >>
   drule_then assume_tac $ cj 1 sbounds_tbounds>>
   gs[SUBSET_DEF]) >>
drule_then assume_tac ffv_mk_FALL_fVslfv >> gs[](* 2 *)
>- metis_tac[] >>
drule_then assume_tac $ cj 2 wft_tbounds >>
   CCONTR_TAC>> gs[GSYM MEMBER_NOT_EMPTY] >>
   drule_then assume_tac $ cj 2 sbounds_tbounds>>
   gs[SUBSET_DEF]
QED




Theorem wff_spec:
 (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧
 wff (Σf,Σp,Σe) (FALL s ϕ) ⇒
 ∀t. wft Σf t ∧ sort_of t = s ⇒
     wff (Σf,Σp,Σe) (substb t ϕ)
Proof
 rw[] >> gs[wff_FALL] >> gs[mk_FALL_def] >>
 ‘0 ∉ fbounds f’
  by (drule_then assume_tac wff_fbounds >>
     metis_tac[MEMBER_NOT_EMPTY]) >>
 drule_then assume_tac substb_abst >>
 ‘(∀n1 s1. (n1,s1) ∈ ffv f ⇒ sbounds s1 = ∅)’
  by metis_tac[wff_no_vbound] >> gs[] >>
 first_x_assum $ drule_then assume_tac >> 
 simp[] >>
 ‘(finst (TO_FMAP [((n,sort_of t),t)]) f) =
  finst (cvmap (ffv f) |+ ((n,sort_of t),t)) f’
   by (irule finst_eq_cvmap1 >> metis_tac[]) >>
 simp[] >> irule wff_finst >> simp[] >>
 rw[] (* 3 *)
 >- (irule cstt_FUPDATE >> rw[] (*2  *)
    >- metis_tac[] >>
    CCONTR_TAC >> gs[is_bound_alt,wft_def])
 >- (irule presname_FUPDATE >> gs[vsname_def,tsname_def] >>
    metis_tac[wft_not_bound,ffv_FINITE,presname_cvmap])
 >- rw[FDOM_cvmap,SUBSET_DEF] >>
 rw[wfcod_def,FAPPLY_FUPDATE_THM] >>
 Cases_on ‘n' = n ∧ s = sort_of t’ >> simp[] >>
 gs[FDOM_cvmap,FAPPLY_cvmap] >>
 rw[wft_def] >> metis_tac[wff_wfs]
QED 





Theorem wff_fVar_subst_lemma:
 (∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
 ∀tl sl ϕ.
 wfabsap Σf sl tl ∧ wff (Σf,Σp,Σe) (FALLL sl ϕ) ⇒
 wff (Σf,Σp,Σe) (fprpl (mk_bmap (REVERSE tl)) ϕ)
Proof
strip_tac >> 
Induct_on ‘tl’ (* 2 *)
>- (Cases_on ‘sl’ >>
    simp[wfabsap_def,fprpl_FEMPTY,FALLL_def]) >>
Cases_on ‘sl’ >>
simp[wfabsap_def,fprpl_FEMPTY,FALLL_def] >>
rw[] >>
drule $ iffLR wff_FALL >> rw[] >>
drule_then assume_tac wff_spec >>
gs[mk_FALL_def] >> pop_assum (assume_tac o GSYM) >> gs[] >>
last_x_assum $ drule_then assume_tac >>
rename [‘wft Σf tm’] >>
qabbrev_tac ‘s = sort_of tm’ >>
first_x_assum (qspecl_then [‘(abst (n,s) f)’,‘Σp’,‘Σe’,‘tm’] assume_tac) >> gs[] >>
rename [‘wfabsap Σf (specsl 0 tm sl) tl’] >> 
‘substb (Var n s) (FALLL sl ϕ) = substb (Var n s) (abst (n,s) f)’
  by simp[] >>
‘substb (Var n s) (abst (n,s) f) = f’
 by (drule_then assume_tac substb_abst >>
    ‘substb (Var n s) (abst (n,s) f) = finst (TO_FMAP [((n,s),(Var n s))]) f’
     by (first_x_assum irule >> rw[] (* 2 *)
        >- metis_tac[wff_no_vbound] >>
        metis_tac[wff_fbounds,MEMBER_NOT_EMPTY]) >>
    simp[] >> metis_tac[finst_TO_FMAP_id]) >>
pop_assum SUBST_ALL_TAC >>
pop_assum (assume_tac o GSYM) >>
pop_assum SUBST_ALL_TAC >>
‘abst (n,s) (substb (Var n s) (FALLL sl ϕ)) =
(FALLL sl ϕ)’
 by rw[abst_def,substb_def]  >> gs[] >> 
first_x_assum (qspecl_then [‘frpl (LENGTH sl) tm ϕ’] assume_tac) >>
‘(fprpl (mk_bmap (REVERSE tl)) (frpl (LENGTH sl) tm ϕ)) =  (fprpl (mk_bmap (REVERSE tl ⧺ [tm])) ϕ)’
by metis_tac[wft_no_bound,fprpl_mk_bmap_CONS,
   wfabsap_LENGTH,LENGTH_specsl] >>
gs[] >> first_x_assum irule >>
‘wff (Σf,Σp,Σe) (substb tm (FALLL sl ϕ))’
 by (irule wff_spec >> simp[]) >>
‘substb tm (FALLL sl ϕ) =
(FALLL (specsl 0 tm sl) (frpl (LENGTH sl) tm ϕ))’
 suffices_by metis_tac[] >>
 rw[substb_def] >>
metis_tac[frpl_FALLL,arithmeticTheory.ADD]
QED  
    
        


Theorem wff_FALLL_no_vbound:
∀sl. wff Σ (FALLL sl ϕ)⇒
    (∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅)
Proof
rw[] >>
‘ffv ϕ ⊆ ffv (FALLL sl ϕ)’
 by metis_tac[wff_FALLL_ffv_SUBSET] >>
drule_then assume_tac wff_no_vbound >>
gs[SUBSET_DEF] >> metis_tac[]
QED

Theorem wff_wfcod_cvmap_ffv:
wff (Σf,Σp,Σe) f ⇒  wfcod Σf (cvmap (ffv f))
Proof
rw[wfcod_def,FAPPLY_cvmap,FDOM_cvmap,wft_def] >>
metis_tac[wff_wfs]
QED



Theorem wff_frename:
∀f. wff (Σf,Σp,Σe) f ∧
         (∀fsym.
            isfsym Σf fsym ⇒
            sfv (fsymout Σf fsym) ⊆
            BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧ wfs Σf s ∧
    (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒ 
    wff (Σf,Σp,Σe) (frename (n,s) nn f)
Proof
 rw[] >> drule_then assume_tac wff_finst >> gs[] >>
 first_x_assum (qspecl_then [‘(cvmap (ffv f) |+ ((n,s),Var nn s))’] assume_tac) >>
 ‘wff (Σf,Σp,Σe) (finst (cvmap (ffv f) |+ ((n,s),Var nn s)) f)’
  by
   (first_x_assum irule >>
   simp[FDOM_FUPDATE,FDOM_cvmap,SUBSET_DEF] >>
   rw[] (* 2 *)
   >- (irule cstt_FUPDATE >> rw[is_bound_def,sort_of_def] >>
      metis_tac[]) 
   >- (irule presname_FUPDATE >>
   gs[is_bound_alt,vsname_def,tsname_def,sort_of_def] >>
   metis_tac[ffv_FINITE,presname_cvmap]) >>
   irule FUPDATE_wfcod >> simp[wft_def] >>
   metis_tac[wff_wfcod_cvmap_ffv]) >>
 rw[frename_def] >>
 ‘ffv f ⊆ ffv f’ by simp[] >>
 drule_at_then Any assume_tac finst_eq_cvmap >>
 first_x_assum (qspecl_then [‘Var nn s’,‘n’] assume_tac) >>
 gs[sort_of_def,ffv_FINITE] >>
 first_x_assum $ drule_then assume_tac >> gs[]
QED


Theorem wfcod_rnmap_ffv:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
     (∀f. wff (Σf,Σp,Σe) f ⇒ ∀n s ss. wfcod Σf (rnmap (n,s) nn (ffv f)))
Proof
rw[] >> irule wfcod_rnmap_cont >>
simp[ffv_is_cont] >> metis_tac[wff_wfs]
QED
        



Theorem wff_frename:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
∀f. wff (Σf,Σp,Σe) f ⇒
    ∀n s nn. wff (Σf,Σp,Σe) (frename (n,s) nn f)
Proof
strip_tac >> Induct_on ‘wff’ >>
rw[] (* 5 *)
>- rw[frename_alt,wff_rules]
>- (gs[frename_eq] >> irule $ cj 2 wff_rules >>
   rw[] (*4 *)
   >- (rw[trename_tinst_tfv] >>
      ‘sort_of (tinst (rnmap (n,s) nn (tfv t1)) t1) =
       sinst (rnmap (n,s) nn (tfv t1)) (sort_of t1) ’
        by (irule cstt_sort_of_tinst' >> rw[] (* 3 *)
           >- metis_tac[cstt_rnmap,tfv_FINITE,tfv_is_cont]
           >- (irule wfcod_no_bound >> qexists ‘Σf’ >>
              rw[wfcod_def] >> gs[FDOM_rnmap,tfv_FINITE] >>
              drule_at_then Any assume_tac FAPPLY_rnmap >>
              gs[tfv_FINITE] >>
              irule $ cj 1 wft_trename >> simp[wft_def] >>
              metis_tac[wft_wfs]) >>
           metis_tac[wft_not_bound]) >>
      ‘sort_of (tinst (rnmap (n,s) nn (tfv t2)) t2) =
       sinst (rnmap (n,s) nn (tfv t2)) (sort_of t2) ’
        by (irule cstt_sort_of_tinst' >> rw[] (* 3 *)
           >- metis_tac[cstt_rnmap,tfv_FINITE,tfv_is_cont]
           >- (irule wfcod_no_bound >> qexists ‘Σf’ >>
              rw[wfcod_def] >> gs[FDOM_rnmap,tfv_FINITE] >>
              drule_at_then Any assume_tac FAPPLY_rnmap >>
              gs[tfv_FINITE] >>
              irule $ cj 1 wft_trename >> simp[wft_def] >>
              metis_tac[wft_wfs]) >>
           metis_tac[wft_not_bound]) >> simp[] >>
     irule $ cj 2 fmap_fv_inst_eq_alt >> gs[FDOM_rnmap,tfv_FINITE] >>
     ‘sfv (sort_of t2) ⊆ tfv t1 ∧ sfv (sort_of t2) ⊆ tfv t2’
       by (rw[SUBSET_DEF] (* 2 *)
     >> (Cases_on ‘x’ >> irule sfv_tfv >> metis_tac[wft_not_bound])) >>
     simp[] >> rw[] >>
     ‘x ∈ tfv t1 ∧ x ∈ tfv t2’ by metis_tac[SUBSET_DEF] >>
     Cases_on ‘x’ >> dxrule_at_then Any assume_tac FAPPLY_rnmap >>
     dxrule_at_then Any assume_tac FAPPLY_rnmap  >> gs[tfv_FINITE])
   >- metis_tac[tsname_trename,wft_not_bound]
   >> (irule $ cj 1 wft_trename >> simp[]))
>- (‘(frename (n,s) nn (Pred p tl)) =
    finst (rnmap (n,s) nn (ffv (Pred p tl))) (Pred p tl)’
    by metis_tac[frename_finst_ffv] >>
   pop_assum SUBST_ALL_TAC >>
   irule wff_finst >>
   simp[] >> simp[FINITE_BIGUNION_tfv,FDOM_rnmap] >>
   rw[] (* 3 *)
   >- (irule cstt_rnmap >> rw[FINITE_BIGUNION_tfv] >>
      irule BIGUNION_is_cont >> gs[tfv_is_cont] >>
      metis_tac[tfv_is_cont])
   >- (irule presname_rnmap >>
      simp[FINITE_BIGUNION_tfv])
   >- (irule wfcod_rnmap_BIGUNION >>
      rw[FINITE_BIGUNION_tfv] >>
      metis_tac[wfcod_rnmap_tfv]) >>
   irule wff_Pred >> simp[])
>- (rw[frename_alt] >> irule wff_IMP >>
   metis_tac[])
>- (‘(frename (n,s) nn (fVar P sl tl)) =
    finst (rnmap (n,s) nn (ffv (fVar P sl tl)))
          (fVar P sl tl)’ by simp[frename_finst_ffv] >>
   pop_assum SUBST_ALL_TAC >>
   irule wff_finst >> simp[] >>
   ‘FINITE (BIGUNION {sfv s | MEM s sl} ∪ BIGUNION {tfv t | MEM t tl})’
   by (simp[] >> rw[] >> simp[FINITE_lemma,tfv_FINITE]) >>
   simp[FDOM_rnmap] >> rw[] (* 3 *)
   >- (rw[GSYM BIGUNION_UNION,Excl "BIGUNION_UNION"] >>
      irule cstt_rnmap >> strip_tac (* 2 *)
      >- (gs[BIGUNION_UNION] >> metis_tac[]) >>
      irule BIGUNION_is_cont >> gs[tfv_is_cont] >>
      metis_tac[tfv_is_cont])
   >- (irule presname_rnmap >> simp[])
   >- (rw[GSYM BIGUNION_UNION,Excl "BIGUNION_UNION"] >>
      irule wfcod_rnmap_BIGUNION >>
      rw[] >> simp[tfv_FINITE,FINITE_lemma] (* 2 *)
      >- (irule wfcod_rnmap_cont >>
         simp[tfv_FINITE] >>
         metis_tac[wffstl_def,wfabsap_wfs,tfv_is_cont]) >>
      metis_tac[wfcod_rnmap_tfv,wffstl_def,wfabsap_wft]) >>
   irule wff_fVar >> simp[]) >>
rw[frename_finst_ffv] >>
irule wff_finst >> simp[FDOM_rnmap] >>
rw[] (* 3 *)
>- (irule cstt_rnmap >> simp[ffv_FINITE,ffv_is_cont])
>- (irule presname_rnmap >> metis_tac[ffv_FINITE])
>- (irule wfcod_rnmap_cont >>
   simp[ffv_FINITE,ffv_is_cont] >> rw[] >>
   irule wff_wfs >>
   first_x_assum $ irule_at Any >>
   qexistsl [‘Σp’,‘Σe’] >>
   irule $ cj 6 wff_rules >>
   simp[] >> metis_tac[]) >>
irule $ cj 6 wff_rules >>
simp[] >> metis_tac[]   
QED

Theorem wff_IMP:
  wff Σ (IMP f1 f2) ⇔ wff Σ f1 ∧ wff Σ f2
Proof
  rw[EQ_IMP_THM]
  >- gs[Once wff_cases,mk_FALL_def,EQ_def]
  >- gs[Once wff_cases,mk_FALL_def,EQ_def] >>
  Cases_on ‘Σ’ >> Cases_on ‘r’ >> irule wff_IMP >>
  simp[]
QED                          


   
Theorem fVmap_no_bound_lemma:        
(∀P sl. (P,sl) ∈ FDOM σ ⇒ wff (Σf,Σp) (FALLL sl (σ ' (P,sl)))) ⇒
(∀P sl n s.
          (P,sl) ∈ FDOM σ ⇒
          (n,s) ∈ ffv (σ ' (P,sl)) ⇒
          sbounds s = ∅)
Proof
rw[] >> metis_tac[wff_FALLL_no_vbound]
QED


Theorem wffVmap_fVmap_rename:
  (∀fsym.
        isfsym Σf
         fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧
  wffVmap (Σf,Σp,Σe) σ ∧
  (∀P sl s0. (P,sl) ∈ FDOM σ ∧ MEM s0 sl ⇒ (n,s) ∉ sfv s0) ⇒
  wffVmap (Σf,Σp,Σe) (fVmap_rename (n,s) nn σ)
Proof
  rw[wffVmap_def] >>
  ‘FALLL sl (frename (n,s) nn (σ ' (P,sl))) =
     frename (n,s) nn (FALLL sl (σ ' (P,sl)))’
     by
     (rw[frename_FALLL] >>
     ‘MAP (srename (n,s) nn) sl = sl’
      suffices_by metis_tac[] >>
     rw[MAP_fix] >> irule $ cj 2 trename_fix >>
     gs[FDOM_fVmap_rename] >>
     metis_tac[]) >>
   gs[FDOM_fVmap_rename] >>
   drule_then assume_tac FAPPLY_fVmap_rename >>
    simp[] >> irule wff_frename >>
    simp[] >> gs[]
QED

Theorem wffVmap_no_vbound:
∀σ. wffVmap Σ σ ⇒
  ∀P sl. (P,sl) ∈ FDOM σ ⇒
        ∀n s. (n,s) ∈ ffv (σ ' (P,sl)) ⇒
               sbounds s = ∅
Proof
rw[] >> irule wff_FALLL_no_vbound >>
gs[wffVmap_def] >>
first_x_assum $ irule_at Any >>
Cases_on ‘Σ’ >> metis_tac[]
QED 



Theorem wff_fVinst:
(∀fsym.
        isfsym (Σf:string |-> sort # (string # sort) list)
         fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
∀f. wff (Σf,Σp,Σe) f ⇒
    ∀σ. wffVmap (Σf,Σp,Σe) σ ⇒
    wff (Σf,Σp,Σe) (fVinst σ f)
Proof
Induct_on ‘wff’ >> rw[fVinst_def,wff_rules,fVinst_EQ] (* 2 *)
>- (Cases_on ‘(P,sl) ∈ FDOM σ’ >> simp[] (* 2 *)
   >- (gs[wffstl_def] >> drule_then assume_tac wfabsap_ok_abs >> simp[] >>
      gvs[] >>
      assume_tac (GEN_ALL $ SRULE [] wff_fVar_subst_lemma) >>
      first_x_assum $ drule_then assume_tac >>
      gs[wffVmap_def] >>
      metis_tac[]) >>
   simp[wff_rules]) >>
rw[mk_FALL_def,fVinst_def] >>
first_x_assum $ drule_then assume_tac >>
‘∀σ. wffVmap (Σf,Σp,Σe) σ ∧
     FDOM σ ⊆ fVars f ⇒ wff (Σf,Σp,Σe) (FALL s (fVinst σ (abst (n,s) f)))’
  suffices_by 
 (rw[] >> Cases_on ‘FDOM σ ⊆ fVars f ’
 >- metis_tac[] >>
 ‘(fVinst σ (abst (n,s) f)) =
  fVinst (DRESTRICT σ (fVars f)) (abst (n,s) f)’
  by (‘fVars (abst (n,s) f) = fVars f’
       by metis_tac[fVars_fabs,abst_def] >>
     metis_tac[fVars_DRESTRICT_fVinst_eq]) >> simp[] >>
 first_x_assum irule >> gs[DRESTRICT_DEF] >>
 gs[wffVmap_def,DRESTRICT_DEF]) >>
 qpat_x_assum ‘wffVmap (Σf,Σp,Σe) σ’ (K all_tac) >> rw[] >>
 ‘(∀P sl.
           (P,sl) ∈ FDOM σ ⇒
           ∀st. MEM st sl ⇒ (n,s) ∉ sfv st)’
    by (gs[IN_fVslfv] >> metis_tac[SUBSET_DEF]) >>
‘∃nn. (∀P sl.
           (P,sl) ∈ FDOM σ ⇒
           (nn,s) ∉ ffv (σ ' (P,sl)) ∧
           ∀st. MEM st sl ⇒ (n,s) ∉ sfv st ∧ (nn,s) ∉ sfv st) ∧
        (nn,s) ∉ ffv f ∧ nn ≠ n ∧ (nn,s) ∉ sfv s’
 by (‘∃nn. (nn,s) ∉
     ffv f ∪ BIGUNION {ffv (σ ' (P,sl)) | (P,sl) | (P,sl) ∈ FDOM σ} ∪ BIGUNION {sfv st | (P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM σ} ∪
     sfv s ∪ {(n,s)}’
     suffices_by
     (rw[] >> qexists ‘nn’ >> simp[] >>
     metis_tac[]) >>
     (*BIG FINITENESS*)
     ‘FINITE
      (ffv f ∪ BIGUNION {ffv (σ ' (P,sl)) | (P,sl) | (P,sl) ∈ FDOM σ} ∪ BIGUNION {sfv st | (P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM σ} ∪
     sfv s ∪ {(n,s)})’
     suffices_by metis_tac[fresh_name_ex] >>
     simp[] >> rw[PULL_EXISTS] (* 2 *)
     >- (‘{ffv (σ ' (P,sl)) | (P,sl) | (P,sl) ∈ FDOM σ} =
         IMAGE (λ(P,sl). ffv (σ ' (P,sl)))
         (FDOM σ)’
          suffices_by rw[] >>
         rw[Once EXTENSION,EQ_IMP_THM] (* 2 *)
         >- (qexists ‘(P,sl)’ >> simp[]) >>
         Cases_on ‘x'’ >>
         qexistsl [‘q’,‘r’] >> simp[]) >>
     (*ask*)
    ‘{sfv st | (P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM σ} = IMAGE (sfv o SND o SND)
            {(P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM σ}’
      by (simp[Once EXTENSION] >> rw[] >>
         rw[EQ_IMP_THM] (* 2 *)
         >> (rw[PULL_EXISTS] >> metis_tac[])) >>
     simp[] >> irule IMAGE_FINITE >>
     ‘{(P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM σ} ⊆
      {P | ∃sl. (P,sl) ∈  FDOM σ} ×
      {sl | ∃P. (P,sl) ∈  FDOM σ} ×
      {st | ∃P sl. (P,sl) ∈ FDOM σ ∧ MEM st sl}’
      by (rw[SUBSET_DEF] >> simp[] >> metis_tac[]) >>
      irule SUBSET_FINITE >>
      first_x_assum $ irule_at Any >>
      irule FINITE_CROSS >> rw[] (* 2 *)
      >- (‘{P | (∃sl. (P,sl) ∈ FDOM σ)} = IMAGE FST (FDOM σ)’
          by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM]
             >- (qexists ‘(x,sl)’ >> simp[]) >>
             qexists ‘SND x'’ >> simp[]) >>
         simp[] >> irule IMAGE_FINITE >>
         irule SUBSET_FINITE >> qexists ‘FDOM σ’ >>
         simp[]) >>
     disj2_tac >> disj2_tac >> rw[] (* 2 *)
     >- (‘{sl | ∃P. (P,sl) ∈ FDOM σ} = IMAGE SND (FDOM σ)’
          by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM]
             >- (qexists ‘(P,x)’ >> simp[]) >>
             qexists ‘FST x'’ >> simp[]) >>
         simp[] >> irule IMAGE_FINITE >>
         irule SUBSET_FINITE >> qexists ‘FDOM σ’ >>
         simp[]) >>
     ‘{st | ∃P sl. (P,sl) ∈ FDOM σ ∧ MEM st sl} =
     BIGUNION {set sl | ∃P. (P,sl) ∈ FDOM σ}’
     by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
        metis_tac[]) >>
     simp[PULL_EXISTS] >>
     ‘{set sl | (∃P. (P,sl) ∈ FDOM σ)} =
      IMAGE (set o SND) (FDOM σ)’
       by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
          >- (qexists ‘(P,sl)’ >> simp[]) >>
          qexistsl [‘SND x'’,‘FST x'’] >> simp[]) >>
     simp[])
(*END OF BIG FINITENESS*)
 >>
first_x_assum $ qspecl_then [‘(fVmap_rename (n,s) nn σ)’]
assume_tac >>
‘wffVmap (Σf,Σp,Σe) (fVmap_rename (n,s) nn σ)’
 by (irule wffVmap_fVmap_rename >> simp[] >>
    metis_tac[]) >> 
‘wff (Σf,Σp,Σe) (fVinst (fVmap_rename (n,s) nn σ) f)’
 by (first_x_assum irule >> rw[FDOM_fVmap_rename]) >>
qspecl_then [‘f’,‘0’] assume_tac fVinst_fabs >> gs[] >>
gs[GSYM abst_def] >>
‘(fVinst σ (abst (n,s) f)) =
 frename (nn,s) n (abst (n,s) (fVinst (fVmap_rename (n,s) nn σ) f))’ by metis_tac[] >>
simp[] >>
‘(FALL s
             (frename (nn,s) n
                (abst (n,s) (fVinst (fVmap_rename (n,s) nn σ) f)))) =
 frename (nn,s) n
  (FALL s (abst (n,s) (fVinst (fVmap_rename (n,s) nn σ) f)))’
  by (rw[frename_alt] >> metis_tac[trename_fix]) >>
rw[] >> irule wff_frename >> simp[] >>
rw[GSYM mk_FALL_def] >>
irule $ cj 6 wff_rules >>
simp[] >>
rw[] (* 2 *)
>- (‘∀n1 s1.
    (n1,s1) ∈ ffv (fVinst (fVmap_rename (n,s) nn σ) f) ∧
    (n1,s1) ∉ ffv f ⇒ (n,s) ∉ sfv s1’
    suffices_by metis_tac[] >>
   qspecl_then [‘f’,‘fVmap_rename (n,s) nn σ’] assume_tac
   ffv_fVinst >>
   ‘ffv f ∪ ffv (fVinst (fVmap_rename (n,s) nn σ) f) =
        ffv f ∪
        ofFMAP ffv (fVmap_rename (n,s) nn σ)
          (FDOM (fVmap_rename (n,s) nn σ) ∩ fVars f)’
     by (first_x_assum irule >>
        rw[] >> irule wffVmap_no_vbound >>
        gs[FDOM_fVmap_rename] >>
        first_x_assum $ irule_at Any >>
        gs[FDOM_fVmap_rename] >> metis_tac[]) >>
   rw[] >> gs[FDOM_fVmap_rename] >> gs[ofFMAP_FDOM] >>
   ‘(n1',s1') ∈ ofFMAP ffv (fVmap_rename (n,s) nn σ) (FDOM σ ∩ fVars f)’
        by (gs[EXTENSION] >> metis_tac[]) >>
   gs[ofFMAP_def,FDOM_fVmap_rename] >> Cases_on ‘a’ >>
   drule_then assume_tac FAPPLY_fVmap_rename >> gs[] >>
   rename [‘(n1,s1) ∉ ffv f’] >>
   pop_assum (K all_tac) >>
   metis_tac[NOTIN_frename,SUBSET_DEF,sfv_ffv]) >>
simp[IN_fVslfv] >>
‘∀P sl s0. (P,sl) ∈ fVars (fVinst (fVmap_rename (n,s) nn σ) f) ∧ MEM s0 sl ⇒ (n,s) ∉ sfv s0’ suffices_by metis_tac[] >>
rw[] >>
Cases_on ‘(P,sl) ∈ fVars f’
>- (CCONTR_TAC >> gs[IN_fVslfv] >> metis_tac[]) >>
qspecl_then [‘f’,‘(fVmap_rename (n,s) nn σ)’] assume_tac
fVars_fVinst >> 
‘(P,sl) ∈ ofFMAP fVars (fVmap_rename (n,s) nn σ) (fVars f)’
 by (gs[Once EXTENSION] >> metis_tac[]) >>
gs[ofFMAP_def,FDOM_fVmap_rename] >>
Cases_on ‘a’ >> drule_then assume_tac FAPPLY_fVmap_rename >>
gs[]>>
‘(n,s) ∉ ffv (frename (n,s) nn (σ ' (q,r)))’
 by metis_tac[NOTIN_frename] >>
qspecl_then [‘(frename (n,s) nn (σ ' (q,r)))’] assume_tac
fVslfv_SUBSET_ffv >>
CCONTR_TAC >>
‘(n,s) ∈ fVslfv (frename (n,s) nn (σ ' (q,r)))’
 suffices_by metis_tac[SUBSET_DEF] >>
simp[IN_fVslfv] >> metis_tac[] 
QED


Theorem mk_FALLL_fVar_wff:
∀f.
wff Σ f ∧ wfvl (FST Σ) vl f ⇒ 
wff Σ (mk_FALLL vl f)
Proof
Induct_on ‘LENGTH vl’
>- rw[mk_FALLL_def] >>
Cases_on ‘vl’ >> simp[] >>
Cases_on ‘h’ >> simp[wfvl_def,mk_FALLL_def] >>
rw[] >> Cases_on ‘Σ’ >> Cases_on ‘r'’ >>
irule $ cj 6 wff_rules >>
rename [‘(Σf,Σp,Σe)’] >> gs[] >> gs[wfdpvl_def] >>
‘wff (Σf,Σp,Σe) (mk_FALLL t f)’
 by (first_x_assum irule >> simp[] >>
    simp[wfvl_def]) >> simp[] >>
‘wfs Σf r’ by gs[DISJ_IMP_THM] >> simp[fVslfv_mk_FALLL1] >>
metis_tac[]
QED 

Theorem wfvl_alt:
(wfvl Σ [] f ⇔ T) ∧
(wfvl Σ (h :: t) f ⇔ wfvl Σ t f ∧ wfs Σ (SND h) ∧
h ∉ fVslfv f ∧ ∀n s. (n,s) ∈ ffv (mk_FALLL t f) ⇒ h ∉ sfv s)
Proof
rw[wfvl_def,wfdpvl_def] >> metis_tac[]
QED



(*tedious*)        
Theorem wfabsap_vl2sl_MAP_Var':
wfvl Σ vl TRUE ∧ ALL_DISTINCT vl ∧ okvnames vl ∧ wfdpvl vl TRUE ⇒
wfabsap Σ (vl2sl vl) (MAP Var' vl)
Proof
Induct_on ‘LENGTH vl’ >> simp[wfabsap_def,vl2sl_EMPTY] >>
Cases_on ‘vl’ >> simp[vl2sl_CONS,wfabsap_def] >> strip_tac >>
strip_tac >> Cases_on ‘h’ >> simp[sort_of_def] >>
gs[wfvl_alt,wfdpvl_TRUE,okvnames_CONS] >> gs[wfvl_alt] >>
‘wfabsap Σ (specsl 0 (Var q r) (abssl (q,r) 0 (vl2sl t))) (MAP Var' t)’
 by (dep_rewrite.DEP_REWRITE_TAC[specsl_abssl] >> simp[LENGTH_vl2sl] >>
    ‘(ssubst (q,r) (Var q r)) = I’ by cheat >> simp[] >>
    (*ok_abs_vl2sl *)cheat) >>
simp[wft_def] >> cheat
QED    
    
Theorem wfdpvl_ALL_DISTINCT_okvnames_wff:
wfvl (FST Σ) vl TRUE ∧ ALL_DISTINCT vl ∧ okvnames vl ⇒
wff Σ (FALLL (vl2sl vl) (plainfV (P,vl2sl vl)))
Proof
rw[] >> 
‘wfdpvl vl TRUE’ by metis_tac[wfvl_def] >>
drule_then assume_tac $ GSYM mk_FALLL_fVar_FALLL >>
simp[] >>
irule mk_FALLL_fVar_wff >> reverse (rw[wfvl_def]) (* 3 *)
>- gs[wfvl_def]
>- (irule wfdpvl_TRUE_fVar >> simp[]) >>
Cases_on ‘Σ’ >> Cases_on ‘r’ >> irule wff_fVar >>
simp[wffstl_def] >>
simp[PULL_EXISTS] >> qexists ‘vl’ >> simp[] >>
gs[] >>metis_tac[wfabsap_vl2sl_MAP_Var']
QED


    
 
val _ = export_theory();

