open HolKernel Parse boolLib bossLib;

val _ = new_theory "Pf0Drv";

(*fconv definition should also union the fvs in b*)
    

        
Inductive Pf0:
[~AX:]
(∀ath. ath ∈ aths ⇒ Pf0 Σ aths [ath]) ∧
[~cong:]
(∀sl Pf0s eqths.
 sl ≠ [] ∧
 (∀n. n < LENGTH sl ⇒
      is_EQ (concl (eqths n)) ∧
      Pf0 Σ aths (Pf0s n) ∧ MEM (eqths n) (Pf0s n) ∧
      sort_of (Leq (concl (eqths n))) = EL n sl) ∧
 (∀s. MEM s sl ⇒ wfs (FST Σ) s) ∧
 wff Σ (FALLL sl b) ∧ is_cfm b ⇒
 Pf0 Σ aths (FLAT (map2list (LENGTH sl - 1) Pf0s)  ++
 [fcong (map2list (LENGTH sl - 1) eqths) sl b])   
 ) ∧
[~vinsth:]
  (∀pf th vσ.
     Pf0 Σ aths pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧
     cont th ⊆ FDOM vσ ⇒
     Pf0 Σ aths (pf ++ [vinsth vσ th])) ∧
[~ALLI:]
  (∀Γ A pf x s f.
     Pf0 Σ aths pf ∧ MEM (Γ,A,f) pf ∧
     wfs (FST Σ) s ∧ (sfv s) ⊆ Γ ∧
     (x,s) ∉ genavds (Γ,A,f) ⇒
     Pf0 Σ aths (pf ++ [gen (x,s) (Γ,A,f)])) ∧
[~ALLE:]
  (∀Γ A pf s f t.
     Pf0 Σ aths pf ∧ MEM (Γ,A,FALL s f) pf ∧
     wft (FST Σ) t ∧ sort_of t = s ⇒
     Pf0 Σ aths (pf ++ [spec t (Γ,A,FALL s f)])) ∧     
[~double_neg:]
  (∀Γ A pf f.
      Pf0 Σ aths pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒
      Pf0 Σ aths (pf ++ [(Γ,A,f)])) ∧
[~fromBot:]
  (∀Γ A pf f.
    Pf0 Σ aths pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ∧ is_cfm f ⇒
    Pf0 Σ aths (pf ++ [(Γ ∪ ffv f,A,f)])) ∧
[~assume:]
  (∀c:form. wff Σ c ∧ is_cfm c ⇒ Pf0 Σ aths [assume c]) ∧
[~mp:]
  (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
     Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧
     MEM (Γ1,A1,IMP f1 f2) pf1 ∧
     MEM (Γ2,A2,f1) pf2 ⇒
     Pf0 Σ aths (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2, A1 ∪ A2,f2)])) ∧     
[~disch:]
  (∀pf th a.
     Pf0 Σ aths pf ∧ MEM th pf ∧ wff Σ a ∧ is_cfm a ⇒
     Pf0 Σ aths (pf ++ [disch a th])) ∧               
[~refl:]
  (∀t.
     wft (FST Σ) t ∧ tsname t ∈ (SND (SND Σ)) ⇒ Pf0 Σ aths [refl t]) ∧
[~sym:]
  (∀Γ A pf t1 t2.
     Pf0 Σ aths pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
     Pf0 Σ aths (pf ++ [(Γ,A,EQ t2 t1)])) ∧
[~trans:]
  (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
     Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧
     MEM (Γ1,A1,EQ t1 t2) pf1 ∧ MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
     Pf0 Σ aths (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
[~add_cont1:]
  (∀pf th n.
    Pf0 Σ aths pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
    Pf0 Σ aths (pf ++ [add_cont1 (n,s) th]))     
End

    
 
Definition Pf0Drv_def:
  Pf0Drv Σ aths th ⇔ ∃pf0. Pf0 Σ aths pf0 ∧ MEM th pf0
End




Theorem Pf0_cont_is_cont:
 (∀th. th ∈ aths ⇒ is_cont (cont th)) ⇒
∀pf. Pf0 Σ aths pf ⇒
 ∀Γ A f. MEM (Γ,A,f) pf ⇒ is_cont Γ
Proof
 Induct_on ‘Pf0’ >> rw[] >> TRY (metis_tac[]) (* 13 *)
 >- metis_tac[cont_def]
 >- (gs[MEM_FLAT,MEM_map2list] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘n0 < LENGTH sl’ by simp[] >>
    first_x_assum $ drule_then assume_tac >> gs[] >>
    metis_tac[])
 >- (gs[fcong_def] >> rw[Uof_def] >>
     irule UNION_is_cont >> simp[ffv_is_cont] >>
    irule BIGUNION_is_cont >> simp[PULL_EXISTS,MEM_map2list] >>
    rw[] >> Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
    gs[cont_def] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘n0 < LENGTH sl’ by simp[] >>
    first_x_assum $ drule_then strip_assume_tac >>
    gs[] >> metis_tac[])
 >- (Cases_on ‘th’ >> Cases_on ‘r’ >>
    gs[vinsth_def] >> gs[vinst_cont_def] >>
    gs[ofFMAP_def] >> irule BIGUNION_is_cont >>
    simp[] >> metis_tac[tfv_is_cont])
 >- (gs[gen_def] >> irule is_cont_DELETE >>
    gs[NOTIN_genavds] >> metis_tac[])
 >- (gs[spec_def] >> irule UNION_is_cont >>
    metis_tac[tfv_is_cont])   
 >- (irule UNION_is_cont >> metis_tac[ffv_is_cont])
 >- (gs[assume_def] >> metis_tac[ffv_is_cont])
 >- metis_tac[UNION_is_cont]
 >- (Cases_on ‘th’ >> Cases_on ‘r’>>
    gs[disch_def] >>
    metis_tac[ffv_is_cont,UNION_is_cont])
 >- (gs[refl_def] >> metis_tac[tfv_is_cont]) 
 >- (irule UNION_is_cont >> metis_tac[]) >>
 Cases_on ‘th’ >> Cases_on ‘r’ >> gs[add_cont1_def] >>
 irule UNION_is_cont >> rw[] (* 2 *)
 >- (‘({(n,s)} ∪ sfv s) = tfv (Var n s)’ by gs[tfv_thm] >>
     metis_tac[tfv_is_cont]) >>
 metis_tac[]
QED



Theorem is_cfm_IFF:
is_cfm (IFF f1 f2) ⇔ is_cfm f1 ∧ is_cfm f2
Proof
gs[is_cfm_def,IFF_def,CONJ_def,NEG_def] >> metis_tac[]
QED

Theorem is_cfm_fprpl:
∀f bmap. is_cfm (fprpl bmap f) ⇔ is_cfm f
Proof
Induct_on ‘f’ >> gs[is_cfm_def,fprpl_def]
QED
        
Theorem is_cfm_finst:
is_cfm (finst σ f) ⇔ is_cfm f
Proof
Induct_on ‘f’ >> gs[is_cfm_def,finst_def]
QED

Theorem is_cfm_fabs:
∀f i. is_cfm (fabs v i f) ⇔ is_cfm f
Proof
Induct_on ‘f’ >> gs[is_cfm_def,fabs_def]
QED



Theorem is_cfm_frpl:
∀f i. is_cfm (frpl i v f) ⇔ is_cfm f
Proof
Induct_on ‘f’ >> gs[is_cfm_def,frpl_def]
QED


Theorem is_cfm_NEG:
∀f. is_cfm (NEG f) ⇔ is_cfm f
Proof
Induct_on ‘f’ >> gs[is_cfm_def,NEG_def]
QED
                
Theorem is_cfm_EQ:
is_cfm (EQ t1 t2)
Proof
gs[EQ_def,is_cfm_def]                
QED



Definition wfaths_def:
  wfaths (Σf,Σp,Σe) aths ⇔
  (∀Γ A f. (Γ,A,f) ∈ aths ⇒
           wff (Σf,Σp,Σe) f ∧ is_cfm f ∧ (∀a. a ∈ A ⇒ wff (Σf,Σp,Σe) a ∧ is_cfm a) ∧
           (∀n s. (n,s) ∈ Γ ⇒ wfs Σf s) ∧
           Uof ffv ({f} ∪ A) ⊆ Γ)
End
                                             
Theorem Pf0_cfm:
  wfaths (Σf,Σp,Σe) aths ⇒
  ∀pf. Pf0 (Σf,Σp,Σe) aths pf ⇒
       ∀Γ A f. MEM (Γ,A,f) pf ⇒ is_cfm f ∧
       ∀a. a ∈ A ⇒ is_cfm a
Proof
 strip_tac >> Induct_on ‘Pf0’ >> rw[] >>
 TRY (gs[wfaths_def] >> metis_tac[]) (* 23 *)
 >- (gs[MEM_FLAT,MEM_map2list] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> Cases_on ‘(eqths n0)’ >>
   Cases_on ‘r’ >> metis_tac[])
 >- (gs[MEM_FLAT,MEM_map2list] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> Cases_on ‘(eqths n0)’ >>
   Cases_on ‘r’ >> metis_tac[])
 >- gs[fcong_def,is_cfm_IFF,is_cfm_fprpl]
 >- (gs[fcong_def,IN_Uof,MEM_map2list] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> Cases_on ‘(eqths n0)’ >> Cases_on ‘r’ >>
   gs[assum_def] >>
   metis_tac[])
 >- (Cases_on ‘th’ >> Cases_on ‘r’ >> gs[vinsth_def] >>
    metis_tac[is_cfm_finst])
 >- (Cases_on ‘th’ >> Cases_on ‘r’ >> gs[vinsth_def] >>
    metis_tac[is_cfm_finst])
 >- (gs[gen_def,mk_FALL_def,abst_def] >>     
    gs[is_cfm_def] >> metis_tac[is_cfm_fabs])
 >- (gs[gen_def]>> metis_tac[])
 >- (gs[spec_def,substb_def] >> gs[is_cfm_frpl]  >>
    metis_tac[is_cfm_def])
 >- (gs[spec_def] >> metis_tac[])
 >- (first_x_assum $ drule_then assume_tac >> gs[] >> metis_tac[is_cfm_NEG])
 >- (first_x_assum $ drule_then assume_tac >> gs[])
 >- gs[assume_def]
 >- gs[assume_def]
 >- metis_tac[is_cfm_def]
 >- (Cases_on ‘th’ >> Cases_on ‘r’ >> gs[disch_def] >>
    metis_tac[is_cfm_def])
 >- (Cases_on ‘th’ >> Cases_on ‘r’ >> gs[disch_def] >>
    metis_tac[is_cfm_def])
 >- gs[refl_def,is_cfm_EQ]
 >- gs[refl_def]
 >- gs[is_cfm_EQ]
 >- gs[is_cfm_EQ]
 >> (Cases_on ‘th’ >> Cases_on ‘r’ >> gs[add_cont1_def] >> metis_tac[])
QED 

Theorem Pf0Drv_cfm:
  wfaths Σ aths ⇒
  ∀Γ A f. Pf0Drv Σ aths (Γ,A,f) ⇒
  is_cfm f ∧
       ∀a. a ∈ A ⇒ is_cfm a
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[Pf0Drv_def] >>
metis_tac[Pf0_cfm]
QED
                
Theorem Pf0Drv_cont_wf:
(∀Γ A f. (Γ,A,f) ∈ aths ⇒ ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s) ⇒
∀pf. Pf0 (Σf,Σp,Σe) aths pf ⇒
 ∀Γ A f. MEM (Γ,A,f) pf ⇒
         ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s
Proof
strip_tac >> 
Induct_on ‘Pf0’ >> rw[] (* 27 *) >> TRY (metis_tac[]) (*12*)
>- (gs[MEM_FLAT,MEM_map2list] >> 
   ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> Cases_on ‘(eqths n0)’ >>
   Cases_on ‘r’ >> metis_tac[])
>- (gs[fcong_def,IN_Uof,MEM_map2list] (* 2 *)
   >- (‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> Cases_on ‘(eqths n0)’ >>
   Cases_on ‘r’ >> gs[cont_def] >> metis_tac[]) >>
   drule_then assume_tac wff_wfs >>
   gs[ffv_FALLL] >> metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   gs[vinsth_def,vinst_cont_def] >>
   metis_tac[wfvmap_IN_ofMAP_wfs])
>- (gs[gen_def] >> metis_tac[])
>- (gs[spec_def] (* 2 *)
   >- metis_tac[] >> metis_tac[wft_wfs])
>- (gs[] (* 2 *) >> metis_tac[wff_wfs])
>- (gs[assume_def] >> metis_tac[wff_wfs])
>- (gs[] (* 2 *)>> metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   gs[disch_def] >- (gs[EXTENSION] >> metis_tac[])>>
   metis_tac[wff_wfs])
>- (gs[refl_def] >> metis_tac[wft_wfs])
>- (gs[] >> metis_tac[]) >>
Cases_on ‘th’ >> Cases_on ‘r’ >> 
gs[add_cont1_def] >- (gs[Once EXTENSION] >> metis_tac[wft_wfs]) >>
metis_tac[]
QED



           
Theorem mk_bmap_BIGUNION:
∀l ϕ.BIGUNION {tfv (mk_bmap l ' i) | i | i ∈ count (LENGTH l) ∩ fbounds ϕ} ⊆
Uof tfv (set l)
Proof
rw[SUBSET_DEF,IN_Uof] >>
drule_then assume_tac FAPPLY_mk_bmap >> gs[MEM_EL,PULL_EXISTS] >>
metis_tac[]
QED

Theorem FAPPLY_mk_bmap_REVERSE_Lofeqthl:
i ≤ n ⇒
(mk_bmap (REVERSE (Lofeqthl (map2list n eqths))) ' i) = Leq (concl (eqths (n - i)))
Proof
rw[] >>
‘LENGTH (REVERSE (Lofeqthl (map2list n eqths))) = n + 1’
 by rw[LENGTH_LRofeqthl,LENGTH_map2list] >>
‘i < LENGTH (REVERSE (Lofeqthl (map2list n eqths)))’
 by simp[] >>
drule_then assume_tac FAPPLY_mk_bmap  >> gs[] >>
‘i < LENGTH (Lofeqthl (map2list n eqths))’ by simp[] >>
drule_then assume_tac EL_REVERSE >> gs[] >>
Cases_on ‘n + 1 -i’ >> gs[] >>
‘n' < LENGTH (map2list n eqths)’
 by simp[LENGTH_map2list] >>
rw[Lofeqths_def,EL_MAP] >>
‘n' ≤ n’ by simp[] >> gs[EL_map2list] >>
rw[Leq_def] >> 
gs[arithmeticTheory.ADD1] >> rpt AP_TERM_TAC  >>
CCONTR_TAC >> gs[]
QED 



Theorem FAPPLY_mk_bmap_REVERSE_Rofeqthl:
i ≤ n ⇒
(mk_bmap (REVERSE (Rofeqthl (map2list n eqths))) ' i) = Req (concl (eqths (n - i)))
Proof
rw[] >>
‘LENGTH (REVERSE (Rofeqthl (map2list n eqths))) = n + 1’
 by rw[LENGTH_LRofeqthl,LENGTH_map2list] >>
‘i < LENGTH (REVERSE (Rofeqthl (map2list n eqths)))’
 by simp[] >>
drule_then assume_tac FAPPLY_mk_bmap  >> gs[] >>
‘i < LENGTH (Rofeqthl (map2list n eqths))’ by simp[] >>
drule_then assume_tac EL_REVERSE >> gs[] >>
Cases_on ‘n + 1 -i’ >> gs[] >>
‘n' < LENGTH (map2list n eqths)’
 by simp[LENGTH_map2list] >>
rw[Rofeqths_def,EL_MAP] >>
‘n' ≤ n’ by simp[] >> gs[EL_map2list] >>
rw[Req_def] >> 
gs[arithmeticTheory.ADD1] >> rpt AP_TERM_TAC  >>
CCONTR_TAC >> gs[]
QED     

        

Theorem Pf0_ffv_SUBSET_wff:
 wfsig (Σf,Σp,Σe) ∧ wfaths (Σf,Σp,Σe) aths ⇒
∀pf. Pf0 (Σf,Σp,Σe) aths pf ⇒
 ∀Γ A f. MEM (Γ,A,f) pf ⇒
         Uof ffv ({f} ∪ A) ⊆ Γ ∧
         wff (Σf,Σp,Σe) f ∧
         (∀a. a ∈ A ⇒ wff (Σf,Σp,Σe) a)
Proof
strip_tac >> 
Induct_on ‘Pf0’ >> rw[] (* 27 *) >> TRY (metis_tac[]) (*42*)
>~ [‘(Γ,A,f) = fcong (map2list (LENGTH sl − 1) eqths) sl b’]
   >- (simp[Uof_UNION,Uof_SUBSET,Uof_Sing] >>
   rw[] (* 2 *)
   >- (gs[fcong_def] >> simp[ffv_IFF] >>
      ‘BIGUNION {tfv t | MEM t (Lofeqthl (map2list (LENGTH sl − 1) eqths))} ⊆
         Uof cont (set (map2list (LENGTH sl − 1) eqths)) ∧
      BIGUNION {tfv t | MEM t (Rofeqthl (map2list (LENGTH sl − 1) eqths))} ⊆
         Uof cont (set (map2list (LENGTH sl − 1) eqths))’
        suffices_by
        (disch_tac >> simp[] >>
        simp[SUBSET_DEF,PULL_EXISTS] >>
        simp[IN_Uof,MEM_map2list,PULL_EXISTS] >>
        simp[MEM_EL,PULL_EXISTS] >>
        rw[] (* 2 *)
        >- (qspecl_then [‘b’,‘(mk_bmap (REVERSE (Lofeqthl (map2list (LENGTH sl − 1) eqths))))’] assume_tac ffv_fprpl >>
           ‘(∀n s. (n,s) ∈ ffv b ⇒ sbounds s = ∅)’
             by (drule_then assume_tac wff_no_vbound >> gs[ffv_FALLL] >>
                metis_tac[]) >>
           first_x_assum $ drule_then assume_tac >>
           qspecl_then [‘(REVERSE (Lofeqthl (map2list (LENGTH sl − 1) eqths)))’,‘b’] assume_tac mk_bmap_BIGUNION >>
           gs[] >>
           ‘x ∈ Uof tfv (set (Lofeqthl (map2list (LENGTH sl − 1) eqths)))’
             by (gs[SUBSET_DEF] >> first_x_assum irule >>
                simp[PULL_EXISTS] >> qexists ‘i’ >>
                gs[LENGTH_LRofeqthl,FDOM_mk_bmap]) >>
            gs[FDOM_mk_bmap,LENGTH_LRofeqthl,LENGTH_map2list] >>
            ‘LENGTH sl ≠ 0’ by simp[] >>
            ‘i < LENGTH sl’ by simp[] >>
            disj1_tac >> qexists ‘(LENGTH sl − (i + 1))’ >> simp[] >>
            ‘(LENGTH sl − (i + 1)) < LENGTH sl’ by simp[] >>
            first_x_assum $ drule_then assume_tac >>
            ‘i ≤ (LENGTH sl − 1)’ by simp[] >>
            drule_then assume_tac FAPPLY_mk_bmap_REVERSE_Lofeqthl >> gs[] >>
            qabbrev_tac ‘n1 = (LENGTH sl − (i + 1))’ >> 
            Cases_on ‘(eqths n1)’ >> Cases_on ‘r’ >>
            first_x_assum $ drule_then assume_tac >>
            gs[concl_def,is_EQ_def,Leq_Req_EQ,cont_def] >>
            gs[Uof_SUBSET,Uof_UNION,Uof_Sing] >>
            gs[SUBSET_DEF] >> first_x_assum irule >>
            qexists ‘EQ t1 t2’ >> simp[ffv_EQ]) >> (*second the same*)
        qspecl_then [‘b’,‘(mk_bmap (REVERSE (Rofeqthl (map2list (LENGTH sl − 1) eqths))))’] assume_tac ffv_fprpl >>
           ‘(∀n s. (n,s) ∈ ffv b ⇒ sbounds s = ∅)’
             by (drule_then assume_tac wff_no_vbound >> gs[ffv_FALLL] >>
                metis_tac[]) >>
           first_x_assum $ drule_then assume_tac >>
           qspecl_then [‘(REVERSE (Rofeqthl (map2list (LENGTH sl − 1) eqths)))’,‘b’] assume_tac mk_bmap_BIGUNION >>
           gs[] >>
           ‘x ∈ Uof tfv (set (Rofeqthl (map2list (LENGTH sl − 1) eqths)))’
             by (gs[SUBSET_DEF] >> first_x_assum irule >>
                simp[PULL_EXISTS] >> qexists ‘i’ >>
                gs[LENGTH_LRofeqthl,FDOM_mk_bmap]) >>
            gs[FDOM_mk_bmap,LENGTH_LRofeqthl,LENGTH_map2list] >>
            ‘LENGTH sl ≠ 0’ by simp[] >>
            ‘i < LENGTH sl’ by simp[] >>
            disj1_tac >> qexists ‘(LENGTH sl − (i + 1))’ >> simp[] >>
            ‘(LENGTH sl − (i + 1)) < LENGTH sl’ by simp[] >>
            first_x_assum $ drule_then assume_tac >>
            ‘i ≤ (LENGTH sl − 1)’ by simp[] >>
            drule_then assume_tac FAPPLY_mk_bmap_REVERSE_Rofeqthl >> gs[] >>
            qabbrev_tac ‘n1 = (LENGTH sl − (i + 1))’ >> 
            Cases_on ‘(eqths n1)’ >> Cases_on ‘r’ >>
            first_x_assum $ drule_then assume_tac >>
            gs[concl_def,is_EQ_def,Leq_Req_EQ,cont_def] >>
            gs[Uof_SUBSET,Uof_UNION,Uof_Sing] >>
            gs[SUBSET_DEF] >> first_x_assum irule >>
            qexists ‘EQ t1 t2’ >> simp[ffv_EQ]) >>
     simp[SUBSET_DEF,PULL_EXISTS] >>
     ‘(∀n0. n0 ≤ (LENGTH sl − 1) ⇒ is_EQ (concl (eqths n0)))’
      by (rw[] >>
         first_x_assum $ qspecl_then [‘n0’] assume_tac >> gs[] >>
         gs[] >> ‘LENGTH sl ≠ 0’ by simp[] >>
         ‘n0 < LENGTH sl’ by simp[] >> gs[]) >>
     drule_then assume_tac MEM_Lofeqthl_map2list >>
     drule_then assume_tac MEM_Rofeqthl_map2list >> 
     simp[PULL_EXISTS] >>
     simp[IN_Uof,PULL_EXISTS,MEM_map2list] >>
     rw[] (* 2 *)
     >> (first_assum $ irule_at Any >>
        ‘LENGTH sl ≠ 0’ by simp[] >>
        ‘n0 < LENGTH sl’ by simp[] >>
        last_x_assum $ drule_then strip_assume_tac >>
        Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
        rename [‘MEM (Γ,A,f) _’] >>
        first_x_assum $ drule_then assume_tac >>
        gs[] >> gs[Uof_Sing,Uof_UNION,cont_def,ffv_EQ] >>
        metis_tac[SUBSET_DEF] )) >>
    gs[fcong_def] >>
    qpat_x_assum ‘f = IFF _ _’ (K all_tac) >>
    gs[IN_Uof,MEM_map2list] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘n0 < LENGTH sl’ by simp[] >>
    first_x_assum $ drule_then strip_assume_tac >>
    Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
    rename [‘MEM (Γ,A,f) _’] >>
    first_x_assum $ drule_then assume_tac >>
    gs[Uof_Sing,Uof_UNION] >>
    simp[SUBSET_DEF,IN_Uof,MEM_map2list,PULL_EXISTS] >>
    gs[Uof_SUBSET,assum_def] >>
    first_x_assum $ drule_then assume_tac >>
    rw[] >> disj1_tac >> qexists ‘n0’ >> simp[cont_def] >>
    gs[SUBSET_DEF] >> metis_tac[])
>~ [‘(Γ,A,f) = fcong (map2list (LENGTH sl − 1) eqths) sl b’]
   >- (gs[fcong_def,wff_IFF] >>
    rw[] (* 2 *) >>cheat (* need to realise as fVinst *))
>~ [‘(Γ,A,f) = fcong (map2list (LENGTH sl − 1) eqths) sl b’]
   >- (gs[fcong_def,IN_Uof,MEM_map2list] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘n0 < LENGTH sl’ by simp[] >>
    first_x_assum $ drule_then strip_assume_tac >>
    Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
    gs[assum_def] >> metis_tac[])   
>- gs[wfaths_def]
>- (gs[wfaths_def] >> metis_tac[])
>- (gs[wfaths_def] >> metis_tac[])
>- (gs[MEM_FLAT,MEM_map2list] >>
    ‘n0 < LENGTH sl’ suffices_by metis_tac[] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘ n0 < LENGTH sl’ by simp[])
>- (gs[MEM_FLAT,MEM_map2list] >>
    ‘n0 < LENGTH sl’ suffices_by metis_tac[] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘ n0 < LENGTH sl’ by simp[])
>- (gs[MEM_FLAT,MEM_map2list] >>
    ‘n0 < LENGTH sl’ suffices_by metis_tac[] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘ n0 < LENGTH sl’ by simp[]) (*36*)
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘MEM (Γ1,A1,f1) _’] >>
gs[Uof_Sing,Uof_UNION,vinsth_def] >>
first_x_assum $ drule_then assume_tac >>
rw[] (* 2 *)
>- (qspecl_then [‘f1’,‘vσ’] assume_tac
               ffv_finst_wfvmap >>
   first_x_assum (qspecl_then [‘Σf’] assume_tac)>>
   gs[cont_def] >>
   ‘ffv f1 ⊆ FDOM vσ’ by metis_tac[SUBSET_TRANS] >>
   gs[] >>
   simp[vinst_cont_def,SUBSET_DEF] >> 
   Cases_on ‘x’ >> simp[] >>
   rw[] >> simp[ofFMAP_def,PULL_EXISTS] >>
   first_x_assum $ irule_at Any >> gs[SUBSET_DEF]) >>
simp[Uof_SUBSET,PULL_EXISTS] >> rw[] >>
qspecl_then [‘x’,‘vσ’] assume_tac
               ffv_finst_wfvmap >>
first_x_assum (qspecl_then [‘Σf’] assume_tac)>>
gs[cont_def] >>
‘ffv x ⊆ FDOM vσ’ by
(gs[Uof_SUBSET] >> metis_tac[SUBSET_TRANS]) >>
   gs[] >>
   simp[vinst_cont_def,SUBSET_DEF] >>
   Cases_on ‘x'’ >> simp[] >>
   rw[] >> simp[ofFMAP_def,PULL_EXISTS] >>
   first_x_assum $ irule_at Any >>
   gs[Uof_SUBSET] >>
   gs[SUBSET_DEF] >> metis_tac[]) (* 29 *)
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
    gs[vinsth_def] >>
    irule wff_finst >>
    gs[wfvmap_def] >> rw[] (* 3 *)
    >- gs[wfsig_def,wffsig_def]
    >- metis_tac[wfvmap_def,wfvmap_presname]
    >- (gs[cont_def] >> irule SUBSET_TRANS >>
       first_x_assum $ irule_at Any >>
       first_x_assum $ drule_then assume_tac >>
       gs[Uof_SUBSET,Uof_UNION,Uof_Sing]) >>
    metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
    gs[vinsth_def] >>
    irule wff_finst >>
    gs[wfvmap_def] >> rw[] (* 3 *)
    >- gs[wfsig_def,wffsig_def]
    >- metis_tac[wfvmap_def,wfvmap_presname]
    >- (gs[cont_def] >> irule SUBSET_TRANS >>
       first_x_assum $ irule_at Any >>
       first_x_assum $ drule_then assume_tac >>
       gs[Uof_SUBSET,Uof_UNION,Uof_Sing]) >>
    metis_tac[]) (* 27 *)    
>- (first_x_assum $ drule_then assume_tac >>
   gs[gen_def]  >>
   ‘ffv (mk_FALL x s f) = ffv f ∪ sfv s DELETE (x,s)’
     by (irule ffv_mk_FALL >>
   gs[NOTIN_genavds] >>
   gs[SUBSET_DEF,Uof_SUBSET,Uof_Sing,Uof_UNION] >>
   metis_tac[]) >>
   gs[Uof_Sing,Uof_UNION] >> rw[] (* 2 *)
   >- (gs[SUBSET_DEF] >> metis_tac[]) >>
   gs[genavds_def,assum_def] >> gs[SUBSET_DEF])
>- (gs[gen_def] >> 
   irule $ cj 6 wff_rules >>
   gs[] >> gs[IN_fVslfv,NOTIN_genavds] >>
   rw[] (* 3 *)
   >- (‘ffv f ⊆ Γ’
        suffices_by metis_tac[SUBSET_DEF] >>
      first_x_assum $ drule_then assume_tac >>
      gs[Uof_Sing,Uof_UNION,Uof_SUBSET])
   >> metis_tac[])
>- (gs[gen_def] >> metis_tac[])
>- (first_x_assum $ drule_then assume_tac >>
   gs[spec_def] >>
   gs[Uof_UNION,Uof_Sing] >> rw[] 
   >- (‘ffv (substb t f) ⊆ ffv f ∪ tfv t’
        by (rw[substb_def] >>
           irule ffv_frpl_SUBSET >>
           rw[] (* 2 *)
           >- (‘(n,s) ∈ Γ’ by metis_tac[SUBSET_DEF]>>
              irule $ cj 2 wft_no_bound >>
              irule_at Any Pf0Drv_cont_wf >>
              rpt (first_x_assum $ irule_at Any) >>
              gs[wfaths_def] >> metis_tac[]) >> 
           metis_tac[wft_no_bound]) >>
      gs[SUBSET_DEF] >> metis_tac[] (*ffv_fprpl *))
   >- gs[SUBSET_DEF]) 
>- (gs[spec_def] >> 
    irule wff_spec >> gs[] >> rw[] (* 2 *)
    >- gs[wfsig_def,wffsig_def]
    >> metis_tac[])   
>- (gs[spec_def] >> metis_tac[]) (*21*)
>- (first_x_assum $ drule_then assume_tac >>
   gs[Uof_lemma_classic])
>- (first_x_assum $ drule_then assume_tac >>
    gs[] >> metis_tac[wff_NEG])    
>- (first_x_assum $ drule_then assume_tac >>
    gs[])   
>- (*form bot step*) (first_x_assum $ drule_then assume_tac>>
   gs[Uof_UNION,Uof_Sing] >> gs[SUBSET_DEF])
>- gs[assume_def,Uof_Sing]   
>- gs[assume_def]
>- gs[assume_def]   
>- (first_x_assum $ drule_then assume_tac >>
   first_x_assum $ drule_then assume_tac >>
   gs[Uof_UNION,Uof_Sing] >> gs[SUBSET_DEF] >> metis_tac[])
>- metis_tac[wff_IMP]
>- (gs[] >> metis_tac[])   
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   rename [‘MEM (Γ1,A1,f1) _’] >>
   gs[disch_def,Uof_UNION,Uof_Sing] >>
   first_x_assum $ drule_then assume_tac>>
   rw[] (* 2 *)
   >- gs[SUBSET_DEF] >>
   ‘Uof ffv (A1 DELETE a) ⊆ Uof ffv A1’
    by (irule Uof_SUBSET_MONO >> simp[]) >>
   irule SUBSET_TRANS >>
   first_x_assum $ irule_at Any >>
   gs[SUBSET_DEF])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
    gs[disch_def,wff_IMP] >> metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
    gs[disch_def] >> metis_tac[])       
>- (gs[refl_def,Uof_UNION,Uof_Sing,Uof_EMPTY,EQ_def] >>
   gs[SUBSET_DEF]) (* 7 *)
>- gs[refl_def,wff_EQ,has_eq]
>- gs[refl_def]  
>- (first_x_assum $ drule_then assume_tac >>
   gs[Uof_Sing,Uof_UNION,EQ_def,SUBSET_DEF] >>
   metis_tac[]) (* 4 *)
>- (gs[wff_EQ] >>
   first_x_assum $ drule_then strip_assume_tac >>
   gs[wff_EQ] >>
   gs[tsname_def])
>- (rpt (first_x_assum $ drule_then assume_tac) >>
   gs[Uof_UNION,Uof_Sing,EQ_def,SUBSET_DEF]  >>
   metis_tac[])
>- (gs[wff_EQ] >>
   rpt
   (first_x_assum $ drule_then strip_assume_tac) >>
   gs[wff_EQ] >>
   gs[tsname_def])
>- (gs[wff_EQ] >>
   rpt
   (first_x_assum $ drule_then strip_assume_tac) >>
   gs[wff_EQ] >>
   gs[tsname_def])
>> (Cases_on ‘th’ >> Cases_on ‘r’ >>
   gs[add_cont1_def,Once EXTENSION,SUBSET_DEF,IN_Uof,Uof_UNION,Uof_Sing] >>
   metis_tac[])        
QED
        
Definition wfsigaths_def:
 wfsigaths Σ aths ⇔ wfsig Σ ∧ wfaths Σ aths
End 

Theorem Pf0_wff:
wfsigaths Σ axs ⇒
     ∀pf.
       Pf0 Σ axs pf ⇒
       ∀Γ A f.
         MEM (Γ,A,f) pf ⇒
         wff Σ f ∧
         ∀a. a ∈ A ⇒ wff Σ a
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >>
gs[wfsigaths_def] >> strip_tac >>
drule_then assume_tac Pf0_ffv_SUBSET_wff >> 
gs[Uof_Sing,Uof_UNION,Uof_SUBSET] >> metis_tac[]
QED



Theorem Pf0Drv_wff:
wfsigaths Σ axs ⇒
     ∀th.
       Pf0Drv Σ axs th ⇒
       wff Σ (concl th) ∧
       ∀a. a ∈ (assum th) ⇒ wff Σ a
Proof         
strip_tac >>
simp[Pf0Drv_def,PULL_EXISTS] >>
Cases_on ‘th’ >> Cases_on ‘r’ >>
simp[concl_def,assum_def] >>
metis_tac[Pf0_wff]
QED


Theorem Pf0Drv_ffv_SUBSET_cont:
wfsigaths Σ axs ⇒
     ∀Γ A f.
       Pf0Drv Σ axs (Γ,A,f) ⇒
       Uof ffv ({f} ∪ A) ⊆ Γ
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >>
strip_tac >>
simp[Pf0Drv_def,PULL_EXISTS] >>
metis_tac[Pf0_ffv_SUBSET_wff,wfsigaths_def]
QED        

        



Theorem Pf0Drv_concl_ffv_SUBSET:
wfsigaths Σ axs ⇒ ∀Γ A f. Pf0Drv Σ axs (Γ,A,f) ⇒
 ffv f ⊆ Γ
Proof 
rw[] >> drule_all_then assume_tac Pf0Drv_ffv_SUBSET_cont >>
gs[Uof_SUBSET,Uof_Sing,Uof_UNION]
QED


Theorem Pf0Drv_assum_ffv_SUBSET:
wfsigaths Σ axs ⇒ ∀Γ A f. Pf0Drv Σ axs (Γ,A,f) ⇒
∀a. a ∈ A ⇒ ffv a ⊆ Γ 
Proof 
rw[] >> drule_all_then assume_tac Pf0Drv_ffv_SUBSET_cont >>
gs[Uof_SUBSET,Uof_Sing,Uof_UNION]
QED




Theorem Pf0Drv_assume:
  ∀Σ aths c. wff Σ c ∧ is_cfm c ⇒ Pf0Drv Σ aths (assume c)
Proof
  rw[Pf0Drv_def] >>
  drule_then assume_tac Pf0_assume >>
  first_x_assum $ irule_at Any >> simp[] >> metis_tac[]
QED


Theorem Pf0Drv_mp:
  Pf0Drv Σ axs (Γ1,A1,IMP f1 f2) ∧
  Pf0Drv Σ axs (Γ2,A2,f1) ⇒
  Pf0Drv Σ axs (Γ1 ∪ Γ2,A1 ∪ A2,f2) 
Proof
  rw[Pf0Drv_def] >>
  drule_all_then assume_tac Pf0_mp >>
  first_x_assum $ irule_at Any >> simp[]
QED
        


        
Theorem Pf0Drv_undisch:
  wfsigaths Σ aths ⇒
  Pf0Drv Σ aths (Γ,A,IMP f1 f2) ⇒ Pf0Drv Σ aths (Γ,A ∪ {f1},f2)
Proof
  rw[] >> 
  drule_all_then assume_tac Pf0Drv_wff >>
  gs[wff_IMP,concl_def,assum_def] >>
  rev_drule_then assume_tac Pf0Drv_assume >>
  first_x_assum (qspecl_then [‘aths’] assume_tac) >>
  gs[assume_def] >> gs[wfsigaths_def] >>
  drule_all_then assume_tac Pf0Drv_cfm >>
  gs[is_cfm_def] >>
  rev_drule_then assume_tac Pf0Drv_mp >>
  first_x_assum $ drule_then assume_tac >> 
  ‘Γ ∪ ffv f1 = Γ’ suffices_by metis_tac[] >>
  ‘ffv f1 ⊆ Γ’ suffices_by
     (gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
  ‘ffv (IMP f1 f2) ⊆ Γ’ suffices_by gs[ffv_thm] >>
  irule Pf0Drv_concl_ffv_SUBSET >>
  metis_tac[wfsigaths_def]
QED  
          

Theorem Pf0Drv_add_cont1:
 Pf0Drv Σ aths th ⇒
  ∀n s. wfs (FST Σ) s ⇒ Pf0Drv Σ aths (add_cont1 (n,s) th)
Proof  
 rw[] >> gs[Pf0Drv_def] >>
 drule_then assume_tac $ Pf0_add_cont1 >>
 rpt (first_x_assum $ irule_at Any) >> qexists ‘n’ >> simp[]
QED
         


        
Theorem Pf0Drv_add_cont0:          
 ∀vs. FINITE vs ⇒
      (∀n s. (n,s) ∈ vs ⇒ wfs (FST Σ) s) ∧ Pf0Drv Σ aths th ⇒
      Pf0Drv Σ aths (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) vs) th)
Proof      
 Induct_on ‘vs’ >> rw[Uof_EMPTY,add_cont_EMPTY] >>
 ‘Pf0Drv Σ aths (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) vs) th)’ by metis_tac[] >>
 ‘(e INSERT vs) = {e} ∪ vs’ by 
 rw[Once INSERT_SING_UNION] >>
 pop_assum SUBST_ALL_TAC >> rw[Uof_Sing,Uof_UNION] >>
 rw[add_cont_UNION] >>
 drule_then assume_tac Pf0Drv_add_cont1 >> 
 Cases_on ‘e’ >> gs[] >> gs[add_cont1_add_cont] >>
 first_x_assum irule >> metis_tac[]
QED

Theorem Pf0Drv_add_cont:
FINITE ct ∧ is_cont ct ⇒
      (∀n s. (n,s) ∈ ct ⇒ wfs (FST Σ) s) ∧ Pf0Drv Σ aths th ⇒
      Pf0Drv Σ aths (add_cont ct th)
Proof
rw[] >> drule_all_then mp_tac cont_decompose >> simp[] >>
rw[] >> 
‘Pf0Drv Σ aths (add_cont ( BIGUNION (IMAGE (λ(n,s). {(n,s)} ∪ sfv s) ct)) th)’ suffices_by simp[] >>
‘Pf0Drv Σ aths
          (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) ct) th)’
  suffices_by  gs[BIGUNION_IMAGE_Uof,PULL_EXISTS] >>  
irule Pf0Drv_add_cont0 >> simp[] >> metis_tac[]
QED




Theorem Pf0Drv_double_neg:
Pf0Drv Σ aths (Γ,A ∪ {NEG f},False) ⇒
Pf0Drv Σ aths (Γ,A,f)
Proof
rw[Pf0Drv_def] >>
drule_all_then assume_tac Pf0_double_neg >>
first_x_assum $ irule_at Any >> simp[]
QED


Theorem Pf0Drv_mp:
Pf0Drv Σ aths (Γ1,A1,IMP ϕ ψ) ∧ Pf0Drv Σ aths (Γ2,A2,ϕ) ⇒
Pf0Drv Σ aths (Γ1 ∪ Γ2,A1 ∪ A2,ψ)
Proof
rw[Pf0Drv_def] >>
drule_all_then assume_tac Pf0_mp >>
first_x_assum $ irule_at Any >> simp[]
QED


Theorem Pf0Drv_disch:
 Pf0Drv Σ aths (Γ,A,f) ∧ wff Σ a ∧ is_cfm a ⇒
 Pf0Drv Σ aths (disch a (Γ,A,f))
Proof
 rw[Pf0Drv_def] >> drule_all_then assume_tac Pf0_disch >>
 first_x_assum $ irule_at Any >> simp[]
QED 
 



        
Theorem Pf0Drv_add_assum:
∀s th. FINITE s ⇒  wfsigaths Σ aths ∧
    (∀ϕ. ϕ ∈ s ⇒ wff Σ ϕ ∧ is_cfm ϕ) ∧
    Pf0Drv Σ aths th ⇒ Pf0Drv Σ aths (add_assum s th)
Proof
 Induct_on ‘FINITE’ >> gs[add_assum_EMPTY] >>
 rw[] >>
 ‘Pf0Drv Σ aths (add_assum s th)’ by metis_tac[] >>
 qpat_x_assum ‘∀th.
          wfsigaths Σ aths ∧ (∀ϕ. ϕ ∈ s ⇒ wff Σ ϕ ∧ is_cfm ϕ) ∧
          Pf0Drv Σ aths th ⇒
          Pf0Drv Σ aths (add_assum s th)’ (K all_tac)>>
 Cases_on ‘th’ >> Cases_on ‘r’ >>
 gs[add_assum_def] >>
 drule_then assume_tac Pf0Drv_disch >>
 ‘wff Σ e ∧ is_cfm e’ by metis_tac[] >>
 first_x_assum $ drule_then assume_tac >>
 gs[disch_def] >>
 drule_then assume_tac Pf0Drv_undisch >>
 first_x_assum $ drule_then assume_tac >> 
 gs[add_assum_def,Uof_UNION,Uof_Sing,Uof_INSERT] >>
 ‘q' ∪ s DELETE e ∪ {e} = q' ∪ (e INSERT s)’
  by (gs[EXTENSION] >> metis_tac[]) >>
 ‘q ∪ (ffv e ∪ Uof ffv s) = q ∪ Uof ffv s ∪ ffv e’
  by  (gs[EXTENSION] >> metis_tac[]) >>
 gs[]
QED  



Theorem Pf0Drv_wff1:
wfsigaths Σ aths ⇒
     ∀Γ A f. Pf0Drv Σ aths (Γ,A,f) ⇒
             wff Σ f ∧ ∀a. a ∈ A ⇒ wff Σ a
Proof
rw[] >> drule_all_then assume_tac Pf0Drv_wff >> gs[concl_def,assum_def]
QED



Theorem Pf0Drv_cont_SUBSET:
  Pf0Drv Σ aths (Γ0,A,f) ∧ FINITE Γ ∧ Γ0 ⊆ Γ ∧ is_cont Γ ∧
  (∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s) ⇒
  Pf0Drv Σ aths (Γ,A,f)
Proof
  rw[] >> drule_then assume_tac Pf0Drv_add_cont >> gs[] >>
  first_x_assum $ drule_all_then assume_tac >>
  gs[add_cont_def] >>
  ‘Γ ∪ Γ0 = Γ’ by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[])>>
  gs[]
QED




Theorem Pf0Drv_assum_SUBSET:
  wfsigaths Σ aths ∧
  Pf0Drv Σ aths (Γ,A0,f) ∧ FINITE A ∧ A0 ⊆ A ∧
  (∀a. a ∈ A ⇒ wff Σ a ∧ is_cfm a) ⇒
  Pf0Drv Σ aths (Γ ∪ Uof ffv A,A,f)
Proof
  rw[] >> drule_then assume_tac Pf0Drv_add_assum >> gs[] >>
  first_x_assum $ drule_then assume_tac >>
  first_x_assum $ qspecl_then [‘(Γ,A0,f)’] assume_tac>> gs[] >>
  gs[add_assum_def] >>
  ‘A0 ∪ A = A’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[])>>
  gs[]
QED
        
   
Theorem Pf0Drv_gen:
Pf0Drv Σ aths (Γ,A,f) ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
(x,s) ∉ genavds (Γ,A,f) ⇒
Pf0Drv Σ aths (gen (x,s) (Γ,A,f))
Proof
rw[Pf0Drv_def] >>
drule_then assume_tac Pf0_ALLI >>
first_x_assum $ drule_all_then assume_tac >>
first_x_assum $ irule_at Any >> simp[]
QED



Theorem Pf0Drv_cont_wf':
 (∀Γ A f. (Γ,A,f) ∈ aths ⇒ ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s) ⇒
  ∀Γ A f. Pf0Drv (Σf,Σp,Σe) aths (Γ,A,f) ⇒
  ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s
Proof
  rw[] >> irule Pf0Drv_cont_wf >>
  gs[Pf0Drv_def] >> metis_tac[]
QED  
        
                
val _ = export_theory();

