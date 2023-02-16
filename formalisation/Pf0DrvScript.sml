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
  (∀c:form. wff Σ c ∧ is_cfm f ⇒ Pf0 Σ aths [assume c]) ∧
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




Theorem PfDrv_cont_wf:
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



Definition wfaths_def:
  wfaths (Σf,Σp,Σe) aths ⇔
  (∀Γ A f. (Γ,A,f) ∈ aths ⇒
           wff (Σf,Σp,Σe) f ∧ (∀a. a ∈ A ⇒ wff (Σf,Σp,Σe) a) ∧
           (∀n s. (n,s) ∈ Γ ⇒ wfs Σf s) ∧
           Uof ffv ({f} ∪ A) ⊆ Γ)
End
           
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
   >- cheat
>~ [‘(Γ,A,f) = fcong (map2list (LENGTH sl − 1) eqths) sl b’]
   >- cheat
>~ [‘(Γ,A,f) = fcong (map2list (LENGTH sl − 1) eqths) sl b’]
   >- cheat   
          
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
    
>- (simp[Uof_UNION,Uof_SUBSET,Uof_Sing] >>
   rw[] (* 2 *)
   >- (gs[fcong_def] >> simp[ffv_IFF] >>
       ffv_fprpl cheat
      ‘BIGUNION {tfv t | MEM t (Lofeqthl (map2list (LENGTH sl − 1) eqths))} ⊆
         Uof cont (set (map2list (LENGTH sl − 1) eqths)) ∧
      BIGUNION {tfv t | MEM t (Rofeqthl (map2list (LENGTH sl − 1) eqths))} ⊆
         Uof cont (set (map2list (LENGTH sl − 1) eqths))’
        suffices_by
        (disch_tac >> simp[] >>
        simp[SUBSET_DEF,PULL_EXISTS] >>
        simp[IN_Uof,MEM_map2list,PULL_EXISTS] >>
        simp[MEM_EL,PULL_EXISTS] >>
        rw[] >>
        qexists ‘n’ >> simp[] >>
        first_x_assum $
                      drule_then strip_assume_tac >>
        Cases_on ‘x’ >>              
        qspecl_then
        [‘(Leq (concl (eqths n)))’,‘q’,‘r’]
        assume_tac sfv_tfv >>
        gs[] >> Cases_on ‘(eqths n)’ >>
        Cases_on ‘r'’ >> rename [‘(Γ,A,f)’] >>
        gs[cont_def] >>
        first_x_assum $ drule_then assume_tac >>
        gs[is_EQ_def,concl_def] >> gs[Leq_Req_EQ] >>
        ‘(q,r) ∈ tfv t1 ∧ tfv t1 ⊆ Γ’
         suffices_by metis_tac[SUBSET_DEF] >>
        gs[wff_EQ,Uof_SUBSET,Uof_UNION,Uof_Sing] >>
        rw[] (* 2 *)
        >- metis_tac[wft_not_bound] >>
        ‘ffv (EQ t1 t2) ⊆ Γ’ by metis_tac[] >>
        qpat_x_assum ‘∀a. a = EQ t1 t2 ∨ a ∈ A ⇒ ffv a ⊆ Γ’ (K all_tac) >> gs[ffv_EQ]) >>
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
    gs[fVcong_def] >>
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
    rw[] >> qexists ‘n0’ >> simp[cont_def] >>
    gs[SUBSET_DEF] >> metis_tac[])
>- (gs[fVcong_def,wff_IFF] >>
    rw[] (* 2 *)
    >- (irule wff_fVar' >>
        irule wfabsap_wfs >> rw[] (* 3 *)
        >- (first_x_assum $ drule_then
                         strip_assume_tac >>
           ‘(Leq (concl (eqths n))) =
            (EL n (Lofeqthl (map2list (LENGTH sl − 1) eqths)))’ suffices_by metis_tac[] >>
           simp[Lofeqths_def] >>
           ‘ EL n (MAP (FST ∘ dest_eq ∘ concl) (map2list (LENGTH sl − 1) eqths)) =
           (FST ∘ dest_eq ∘ concl)
           (EL n (map2list (LENGTH sl − 1) eqths))’
           by (irule EL_MAP >>
               simp[LENGTH_map2list]) >>
           gs[Leq_def] >>
           ‘n ≤  (LENGTH sl − 1)’ by simp[] >>
           rpt AP_TERM_TAC >>
           rw[Once EQ_SYM_EQ] >>
           irule EL_map2list >> simp[])
       >- (gs[Lofeqths_def,MEM_MAP,MEM_map2list] >>
          ‘LENGTH sl ≠ 0’ by simp[] >>
          ‘n0 < LENGTH sl’ by simp[] >>
          first_x_assum $ drule_then
                      strip_assume_tac >>
          Cases_on ‘eqths n0’ >>
          gs[concl_def,is_EQ_def] >>
          gs[dest_eq_EQ] >> Cases_on ‘r’ >>
          first_x_assum $ drule_then
          strip_assume_tac >>
          gs[concl_def,wff_EQ]) >>
       simp[Lofeqths_def,LENGTH_map2list] >>
       Cases_on ‘sl’ >> gs[]) >>
   (irule wff_fVar' >>
        irule wfabsap_wfs >> rw[] (* 3 *)
        >- (first_x_assum $ drule_then
                         strip_assume_tac >>
            ‘sort_of (Leq (concl (eqths n))) =
             sort_of (Req (concl (eqths n)))’
             by (irule is_EQ_wff_Leq_Req >>
                simp[] >>
                last_x_assum $ irule_at Any>>
                Cases_on ‘(eqths n)’ >>
                Cases_on ‘r’ >>
                first_x_assum $
                  drule_then assume_tac >>
                simp[concl_def]) >>
            gs[] >>
           ‘(Req (concl (eqths n))) =
            (EL n (Rofeqthl (map2list (LENGTH sl − 1) eqths)))’ suffices_by metis_tac[] >>
           simp[Rofeqths_def] >>
           ‘ EL n (MAP (SND ∘ dest_eq ∘ concl) (map2list (LENGTH sl − 1) eqths)) =
           (SND ∘ dest_eq ∘ concl)
           (EL n (map2list (LENGTH sl − 1) eqths))’
           by (irule EL_MAP >>
               simp[LENGTH_map2list]) >>
           gs[Req_def] >>
           ‘n ≤  (LENGTH sl − 1)’ by simp[] >>
           rpt AP_TERM_TAC >>
           rw[Once EQ_SYM_EQ] >>
           irule EL_map2list >> simp[])
       >- (gs[Rofeqths_def,MEM_MAP,MEM_map2list] >>
          ‘LENGTH sl ≠ 0’ by simp[] >>
          ‘n0 < LENGTH sl’ by simp[] >>
          first_x_assum $ drule_then
                      strip_assume_tac >>
          Cases_on ‘eqths n0’ >>
          gs[concl_def,is_EQ_def] >>
          gs[dest_eq_EQ] >> Cases_on ‘r’ >>
          first_x_assum $ drule_then
          strip_assume_tac >>
          gs[concl_def,wff_EQ]) >>
       simp[Rofeqths_def,LENGTH_map2list] >>
       Cases_on ‘sl’ >> gs[]))
>- (gs[fVcong_def,IN_Uof,MEM_map2list] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘n0 < LENGTH sl’ by simp[] >>
    first_x_assum $ drule_then strip_assume_tac >>
    Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
    gs[assum_def] >> metis_tac[])    (* 33 *)
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   rename [‘MEM (Γ1,A1,f1) _’] >>
   gs[fVinsth_def] >>
   first_x_assum $ drule_then assume_tac >>
   gs[Uof_Sing,Uof_UNION] >> rw[]
   >- (qspecl_then [‘f1’,‘fσ’] assume_tac
      ffv_fVinst >>
      ‘ffv f1 ∪ ffv (fVinst fσ f1) =
        ffv f1 ∪ ofFMAP ffv fσ (FDOM fσ ∩ fVars f1)’
      suffices_by
        (rw[] >>
        ‘ffv f1 ∪ ffv (fVinst fσ f1) ⊆ Γ1 ∪ ofFMAP ffv fσ (fVars f1 ∪ Uof fVars A1)’
         suffices_by
          (gs[SUBSET_DEF] >> metis_tac[]) >>
        pop_assum SUBST_ALL_TAC >>
        gs[] >> rw[] (* 2 *)
        >- gs[SUBSET_DEF] >>
        gs[ofFMAP_FDOM] >>
        ‘ofFMAP ffv fσ (fVars f1) ⊆
        ofFMAP ffv fσ (fVars f1 ∪ Uof fVars A1)’
         suffices_by
          (gs[SUBSET_DEF] >> metis_tac[]) >>
        irule ofFMAP_SUBSET_MONO >>
        gs[SUBSET_DEF]) >>
     first_x_assum irule >> rw[] >>
     irule wffVmap_no_vbound >>
     metis_tac[]) >>
    simp[Uof_SUBSET,PULL_EXISTS] >>
    rw[] >>
    ‘ffv x ∪ ffv (fVinst fσ x) =
        ffv x ∪ ofFMAP ffv fσ (FDOM fσ ∩ fVars x)’
     by (irule ffv_fVinst >> rw[] >>
     irule wffVmap_no_vbound >> 
     metis_tac[]) >>
    ‘ffv x ∪ ffv (fVinst fσ x) ⊆ Γ1 ∪ ofFMAP ffv fσ (fVars f1 ∪ Uof fVars A1)’
         suffices_by
          (gs[Uof_SUBSET,SUBSET_DEF] >>
           metis_tac[]) >>
        pop_assum SUBST_ALL_TAC >>
        gs[] >> rw[] (* 2 *)
        >- (gs[SUBSET_DEF,Uof_SUBSET] >>
           metis_tac[]) >> 
        gs[ofFMAP_FDOM] >>
        ‘ofFMAP ffv fσ (fVars x) ⊆
        ofFMAP ffv fσ (fVars f1 ∪ Uof fVars A1)’
         suffices_by
          (gs[SUBSET_DEF] >> metis_tac[]) >>
        irule ofFMAP_SUBSET_MONO >>
        gs[SUBSET_DEF,Uof_def] >> metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
     gs[fVinsth_def] >> 
     irule wff_fVinst >> simp[] >>
     rw[] (* 2 *)
     >- gs[wfsig_def,wffsig_def] >>
     metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
     gs[fVinsth_def] >> 
     irule wff_fVinst >> simp[] >>
     rw[] (* 2 *)
     >- gs[wfsig_def,wffsig_def] >>
     metis_tac[])     
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
              metis_tac[PfDrv_cont_wf]) >> 
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
        
        

                
val _ = export_theory();

