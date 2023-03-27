open HolKernel Parse boolLib bossLib;

val _ = new_theory "PfDrv";


Definition Leq_def:
Leq = FST o dest_eq
End

Definition Req_def:
Req = SND o dest_eq
End
        
Inductive Pf:
[~AX:]
(∀ax. ax ∈ axs ⇒ Pf Σ axs [(ffv ax,{},ax)]) ∧
[~fVcong:]
(∀P sl Pfs eqths.
 sl ≠ [] ∧
 (∀n. n < LENGTH sl ⇒
      is_EQ (concl (eqths n)) ∧
      Pf Σ axs (Pfs n) ∧ MEM (eqths n) (Pfs n) ∧
      sort_of (Leq (concl (eqths n))) = EL n sl) ∧
 (∀s. MEM s sl ⇒ wfs (FST Σ) s) ⇒
 Pf Σ axs (FLAT (map2list (LENGTH sl - 1) Pfs)  ++
 [fVcong (map2list (LENGTH sl - 1) eqths) P sl])   
 ) ∧
[~fVinsth:]
  (∀pf th fσ.
     Pf Σ axs pf ∧ MEM th pf ∧
     wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ⇒
     Pf Σ axs (pf ++ [fVinsth fσ th])) ∧
[~vinsth:]
  (∀pf th vσ.
     Pf Σ axs pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧
     cont th ⊆ FDOM vσ ⇒
     Pf Σ axs (pf ++ [vinsth vσ th])) ∧
[~ALLI:]
  (∀Γ A pf x s f.
     Pf Σ axs pf ∧ MEM (Γ,A,f) pf ∧
     wfs (FST Σ) s ∧ (sfv s) ⊆ Γ ∧
     (x,s) ∉ genavds (Γ,A,f) ⇒
     Pf Σ axs (pf ++ [gen (x,s) (Γ,A,f)])) ∧
[~ALLE:]
  (∀Γ A pf s f t.
     Pf Σ axs pf ∧ MEM (Γ,A,FALL s f) pf ∧
     wft (FST Σ) t ∧ sort_of t = s ⇒
     Pf Σ axs (pf ++ [spec t (Γ,A,FALL s f)])) ∧     
[~double_neg:]
  (∀Γ A pf f.
      Pf Σ axs pf ∧ MEM (Γ,A ∪ {NEG f},False) pf ⇒
      Pf Σ axs (pf ++ [(Γ,A,f)])) ∧
[~fromBot:]
  (∀Γ A pf f.
    Pf Σ axs pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ⇒
    Pf Σ axs (pf ++ [(Γ ∪ ffv f,A,f)])) ∧
[~assume:]
  (∀c:form. wff Σ c ⇒ Pf Σ axs [assume c]) ∧
[~mp:]
  (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
     Pf Σ axs pf1 ∧ Pf Σ axs pf2 ∧
     MEM (Γ1,A1,IMP f1 f2) pf1 ∧
     MEM (Γ2,A2,f1) pf2 ⇒
     Pf Σ axs (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2, A1 ∪ A2,f2)])) ∧     
[~disch:]
  (∀pf th a.
     Pf Σ axs pf ∧ MEM th pf ∧ wff Σ a ⇒
     Pf Σ axs (pf ++ [disch a th])) ∧               
[~refl:]
  (∀t.
     wft (FST Σ) t ∧ tsname t ∈ (SND (SND Σ)) ⇒ Pf Σ axs [refl t]) ∧
[~sym:]
  (∀Γ A pf t1 t2.
     Pf Σ axs pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
     Pf Σ axs (pf ++ [(Γ,A,EQ t2 t1)])) ∧
[~trans:]
  (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
     Pf Σ axs pf1 ∧ Pf Σ axs pf2 ∧
     MEM (Γ1,A1,EQ t1 t2) pf1 ∧ MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
     Pf Σ axs (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
[~add_cont1:]
  (∀pf th n.
    Pf Σ axs pf ∧ MEM th pf ∧ wfs (FST Σ) s ⇒
    Pf Σ axs (pf ++ [add_cont1 (n,s) th]))
End
        
  
Theorem Pf_cont_is_cont:
∀pf. Pf Σ axs pf ⇒
 ∀Γ A f. MEM (Γ,A,f) pf ⇒ is_cont Γ
Proof
 Induct_on ‘Pf’ >> rw[] >> TRY (metis_tac[]) (* 14 *)
 >- metis_tac[ffv_is_cont]
 >- (gs[MEM_FLAT,MEM_map2list] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘n0 < LENGTH sl’ by simp[] >>
    first_x_assum $ drule_then assume_tac >>
    metis_tac[])
 >- (gs[fVcong_def] >>
    rw[Uof_def] >> irule BIGUNION_is_cont >>
    simp[PULL_EXISTS,MEM_map2list] >> rw[] >>
    ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘n0 < LENGTH sl’ by simp[] >>
    first_x_assum $ drule_then assume_tac >>
    gs[] >>
    Cases_on ‘(eqths n0)’ >> Cases_on ‘r’ >>
    gs[cont_def] >>
    metis_tac[])
 >- (Cases_on ‘th’ >> Cases_on ‘r’ >>
    gs[fVinsth_def] >>
    irule UNION_is_cont >>
    rw[] >- metis_tac[] >>
    rw[ofFMAP_def] >> irule BIGUNION_is_cont >>
    simp[PULL_EXISTS] >> metis_tac[ffv_is_cont])
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
(∀ax. ax ∈ axs ⇒ wff (Σf,Σp,Σe) ax) ⇒
∀pf. Pf (Σf,Σp,Σe) axs pf ⇒
 ∀Γ A f. MEM (Γ,A,f) pf ⇒
         ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s
Proof
strip_tac >> 
Induct_on ‘Pf’ >> rw[] (* 27 *) >> TRY (metis_tac[]) (*13*)
>- metis_tac[wff_wfs]
>- (gs[MEM_FLAT,MEM_map2list] >> 
   ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> Cases_on ‘(eqths n0)’ >>
   Cases_on ‘r’ >> metis_tac[])
>- (gs[fVcong_def,IN_Uof,MEM_map2list] >>
   ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> Cases_on ‘(eqths n0)’ >>
   Cases_on ‘r’ >> gs[cont_def] >> metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   gs[fVinsth_def] (* 2 *) >- metis_tac[]  >>
   gs[ofFMAP_def,IN_Uof] >>
   irule wff_wfs >> gs[wffVmap_def] >>
   Cases_on ‘a’ >>
   first_x_assum $ drule_then assume_tac >>
   first_x_assum $ irule_at Any >>
   gs[ffv_FALLL]>> metis_tac[])
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




Theorem Leq_Req_EQ:
Leq (EQ t1 t2) = t1 ∧ Req (EQ t1 t2) = t2
Proof
rw[EQ_def,Leq_def,Req_def,dest_eq_def]
QED

        
Theorem wfabsap_wfs:
 ∀tl sl.(∀s. MEM s sl ⇒ wfs Σf s) ∧
 (∀t. MEM t tl ⇒ wft Σf t) ∧
 LENGTH tl = LENGTH sl ∧
 (∀n. n < LENGTH sl ⇒
     sort_of (EL n tl) = EL n sl) ⇒
 wfabsap Σf sl tl
Proof
 Induct_on ‘tl’ >> Cases_on ‘sl’ >>
 gs[wfabsap_def] >>rw[] (* 3 *)
 >- (‘wfs Σf st’ by metis_tac[] >>
    drule_then assume_tac $ cj 2 wft_no_bound >>
    drule_then assume_tac $ cj 2 sbounds_tbounds >>
    gs[SUBSET_DEF,EXTENSION] >> metis_tac[])
 >- (first_x_assum (qspecl_then [‘0’] assume_tac) >>
    gs[]) >>
 first_x_assum irule >> simp[LENGTH_specsl] >>
 ‘(specsl 0 h' t) = t’
  by (irule LIST_EQ >> simp[LENGTH_specsl] >>
     rw[] >> drule_then assume_tac specsl_EL >>
     gs[] >> irule $ cj 2 trpl_id >>
     ‘sbounds (EL x t) = {}’
      suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
     irule $ cj 2 wft_no_bound >>
     qexists ‘Σf’ >> first_x_assum irule >>
     simp[MEM_EL] >> metis_tac[]) >>
  gs[] >> rw[] >>
  first_x_assum $ qspecl_then [‘SUC n’] assume_tac >>
  gs[]
QED   
 


Theorem is_EQ_wff_Leq_Req:
 wfsig Σ ∧ is_EQ f ∧ wff Σ f ⇒ sort_of (Leq f) = sort_of (Req f)
Proof
rw[is_EQ_def] >> Cases_on ‘Σ’ >> Cases_on ‘r’ >>
gs[wff_EQ] >> rw[Leq_Req_EQ]
QED




Theorem wff_IFF:
wff Σ (IFF f1 f2) ⇔ wff Σ f1 ∧ wff Σ f2
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >>
rw[IFF_def,CONJ_def,NEG_def,wff_IMP,wff_False,EQ_def] >>
metis_tac[]
QED   

Theorem wff_fVar':
 ∀P sl tl. wffstl (FST Σ) sl tl ⇒ wff Σ (fVar P sl tl)
Proof
 Cases_on ‘Σ’ >> Cases_on ‘r’>> simp[] >>
 metis_tac[wff_fVar]
QED 

Theorem wff_False':    
wff Σ False
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[wff_False]
QED

Theorem wff_NEG:
 wff Σ (NEG f) ⇔ wff Σ f
Proof
 gs[NEG_def,wff_IMP,wff_False']
QED

                
Theorem Pf_ffv_SUBSET_wff:
 wfsig (Σf,Σp,Σe) ∧ 
(∀ax. ax ∈ axs ⇒ wff (Σf,Σp,Σe) ax) ⇒
∀pf. Pf (Σf,Σp,Σe) axs pf ⇒
 ∀Γ A f. MEM (Γ,A,f) pf ⇒
         Uof ffv ({f} ∪ A) ⊆ Γ ∧
         wff (Σf,Σp,Σe) f ∧
         (∀a. a ∈ A ⇒ wff (Σf,Σp,Σe) a)
Proof
strip_tac >> 
Induct_on ‘Pf’ >> rw[] (* 27 *) >> TRY (metis_tac[]) (*43*)
>- rw[Uof_def,SUBSET_DEF] (*ax*)
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
   >- (gs[fVcong_def] >> simp[ffv_IFF] >>
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
    >- (irule wff_fVar' >> simp[] >>
        ‘wfabsap Σf sl (Lofeqthl (map2list (LENGTH sl − 1) eqths))’
         suffices_by cheat >>
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
   ‘wfabsap (FST (Σf,Σp,Σe)) sl
          (Rofeqthl (map2list (LENGTH sl − 1) eqths))’ suffices_by cheat >>
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
    gs[wfvmap_def] >> rw[] (* 4 *)
    >- gs[wfsig_def,wffsig_def]
    >- metis_tac[wfvmap_presname,wfvmap_def]
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
    >- metis_tac[wfvmap_presname,wfvmap_def]
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
        
Definition wfsigaxs_def:
wfsigaxs (Σf,Σp,Σe) axs ⇔
wfsig (Σf,Σp,Σe) ∧ (∀ax. ax ∈ axs ⇒ wff (Σf,Σp,Σe) ax)
End

Definition PfDrv_def:
  PfDrv Σ axs th ⇔ ∃pf. Pf Σ axs pf ∧ MEM th pf
End   
        
Theorem Pf_wff:
wfsigaxs Σ axs ⇒
     ∀pf.
       Pf Σ axs pf ⇒
       ∀Γ A f.
         MEM (Γ,A,f) pf ⇒
         wff Σ f ∧
         ∀a. a ∈ A ⇒ wff Σ a
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >>
gs[wfsigaxs_def] >> strip_tac >>
drule_then assume_tac Pf_ffv_SUBSET_wff >>
gs[Uof_Sing,Uof_UNION,Uof_SUBSET] >> metis_tac[]
QED

Theorem PfDrv_wff:
wfsigaxs Σ axs ⇒
     ∀th.
       PfDrv Σ axs th ⇒
       wff Σ (concl th) ∧
       ∀a. a ∈ (assum th) ⇒ wff Σ a
Proof         
strip_tac >>
simp[PfDrv_def,PULL_EXISTS] >>
Cases_on ‘th’ >> Cases_on ‘r’ >>
simp[concl_def,assum_def] >>
metis_tac[Pf_wff]
QED


Theorem PfDrv_ffv_SUBSET_cont:
wfsigaxs Σ axs ⇒
     ∀Γ A f.
       PfDrv Σ axs (Γ,A,f) ⇒
       Uof ffv ({f} ∪ A) ⊆ Γ
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >>
strip_tac >>
simp[PfDrv_def,PULL_EXISTS] >>
metis_tac[Pf_ffv_SUBSET_wff,wfsigaxs_def]
QED        

        



Theorem PfDrv_concl_ffv_SUBSET:
wfsigaxs Σ axs ⇒ ∀Γ A f. PfDrv Σ axs (Γ,A,f) ⇒
 ffv f ⊆ Γ
Proof 
rw[] >> drule_all_then assume_tac PfDrv_ffv_SUBSET_cont >>
gs[Uof_SUBSET,Uof_Sing,Uof_UNION]
QED


Theorem PfDrv_assum_ffv_SUBSET:
wfsigaxs Σ axs ⇒ ∀Γ A f. PfDrv Σ axs (Γ,A,f) ⇒
∀a. a ∈ A ⇒ ffv a ⊆ Γ 
Proof 
rw[] >> drule_all_then assume_tac PfDrv_ffv_SUBSET_cont >>
gs[Uof_SUBSET,Uof_Sing,Uof_UNION]
QED

        
Theorem PfDrv_assume:
  ∀Σ axs c. wff Σ c ⇒ PfDrv Σ axs (assume c)
Proof
  rw[PfDrv_def] >>
  drule_then assume_tac Pf_assume >>
  first_x_assum $ irule_at Any >> simp[]
QED


Theorem PfDrv_mp:
  PfDrv Σ axs (Γ1,A1,IMP f1 f2) ∧
  PfDrv Σ axs (Γ2,A2,f1) ⇒
  PfDrv Σ axs (Γ1 ∪ Γ2,A1 ∪ A2,f2) 
Proof
  rw[PfDrv_def] >>
  drule_all_then assume_tac Pf_mp >>
  first_x_assum $ irule_at Any >> simp[]
QED
  
          

Theorem PfDrv_undisch:
  wfsigaxs Σ axs ⇒
  PfDrv Σ axs (Γ,A,IMP f1 f2) ⇒ PfDrv Σ axs (Γ,A ∪ {f1},f2)
Proof
  rw[] >> 
  drule_all_then assume_tac PfDrv_wff >>
  gs[wff_IMP,concl_def,assum_def] >>
  rev_drule_then assume_tac PfDrv_assume >>
  first_x_assum (qspecl_then [‘axs’] assume_tac) >>
  gs[assume_def] >>
  rev_drule_then assume_tac PfDrv_mp >>
  first_x_assum $ drule_then assume_tac >> 
  ‘Γ ∪ ffv f1 = Γ’ suffices_by metis_tac[] >>
  ‘ffv f1 ⊆ Γ’ suffices_by
     (gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
  ‘ffv (IMP f1 f2) ⊆ Γ’ suffices_by gs[ffv_thm] >>
  irule PfDrv_concl_ffv_SUBSET >>
  metis_tac[]
QED  



Theorem PfDrv_add_cont1:
 PfDrv Σ axs th ⇒
  ∀n s. wfs (FST Σ) s ⇒ PfDrv Σ axs (add_cont1 (n,s) th)
Proof  
 rw[] >> gs[PfDrv_def] >>
 drule_then assume_tac $ Pf_add_cont1 >>
 rpt (first_x_assum $ irule_at Any) >> qexists ‘n’ >> simp[]
QED
         


        
Theorem PfDrv_add_cont0:          
 ∀vs. FINITE vs ⇒
      (∀n s. (n,s) ∈ vs ⇒ wfs (FST Σ) s) ∧ PfDrv Σ axs th ⇒
      PfDrv Σ axs (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) vs) th)
Proof      
 Induct_on ‘vs’ >> rw[Uof_EMPTY,add_cont_EMPTY] >>
 ‘PfDrv Σ axs (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) vs) th)’ by metis_tac[] >>
 ‘(e INSERT vs) = {e} ∪ vs’ by 
 rw[Once INSERT_SING_UNION] >>
 pop_assum SUBST_ALL_TAC >> rw[Uof_Sing,Uof_UNION] >>
 rw[add_cont_UNION] >>
 drule_then assume_tac PfDrv_add_cont1 >> 
 Cases_on ‘e’ >> gs[] >> gs[add_cont1_add_cont] >>
 first_x_assum irule >> metis_tac[]
QED

Theorem PfDrv_add_cont:
FINITE ct ∧ is_cont ct ⇒
      (∀n s. (n,s) ∈ ct ⇒ wfs (FST Σ) s) ∧ PfDrv Σ axs th ⇒
      PfDrv Σ axs (add_cont ct th)
Proof
rw[] >> drule_all_then mp_tac cont_decompose >> simp[] >>
rw[] >> 
‘PfDrv Σ axs (add_cont ( BIGUNION (IMAGE (λ(n,s). {(n,s)} ∪ sfv s) ct)) th)’ suffices_by simp[] >>
‘PfDrv Σ axs
          (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) ct) th)’
  suffices_by  gs[BIGUNION_IMAGE_Uof,PULL_EXISTS] >>  
irule PfDrv_add_cont0 >> simp[] >> metis_tac[]
QED





Theorem PfDrv_double_neg:
PfDrv Σ axs (Γ,A ∪ {NEG f},False) ⇒
PfDrv Σ axs (Γ,A,f)
Proof
rw[PfDrv_def] >>
drule_all_then assume_tac Pf_double_neg >>
first_x_assum $ irule_at Any >> simp[]
QED


Theorem PfDrv_mp:
PfDrv Σ axs (Γ1,A1,IMP ϕ ψ) ∧ PfDrv Σ axs (Γ2,A2,ϕ) ⇒
PfDrv Σ axs (Γ1 ∪ Γ2,A1 ∪ A2,ψ)
Proof
rw[PfDrv_def] >>
drule_all_then assume_tac Pf_mp >>
first_x_assum $ irule_at Any >> simp[]
QED


Theorem PfDrv_disch:
 PfDrv Σ axs (Γ,A,f) ∧ wff Σ a ⇒
 PfDrv Σ axs (disch a (Γ,A,f))
Proof
 rw[PfDrv_def] >> drule_all_then assume_tac Pf_disch >>
 first_x_assum $ irule_at Any >> simp[]
QED 
 



        
Theorem PfDrv_add_assum:
∀s th. FINITE s ⇒  wfsigaxs Σ axs ∧
    (∀ϕ. ϕ ∈ s ⇒ wff Σ ϕ) ∧
    PfDrv Σ axs th ⇒ PfDrv Σ axs (add_assum s th)
Proof
 Induct_on ‘FINITE’ >> gs[add_assum_EMPTY] >>
 rw[] >>
 ‘PfDrv Σ axs (add_assum s th)’ by metis_tac[] >>
 qpat_x_assum ‘∀th.
          wfsigaxs Σ axs ∧ (∀ϕ. ϕ ∈ s ⇒ wff Σ ϕ) ∧ PfDrv Σ axs th ⇒
          PfDrv Σ axs (add_assum s th)’ (K all_tac)>>
 Cases_on ‘th’ >> Cases_on ‘r’ >>
 gs[add_assum_def] >>
 drule_then assume_tac PfDrv_disch >>
 ‘wff Σ e’ by metis_tac[] >>
 first_x_assum $ drule_then assume_tac >>
 gs[disch_def] >>
 drule_then assume_tac PfDrv_undisch >>
 first_x_assum $ drule_then assume_tac >> 
 gs[add_assum_def,Uof_UNION,Uof_Sing,Uof_INSERT] >>
 ‘q' ∪ s DELETE e ∪ {e} = q' ∪ (e INSERT s)’
  by (gs[EXTENSION] >> metis_tac[]) >>
 ‘q ∪ (ffv e ∪ Uof ffv s) = q ∪ Uof ffv s ∪ ffv e’
  by  (gs[EXTENSION] >> metis_tac[]) >>
 gs[]
QED  

Theorem PfDrv_wff1:
wfsigaxs Σ axs ⇒
     ∀Γ A f. PfDrv Σ axs (Γ,A,f) ⇒
             wff Σ f ∧ ∀a. a ∈ A ⇒ wff Σ a
Proof
rw[] >> drule_all_then assume_tac PfDrv_wff >> gs[concl_def,assum_def]
QED
 
Theorem PfDrv_contrapos0:
wfsigaxs Σ axs ∧
PfDrv Σ axs (Γ1,A1,IMP ϕ ψ) ⇒
PfDrv Σ axs (Γ1,A1 DELETE ϕ DELETE NEG ψ,IMP (NEG ψ) (NEG ϕ))
Proof
rw[] >>
drule_then assume_tac PfDrv_undisch >>
‘wff Σ (IMP ϕ ψ)’
 by (irule $ cj 1 PfDrv_wff1 >> metis_tac[]) >>
gs[wff_IMP] >>
‘wff Σ (NEG ψ)’ by gs[wff_NEG] >>
drule_then assume_tac PfDrv_assume >>
first_x_assum $ qspecl_then [‘axs’] assume_tac >> 
gs[assume_def,NEG_def] >>
first_x_assum $ rev_drule_then assume_tac >> 
drule_all_then assume_tac PfDrv_mp >>
gs[GSYM NEG_def,UNION_ASSOC] >>
‘ffv (IMP ϕ ψ) ⊆ Γ1’ by (irule PfDrv_concl_ffv_SUBSET >> metis_tac[]) >>
gs[ffv_thm] >>
‘ffv ψ ∪ Γ1 = Γ1’
 by (gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
gs[] >>
qpat_x_assum ‘wff Σ ϕ’ assume_tac >>
drule_all_then assume_tac PfDrv_disch >>
gs[disch_def] >> gs[GSYM NEG_def] >>
qpat_x_assum ‘wff Σ (NEG ψ)’ assume_tac >>
drule_then assume_tac PfDrv_disch>>
first_x_assum $ drule_then assume_tac >>
gs[disch_def] >>
‘Γ1 ∪ ffv ϕ ∪ ffv (NEG ψ) = Γ1’
  by (gs[ffv_NEG,EXTENSION,SUBSET_DEF] >> metis_tac[]) >> gs[]>>
‘{NEG ψ} ∪ A1 ∪ {ϕ} DELETE ϕ DELETE NEG ψ = A1 DELETE ϕ DELETE NEG ψ’
 by (rw[EXTENSION] >> metis_tac[]) >>
gs[] 
QED



Theorem PfDrv_contrapos:
wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ1,A1,IMP ϕ ψ) ⇒
PfDrv Σ axs (Γ1,A1,IMP (NEG ψ) (NEG ϕ))
Proof
rw[] >>
drule_then assume_tac PfDrv_contrapos0 >>
Cases_on ‘ϕ ∈ A1’ >> Cases_on ‘NEG ψ ∈ A1’ (* 4 *)
>- (first_x_assum $ drule_then assume_tac >>
   ‘(Γ1,A1,IMP (NEG ψ) (NEG ϕ)) =
    add_assum ({ϕ} ∪ {NEG ψ}) (Γ1,A1 DELETE ϕ DELETE NEG ψ,IMP (NEG ψ) (NEG ϕ))’  by
    (rw[add_assum_def,Uof_UNION,Uof_Sing] (* 2 *)
    >- (drule_then assume_tac PfDrv_concl_ffv_SUBSET >>
    first_x_assum $ rev_drule_then assume_tac >> gs[ffv_thm,ffv_NEG] >>
    gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
    gs[EXTENSION] >> metis_tac[]) >>
    gs[] >> irule PfDrv_add_assum >>
    simp[] >> rev_drule_then assume_tac $ cj 1 PfDrv_wff1 >>
    first_x_assum $ rev_drule_then assume_tac >>
    gs[wff_IMP] >> rw[] (* 2 *) >> simp[] >>
    simp[wff_NEG])
>- (first_x_assum $ drule_then assume_tac >>
   ‘A1 DELETE ϕ DELETE NEG ψ = A1 DELETE ϕ’
     by (gs[EXTENSION] >> metis_tac[]) >> gs[] >>
   ‘(Γ1,A1,IMP (NEG ψ) (NEG ϕ)) =
    add_assum {ϕ} (Γ1,A1 DELETE ϕ,IMP (NEG ψ) (NEG ϕ))’  by
    (rw[add_assum_def,Uof_UNION,Uof_Sing] (* 2 *)
    >- (drule_then assume_tac PfDrv_concl_ffv_SUBSET >>
    first_x_assum $ rev_drule_then assume_tac >> gs[ffv_thm,ffv_NEG] >>
    gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
    gs[EXTENSION] >> metis_tac[]) >>
    gs[] >> irule PfDrv_add_assum >>
    simp[] >> rev_drule_then assume_tac $ cj 1 PfDrv_wff1 >>
    first_x_assum $ rev_drule_then assume_tac >>
    gs[wff_IMP] >> rw[] (* 2 *) >> simp[] >>
    simp[wff_NEG])
>- (first_x_assum $ drule_then assume_tac >>
    ‘A1 DELETE ϕ DELETE NEG ψ = A1 DELETE (NEG ψ)’
     by (gs[EXTENSION] >> metis_tac[]) >> gs[] >>
   ‘(Γ1,A1,IMP (NEG ψ) (NEG ϕ)) =
    add_assum {NEG ψ} (Γ1,A1 DELETE NEG ψ,IMP (NEG ψ) (NEG ϕ))’  by
    (rw[add_assum_def,Uof_UNION,Uof_Sing] (* 2 *)
    >- (drule_then assume_tac PfDrv_concl_ffv_SUBSET >>
    first_x_assum $ rev_drule_then assume_tac >> gs[ffv_thm,ffv_NEG] >>
    gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
    gs[EXTENSION] >> metis_tac[]) >>
    gs[] >> irule PfDrv_add_assum >>
    simp[] >> rev_drule_then assume_tac $ cj 1 PfDrv_wff1 >>
    first_x_assum $ rev_drule_then assume_tac >>
    gs[wff_IMP] >> rw[] (* 2 *) >> simp[] >>
    simp[wff_NEG]) >>
first_x_assum $ drule_then assume_tac >>
‘A1 DELETE ϕ DELETE NEG ψ = A1’ by (gs[EXTENSION] >> metis_tac[]) >>
gs[]
QED

Theorem fVslfv_IMP:
fVslfv (IMP f1 f2) = fVslfv f1 ∪ fVslfv f2
Proof
rw[fVslfv_def,Uof_UNION,fVars_def]
QED

Theorem fVslfv_False:
  fVslfv False = {}
Proof
rw[fVslfv_def,Uof_EMPTY,fVars_def]
QED
       
        
        
Theorem wff_FALL_EX:
wff Σ (FALL s b) ⇔ wff Σ (EX s b)
Proof
rw[EX_def,wff_NEG,NEG_def,wff_IMP,wff_False'] >>
rw[EQ_IMP_THM] (* 2 *)
>- (Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[wff_FALL] >>
   qexistsl [‘IMP f False’,‘n’] >> simp[wff_IMP,wff_False'] >>
   simp[fVslfv_IMP,fVslfv_False] >> gs[mk_FALL_def,abst_def,fabs_def] >>
   metis_tac[]) >>
Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[wff_FALL] >>
Cases_on ‘f’ >> gs[mk_FALL_def,abst_def,fabs_def] >>
Cases_on ‘f0’ >> gs[fabs_def] >>
qexistsl [‘f'’,‘n’] >> gs[fVslfv_False,fVslfv_IMP,wff_IMP] >>
metis_tac[]
QED
   



Theorem PfDrv_cont_SUBSET:
  PfDrv Σ axs (Γ0,A,f) ∧ FINITE Γ ∧ Γ0 ⊆ Γ ∧ is_cont Γ ∧
  (∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s) ⇒
  PfDrv Σ axs (Γ,A,f)
Proof
  rw[] >> drule_then assume_tac PfDrv_add_cont >> gs[] >>
  first_x_assum $ drule_all_then assume_tac >>
  gs[add_cont_def] >>
  ‘Γ ∪ Γ0 = Γ’ by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[])>>
  gs[]
QED




Theorem PfDrv_assum_SUBSET:
  wfsigaxs Σ axs ∧
  PfDrv Σ axs (Γ,A0,f) ∧ FINITE A ∧ A0 ⊆ A ∧
  (∀a. a ∈ A ⇒ wff Σ a) ⇒
  PfDrv Σ axs (Γ ∪ Uof ffv A,A,f)
Proof
  rw[] >> drule_then assume_tac PfDrv_add_assum >> gs[] >>
  first_x_assum $ drule_all_then assume_tac >>
  gs[add_assum_def] >>
  ‘A0 ∪ A = A’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[])>>
  gs[]
QED
        
   
Theorem PfDrv_gen:
PfDrv Σ axs (Γ,A,f) ∧ wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
(x,s) ∉ genavds (Γ,A,f) ⇒
PfDrv Σ axs (gen (x,s) (Γ,A,f))
Proof
rw[PfDrv_def] >>
drule_then assume_tac Pf_ALLI >>
first_x_assum $ drule_all_then assume_tac >>
first_x_assum $ irule_at Any >> simp[]
QED

Theorem ffv_EX:
ffv (EX s b) = sfv s ∪ ffv b
Proof
rw[EX_def,ffv_NEG,ffv_def]
QED

Theorem PfDrv_cont_wf':
  (∀ax. ax ∈ axs ⇒ wff (Σf,Σp,Σe) ax) ⇒
  ∀Γ A f. PfDrv (Σf,Σp,Σe) axs (Γ,A,f) ⇒
  ∀n s. (n,s) ∈ Γ ⇒ wfs Σf s
Proof
  rw[] >> irule PfDrv_cont_wf >>
  gs[PfDrv_def] >> metis_tac[]
QED  
  
Theorem fVars_NEG:
∀f.(fVars (NEG f)) = fVars f
Proof
Induct_on ‘f’ >> gs[NEG_def,fVars_def]
QED

Theorem fVars_frpl:
∀f i. fVars (frpl i v f) = fVars f
Proof
Induct_on ‘f’ >> gs[frpl_def,fVars_def]
QED


        


 
        
Theorem Uof_sfv_SUBSET_cont:
∀ct. is_cont ct ⇒ Uof (sfv ∘ SND) ct ⊆ ct
Proof
rw[Uof_SUBSET]  >> Cases_on ‘a’ >> simp[] >>
metis_tac[is_cont_def]
QED



        
Theorem PfDrv_EX_E:
  wfsigaxs Σ axs ∧ 
  PfDrv Σ axs (G1,A1,EX s b) ∧
  (a,s) ∉ ffv b ∧
  (a,s) ∉ G2 ∧ substb (Var a s) b ∉ A2 ∧
  PfDrv Σ axs (G2 ∪ {(a,s)},A2 ∪ {substb (Var a s) b},f) ∧
  (a,s) ∉ Uof (sfv ∘ SND) G2 ∧ (a,s) ∉ Uof ffv (A2 ∪ {f}) ∧
  (a,s) ∉ Uof (slfv ∘ SND) (Uof fVars (A2 ∪ {f})) ⇒
  PfDrv Σ axs (G1 ∪ G2,A1 ∪ A2,f)
Proof
  rw[] >> irule PfDrv_double_neg >> rw[GSYM UNION_ASSOC] >>
  rev_drule_then assume_tac PfDrv_concl_ffv_SUBSET >>
  first_x_assum $ rev_drule_then assume_tac >>
  gs[ffv_EX] >> 
  ‘G1 ∪ G2 = G1 ∪ (G2 ∪ sfv s)’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>gs[] >> 
  irule PfDrv_mp >>
  qexists ‘FALL s (NEG b)’ >>
  rw[] (* 2 *)
  >- (rw[GSYM NEG_def] >> gs[EX_def]) >>
  ‘wff Σ (EX s b)’
    by (irule $ cj 1 PfDrv_wff1 >> metis_tac[]) >>
  ‘wff Σ (FALL s b)’ by metis_tac[wff_FALL_EX] >>
  Cases_on ‘Σ’ >> Cases_on ‘r’ >>
  rename [‘(Σf,Σp,Σe)’] >>
  ‘wfs Σf s’ by metis_tac[wff_FALL] >>
  ‘wff (Σf,Σp,Σe) (substb (Var a s) b)’
    by (irule wff_spec >> simp[sort_of_def,wft_def] >>
       gs[wfsigaxs_def,wfsig_def,wffsig_def]) >>
   (*wff_subfm_fVar_LENGTH cheat >> *)
  drule_all_then assume_tac PfDrv_disch >>
  ‘(disch (substb (Var a s) b)
             (G2 ∪ {(a,s)},A2 ∪ {substb (Var a s) b},f)) =
  (G2 ∪ {(a,s)},A2, IMP (substb (Var a s) b) f)’
   by (rw[disch_def] (* 2 *)
      >- (‘ffv (substb (Var a s) b) ⊆ G2 ∪ {(a,s)}’
          suffices_by
          (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
          qpat_x_assum ‘PfDrv Σ axs (G2 ∪ {(a,s)},A2 ∪ {substb (Var a s) b},f)’ assume_tac >>
          drule_then assume_tac PfDrv_assum_ffv_SUBSET >>
          first_x_assum irule >> first_x_assum $ irule_at Any >>
          simp[]) >>
      gs[EXTENSION] >> metis_tac[]) >> gs[] >>
   irule PfDrv_undisch >> simp[] >>
   drule_then assume_tac PfDrv_contrapos >>
   first_x_assum  $ drule_then assume_tac >> 
   drule_then assume_tac PfDrv_undisch >>
   first_x_assum $ drule_then assume_tac >>
   ‘PfDrv (Σf,Σp,Σe) axs
          (G2 ∪ sfv s ∪ {(a,s)},A2 ∪ {NEG f},NEG (substb (Var a s) b))’
     by (‘FINITE (sfv s)’ by simp[tfv_FINITE] >>
        drule_then assume_tac PfDrv_add_cont >>
        gs[tfv_is_cont] >>
        first_x_assum $ drule_at_then Any assume_tac >>
        gs[add_cont_def]>>
        ‘sfv s ∪ (G2 ∪ {(a,s)}) = G2 ∪ sfv s ∪ {(a,s)}’
        by (rw[EXTENSION] >> metis_tac[]) >>
        gs[] >> first_x_assum irule >>
        rw[] >> irule PfDrv_cont_wf' >>
        gs[SUBSET_DEF] >>
        first_x_assum $ drule_then assume_tac >>
        rpt (first_x_assum $ irule_at Any) >>
        gs[wfsigaxs_def]) >>
   drule_then assume_tac PfDrv_gen >>
   gs[] >>
   first_x_assum $ qspecl_then [‘a’,‘s’] assume_tac >> gs[] >>
   ‘sfv s ⊆ G2 ∪ sfv s ∪ {(a,s)}’ by gs[SUBSET_DEF] >> gs[] >>
   ‘PfDrv (Σf,Σp,Σe) axs
          (gen (a,s)
             (G2 ∪ sfv s ∪ {(a,s)},A2 ∪ {NEG f},NEG (substb (Var a s) b)))’
     by (first_x_assum irule >>
        simp[genavds_def,cont_def,assum_def,concl_def] >>
        gs[Uof_UNION,Uof_Sing,ffv_NEG,fVars_NEG] >>
        simp[substb_def,fVars_frpl]  >>
        gs[GSYM fVslfv_def] >>
        ‘Uof (sfv ∘ SND) (sfv s) ⊆ sfv s’
         by metis_tac[Uof_sfv_SUBSET_cont,tfv_is_cont] >>
        ‘fVslfv b ⊆ ffv b’ by metis_tac[fVslfv_SUBSET_ffv] >>
        gs[SUBSET_DEF] >> metis_tac[tm_tree_WF]) >>
   gs[gen_def] >>
   ‘G2 ∪ sfv s ∪ {(a,s)} DELETE (a,s) = G2 ∪ sfv s’
    by (gs[EXTENSION,EQ_IMP_THM] >> metis_tac[tm_tree_WF]) >>
   gs[] >>
   ‘wff (Σf,Σp,Σe) (NEG f)’
    by (simp[wff_NEG] >> irule $ cj 1 PfDrv_wff1 >>
       metis_tac[]) >>
   drule_then assume_tac PfDrv_disch >>
   first_x_assum $ drule_then assume_tac >>
   gs[disch_def] >>
   ‘(mk_FALL a s (NEG (substb (Var a s) b))) =
    (FALL s (NEG b))’
    by (rw[mk_FALL_def,abst_def,NEG_def,fabs_def,substb_def,frpl_def] >>
       irule fabs_frpl >> simp[]) >> gs[] >>
   gs[ffv_NEG] >> 
   ‘ffv f ⊆ G2’
     by (qpat_x_assum ‘ PfDrv (Σf,Σp,Σe) axs (G2 ∪ {(a,s)},A2 ∪ {substb (Var a s) b},f)’ assume_tac >>
        drule_all_then assume_tac PfDrv_concl_ffv_SUBSET >>
        ‘(a,s) ∉ ffv f’ by gs[Uof_UNION,Uof_Sing] >>
        gs[SUBSET_DEF] >> metis_tac[]) >>
   ‘G2 ∪ sfv s ∪ ffv f = G2 ∪ sfv s’
     by (gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
   gs[] >>
   Cases_on ‘NEG f ∈ A2’ >- 
   (‘FINITE {NEG f}’ by simp[] >>
   drule_then assume_tac PfDrv_add_assum >>
   gs[] >>
   first_x_assum $ drule_all_then assume_tac >>
   gs[add_assum_def,Uof_Sing] >>
   ‘A2 ∪ {NEG f} DELETE NEG f ∪ {NEG f} = A2’
    by (gs[EXTENSION] >> metis_tac[]) >>
   gs[] >> gs[ffv_NEG]) >>
   ‘A2 ∪ {NEG f} DELETE NEG f = A2’
    by (gs[EXTENSION] >> metis_tac[]) >>
   gs[]
QED   





        
(*

Theorem tinst_no_bound:
(∀tm bmap σ.
   (∀n s. (n,s) ∈ FDOM σ ⇒
          tbounds (σ ' (n,s)) = {}) ⇒
   tbounds (tinst σ tm) = tbounds tm) ∧
(∀st bmap σ.
   (∀n s. (n,s) ∈ FDOM σ ⇒
          tbounds (σ ' (n,s)) = {}) ⇒
   sbounds (sinst σ st) = sbounds st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tinst_def,tbounds_thm,MEM_MAP] >> rw[] (* 3 *)
>- (Cases_on ‘(s0,st) ∈ FDOM σ’ >> gs[tbounds_thm] >>
   metis_tac[])
>- (‘sbounds (sinst σ st) = sbounds st’
    by metis_tac[] >> gs[] >>
   ‘{tbounds t | (∃a. t = tinst σ a ∧ MEM a l)} =
    {tbounds t | MEM t l}’ suffices_by metis_tac[]>>
   rw[Once EXTENSION,PULL_EXISTS] >>
   metis_tac[]) >>
 ‘{tbounds t | (∃a. t = tinst σ a ∧ MEM a l)} =
    {tbounds t | MEM t l}’ suffices_by metis_tac[]>>
   rw[Once EXTENSION,PULL_EXISTS] >>
   metis_tac[]
QED      
*)

        
(*Theorem tbounds_tbounds:
(∀tm bmap σ.
   (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = {}) ∧
   (∀n s. (n,s) ∈ FDOM σ ⇒
          tbounds (σ ' (n,s)) = {}) ⇒
   tbounds (tinst σ tm) = tbounds tm) ∧
(∀st bmap σ.
   (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = {}) ∧
   (∀n s. (n,s) ∈ FDOM σ ⇒
          tbounds (σ ' (n,s)) = {}) ⇒
   sbounds (sinst σ st) = sbounds st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tinst_def,tbounds_thm,MEM_MAP] >> rw[] (* 3 *)
>- (Cases_on ‘(s0,st) ∈ FDOM σ’ >> gs[tbounds_thm] >>
   metis_tac[])
>- (‘sbounds (sinst σ st) = sbounds st’
    by metis_tac[] >> gs[] >>
   ‘{tbounds t | (∃a. t = tinst σ a ∧ MEM a l)} =
    {tbounds t | MEM t l}’ suffices_by metis_tac[]>>
   rw[Once EXTENSION,PULL_EXISTS] >>
   metis_tac[]) >>
 ‘{tbounds t | (∃a. t = tinst σ a ∧ MEM a l)} =
    {tbounds t | MEM t l}’ suffices_by metis_tac[]>>
   rw[Once EXTENSION,PULL_EXISTS] >>
   metis_tac[]
QED      
*)   
              
   

        
Theorem PfDrv_thfVars_wffV:
wfsigaxs (Σf,Σp,Σe) axs ∧ PfDrv (Σf,Σp,Σe) axs th ⇒ ∀fv. fv ∈ thfVars th ⇒ wffV Σf fv
Proof
rw[] >> irule wff_wffV' >>
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[IN_thfVars] (* 2 *)
>- (drule_then assume_tac $ GEN_ALL PfDrv_concl_wff >>
   first_x_assum $ drule_then assume_tac >> metis_tac[]) >>
drule_then assume_tac $ PfDrv_assum_wff >>
metis_tac[]
QED


(*        

Theorem PfDrv_assum_FINITE:


        
Theorem PfDrv_thfVars_FINITE:
PfDrv (Σf,Σp,Σe) axs th ⇒ FINITE (thfVars th)
Proof
cheat
*)

                                        
val _ = export_theory();

