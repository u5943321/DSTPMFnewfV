open HolKernel Parse boolLib bossLib;

val _ = new_theory "main";


Theorem main:
 wfsigaxs Σ axs ⇒
 ∀pf. Pf Σ axs pf ⇒
      Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ⇒
      ∀th. MEM th pf ⇒
 ∀vσ fσ uσ. wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
           thfVars (vinsth vσ (uniqify uσ th)) ⊆ FDOM fσ ∧
           cont th ⊆ FDOM vσ ∧ uniqifn uσ (thfVars th) ∧
           ofFMAP ffv fσ (thfVars th) ⊆ vinst_cont vσ (cont th) ⇒
           Pf0Drv Σ aths (insth fσ vσ (uniqify uσ th))
Proof
strip_tac >>
Induct_on ‘Pf’ >> rw[] >> TRY (metis_tac[]) (* 16 *)
>~ [‘MEM (Γ1,A1,IMP f1 f2) pf’]
>- gs[cont_def]

          
>~ [‘(insth fσ' vσ (uniqify uσ (fVinsth fσ th)))’] (* M-h M-p *)
>- metis_tac[main_fVinst_case]
>~ [‘uniqifn uσ (thfVars (vinsth vσ th))’]
>- metis_tac[main_vinsth_case]
>~ [‘MEM (Γ,A ∪ {NEG f},False) pf’]
>- (gs[] >>
first_x_assum $ drule_then assume_tac >>
first_x_assum $ qspecl_then [‘vσ’,‘fσ’,‘uσ’]
assume_tac >>
‘Pf0Drv Σ aths (insth fσ vσ (uniqify uσ (Γ,A ∪ {NEG f},False)))’ suffices_by
 metis_tac[main_double_neg_lemma] >>
 first_x_assum irule >>
 gs[cont_def] >>
 ‘thfVars (Γ,A ∪ {NEG f},False) = thfVars (Γ,A,f)’
   by (simp[thfVars_def,Uof_UNION,Uof_Sing,fVars_NEG,
        fVars_def] >> metis_tac[UNION_COMM]) >>
  gs[]  >>
 ‘thfVars (vinsth vσ (uniqify uσ (Γ,A ∪ {NEG f},False))) = thfVars (vinsth vσ (uniqify uσ (Γ,A,f)))’
  by (simp[uniqify_def,vinsth_def,thfVars_def,
          Uof_UNION,Uof_Sing,
          fVars_NEG,finst_NEG,ffVrn_NEG] >>
     simp[ffVrn_def,finst_def,fVars_def]>>
     metis_tac[UNION_COMM]) >> gs[])
>~ [‘cont (assume c) ⊆ FDOM vσ’]
>- (simp[assume_def,uniqify_def,insth_def,
        fVinsth_def,vinsth_def] >> 
   irule Pf0Drv_cont_SUBSET_cong >>
   rpt (irule_at Any EQ_REFL) >>
   qexists
   ‘ffv (fVinst fσ (finst vσ (ffVrn uσ c)))’ >>
   rw[] (* 7 *)
   >- (irule vinst_cont_wf >>
      gs[wfvmap_def] >> first_assum $ irule_at Any>>
      simp[] >> rw[] >> irule wff_wfs >>
      Cases_on ‘Σ’ >> Cases_on ‘r’ >>
      gs[] >> metis_tac[])
   >- (irule wffVmap_ofFMAP_var_wf >>
      Cases_on ‘Σ’ >> Cases_on ‘r’ >>
      gs[] >> metis_tac[wfcfVmap_def])
   >- (simp[vinst_cont_def] >>
      irule ofFMAP_FINITE >>
      simp[tfv_FINITE,ffv_FINITE])
   >- (irule ofFMAP_FINITE >>
      simp[tfv_FINITE,ffv_FINITE,
      Uof_Sing,fVars_FINITE])
   >- (irule UNION_is_cont >> rw[] (* 2 *)
      >- irule vinst_cont_is_cont >>
      simp[ofFMAP_ffv_is_cont])
   >- (irule SUBSET_TRANS >>
      qexists ‘ffv (finst vσ (ffVrn uσ c)) ∪
      ffv (fVinst fσ (finst vσ (ffVrn uσ c)))’ >>
      strip_tac >- gs[SUBSET_DEF] >>
      qspecl_then [‘(finst vσ (ffVrn uσ c))’,
      ‘fσ’] assume_tac ffv_fVinst >>
      ‘ffv (finst vσ (ffVrn uσ c)) ∪ ffv (fVinst fσ (finst vσ (ffVrn uσ c))) =
        ffv (finst vσ (ffVrn uσ c)) ∪
        ofFMAP ffv fσ (FDOM fσ ∩ fVars (finst vσ (ffVrn uσ c)))’
        by (first_x_assum irule >>
           cheat) >>
      pop_assum SUBST_ALL_TAC >>
      REWRITE_TAC[ffv_finst_ffVrn] >>
      simp[Uof_Sing] >> rw[] (* 2 *)
      >- (simp[GSYM ofFMAP_tfv_vinst_cont] >>
         ‘ffv (finst vσ c) = ofFMAP tfv vσ (ffv c)’
          suffices_by rw[] >>
         irule ffv_finst_alt >>
         gs[cont_def,assume_def,wfvmap_def,
            wfcod_no_bound] >>
         metis_tac[wfcod_no_bound]) >>
      ‘ofFMAP ffv fσ (FDOM fσ ∩ fVars (finst vσ (ffVrn uσ c))) ⊆  ofFMAP ffv fσ (fVars (finst vσ (ffVrn uσ c)))’ by (irule ofFMAP_SUBSET_MONO >> simp[]) >>
      gs[SUBSET_DEF]) >>
   gs[GSYM assume_def] >>
   irule Pf0Drv_assume >> rw[] (* 2 *)
   >- (irule fVinst_cfVmap_is_cfm >>
      gs[wfcfVmap_def] >>
      gs[thfVars_vinsth,thfVars_uniqify] >>
      gs[thfVars_assume] >>
      simp[fVars_finst,fVars_ffVrn]) >>
   cheat)



val _ = export_theory();

