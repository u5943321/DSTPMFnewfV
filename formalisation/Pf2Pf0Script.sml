open HolKernel Parse boolLib bossLib;

val _ = new_theory "Pf2Pf0";

Definition ax2th_def:
  ax2th ax = (ffv ax,{},ax)
End  


Definition uniqify_def:
  uniqify uσ (Γ,A,f) = (Γ,IMAGE (ffVrn uσ) A, ffVrn uσ f)
End

Theorem PfDrv_uniqify:
 PfDrv Σ axs th ⇒ ∀uσ. PfDrv Σ axs (uniqify uσ th)
Proof
cheat
QED        

(*Uniqified Concrete Instance*)           
Definition UCI_def:
  UCI Σ f =
  {instf fσ vσ (ffVrn uσ f) | (fσ,vσ,uσ) |
   uniqifn uσ (fVars f) ∧
   IMAGE
   (λ(P,sl). (P, MAP (sinst vσ) sl)) (fVars f) ⊆ FDOM fσ ∧
   wfvmap (FST Σ) vσ ∧
   wfcfVmap Σ fσ ∧
   ffv f ⊆ FDOM vσ}
End    


      
Definition UCIth_def:
  UCIth Σ th =
  {insth fσ vσ (uniqify uσ th) | (fσ,vσ,uσ) |
   uniqifn uσ (thfVars th) ∧
   IMAGE
   (λ(P,sl). (P, MAP (sinst vσ) sl)) (thfVars th) ⊆ FDOM fσ ∧
   wfvmap (FST Σ) vσ ∧
   wfcfVmap Σ fσ ∧
   cont th ⊆ FDOM vσ}
End            


Theorem main:
 ∀pf. Pf Σ axs pf ⇒
      Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ⇒
      ∀th. MEM th pf ⇒
 ∀vσ fσ uσ. wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
           thfVars (vinsth vσ th) ⊆ FDOM fσ ∧
           cont th ⊆ FDOM vσ ∧ uniqifn uσ (thfVars th) ⇒
           Pf0Drv Σ aths (insth fσ vσ (uniqify uσ th))
Proof         
Induct_on ‘Pf’ >> rw[] >> TRY (metis_tac[]) (* 15 *)
>- rw[Pf0Drv_def] >> irule_at Any Pf0_AX >>
   gs[Uof_SUBSET,PULL_EXISTS] >>
   first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >>
   first_x_assum irule >> gs[UCIth_def] >>
   gs[ax2th_def] >> first_x_assum $ irule_at Any >>
   irule_at Any EQ_REFL >>
   gs[] >> simp[SUBSET_DEF] >>
   simp[PULL_EXISTS,thfVars_def,Uof_Sing] >>
   rw[] >> first_x_assum irule >>
   simp[thfVars_def,vinsth_def,Uof_Sing] >>
   rw[fVars_finst,vinst_fVar_def] >>
   Cases_on ‘x'’ >> first_x_assum $ irule_at Any >>
   qspecl_then [‘vσ’,‘q’,‘r’] assume_tac vinst_fVar_def >>
   pop_assum SUBST_ALL_TAC
   simp[vinst_fVar_def] >> cheat
>- cheat (* hyp *)
>- (qabbrev_tac ‘eqthl = (map2list (LENGTH sl − 1) eqths)’ >>
   ‘insth fσ vσ (uniqify uσ (fVcong eqthl P sl)) =
    fcong eqthl (MAP (sinst vσ) sl)
    (fσ ' (uσ ' (P,sl),MAP (sinst vσ) sl))’
    by cheat >>
   gs[] >> cheat)
>- gs[] >> cheat
   first_x_assum $ drule_then assume_tac >>
   simp[insth_def] >>
   ‘∃ufσ. uniqify uσ (fVinsth fσ th) =
          fVinsth ufσ th’ by cheat >>
    gs[] >> rw[insth_def] >>
   
   ‘vinsth vσ (fVinsth ufσ th) =
    insth (vinst_fVmap vσ ufσ) vσ th’ by cheat >>
   gs[]>> simp[insth_def] >>
   ‘’
     (* instf_fVinst fVar_prpl_o_fVmap *)
>- cheat
>- cheat


Theorem main:
 ∀pf. Pf Σ axs pf ⇒
      ∀th. MEM th pf ⇒
           Uof (cinststh Σ) (IMAGE ax2th axs) ⊆ aths ⇒
 ∀vσ fσ. wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
           thfVars (vinsth vσ th) ⊆ FDOM fσ ∧
           cont th ⊆ FDOM vσ ⇒
           ∃pf0. Pf0 Σ aths pf0 ∧ MEM (insth fσ vσ th) pf0
Proof           
Induct_on ‘Pf’ >> rw[] (* 27 *) >> TRY (metis_tac[]) (* 15 *)
>- (rw[] >>
   gs[Uof_SUBSET,PULL_EXISTS] >>
   first_x_assum $ drule_then assume_tac >>
   gs[cinststh_def] >>
   pop_assum mp_tac >>
   simp[SUBSET_DEF,PULL_EXISTS] >>
   rw[] >>
   first_x_assum
   (qspecl_then [‘fσ’,‘vσ’] assume_tac) >>
   ‘insth fσ vσ (ax2th ax) ∈ aths’
     by (first_x_assum irule >>
        gs[wfcfVmap_def] >>
        gs[SUBSET_DEF,ax2th_def] >>
        gs[vinsth_def,thfVars_def,Uof_Sing,
           fVars_finst,PULL_EXISTS] >>
        rw[] >>
        Cases_on ‘x'’ >>
        first_x_assum $ drule_then assume_tac >>
        gs[vinst_fVar_def]) >>
   drule_then assume_tac Pf0_AX >>
   first_x_assum $ irule_at Any >> simp[ax2th_def])
>- (gs[MEM_FLAT,PULL_EXISTS] >>
   gs[MEM_map2list] >>
   ‘sl ≠ []’
     by metis_tac[wfabsap_Lofeqthl_sl_NONNIL] >>
   ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then strip_assume_tac >>
   first_x_assum irule >> simp[])
>- (qabbrev_tac ‘Lts = (Lofeqthl (map2list (LENGTH sl − 1) eqths))’ >>
   qabbrev_tac ‘Rts = (Rofeqthl (map2list (LENGTH sl − 1) eqths))’ >>
   ‘vinst_fVar vσ (P,sl) ∈ FDOM fσ’ by cheat >>
   (*by asm 5*)
   ‘instf fσ vσ (IFF (fVar P sl Lts) (fVar P sl Rts))   = IFF (fprpl (mk_bmap (REVERSE Lts))
          (fσ ' (vinst_fVar vσ (P,sl))))
         (fprpl (mk_bmap (REVERSE Rts))
          (fσ ' (vinst_fVar vσ (P,sl))))
         ’ by cheat >>
    simp[] >>
    ‘is_cfm (fσ ' (vinst_fVar vσ (P,sl)))’
     by (gs[wfcfVmap_def,cfVmap_def] >>
        gs[vinst_fVar_def]) >>
    drule_at_then Any assume_tac Pf0_cong >>
    ‘wff Σ (FALLL (MAP (sinst vσ) sl) (fσ ' (vinst_fVar vσ (P,sl))))’
     by (gs[wfcfVmap_def,cfVmap_def] >>
        gs[vinst_fVar_def,wffVmap_def]) >>
    first_x_assum $ drule_at_then Any assume_tac >>
    (* choice *) cheat)
>-     
         
    ‘’
    Pf0_cong fcong_def
   

           rw[fVcong_def,insth_instf]
   
   
        
   drule_then assume_tac Pf0_AX >>
   rw[insth_instf] >>
   
    


cheat metis_tac[]
>- rw[] >>
   rw[insth_def,fVins]
   double_neg Pf_vinsth
       

val _ = export_theory();

