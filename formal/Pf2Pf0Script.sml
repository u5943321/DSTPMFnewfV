open HolKernel Parse boolLib bossLib;

val _ = new_theory "Pf2Pf0";

Definition ax2th_def:
  ax2th ax = (ffv ax,{},ax)
End  


Definition uniqify_def:
  uniqify uσ (Γ,A,f) = (Γ,IMAGE (ffVrn uσ) A, ffVrn uσ f)
End



Theorem ffv_plainfV:
ffv (plainfV (P,sl)) = slfv sl
Proof
simp[plainfV_def,ffv_thm] >>
‘BIGUNION {tfv t | MEM t (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))} = {}’
 by (simp[MEM_MAP] >> Cases_on ‘sl’ >>
 gs[rich_listTheory.COUNT_LIST_def] >>
 disj2_tac >>
 simp[MEM_MAP,Once EXTENSION,PULL_EXISTS,
     rich_listTheory.MEM_COUNT_LIST] >>
 rw[EQ_IMP_THM] >>
 qexists ‘0’ >> simp[]) >> simp[slfv_alt]
QED
 

Theorem slfv_fVslfv:
∀P sl s. (P,sl) ∈ fVars f ⇒ slfv sl ⊆ fVslfv f
Proof
simp[slfv_def,Uof_SUBSET] >>
metis_tac[MEM_fVsl_SUBSET_fVslfv]
QED

        
Theorem uniqify_fVinst:
wfsigaxs Σ axs ∧ PfDrv Σ axs th ⇒ uniqify uσ th = fVinsth (rn2fVmap uσ) th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
simp[uniqify_def,fVinsth_def] >> reverse (rw[]) (* 3 *)
>- (irule ffVrn_fVinst >>
   rw[] >>
   irule wff_subfm_fVar_LENGTH >>
   drule_all_then assume_tac PfDrv_concl_wff >>
   metis_tac[])
>- (irule IMAGE_eq_lemma >> rw[] >>
   irule ffVrn_fVinst >>
   rw[] >>
   irule wff_subfm_fVar_LENGTH >>
   drule_all_then assume_tac PfDrv_assum_wff >>
   metis_tac[]) >>
‘ofFMAP ffv (rn2fVmap uσ) (Uof fVars ({r'} ∪ q')) ⊆ q’
suffices_by (gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
gs[ofFMAP_SUBSET,Uof_UNION,Uof_Sing,FDOM_rn2fVmap,IN_Uof,PULL_EXISTS] >> rw[] (* 2 *)
>- (drule_then assume_tac FAPPLY_rn2fVmap >>
   simp[] >> Cases_on ‘a’ >> gs[fVrn_def] >>
   simp[ffv_plainfV] >>
   irule SUBSET_TRANS >>
   qexists ‘fVslfv a'’ >> rw[] (* 2 *)
   >- (irule slfv_fVslfv >> metis_tac[]) >>
   irule SUBSET_TRANS >> qexists ‘ffv a'’ >>
   simp[fVslfv_SUBSET_ffv] >>
   drule_then assume_tac PfDrv_concl_ffv_SUBSET >>
   metis_tac[]) >>
drule_then assume_tac FAPPLY_rn2fVmap >>
simp[] >> Cases_on ‘a’ >> gs[fVrn_def] >>
simp[ffv_plainfV] >>
irule SUBSET_TRANS >>
qexists ‘fVslfv a'’ >> rw[] (* 2 *)
>- (irule slfv_fVslfv >> metis_tac[]) >>
irule SUBSET_TRANS >> qexists ‘ffv a'’ >>
simp[fVslfv_SUBSET_ffv] >>
drule_then assume_tac PfDrv_assum_ffv_SUBSET >>
metis_tac[]
QED
   


Theorem PfDrv_uniqify:
 wfsigaxs Σ axs ∧ PfDrv Σ axs th ⇒
 ∀uσ. PfDrv Σ axs (uniqify uσ th)
Proof
 rw[] >>
 drule_all_then assume_tac uniqify_fVinst >> simp[] >>
 irule PfDrv_fVinsth >> simp[FDOM_rn2fVmap] >>
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

Theorem insth_uniqify_fVinsth:
insth σ vσ (uniqify uσ (fVinsth fσ (Γ,A,f))) =
(vinst_cont vσ
 (Γ ∪
  (ofFMAP ffv fσ (fVars f) ∪ ofFMAP ffv fσ (Uof fVars A))) ∪
 (ofFMAP ffv σ
  (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f)))) ∪
  ofFMAP ffv σ
  (Uof (IMAGE (vinst_fVar vσ) ∘ fVars) (IMAGE (ffVrn uσ ∘ fVinst fσ) A))),
 IMAGE ((fVinst σ) o (finst vσ) o  (ffVrn uσ) o  (fVinst fσ)) A,
 fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))))
Proof         
gs[fVinsth_def,uniqify_def,insth_instf,Uof_UNION,Uof_Sing,instf_def,ofFMAP_UNION,IMAGE_IMAGE] >>
‘(instf σ vσ ∘ ffVrn uσ ∘ fVinst fσ) =
 (fVinst σ ∘ finst vσ ∘ ffVrn uσ ∘ fVinst fσ)’
 suffices_by metis_tac[] >>
rw[FUN_EQ_THM,instf_def]
QED



Theorem ofFMAP_Uof:
ofFMAP f σ s = Uof f (IMAGE ($' σ) (FDOM σ ∩ s))
Proof
rw[ofFMAP_def,Uof_def,Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] 
QED

Theorem Uof_fVars_finst_ffVrn:
(Uof (fVars ∘ finst vσ ∘ ffVrn uσf) A) =
Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) o fVars) A
Proof
 rw[Once EXTENSION,IN_Uof,PULL_EXISTS,fVars_finst,fVars_ffVrn]
QED     
        


Theorem fVinst_o_Vmap_finst_ffVrn:
insth (o_fVmap σ
               (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
      vσ
      (uniqify uσf (Γ,A,f)) =
(vinst_cont vσ Γ ∪
   (ofFMAP ffv
      (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
      (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) ∪
    ofFMAP ffv
      (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
      (Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) o fVars) A)),
IMAGE
 ((instf (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
       vσ) o (ffVrn uσf)) A
,
fVinst (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
       (finst vσ (ffVrn uσf f))
)
Proof
rw[insth_def,fVinsth_def,uniqify_def,vinsth_def,
   IMAGE_IMAGE,Uof_Sing,Uof_UNION,fVars_finst,Uof_IMAGE,ofFMAP_UNION,
   fVars_ffVrn,Uof_fVars_finst_ffVrn] >>
rw[instf_fVinst_finst]
QED
        
(*        
Theorem fVinst_o_Vmap_finst_ffVrn:
insth (o_fVmap σ
               (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
      vσ
      (uniqify uσf (Γ,A,f)) =
(vinst_cont vσ Γ ∪
   (ofFMAP ffv
      (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
      (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) ∪
    ofFMAP ffv
      (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
      (Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) o fVars) A)),
IMAGE
 ((instf (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
       vσ) o (ffVrn uσf)) A
,
fVinst (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
       (finst vσ (ffVrn uσf f))
)
Proof
rw[insth_def,fVinsth_def,uniqify_def,vinsth_def,
   IMAGE_IMAGE,Uof_Sing,Uof_UNION,fVars_finst,Uof_IMAGE,ofFMAP_UNION,
   fVars_ffVrn,Uof_fVars_finst_ffVrn] >>
rw[instf_fVinst_finst]
QED
*)


        
Theorem vinst_cont_UNION:
vinst_cont vσ (A ∪ B) = vinst_cont vσ A ∪ vinst_cont vσ B
Proof
rw[vinst_cont_def,ofFMAP_UNION]
QED         


Theorem ofFMAP_ffv_o_fVmap:
ofFMAP ffv (o_fVmap σ2 σ1) s ⊆
Uof ffv (IMAGE ((fVinst σ2) o ($' σ1)) (s ∩ FDOM σ1)) ∪
Uof ffv (IMAGE (($' σ2)) (s ∩ (FDOM σ2 DIFF FDOM σ1)))
Proof
simp[ofFMAP_Uof,FDOM_o_fVmap,SUBSET_DEF,IN_Uof,PULL_EXISTS] >>
rw[] (* 2 *)
>- (Cases_on ‘x'’ >> drule_then assume_tac FAPPLY_o_fVmap1 >>
   gs[] >> disj1_tac >> metis_tac[]) >>   
Cases_on ‘x' ∈ FDOM σ1’ >> Cases_on ‘x'’ (* 2 *)
>- (drule_then assume_tac FAPPLY_o_fVmap1 >> metis_tac[]) >>
drule_all_then assume_tac FAPPLY_o_fVmap2 >> metis_tac[]
QED

(*
Theorem  FAPPLY_vinst_fVmap1:
 ∀fv fσ vσ.fv ∈ FDOM fσ ∧ alluniq (FDOM fσ) ⇒
       vinst_fVmap vσ fσ ' (vinst_fVar vσ fv) = finst vσ (fσ ' fv)
Proof
Cases_on ‘fv’ >> metis_tac[FAPPLY_vinst_fVmap]
QED       

Theorem FAPPLY_fVmap_fVrn1:
∀uσ σ. uniqifn uσ (FDOM σ) ⇒
     ∀fv. fv ∈ FDOM σ ⇒ fVmap_fVrn σ uσ ' (fVrn uσ fv) = σ ' fv
Proof     
rw[] >> Cases_on ‘fv’ >> rw[fVrn_def] (*2 *)
>- (irule FAPPLY_fVmap_fVrn >> simp[]) >>
gs[uniqifn_def,SUBSET_DEF] >> metis_tac[]
QED
               
Theorem FAPPLY_vinst_fVmap_fVmap_fVrn:
(P,sl) ∈ FDOM σ ∧ (P,sl) ∈ FDOM uσf ∧ uniqifn uσf (FDOM σ)  ⇒ 
vinst_fVmap vσ (fVmap_fVrn σ uσf) ' (vinst_fVar vσ (fVrn uσf (P,sl))) =
finst vσ (σ ' (P,sl))
Proof
rw[] >> 
qspecl_then [‘(fVrn uσf (P,sl))’,‘(fVmap_fVrn σ uσf)’,‘vσ’] assume_tac
FAPPLY_vinst_fVmap1 >>
gs[FDOM_fVmap_fVrn] >> drule_then assume_tac uniqifn_alluniq0 >>
gs[] >>
AP_TERM_TAC >> irule FAPPLY_fVmap_fVrn1 >> simp[]
QED

Theorem FAPPLY_vinst_fVmap_fVmap_fVrn1:
∀uσf vσ σ.fv ∈ FDOM σ ∧ fv ∈ FDOM uσf ∧ uniqifn uσf (FDOM σ)  ⇒ 
vinst_fVmap vσ (fVmap_fVrn σ uσf) ' (vinst_fVar vσ (fVrn uσf fv)) =
finst vσ (σ ' fv)
Proof
Cases_on ‘fv’ >> metis_tac[FAPPLY_vinst_fVmap_fVmap_fVrn]
QED
*)
        

(*need uniqifn uσf (FDOM fσ ∪ FDOM uσ), x' ∈ FDOM uσf (fσ ⊆ uσf)*)


Theorem vinst_fVar_fVrn_eq_eq:
uniqifn uσf s ∧ x1 ∈ s ∧ x2 ∈ s ⇒
∀vσ. vinst_fVar vσ (fVrn uσf x1) = vinst_fVar vσ (fVrn uσf x2) ⇒ x1 = x2
Proof
rw[uniqifn_def] >> Cases_on ‘x1’ >> Cases_on ‘x2’ >>
gs[fVrn_def,vinst_fVar_def] >> gs[SUBSET_DEF] >>
gs[fVrn_def,vinst_fVar_def] >> metis_tac[]
QED

Theorem ffv_finst_ffVrn:
ffv (finst σ (ffVrn uσ f)) = ffv (finst σ f)
Proof
Induct_on ‘f’ >> gs[ffVrn_def,finst_def,ffv_thm] >> rw[]
QED
       

Theorem ofFMAP_fVars_SUBSET_fVars_fVinst:
∀f. ofFMAP fVars σ (fVars f) ⊆ fVars (fVinst σ f)
Proof
Induct_on ‘f’ >> gs[fVars_def,fVinst_def,ofFMAP_EMPTY,ofFMAP_UNION] (* 2 *)
>- (gs[SUBSET_DEF] >> metis_tac[]) >>
rw[fVars_fprpl,ofFMAP_Sing] >> rw[SUBSET_DEF,ofFMAP_Sing_EMPTY]
QED 




Theorem fVinst_subset_lemma0:
wffVmap Σ fσ ∧  wffVmap Σ σ ∧ wfvmap (FST Σ) vσ ∧
(∀fv. fv ∈ fVars f ⇒ ffv (fσ ' fv) ⊆ FDOM vσ) ∧
 uniqifn uσf (FDOM fσ) ∧ fVars f ⊆ FDOM fσ ⇒
Uof ffv
          (IMAGE
             (fVinst σ ∘
              $' (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
             (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f))) ⊆
        vinst_cont vσ (ffv f) ∪ vinst_cont vσ (ofFMAP ffv fσ (fVars f)) ∪
        ofFMAP ffv σ (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f))))
Proof
simp[Uof_SUBSET,PULL_EXISTS] >> rw[] >>
gs[] >> Cases_on ‘x'’ >> rename [‘(P,sl)’] >>
‘(P,sl) ∈ FDOM (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))’
 by (simp[FDOM_o_fVmap,DRESTRICT_DEF] >> gs[SUBSET_DEF]) >>
drule_then assume_tac FAPPLY_vinst_fVmap_fVmap_fVrn >>
first_x_assum $ qspecl_then [‘vσ’,‘uσf’] assume_tac >>
gs[FDOM_DRESTRICT,FDOM_o_fVmap,FDOM_rn2fVmap,
   INTER_UNION]>> 
‘(P,sl) ∈ FDOM uσf’ by (gs[SUBSET_DEF,uniqifn_def]) >>
gs[] >>
simp[SUBSET_DEF] >> rw[] >>
Cases_on ‘x’ >> rename[‘(n,s) ∈ ffv _’] >> gs[] >>
‘(P,sl) ∈ FDOM fσ’ by gs[SUBSET_DEF] >>
drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >> 
‘(fVinst (rn2fVmap uσ) (fσ ' (P,sl))) = ffVrn uσ (fσ ' (P,sl))’
     by (irule $ GSYM ffVrn_fVinst >>
        rev_drule_then assume_tac $ iffLR wffVmap_def >>
        rw[] >>
        irule $ GSYM wff_subfm_fVar_LENGTH >>
        first_x_assum $ drule_then assume_tac >>
        first_x_assum $ irule_at Any >>
        qexists ‘P'’ >> irule fVar_FALLL_inc >> simp[]) >>
Cases_on ‘(n,s) ∈ ffv (finst vσ (ffVrn uσ (fσ ' (P,sl))))’     
(* 2 *)
>- (gs[ffv_finst_ffVrn] >> disj1_tac >> disj2_tac >>
   simp[vinst_cont_def,ofFMAP_def,PULL_EXISTS] >>
   qspecl_then [‘(fσ ' (P,sl))’,‘vσ’] assume_tac ffv_finst >>
   ‘cstt vσ ∧ ffv (fσ ' (P,sl)) ⊆ FDOM vσ ∧ no_bound vσ’
     by (gs[wfvmap_def] >> metis_tac[wfcod_no_bound]) >>
   gs[]>> qexistsl [‘(n0,st0)’,‘(P,sl)’] >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
‘(DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ) ' (P,sl)) =
 (o_fVmap (rn2fVmap uσ) fσ) ' (P,sl)’
 by simp[DRESTRICT_DEF,FDOM_o_fVmap] >> gs[] >>
qspecl_then [‘(finst vσ (ffVrn uσ (fσ ' (P,sl))))’,‘σ’]
            assume_tac ffv_fVinst >>
‘(∀P' sl' n s.
           (P',sl') ∈
           FDOM σ ⇒
           (n,s) ∈ ffv (σ ' (P',sl')) ⇒
           sbounds s = ∅)’
 by metis_tac[wffVmap_no_vbound] >>
gs[] >>           
‘ffv (finst vσ (ffVrn uσ (fσ ' (P,sl)))) ∪
        ffv (fVinst σ (finst vσ (ffVrn uσ (fσ ' (P,sl))))) =
        ffv (finst vσ (ffVrn uσ (fσ ' (P,sl)))) ∪
        ofFMAP ffv σ (FDOM σ ∩ fVars (finst vσ (ffVrn uσ (fσ ' (P,sl)))))’
 by metis_tac[] >> 
‘(n,s) ∈
ofFMAP ffv σ (FDOM σ ∩ fVars (finst vσ (ffVrn uσ (fσ ' (P,sl)))))’         
 by (gs[Once EXTENSION] >> gs[EXTENSION] >> metis_tac[]) >>
disj2_tac >> gs[fVars_finst] >>
‘(FDOM σ ∩ IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fσ ' (P,sl))))) ⊆
(IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f))))’
 suffices_by
   (rw[] >>
   qspecl_then [‘σ’,‘ffv’] (drule_then assume_tac) (Q.GENL [‘σ’,‘f’] ofFMAP_SUBSET_MONO) >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
  simp[SUBSET_DEF,PULL_EXISTS,ffVrn_fVinst,fVars_ffVrn] >> rw[] >>
  qexists ‘x''’ >> simp[] >>
qspecl_then [‘fσ’,‘f’] assume_tac
(Q.GEN ‘σ’ ofFMAP_fVars_SUBSET_fVars_fVinst) >>
gs[SUBSET_DEF] >> first_x_assum irule >>
simp[ofFMAP_def,PULL_EXISTS] >> qexists ‘(P,sl)’ >> simp[]
QED

    
Theorem ofFMAP_IMAGE:
ofFMAP f σ (IMAGE g s) = Uof (f ∘ $' σ) (FDOM σ ∩ IMAGE g s)
Proof
simp[ofFMAP_Uof,Uof_IMAGE]
QED


Theorem fVinst_subset_lemma:
PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ∧
wffVmap Σ fσ ∧ wffVmap Σ σ ∧ wfvmap (FST Σ) vσ ∧
        (∀fv. fv ∈ Uof fVars ({f} ∪ A) ⇒ ffv (fσ ' fv) ⊆ FDOM vσ) ∧
        uniqifn uσf (FDOM fσ) ∧ Uof fVars ({f} ∪ A) ⊆ FDOM fσ
        ⇒
vinst_cont vσ Γ ∪
   (ofFMAP ffv
      (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
      (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) ∪
    ofFMAP ffv
      (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
      (Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) o fVars) A)) ⊆    
vinst_cont vσ
 (Γ ∪
  (ofFMAP ffv fσ (fVars f) ∪ ofFMAP ffv fσ (Uof fVars A))) ∪
 (ofFMAP ffv σ
  (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f)))) ∪
  ofFMAP ffv σ
  (Uof (IMAGE (vinst_fVar vσ) ∘ fVars) (IMAGE (ffVrn uσ ∘ fVinst fσ) A)))
Proof
simp[vinst_cont_UNION,SUBSET_UNION] >> rw[] (* 3 *)
>- (gs[SUBSET_DEF] >> metis_tac[])
>- (gs[Uof_UNION,Uof_Sing] >>
    gs[Uof_SUBSET] >>
   ‘ofFMAP ffv
          (o_fVmap σ
             (vinst_fVmap vσ
                (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))
                   uσf))) (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f))  ⊆
   vinst_cont vσ (ffv f) ∪   
   vinst_cont vσ (ofFMAP ffv fσ (fVars f)) ∪
   ofFMAP ffv σ (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f))))’
   suffices_by
    (rw[] >> irule SUBSET_TRANS >>
    first_x_assum $ irule_at Any >>
    rw[] (* 3 *)
    >- (‘vinst_cont vσ (ffv f) ⊆ vinst_cont vσ Γ’
       suffices_by gs[SUBSET_DEF] >>
       simp[vinst_cont_def] >>
       irule ofFMAP_SUBSET_MONO >>
       drule_all_then assume_tac
       PfDrv_ffv_SUBSET_cont >>
       gs[Uof_Sing,Uof_SUBSET,Uof_UNION])
   >> gs[SUBSET_DEF]) >>
   irule SUBSET_TRANS >>
   assume_tac fVinst_subset_lemma0 >> gs[] >>
   qexists
   ‘Uof ffv
          (IMAGE
             (fVinst σ ∘
              $'
                (vinst_fVmap vσ
                   (fVmap_fVrn
                      (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
             (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)))’ >>
   simp[ofFMAP_Uof] >>
   simp[FDOM_vinst_fVmap,FDOM_fVmap_fVrn,FDOM_o_fVmap,
           FDOM_rn2fVmap,UNION_OVER_INTER,Uof_UNION,IMAGE_IMAGE,FDOM_DRESTRICT] >>
   ‘((IMAGE (vinst_fVar vσ ∘ fVrn uσf) ((FDOM fσ ∪ FDOM uσ) ∩ FDOM fσ) ∪
            FDOM σ) ∩ IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) =
    IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)’
    by (simp[INTER_UNION,INTER_SUBSET_EQN] >>
       ‘IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f) ⊆
        IMAGE (vinst_fVar vσ ∘ fVrn uσf) (FDOM fσ)’
        suffices_by (gs[SUBSET_DEF] >>
                    metis_tac[]) >>
        irule IMAGE_SUBSET >> simp[] >>
        gs[Uof_UNION,Uof_Sing,Uof_SUBSET]) >> 
    simp[Uof_IMAGE] >>
    simp[GSYM Uof_IMAGE] >>
    irule Uof_SUBSET_MONO >>
    ‘IMAGE
          ($'
             (o_fVmap σ
                (vinst_fVmap vσ
                   (fVmap_fVrn
                      (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf))) ∘
           vinst_fVar vσ ∘ fVrn uσf) (fVars f) =
        IMAGE
          (fVinst σ ∘
           $'
             (vinst_fVmap vσ
                (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))
                   uσf)) ∘ vinst_fVar vσ ∘ fVrn uσf) (fVars f)’ suffices_by
                   metis_tac[SET_EQ_SUBSET] >>
    irule IMAGE_eq_lemma >>
    rw[] >>
    Cases_on ‘(vinst_fVar vσ (fVrn uσf a))’ >>
    irule FAPPLY_o_fVmap1 >>
    simp[FDOM_vinst_fVmap,FDOM_fVmap_fVrn,
         FDOM_DRESTRICT,FDOM_o_fVmap,FDOM_rn2fVmap]>>
    simp[PULL_EXISTS] >>
    qexists ‘a’ >> simp[] >> gs[SUBSET_DEF]) >>
gs[Uof_UNION,Uof_Sing] >> gs[Uof_SUBSET] >>    
‘ofFMAP ffv
          (o_fVmap σ
             (vinst_fVmap vσ
                (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))
                   uσf))) (Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) ∘ fVars) A)  ⊆
vinst_cont vσ (Uof ffv A) ∪                  
vinst_cont vσ (ofFMAP ffv fσ (Uof fVars A)) ∪
   ofFMAP ffv σ
           (Uof (IMAGE (vinst_fVar vσ) ∘ fVars)
              (IMAGE (ffVrn uσ ∘ fVinst fσ) A))’
   suffices_by
    (rw[] >> irule SUBSET_TRANS >>
    first_x_assum $ irule_at Any >>
    rw[] (* 3 *)
    >- (‘vinst_cont vσ (Uof ffv A)  ⊆ vinst_cont vσ Γ’
       suffices_by gs[SUBSET_DEF] >>
       simp[vinst_cont_def] >>
       irule ofFMAP_SUBSET_MONO >>
       drule_all_then assume_tac
       PfDrv_ffv_SUBSET_cont >>
       gs[Uof_Sing,Uof_SUBSET,Uof_UNION])
   >> gs[SUBSET_DEF]) >>
   ‘∀a. a ∈ A ⇒
   ofFMAP ffv
          (o_fVmap σ
             (vinst_fVmap vσ
                (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))
                   uσf))) (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars a))  ⊆
   vinst_cont vσ (ffv a) ∪   
   vinst_cont vσ (ofFMAP ffv fσ (fVars a)) ∪
   ofFMAP ffv σ (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ a))))’
    suffices_by
    (qabbrev_tac ‘σσ =
    (o_fVmap σ
                  (vinst_fVmap vσ
                     (fVmap_fVrn
                        (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))’ >> rw[] >>
     irule ofFMAP_Uof_SUBSET_lemma >>
     simp[] >>
     rw[] >>
     first_x_assum $ drule_then assume_tac >>
     irule SUBSET_TRANS >>
     first_x_assum $ irule_at Any >>
     rw[] (* 3 *)
     >- (‘vinst_cont vσ (ffv a) ⊆
         vinst_cont vσ (Uof ffv A)’
         suffices_by gs[SUBSET_DEF] >>
        simp[vinst_cont_def] >>
        irule ofFMAP_SUBSET_MONO >>
        gs[SUBSET_DEF,Uof_def] >>
        metis_tac[])
     >- (‘vinst_cont vσ (ofFMAP ffv fσ (fVars a)) ⊆
         vinst_cont vσ (ofFMAP ffv fσ (Uof fVars A))’
         suffices_by gs[SUBSET_DEF] >>
         simp[vinst_cont_def] >>
        irule ofFMAP_SUBSET_MONO >>
        irule ofFMAP_SUBSET_MONO >>
        gs[SUBSET_DEF,Uof_def] >>
        metis_tac[]) >>
     ‘ofFMAP ffv σ (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ a)))) ⊆
      ofFMAP ffv σ
          (Uof (IMAGE (vinst_fVar vσ) ∘ fVars)
             (IMAGE (ffVrn uσ ∘ fVinst fσ) A))’
       suffices_by gs[SUBSET_DEF] >>
     irule ofFMAP_SUBSET_MONO >>
     simp[Uof_IMAGE] >>
     simp[IMAGE_DEF,SUBSET_DEF,IN_Uof] >>
     metis_tac[]) >> rw[] >>
   first_x_assum $ drule_then assume_tac >> 
   irule SUBSET_TRANS >>
   qspecl_then [‘a’] assume_tac (Q.GEN ‘f’ fVinst_subset_lemma0) >> gs[] >> gs[IN_Uof,PULL_EXISTS] >>
   ‘(∀fv. fv ∈ fVars a ⇒ ffv (fσ ' fv) ⊆ FDOM vσ) ’
    by metis_tac[] >>
   qexists
   ‘Uof ffv
          (IMAGE
             (fVinst σ ∘
              $'
                (vinst_fVmap vσ
                   (fVmap_fVrn
                      (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
             (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars a)))’ >>
   simp[ofFMAP_Uof] >>
   simp[FDOM_vinst_fVmap,FDOM_fVmap_fVrn,FDOM_o_fVmap,
           FDOM_rn2fVmap,UNION_OVER_INTER,Uof_UNION,IMAGE_IMAGE,FDOM_DRESTRICT] >>
   ‘((IMAGE (vinst_fVar vσ ∘ fVrn uσf) ((FDOM fσ ∪ FDOM uσ) ∩ FDOM fσ) ∪
            FDOM σ) ∩ IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars a)) =
    IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars a)’
    by (simp[INTER_UNION,INTER_SUBSET_EQN] >>
       ‘IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars a) ⊆
        IMAGE (vinst_fVar vσ ∘ fVrn uσf) (FDOM fσ)’
        suffices_by (gs[SUBSET_DEF] >>
                    metis_tac[]) >>
        irule IMAGE_SUBSET >> simp[]) >> 
    simp[Uof_IMAGE] >>
    simp[GSYM Uof_IMAGE] >>
    irule Uof_SUBSET_MONO >>
    ‘IMAGE
          ($'
             (o_fVmap σ
                (vinst_fVmap vσ
                   (fVmap_fVrn
                      (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf))) ∘
           vinst_fVar vσ ∘ fVrn uσf) (fVars a) =
        IMAGE
          (fVinst σ ∘
           $'
             (vinst_fVmap vσ
                (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))
                   uσf)) ∘ vinst_fVar vσ ∘ fVrn uσf) (fVars a)’ suffices_by
                   metis_tac[SET_EQ_SUBSET] >>
    irule IMAGE_eq_lemma >>
    rw[] >>
    Cases_on ‘(vinst_fVar vσ (fVrn uσf a'))’ >>
    irule FAPPLY_o_fVmap1 >>
    simp[FDOM_vinst_fVmap,FDOM_fVmap_fVrn,
         FDOM_DRESTRICT,FDOM_o_fVmap,FDOM_rn2fVmap]>>
    simp[PULL_EXISTS] >>
    qexists ‘a'’ >> simp[] >> gs[SUBSET_DEF]
QED    
             
   

                

Theorem cont_fVinsth:
cont th ⊆ cont (fVinsth fσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[fVinsth_def,cont_def]
QED

Theorem IMAGE_Uof:
IMAGE f (Uof g s) = Uof (IMAGE f o g) s
Proof
rw[Uof_def,IMAGE_BIGUNION,IMAGE_SING] >>
‘(IMAGE (IMAGE f) {g e | e ∈ s})  = {IMAGE f (g e) | e ∈ s}’
 by (simp[Once EXTENSION] >> gs[PULL_EXISTS]) >>
gs[]
QED


Theorem IMAGE_vinst_fVar_fVars:
(IMAGE (vinst_fVar vσ) ∘ fVars) = (fVars ∘ finst vσ)
Proof
rw[FUN_EQ_THM,fVars_finst]
QED


Theorem thfVars_vinsth:
thfVars (vinsth vσ th) = IMAGE (vinst_fVar vσ) (thfVars th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[vinsth_def,cont_def,thfVars_def,
Uof_UNION,Uof_Sing,Uof_IMAGE,fVars_finst,IMAGE_vinst_fVar_fVars] >>
simp[IMAGE_Uof,IMAGE_vinst_fVar_fVars]
QED

Theorem IMAGE_fVrn_fVars:
(IMAGE (fVrn uσf) ∘ fVars) = (fVars ∘ ffVrn uσf)
Proof
rw[FUN_EQ_THM,fVars_ffVrn]
QED
        
                
Theorem thfVars_uniqify:
(thfVars (uniqify uσf th)) = (IMAGE (fVrn uσf) (thfVars th))
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[thfVars_def,uniqify_def,
Uof_UNION,Uof_Sing,Uof_IMAGE,fVars_ffVrn] >>
simp[IMAGE_Uof,IMAGE_fVrn_fVars]
QED


Theorem is_cfm_fprpl:
∀f bmap. is_cfm (fprpl bmap f) ⇔ is_cfm f
Proof
Induct_on ‘f’ >> gs[fprpl_def,is_cfm_def]
QED
        
Theorem fVinst_cfVmap_is_cfm:
∀f σ. cfVmap σ ∧ fVars f ⊆ FDOM σ ⇒ is_cfm (fVinst σ f)
Proof
Induct_on ‘f’ >> gs[cfVmap_def,fVars_def,fVinst_def,is_cfm_def] >>
rw[is_cfm_fprpl]
QED

Theorem cfVmap_o_fVmap:
  cfVmap cσ ∧ ofFMAP fVars σ (FDOM σ) ⊆ FDOM cσ ⇒
  cfVmap (o_fVmap cσ σ)
Proof
rw[cfVmap_def,FDOM_o_fVmap] (* 2 *)
>- (drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
   irule fVinst_cfVmap_is_cfm >> gs[cfVmap_def,ofFMAP_SUBSET]) >>
Cases_on ‘(P,sl) ∈ FDOM σ’ (* 2 *)
>- (drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
   irule fVinst_cfVmap_is_cfm >> gs[cfVmap_def,ofFMAP_SUBSET]) >>
drule_then assume_tac FAPPLY_o_fVmap2 >> gs[]
QED


Theorem ofFMAP_DRESTRICT:
s ⊆ A ⇒ ofFMAP f (DRESTRICT σ A) s = ofFMAP f σ s
Proof
rw[SUBSET_DEF,ofFMAP_def] >> AP_TERM_TAC >>
rw[Once EXTENSION,DRESTRICT_DEF] >> rw[EQ_IMP_THM] >> gs[]
>- metis_tac[EXTENSION] >>
qexists ‘a’ >> simp[]
QED


Theorem fVinsth_DRESTRICT:
(fVinsth (DRESTRICT fσ (thfVars th)) th) =  (fVinsth fσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[fVinsth_def] >>
rw[] (* 3 *)
>- (AP_TERM_TAC >> irule ofFMAP_DRESTRICT >> rw[thfVars_def])
>- (irule IMAGE_eq_lemma >> rw[] >>
   irule $ GSYM fVars_DRESTRICT_fVinst_eq1 >>
   gs[thfVars_def,Uof_UNION,Uof_Sing] >> rw[Uof_def] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
irule $ GSYM fVars_DRESTRICT_fVinst_eq1 >>
gs[thfVars_def,Uof_UNION,Uof_Sing]
QED 



Theorem uniqifn_DRESTRICT:
uniqifn uσ A ⇒ uniqifn (DRESTRICT uσ A) A
Proof
gs[uniqifn_def,DRESTRICT_DEF,SUBSET_DEF]
QED



Theorem ffVrn_eq:
∀f σ1 σ2.
 (DRESTRICT σ1 (fVars f)  = DRESTRICT σ2 (fVars f)) ⇒ ffVrn σ1 f = ffVrn σ2 f
Proof
Induct_on ‘f’ >> gs[ffVrn_def,fVars_def,INTER_UNION] >> rw[] (* 5 *)
>- (first_x_assum irule >>
   drule_then assume_tac DRESTRICT_SUBSET >>
   first_x_assum $
   qspecl_then [‘fVars f’] assume_tac >>
   gs[SUBSET_DEF])
>- (first_x_assum irule >>
   drule_then assume_tac DRESTRICT_SUBSET >>
   first_x_assum $
   qspecl_then [‘fVars f'’] assume_tac >>
   gs[SUBSET_DEF])
>- (qspecl_then [‘σ1’,‘{(s,l)}’,‘(s,l)’] assume_tac
   (SRULE [PULL_FORALL] DRESTRICT_DEF) >>
   qspecl_then [‘σ2’,‘{(s,l)}’,‘(s,l)’] assume_tac
   (SRULE [PULL_FORALL] DRESTRICT_DEF)  >> gs[]) >>
qspecl_then [‘σ1’,‘{(s,l)}’] assume_tac
  DRESTRICT_DEF >>
qspecl_then [‘σ2’,‘{(s,l)}’] assume_tac
  DRESTRICT_DEF >>
gs[] >> gs[Once EXTENSION] >> metis_tac[]
QED

        
Theorem ffVrn_eq1:
∀f σ1 σ2.
 (FDOM σ1 ∩ fVars f = FDOM σ2 ∩ fVars f) ∧
 (∀fv. fv ∈ fVars f ⇒ σ1 ' fv = σ2 ' fv) ⇒ ffVrn σ1 f = ffVrn σ2 f
Proof
rw[] >> irule ffVrn_eq >>
simp[fmap_EXT,DRESTRICT_DEF] >> rw[] >>
gs[EXTENSION] >> metis_tac[]
QED
 
Theorem uniqify_DRESTRICT:
thfVars th ⊆ s ⇒
uniqify (DRESTRICT uσ s) th = uniqify uσ th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
simp[uniqify_def] >> rw[] (* 2 *)
>- (irule IMAGE_eq_lemma >> rw[] >>
   irule ffVrn_eq >>
   rw[DRESTRICT_DRESTRICT] >>
   gs[SUBSET_DEF,thfVars_def,Uof_UNION,Uof_Sing] >>
   AP_TERM_TAC >> gs[Once EXTENSION,IN_Uof] >>
   metis_tac[EXTENSION]) >>
 irule ffVrn_eq >>
   rw[DRESTRICT_DRESTRICT] >>
   gs[SUBSET_DEF,thfVars_def,Uof_UNION,Uof_Sing] >>
   AP_TERM_TAC >> gs[Once EXTENSION,IN_Uof] >>
   metis_tac[EXTENSION]   
QED

Theorem wfvmap_DRESTRICT:
wfvmap Σ vσ ⇒
∀s. s ⊆ FDOM vσ ∧ is_cont s ⇒
 wfvmap Σ (DRESTRICT vσ s)
Proof
simp[wfvmap_def,DRESTRICT_DEF] >> gs[] >>
rw[] (* 2 *)
>- (irule DRESTRICT_cstt >> simp[]) >>
simp[DRESTRICT_wfcod]
QED

Theorem vinst_cont_DRESTRICT:
Γ ⊆ s ∧ s ⊆ FDOM vσ ⇒
vinst_cont (DRESTRICT vσ s) Γ = vinst_cont vσ Γ
Proof
rw[vinst_cont_def] >> rw[Once EXTENSION] >>
simp[ofFMAP_def,PULL_EXISTS] >>
‘∀a. a ∈ Γ ⇒  (DRESTRICT vσ s ' a) = (vσ ' a)’
 suffices_by (simp[FDOM_DRESTRICT] >>
             gs[SUBSET_DEF] >>metis_tac[]) >>
rw[] >> gs[DRESTRICT_DEF] >>
gs[SUBSET_DEF]
QED


Theorem vinsth_DRESTRICT:
Uof ffv ({f} ∪ A) ⊆ s ∧ Γ ⊆ s ∧ s ⊆ FDOM vσ ⇒
vinsth (DRESTRICT vσ s) (Γ,A,f) =
vinsth vσ (Γ,A,f)
Proof
rw[] >> rw[vinsth_def] (* 3 *)
>- (irule vinst_cont_DRESTRICT >> simp[])
>- (irule IMAGE_eq_lemma >>
   rw[] >> irule fmap_ffv_finst_eq1 >>
   simp[DRESTRICT_DRESTRICT] >>
   ‘(s ∩ ffv a) = ffv a’ suffices_by metis_tac[] >>
   gs[Uof_SUBSET] >> simp[INTER_SUBSET_EQN]) >>
irule fmap_ffv_finst_eq1 >>
simp[DRESTRICT_DRESTRICT] >>
‘(s ∩ ffv f) = ffv f’ suffices_by metis_tac[] >>
gs[Uof_SUBSET] >> simp[INTER_SUBSET_EQN]   
QED


Theorem vinsth_DRESTRICT1:
Uof ffv ({concl th} ∪ assum th) ⊆ s ∧
 cont th ⊆ s ∧ s ⊆ FDOM vσ ⇒
vinsth (DRESTRICT vσ s) th =
vinsth vσ th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[assum_def,concl_def,cont_def] >> 
metis_tac[vinsth_DRESTRICT]   
QED

        
        

Theorem cont_uniqify:
cont (uniqify σ th) = cont th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> simp[cont_def,uniqify_def]
QED

Theorem Uof_ffv_uniqify:
Uof ffv
          ({concl (uniqify uσ th)} ∪
           assum (uniqify uσ th)) =
Uof ffv ({concl th} ∪ assum th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘(Γ,A,f)’] >>
rw[Uof_def,Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
gs[uniqify_def,concl_def,assum_def,ffv_ffVrn]
(* 4 *)
>>metis_tac[ffv_ffVrn]
QED

Theorem cfVmap_DRESTRICT:
cfVmap σ ⇒ cfVmap (DRESTRICT σ s)
Proof
rw[cfVmap_def,DRESTRICT_DEF]
QED
   
Theorem wfcfVmap_DRESTRICT:
wfcfVmap Σ σ ⇒ wfcfVmap Σ (DRESTRICT σ s)
Proof
gs[wfcfVmap_def,wffVmap_DRESTRICT,cfVmap_DRESTRICT]
QED


Theorem PfDrv_cont_is_cont:
∀th. PfDrv Σ axs th ⇒ is_cont (cont th)
Proof
rw[] >> irule Pf_cont_is_cont >>
gs[PfDrv_def] >> Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[cont_def] >> metis_tac[]
QED



        
Theorem precise_maps_ex:
∀th fσ uσ vσ σ.
PfDrv Σ axs th ∧ wfsigaxs Σ axs ⇒
wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ∧ wfvmap (FST Σ) vσ ∧
wfcfVmap Σ σ ∧
thfVars (vinsth vσ (uniqify uσ (fVinsth fσ th))) ⊆ FDOM σ ∧
cont (fVinsth fσ th) ⊆ FDOM vσ ∧
uniqifn uσ (thfVars (fVinsth fσ th)) ⇒
∃fσ1 uσ1 vσ1 σ1.
wffVmap Σ fσ1 ∧ thfVars th = FDOM fσ1 ∧ wfvmap (FST Σ) vσ1 ∧
wfcfVmap Σ σ1 ∧
thfVars (vinsth vσ1 (uniqify uσ1 (fVinsth fσ1 th))) = FDOM σ1 ∧
cont (fVinsth fσ1 th) = FDOM vσ1 ∧
uniqifn uσ1 (thfVars (fVinsth fσ1 th)) ∧
(thfVars (fVinsth fσ1 th)) = FDOM uσ1 ∧
(insth σ vσ (uniqify uσ (fVinsth fσ th))) =
(insth σ1 vσ1 (uniqify uσ1 (fVinsth fσ1 th)))
Proof
rw[] >>
qexists ‘DRESTRICT fσ (thfVars th)’ >>
‘ wffVmap Σ (DRESTRICT fσ (thfVars th)) ∧
          thfVars th = FDOM (DRESTRICT fσ (thfVars th))’
 by (gs[wffVmap_DRESTRICT,FDOM_DRESTRICT] >>
    gs[SUBSET_DEF,Once EXTENSION] >> metis_tac[]) >> gs[] >>
‘(fVinsth (DRESTRICT fσ (thfVars th)) th) = (fVinsth fσ th)’
 by simp[fVinsth_DRESTRICT] >> gs[] >>
qexists ‘DRESTRICT uσ (thfVars (fVinsth fσ th))’ >>
simp[uniqifn_DRESTRICT] >> simp[FDOM_DRESTRICT]  >>
‘(thfVars (fVinsth fσ th)) ⊆ FDOM uσ’ by metis_tac[uniqifn_def] >>
simp[INTER_SUBSET_EQN] >>
‘(uniqify (DRESTRICT uσ (thfVars (fVinsth fσ th)))
                  (fVinsth fσ th)) =
(uniqify uσ (fVinsth fσ th))’
 by (irule uniqify_DRESTRICT >> simp[SUBSET_DEF]) >>
simp[] >>
qexists ‘DRESTRICT vσ (cont (fVinsth fσ th))’ >>
simp[FDOM_DRESTRICT] >>
‘wfvmap (FST Σ)
 (DRESTRICT vσ (cont (fVinsth fσ th)))’
 by (irule wfvmap_DRESTRICT >>
    simp[] >> irule PfDrv_cont_is_cont >>
    irule_at Any PfDrv_fVinsth >> metis_tac[]) >>
simp[INTER_SUBSET_EQN] >>
simp[insth_def]>>
‘(vinsth (DRESTRICT vσ (cont (fVinsth fσ th)))
               (uniqify uσ (fVinsth fσ th))) =
 (vinsth vσ (uniqify uσ (fVinsth fσ th)))’
 by (irule vinsth_DRESTRICT1 >>
    simp[] >> simp[cont_uniqify] >>
    simp[Uof_ffv_uniqify] >>
    drule_all_then assume_tac PfDrv_fVinsth >>
    irule PfDrv_ffv_SUBSET_cont >>
    Cases_on ‘(fVinsth fσ th)’ >> Cases_on ‘r’ >>
    gs[cont_def,assum_def,concl_def] >>
    metis_tac[]) >>
simp[] >>
qexists ‘DRESTRICT σ
(thfVars (vinsth vσ (uniqify uσ (fVinsth fσ th))))’>>
simp[FDOM_DRESTRICT,INTER_SUBSET_EQN] >>
simp[wfcfVmap_DRESTRICT] >>
rw[fVinsth_DRESTRICT]
QED

                        
Theorem Uof_FINITE_lemma:
FINITE A ∧ (∀a. a ∈ A ⇒ FINITE (f a)) ⇒
FINITE (Uof f A)
Proof
rw[Uof_def] (* 2 *)
>- (‘{f e | e ∈ A} = IMAGE f A’
    by simp[Once EXTENSION] >>
    gs[]) >>
metis_tac[]
QED    

Theorem Pf_assum_FINITE:
∀pf. Pf Σ axs pf ⇒
     ∀Γ A f. MEM (Γ,A,f) pf ⇒
             FINITE A
Proof             
Induct_on ‘Pf’ >> rw[] >> TRY (gs[]>>metis_tac[])
(* 11 *)
>- (gs[MEM_FLAT,MEM_map2list] >>
   ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> metis_tac[])
>- (gs[fVcong_def] >>
   irule Uof_FINITE_lemma >>
   simp[] >> simp[MEM_map2list,PULL_EXISTS] >>
   rw[] >>
   ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
   gs[assum_def] >> metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   gs[fVinsth_def] >>
   irule IMAGE_FINITE >> metis_tac[])   
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   gs[vinsth_def] >>
   irule IMAGE_FINITE >> metis_tac[])
>- (gs[gen_def] >> metis_tac[])
>- (gs[spec_def] >> metis_tac[])
>- (first_x_assum $ drule_then assume_tac >>
   gs[])
>- gs[assume_def]
>- (Cases_on ‘th’ >> Cases_on ‘r’ >> gs[disch_def] >>
   metis_tac[])
>- gs[refl_def] >>
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[add_cont1_def] >>
metis_tac[]
QED


Theorem wffVmap_fVar_subfm_LENGTH:
wffVmap Σ σ ⇒
∀fv. fv ∈ FDOM σ ⇒
  ∀P sl tl. fVar P sl tl ∈ subfm (σ ' fv) ⇒
  LENGTH sl = LENGTH tl
Proof
 rw[] >>
 irule $ wff_subfm_fVar_LENGTH >>
 gs[wffVmap_def] >>
 Cases_on ‘fv’ >>
 first_x_assum $ drule_then assume_tac >>
 first_x_assum $ irule_at Any >>
 irule_at Any fVar_FALLL_inc >>
 metis_tac[]
QED 

Theorem thfVars_FAPPLY_IN_cont:        
fv ∈ thfVars th ∧ fv ∈ FDOM fσ ⇒
           ffv (fσ ' fv) ⊆
           cont (fVinsth fσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘(Γ,A,f)’] >> gs[fVinsth_def,cont_def] >>
gs[thfVars_def,Uof_UNION,Uof_def,Uof_Sing,
   IN_Uof,PULL_EXISTS] >>
rw[] (* 2 *)
>>(‘ffv (fσ ' fv) ⊆
    ofFMAP ffv fσ (fVars f ∪ BIGUNION {fVars e | e ∈ A})’ suffices_by gs[SUBSET_DEF] >>
    simp[ofFMAP_def,SUBSET_DEF,PULL_EXISTS] >>
    rw[] >> metis_tac[])
QED    
    

Theorem slfv_SUBSET_ffv:
(P,sl) ∈ fVars f ⇒ slfv sl ⊆ ffv f
Proof
rw[] >>
qspecl_then [‘f’] assume_tac fVslfv_SUBSET_ffv >>
gs[SUBSET_DEF,fVslfv_def,IN_Uof,PULL_EXISTS] >>
rw[] >>
first_x_assum
 (qspecl_then [‘x’,‘(P,sl)’] assume_tac) >>
gs[]
QED
        
Theorem thfVars_slfv_cont_fVinsth:
PfDrv Σ axs th ∧ wfsigaxs Σ axs ∧ (P,sl) ∈ thfVars th ⇒
slfv sl ⊆ cont (fVinsth fσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘(Γ,A,f)’] >> gs[fVinsth_def,cont_def,PULL_EXISTS] >> rw[] >>
drule_all_then assume_tac PfDrv_ffv_SUBSET_cont >>
‘slfv sl ⊆ Γ’ suffices_by gs[SUBSET_DEF]>>
gs[thfVars_def,Uof_SUBSET,Uof_Sing,Uof_UNION]
(* 2 *)
>- (irule SUBSET_TRANS >>
   qexists ‘ffv f’ >> simp[] >>
   irule slfv_SUBSET_ffv >> metis_tac[]) >>
gs[IN_Uof,PULL_EXISTS] >>
irule SUBSET_TRANS >>
qexists ‘ffv a’ >> simp[] >>
irule slfv_SUBSET_ffv >> metis_tac[]
QED



Theorem fVars_FAPPLY_SUBSET_thfVars_fVinsth:
 fv ∈ thfVars th ∧ fv ∈ FDOM fσ ⇒
 fVars (fσ ' fv) ⊆ thfVars (fVinsth fσ th)
Proof
 Cases_on ‘th’ >> Cases_on ‘r’ >>
 rename [‘(Γ,A,f)’] >> rw[thfVars_def] >>
 gs[thfVars_def,fVinsth_def] >> 
 gs[Uof_Sing,Uof_UNION] (* 2 *)
 >- (‘fVars (fσ ' fv) ⊆ fVars (fVinst fσ f)’
     suffices_by gs[SUBSET_DEF] >>
     irule SUBSET_TRANS >>
    qexists ‘ofFMAP fVars fσ (fVars f)’ >>
    simp[ofFMAP_fVars_SUBSET_fVars_fVinst] >>
    gs[ofFMAP_def,SUBSET_DEF] >>
    metis_tac[]) >>
 ‘fVars (fσ ' fv) ⊆ Uof fVars (IMAGE (fVinst fσ) A)’
   suffices_by gs[SUBSET_DEF] >>
 irule SUBSET_TRANS >> gs[IN_Uof,PULL_EXISTS] >>
 qexists ‘ofFMAP fVars fσ (fVars a)’ >>
 simp[ofFMAP_fVars_SUBSET_fVars_fVinst] >> rw[]
 (* 2 *)
 >- (gs[SUBSET_DEF,ofFMAP_def,PULL_EXISTS] >>
    metis_tac[]) >>
 irule SUBSET_TRANS >>
 qexists ‘fVars (fVinst fσ a)’ >>
 simp[ofFMAP_fVars_SUBSET_fVars_fVinst] >>
 gs[SUBSET_DEF,IN_Uof] >> metis_tac[]
QED  

  

Theorem Pf0Drv_cont_SUBSET_cong:
Pf0Drv Σ aths (Γ0,A,f) ∧
FINITE Γ ∧ Γ0 ⊆ Γ ∧ is_cont Γ ∧
(∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s) ∧
A = A' ∧ f = f' ⇒
Pf0Drv Σ aths (Γ,A',f')
Proof
metis_tac[Pf0Drv_cont_SUBSET]
QED


Theorem Pf0Drv_cont_assum_SUBSET_cong:
wfsigaths Σ aths ∧ 
Pf0Drv Σ aths (Γ0,A,f) ∧
FINITE Γ ∧ Γ0 ⊆ Γ ∧ is_cont Γ ∧
(∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s) ∧
A ⊆ A' ∧ FINITE A' ∧
(∀f. f ∈ A' ⇒ wff Σ f ∧ is_cfm f) ∧
 Uof ffv A' ⊆ Γ ∧ f = f' ⇒
Pf0Drv Σ aths (Γ,A',f')
Proof
rw[] >>
‘Pf0Drv Σ aths (Γ,A,f)’
 by metis_tac[Pf0Drv_cont_SUBSET] >>
drule_then assume_tac Pf0Drv_add_assum >>
rpt (first_x_assum $ drule_then assume_tac) >>
gs[add_assum_def] >>
‘(Γ ∪ Uof ffv A',A ∪ A',f) = (Γ,A',f)’
 by (simp[] >> rw[EXTENSION] (* 2 *)
    >> gs[SUBSET_DEF] >> metis_tac[]) >>
gs[]    
QED
        

Theorem ffv_ffVinst_SUBSET_cont_fVinsth:
PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ∧
 wffVmap Σ fσ ∧ thfVars (Γ,A,f) ⊆ FDOM fσ ⇒
ffv f ∪ ffv (fVinst fσ f) ⊆
cont (fVinsth fσ (Γ,A,f))
Proof
rw[] (* 2 *)
>- (drule_all_then assume_tac PfDrv_ffv_SUBSET_cont>>
   gs[Uof_SUBSET] >>
   irule SUBSET_TRANS >>
   qexists ‘cont (Γ,A,f)’ >>
   simp[cont_fVinsth] >> gs[cont_def]) >>
drule_all_then assume_tac PfDrv_fVinsth >>
gs[fVinsth_def] >> 
drule_all_then assume_tac PfDrv_ffv_SUBSET_cont>>
gs[Uof_SUBSET] >>
simp[cont_def]
QED

Theorem wffVmap_ofFMAP_var_wf:
  wffVmap (Σf,Σp,Σe) σ ⇒
  ∀n s A. (n,s) ∈ ofFMAP ffv σ A ⇒ wfs Σf s
Proof
 rw[ofFMAP_def,PULL_EXISTS] >>
 gs[wffVmap_def] >>
 Cases_on ‘a’ >>
 first_x_assum $ drule_then assume_tac >>
 irule wff_wfs >>
 first_x_assum $ irule_at Any >>
 simp[ffv_FALLL] >>
 metis_tac[]
QED


Theorem vinst_cont_wf:
(∀n:string s. (n,s) ∈ ct ⇒ wfs Σf s) ∧
wfcod Σf vσ ⇒
(∀n s. (n,s) ∈ vinst_cont vσ ct ⇒ wfs Σf s)
Proof
rw[vinst_cont_def] >>
gs[ofFMAP_def] >> gs[wfvmap_def] >>
irule $ cj 1 wft_wfs >>
gs[wfcod_def] >>
Cases_on ‘a’ >> metis_tac[]
QED

Theorem ofFMAP_as_IMAGE:
ofFMAP f σ s =
BIGUNION (IMAGE (f o ($' σ)) (FDOM σ ∩ s))
Proof
rw[ofFMAP_def,Once EXTENSION]
QED 
        
Theorem ofFMAP_FINITE:
FINITE A ∧
(∀a. a ∈ A ∧ a ∈ FDOM σ ⇒ FINITE (f (σ ' a))) ⇒
FINITE (ofFMAP f σ A)
Proof
rw[ofFMAP_as_IMAGE] >> metis_tac[]
QED 

Theorem fVars_FINITE:
∀f. FINITE (fVars f)
Proof
Induct_on ‘f’ >> gs[fVars_def]
QED
        
Theorem PfDrv_cont_FINITE:
∀pf. Pf Σ axs pf ⇒
     ∀th. MEM th pf ⇒ FINITE (cont th)
Proof
Induct_on ‘Pf’ >> rw[] >>
TRY (gs[cont_def] >> metis_tac[]) (* 15 *)
>- (gs[MEM_FLAT,MEM_map2list] >>
   ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[] >> metis_tac[])
>- (gs[fVcong_def,cont_def] >>
   irule Uof_FINITE_lemma >>
   simp[] >> simp[MEM_map2list,PULL_EXISTS] >>
   rw[] >>
   ‘LENGTH sl ≠ 0’ by simp[] >>
   ‘n0 < LENGTH sl’ by simp[] >>
   first_x_assum $ drule_then assume_tac >>
   Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
   gs[assum_def] >> metis_tac[])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   gs[fVinsth_def,cont_def] >> rw[] (* 2 *)
   >- metis_tac[cont_def] >>
   irule ofFMAP_FINITE >> simp[ffv_FINITE] >>
   irule Uof_FINITE_lemma >>
   simp[fVars_FINITE] >>
   metis_tac[Pf_assum_FINITE])   
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
   gs[vinsth_def,cont_def] >>
   simp[vinst_cont_def,ofFMAP_as_IMAGE] >>
   rw[] >> simp[tfv_FINITE])
>- (gs[gen_def,cont_def] >> metis_tac[cont_def])
>- (gs[spec_def,cont_def] >> metis_tac[cont_def])
>- (first_x_assum $ drule_then assume_tac >>
   gs[cont_def])
>- (gs[cont_def] >> metis_tac[cont_def])
>- gs[assume_def,cont_def]
>- (gs[cont_def] >> metis_tac[cont_def])
>- (Cases_on ‘th’ >> Cases_on ‘r’ >>
    gs[disch_def,cont_def] >> metis_tac[cont_def])
>- gs[refl_def,cont_def,tfv_FINITE] 
>- (gs[cont_def] >> metis_tac[cont_def])
>- (gs[cont_def] >> metis_tac[cont_def]) >>
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[add_cont1_def,cont_def,tfv_FINITE] >>
metis_tac[cont_def]
QED

Theorem ofFMAP_ffv_is_cont:
is_cont (ofFMAP ffv σ A)
Proof
rw[ofFMAP_def] >> irule BIGUNION_is_cont >>
gs[] >> metis_tac[ffv_is_cont]
QED


Theorem ofFMAP_tfv_is_cont:
is_cont (ofFMAP tfv σ A)
Proof
rw[ofFMAP_def] >> irule BIGUNION_is_cont >>
gs[] >> metis_tac[tfv_is_cont]
QED

        

Theorem vinst_cont_is_cont:
is_cont (vinst_cont vσ ct)
Proof
rw[vinst_cont_def,ofFMAP_tfv_is_cont]
QED     

Theorem SUBSET_thfVars:
fVars f ⊆ thfVars (Γ,A,f) ∧
∀a. a ∈ A ⇒ fVars a ⊆ thfVars (Γ,A,f)
Proof
simp[thfVars_def,Uof_def,SUBSET_DEF] >>
metis_tac[]
QED

Theorem ffv_SUBSET_cont_fVinsth:
wfsigaxs Σ axs ∧
PfDrv Σ axs (Γ,A,f) ⇒ ffv f ⊆ cont (fVinsth fσ (Γ,A,f))
Proof
rw[] >> irule SUBSET_TRANS >>
qexists ‘cont (Γ,A,f)’ >> simp[cont_fVinsth] >>
gs[cont_def] >>
metis_tac[PfDrv_concl_ffv_SUBSET]
QED



Theorem ffv_SUBSET_cont_fVinsth:
wfsigaxs Σ axs ∧
PfDrv Σ axs (Γ,A,f) ⇒ ffv f ⊆ cont (fVinsth fσ (Γ,A,f)) 
Proof
rw[] >> irule SUBSET_TRANS >>
qexists ‘cont (Γ,A,f)’ >> simp[cont_fVinsth] >>
gs[cont_def] >>
metis_tac[PfDrv_concl_ffv_SUBSET]
QED



Theorem ffv_assum_SUBSET_cont_fVinsth:
wfsigaxs Σ axs ∧
PfDrv Σ axs (Γ,A,f) ⇒
∀a. a ∈ A ⇒ ffv a ⊆ cont (fVinsth fσ (Γ,A,f)) 
Proof
rw[] >> irule SUBSET_TRANS >>
qexists ‘cont (Γ,A,f)’ >> simp[cont_fVinsth] >>
gs[cont_def] >>
metis_tac[PfDrv_assum_ffv_SUBSET]
QED

                        
Theorem cont_assum_concl:
(cont th,assum th,concl th) = th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[cont_def,assum_def,concl_def]
QED
        

        

Theorem uniqifn_INJ:
uniqifn (σ:string # sort list |-> string) s ∧ fv1 ∈ s ∧ fv2 ∈ s ∧
σ ' fv1 = σ ' fv2 ⇒ fv1 = fv2
Proof
rw[uniqifn_def] >>
Cases_on ‘fv1’ >> Cases_on ‘fv2’ >>
simp[] >> metis_tac[]
QED


        


Theorem main_fVinst_case:
     wfsigaxs Σ axs ∧
     Pf Σ axs pf ∧
     Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ⇒
     (∀th.
       MEM th pf ⇒
       ∀vσ fσ uσ.
         wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
         thfVars (vinsth vσ (uniqify uσ th)) ⊆ FDOM fσ ∧
         cont th ⊆ FDOM vσ ∧ uniqifn uσ (thfVars th) ⇒
         Pf0Drv Σ aths (insth fσ vσ (uniqify uσ th)))
         ∧
     MEM th pf ∧
     wffVmap Σ fσ ∧
     thfVars th ⊆ FDOM fσ ∧
     Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ∧ 
     wfvmap (FST Σ) vσ ∧
     wfcfVmap Σ fσ' ∧
     thfVars (vinsth vσ (uniqify uσ (fVinsth fσ th))) ⊆ FDOM fσ' ∧
     cont (fVinsth fσ th) ⊆ FDOM vσ ∧
     uniqifn uσ (thfVars (fVinsth fσ th))  ⇒
      Pf0Drv Σ aths (insth fσ' vσ (uniqify uσ (fVinsth fσ th)))          
Proof
  rpt strip_tac >>
  gs[] >> rename [‘wfcfVmap Σ σ’] >>
  Cases_on ‘Σ’ >> Cases_on ‘r’ >> rename [‘(Σf,Σp,Σe)’] >>
  ‘PfDrv (Σf,Σp,Σe) axs th’
    by metis_tac[PfDrv_def] >>
  drule_all_then assume_tac precise_maps_ex >>
  rename
  [‘thfVars (vinsth vσ0 (uniqify uσ0 (fVinsth fσ0 th))) ⊆ FDOM σ0’] >>
  pop_assum strip_assume_tac >>
  rename
  [‘insth σ0 vσ0 (uniqify uσ0 (fVinsth fσ0 th)) =
    insth σ vσ (uniqify uσ (fVinsth fσ th))’] >>
  qpat_x_assum ‘wffVmap (Σf,Σp,Σe) fσ0’
               (K all_tac) >>
  qpat_x_assum ‘ wfvmap (FST (Σf,Σp,Σe)) vσ0’
               (K all_tac) >>
  qpat_x_assum ‘thfVars th ⊆ FDOM fσ0’ (K all_tac)>>
  qpat_x_assum ‘wfcfVmap (Σf,Σp,Σe) σ0’(K all_tac)>>
  qpat_x_assum ‘thfVars (vinsth vσ0 (uniqify uσ0 (fVinsth fσ0 th))) ⊆ FDOM σ0’ (K all_tac) >>
  qpat_x_assum ‘cont (fVinsth fσ0 th) ⊆ FDOM vσ0’
               (K all_tac) >>
  qpat_x_assum ‘uniqifn uσ0 (thfVars (fVinsth fσ0 th))’ (K all_tac) >>
  gs[] >> pop_assum (K all_tac) >> 
  ‘∃uσf:string # sort list |-> string.
     uniqifn uσf (thfVars th) ∧
     FDOM uσf = thfVars th’
    by (irule uniqifn_ex >> simp[])  >>
  assume_tac (Pf2Pf0_fVinsth_lemma |> SPEC_ALL |> Q.GEN ‘f’) >>
  last_x_assum $ drule_then assume_tac >>
  first_x_assum $ qspecl_then [‘vσ’,‘(o_fVmap σ
                                      (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT
                                                                   (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))’,
                               ‘uσf’] assume_tac >> gs[] >>
  ‘cont th ⊆ cont (fVinsth fσ th)’
    by simp[cont_fVinsth] >>
  ‘PfDrv (Σf,Σp,Σe) axs (fVinsth fσ th)’
   by (irule PfDrv_fVinsth >> simp[]) >>
  ‘(∀fv. fv ∈ FDOM uσ ⇒ wffV Σf fv)’
    by (qpat_x_assum ‘_ = FDOM uσ’ (assume_tac o GSYM) >>
       simp[] >>
       match_mp_tac PfDrv_thfVars_wffV >>
       simp[]) >>
  ‘wffVmap (Σf,Σp,Σe) (rn2fVmap uσ)’
   by (irule wffVmap_rn2fVmap1 >> simp[]) >>
  ‘Pf0Drv (Σf,Σp,Σe)  aths
   (insth
    (o_fVmap σ
     (vinst_fVmap vσ
      (fVmap_fVrn
       (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
    vσ (uniqify uσf th))’
    by
    (first_x_assum irule >>
  simp[FDOM_o_fVmap,FDOM_vinst_fVmap,FDOM_fVmap_fVrn,FDOM_DRESTRICT,
       INTER_UNION]   >>
  simp[thfVars_vinsth,thfVars_uniqify] >>
  rw[] (* 2 *)
  >- gs[] >>
  rw[wfcfVmap_def] (* 2 *) 
  >- (irule wffVmap_o_fVmap >>
      gs[wfcfVmap_def,wfsigaxs_def,wffsig_def,wfsig_def] >>
      irule wffVmap_vinst_fVmap >>
      gs[wffsig_def] >>
      drule_then assume_tac wfvmap_presname >> gs[] >>
      simp[FDOM_fVmap_fVrn,FDOM_DRESTRICT,FDOM_o_fVmap,
           INTER_UNION,FDOM_rn2fVmap] >>
      ‘alluniq (IMAGE (fVrn uσf) (FDOM fσ))’
        by (irule uniqifn_alluniq0 >>simp[]) >>
      simp[] >> 
      ‘wffVmap (Σf,Σp,Σe)
       (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)’
        by (irule wffVmap_fVmap_fVrn >>
           simp[FDOM_DRESTRICT,FDOM_o_fVmap,
                FDOM_rn2fVmap,INTER_UNION] >>
           irule wffVmap_DRESTRICT >>
           irule wffVmap_o_fVmap >> simp[] >>
           gs[wffsig_def]) >> simp[] >>
      simp[BIGUNION_SUBSET,PULL_EXISTS] >>
      rw[] (* 2 *)
      >- (qspecl_then [‘uσf’,‘(DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))’] 
          assume_tac FAPPLY_fVmap_fVrn1 >>
          gs[FDOM_DRESTRICT,FDOM_o_fVmap,FDOM_rn2fVmap,INTER_UNION] >>
          simp[DRESTRICT_DEF,FDOM_o_fVmap,FDOM_rn2fVmap,FDOM_rn2fVmap] >>
          Cases_on ‘x’ >> drule_then assume_tac FAPPLY_o_fVmap1 >>
          gs[] >>
          ‘(fVinst (rn2fVmap uσ) (fσ ' (q,r))) =
           ffVrn uσ (fσ ' (q,r))’
            by (irule $ GSYM ffVrn_fVinst >> rw[] >>  
                irule $
                      GSYM wffVmap_fVar_subfm_LENGTH>>
                metis_tac[]) >>
          gs[ffv_ffVrn] >>
          ‘ffv (fσ ' (q,r)) ⊆ cont (fVinsth fσ th) ’
            suffices_by simp[] >>
          irule thfVars_FAPPLY_IN_cont >>
          simp[]) >>
      ‘slfv sl ⊆ cont (fVinsth fσ th)’
        suffices_by metis_tac[] >>
      irule thfVars_slfv_cont_fVinsth >>
      simp[PULL_EXISTS] >> Cases_on ‘x’ >>
      gs[fVrn_def] >> 
      qexistsl [‘q’,‘axs’,‘(Σf,Σp,Σe)’] >>
      gs[wfsigaxs_def,wfsig_def]) >>
  irule cfVmap_o_fVmap >> gs[wfcfVmap_def] >>
  simp[FDOM_vinst_fVmap,FDOM_fVmap_fVrn,FDOM_DRESTRICT,FDOM_o_fVmap,
       FDOM_rn2fVmap,INTER_UNION] >>
  simp[ofFMAP_SUBSET,PULL_EXISTS,FDOM_vinst_fVmap,
       FDOM_fVmap_fVrn,FDOM_DRESTRICT,FDOM_o_fVmap,
       FDOM_rn2fVmap,INTER_UNION] >> rw[] >>
  ‘x'' = x'’
    by (irule uniqifn_INJ >>
       qexistsl [‘FDOM fσ’,‘uσf’] >>
       simp[] >> Cases_on ‘x'’ >> Cases_on ‘x''’ >>
       gs[fVrn_def,vinst_fVar_def]) >> gs[] >>
  Cases_on ‘x'’  >>
  qspecl_then [‘(q,r)’,‘uσf’,‘vσ’,‘(DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))’] assume_tac (FAPPLY_vinst_fVmap_fVmap_fVrn1 |> Q.GEN ‘fv’) >>
  gs[ofFMAP_SUBSET,PULL_EXISTS,FDOM_vinst_fVmap,
     FDOM_fVmap_fVrn,FDOM_DRESTRICT,FDOM_o_fVmap,
     FDOM_rn2fVmap,INTER_UNION] >>
  ‘(q,r) ∈ FDOM uσf ∧ uniqifn uσf (FDOM fσ)’ by
   metis_tac[] >>
  gs[] >>
  simp[fVars_finst] >>
  ‘(DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ) ' (q,r)) =
   (o_fVmap (rn2fVmap uσ) fσ) ' (q,r)’
   by gs[DRESTRICT_DEF,FDOM_o_fVmap,FDOM_rn2fVmap]>>
  gs[] >>
  ‘(o_fVmap (rn2fVmap uσ) fσ ' (q,r)) = ffVrn uσ (fσ ' (q,r))’
    by (drule_then assume_tac FAPPLY_o_fVmap1 >>
       gs[] >>
       irule $ GSYM ffVrn_fVinst >> rw[] >>
       irule $ GSYM wffVmap_fVar_subfm_LENGTH >>
       metis_tac[]) >>
  gs[fVars_ffVrn] >>
  gs[thfVars_vinsth,thfVars_uniqify] >>
  ‘IMAGE (vinst_fVar vσ) (IMAGE (fVrn uσ) (fVars (fσ ' (q,r)))) ⊆
  IMAGE (vinst_fVar vσ) (IMAGE (fVrn uσ) (FDOM uσ))’
   suffices_by metis_tac[] >>
  irule IMAGE_SUBSET >>
  irule IMAGE_SUBSET >>
  ‘fVars (fσ ' (q,r)) ⊆ thfVars (fVinsth fσ th)’
   suffices_by metis_tac[] >>
  irule fVars_FAPPLY_SUBSET_thfVars_fVinsth >>
  simp[]) >>
  Cases_on ‘th’ >> Cases_on ‘r’ >>
  rename [‘fVinsth fσ (Γ,A,f)’] >> 
  simp[insth_uniqify_fVinsth] >>
 gs[fVinst_o_Vmap_finst_ffVrn] >>
drule_then assume_tac Pf0Drv_cont_SUBSET_cong >>
first_x_assum irule >>
‘vinst_cont vσ Γ ∪
        (ofFMAP ffv
           (o_fVmap σ
              (vinst_fVmap vσ
                 (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))
                    uσf))) (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) ∪
         ofFMAP ffv
           (o_fVmap σ
              (vinst_fVmap vσ
                 (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))
                    uσf))) (Uof (IMAGE (vinst_fVar vσ ∘ fVrn uσf) ∘ fVars) A)) ⊆
        vinst_cont vσ
          (Γ ∪ (ofFMAP ffv fσ (fVars f) ∪ ofFMAP ffv fσ (Uof fVars A))) ∪
        (ofFMAP ffv σ
           (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f)))) ∪
         ofFMAP ffv σ
           (Uof (IMAGE (vinst_fVar vσ) ∘ fVars)
              (IMAGE (ffVrn uσ ∘ fVinst fσ) A)))’
by
(irule fVinst_subset_lemma >> simp[] >>
last_x_assum $ irule_at Any >> simp[] >>
gs[wfcfVmap_def] >> rw[] (* 2 *)
>- (‘ffv (fσ ' fv) ⊆ cont (fVinsth fσ (Γ,A,f)) ’
    suffices_by metis_tac[] >>
   irule thfVars_FAPPLY_IN_cont >>
   qpat_x_assum ‘thfVars (Γ,A,f) = FDOM fσ’
   (assume_tac o GSYM) >> 
   simp[thfVars_def]) >>
qpat_x_assum ‘thfVars (Γ,A,f) = FDOM fσ’
   (assume_tac o GSYM) >> 
   simp[thfVars_def]) >>
simp[] >> rw[] (* 9 *)
>- (irule vinst_cont_wf >>
  first_x_assum $ irule_at Any >>
   gs[wfvmap_def] >> rw[] (* 3 *)
   >- (irule PfDrv_cont_wf >>
      metis_tac[wfsigaxs_def])
   >> (irule wffVmap_ofFMAP_var_wf >>
      metis_tac[]))
>- (irule wffVmap_ofFMAP_var_wf >>
      metis_tac[wfcfVmap_def])
>- (irule wffVmap_ofFMAP_var_wf >>
    metis_tac[wfcfVmap_def])
>- (simp[vinst_cont_def] >>
   irule ofFMAP_FINITE >>
   simp[tfv_FINITE] >>
   rw[] (* 3 *)
   >- (‘FINITE (cont (Γ,A,f))’
       suffices_by simp[cont_def] >>
      irule PfDrv_cont_FINITE >> metis_tac[])
   >- (irule ofFMAP_FINITE >>
      simp[ffv_FINITE,fVars_FINITE]) >>
   irule ofFMAP_FINITE >>
  simp[ffv_FINITE,fVars_FINITE] >>
  irule Uof_FINITE_lemma >>
  simp[fVars_FINITE] >>
  metis_tac[Pf_assum_FINITE]) (* 5 *)
>- (irule ofFMAP_FINITE >>
   simp[ffv_FINITE] >>
   irule IMAGE_FINITE >>
   simp[fVars_FINITE])
>- (irule ofFMAP_FINITE >>  simp[ffv_FINITE] >>
    irule Uof_FINITE_lemma >>
    rw[] (* 2 *)
    >- (irule IMAGE_FINITE >> simp[fVars_FINITE]) >>
   irule IMAGE_FINITE >> metis_tac[Pf_assum_FINITE])
>- (rpt $ irule_at Any UNION_is_cont >>
   simp[ofFMAP_ffv_is_cont,vinst_cont_is_cont]) (*2*)
>- (irule $ GSYM Pf2Pf0_fVinsth_lemma >>
   last_assum $ irule_at Any >>
   gs[] >> rw[] (* 5 *)
   >- metis_tac[SUBSET_thfVars]
   >- metis_tac[ffv_SUBSET_cont_fVinsth]
   >- (qpat_x_assum ‘cont (fVinsth fσ (Γ,A,f)) = FDOM vσ’ (assume_tac o GSYM) >> simp[] >>
      irule PfDrv_concl_ffv_SUBSET >>
      last_x_assum $ irule_at Any >>
      qexists ‘assum (fVinsth fσ (Γ,A,f))’ >>
      ‘fVinst fσ f = concl (fVinsth fσ (Γ,A,f))’
       by simp[fVinsth_def,concl_def] >>
      ‘PfDrv (Σf,Σp,Σe) axs (fVinsth fσ (Γ,A,f))’
       suffices_by metis_tac[cont_assum_concl] >>
       irule PfDrv_fVinsth >> simp[])
   >- gs[wfsigaxs_def,wffsig_def,wfsig_def] >>
   metis_tac[PfDrv_concl_wff]) >>
irule IMAGE_eq_lemma >>
  rw[] >> simp[instf_def] >>
  irule $ GSYM Pf2Pf0_fVinsth_lemma >>
  last_assum $ irule_at Any >>
  gs[] >> rw[] (* 5 *)
  >- metis_tac[SUBSET_thfVars]
  >- metis_tac[ffv_assum_SUBSET_cont_fVinsth]
  >- (qpat_x_assum ‘cont (fVinsth fσ (Γ,A,f)) = FDOM vσ’ (assume_tac o GSYM) >> simp[] >>
      irule PfDrv_assum_ffv_SUBSET >>
      last_x_assum $ irule_at Any >>
      qexistsl
      [‘fVinst fσ f’,‘assum (fVinsth fσ (Γ,A,f))’] >>
      ‘fVinst fσ f = concl (fVinsth fσ (Γ,A,f))’
        by simp[fVinsth_def,concl_def] >>
      rw[] (* 2 *)
      >- (pop_assum (K all_tac) >>
         simp[fVinsth_def,assum_def]) >>
      ‘PfDrv (Σf,Σp,Σe) axs (fVinsth fσ (Γ,A,f))’
        suffices_by metis_tac[cont_assum_concl] >>
      irule PfDrv_fVinsth >> simp[])
  >- gs[wfsigaxs_def,wffsig_def,wfsig_def] >>
  metis_tac[PfDrv_assum_wff]
QED  


Theorem Uof_concl_assum_SUBSET_cont:
wfsigaxs Σ axs ∧ PfDrv Σ axs th ⇒
Uof ffv ({concl th} ∪ assum th) ⊆ cont th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[concl_def,assum_def,cont_def] >>
metis_tac[PfDrv_ffv_SUBSET_cont]
QED

Theorem gen_precise_maps_ex:
wfsigaxs Σ axs ∧
     Pf Σ axs pf ∧
     MEM th pf ∧
     wfvmap (FST Σ) hσ ∧
     wfcfVmap Σ fσ ∧
     thfVars (vinsth hσ (uniqify uσ th)) ⊆ FDOM fσ ∧
     cont th ⊆ FDOM hσ ∧
    uniqifn uσ (thfVars th) ⇒
∃uσ1 hσ1 fσ1.
 wfvmap (FST Σ) hσ1 ∧ wfcfVmap Σ fσ1 ∧
 thfVars (vinsth hσ1 (uniqify uσ1 th)) =
 FDOM fσ1 ∧
 cont th = FDOM hσ1 ∧
 uniqifn uσ1 (thfVars th) ∧
 (thfVars th) = FDOM uσ1 ∧
 (insth fσ hσ (uniqify uσ th)) =
 (insth fσ1 hσ1 (uniqify uσ1 th))
Proof
rw[] >>
qexists ‘DRESTRICT uσ (thfVars th)’ >>
simp[uniqifn_DRESTRICT] >> simp[FDOM_DRESTRICT]  >>
‘(thfVars th) ⊆ FDOM uσ’ by metis_tac[uniqifn_def] >>
simp[INTER_SUBSET_EQN] >>
‘(uniqify (DRESTRICT uσ (thfVars th)) th) =
(uniqify uσ th)’
 by (irule uniqify_DRESTRICT >> simp[SUBSET_DEF]) >>
simp[] >>
qexists ‘DRESTRICT hσ (cont th)’ >>
simp[FDOM_DRESTRICT] >>
‘wfvmap (FST Σ) (DRESTRICT hσ (cont th))’
 by (irule wfvmap_DRESTRICT >>
    simp[] >> irule PfDrv_cont_is_cont >>
    metis_tac[PfDrv_def]) >>
simp[INTER_SUBSET_EQN] >>
simp[insth_def]>>
‘(vinsth (DRESTRICT hσ (cont th))
               (uniqify uσ th)) =
 (vinsth hσ (uniqify uσ th))’
 by (irule vinsth_DRESTRICT1 >>
    simp[] >> simp[cont_uniqify] >>
    simp[Uof_ffv_uniqify] >>
    irule Uof_concl_assum_SUBSET_cont >>
    metis_tac[PfDrv_def]) >>
simp[] >>
qexists ‘DRESTRICT fσ
(thfVars (vinsth hσ (uniqify uσ th)))’>>
simp[FDOM_DRESTRICT,INTER_SUBSET_EQN] >>
simp[wfcfVmap_DRESTRICT] >>
simp[fVinsth_DRESTRICT]
QED

     

Theorem PfDrv_vinsth:
∀Σ axs th vσ.
       PfDrv Σ axs th ∧ wfvmap (FST Σ) vσ ∧
       cont th ⊆ FDOM vσ ⇒
       PfDrv Σ axs (vinsth vσ th)
Proof
rw[PfDrv_def] >>
drule_all_then assume_tac Pf_vinsth >>
first_x_assum $ irule_at Any >> gs[]
QED


Theorem vinsth_case_precise_maps_ex:
 wfsigaxs Σ axs ∧
     Pf Σ axs pf ∧
     MEM th pf ∧
     wfvmap (FST Σ) vσ ∧
     cont th ⊆ FDOM vσ ∧
     wfvmap (FST Σ) hσ ∧
     wfcfVmap Σ fσ ∧
     thfVars (vinsth hσ (uniqify uσ (vinsth vσ th))) ⊆ FDOM fσ ∧
     cont (vinsth vσ th) ⊆ FDOM hσ ∧
    uniqifn uσ (thfVars (vinsth vσ th)) ⇒
∃vσ1 uσ1 hσ1 fσ1.
 wfvmap (FST Σ) vσ1 ∧
 cont th = FDOM vσ1 ∧
 wfvmap (FST Σ) hσ1 ∧ wfcfVmap Σ fσ1 ∧
 thfVars (vinsth hσ1 (uniqify uσ1 (vinsth vσ1 th))) =
 FDOM fσ1 ∧
 cont (vinsth vσ1 th) = FDOM hσ1 ∧
 uniqifn uσ1 (thfVars (vinsth vσ1 th)) ∧
 (thfVars (vinsth vσ1 th)) = FDOM uσ1 ∧
 (insth fσ hσ (uniqify uσ (vinsth vσ th))) =
 (insth fσ1 hσ1 (uniqify uσ1 (vinsth vσ1 th)))
Proof
rw[] >>
qexists ‘DRESTRICT vσ (cont th)’ >> 
simp[FDOM_DRESTRICT,INTER_SUBSET_EQN] >>
‘wfvmap (FST Σ) (DRESTRICT vσ (cont th))’
 by (irule wfvmap_DRESTRICT >>
    simp[] >>
    irule PfDrv_cont_is_cont >> gs[PfDrv_def] >>
    metis_tac[]) >> simp[] >>
‘(vinsth (DRESTRICT vσ (cont th)) th) =
 vinsth vσ th’
 by (irule vinsth_DRESTRICT1 >> simp[SUBSET_REFL] >>
irule Uof_concl_assum_SUBSET_cont >>
metis_tac[PfDrv_def]) >>
gs[] >>
‘PfDrv Σ axs (vinsth vσ th)’
 by (irule PfDrv_vinsth >> gs[] >>
    metis_tac[PfDrv_def]) >>
irule gen_precise_maps_ex >> gs[] >>
metis_tac[PfDrv_def]
QED
    
Theorem IN_cont_FAPPLY_SUBSET_cont_vinst:
x ∈ cont th ∧ x ∈ FDOM vσ ⇒ tfv (vσ ' x) ⊆ cont (vinsth vσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[vinsth_def,cont_def,vinst_cont_def] >>
gs[ofFMAP_def,SUBSET_DEF,PULL_EXISTS] >>
metis_tac[]
QED
   
Theorem wfcod_o_vmap:
wfcod Σ (σ1:string # sort |-> term) ∧ wfcod Σ σ2 ∧
cstt σ2 ∧ wffsig Σ ∧
     (∀x. x ∈ FDOM σ1 ⇒ tfv (σ1 ' x) ⊆ FDOM σ2) ⇒
     wfcod Σ (o_vmap σ2 σ1)
Proof
rw[wfcod_def] >>
gs[FDOM_o_vmap] >>
drule_then assume_tac FAPPLY_o_vmap >> gs[] >>
irule $ cj 1 wft_tinst >>
gs[wffsig_def] >> gs[wfcod_def]
QED
     
Theorem ofFMAP_fVars_rn2fVmap:
  ofFMAP fVars (rn2fVmap uσ) A =
  IMAGE (fVrn uσ) (FDOM uσ ∩ A)
Proof
  rw[ofFMAP_def,IMAGE_DEF] >>
  rw[Once EXTENSION,EQ_IMP_THM] (* 2 *)
  >- (gs[FDOM_rn2fVmap] >>
     drule_then assume_tac FAPPLY_rn2fVmap >>
     Cases_on ‘a’ >>
     gs[fVrn_def,plainfV_def,fVars_def] >>
     qexists ‘(q,r)’ >> simp[fVrn_def]) >>
  simp[PULL_EXISTS] >>
  drule_then assume_tac FAPPLY_rn2fVmap >>
  Cases_on ‘x'’ >>
  gs[fVrn_def,plainfV_def,fVars_def,FDOM_rn2fVmap]>>
  qexists ‘(q,r)’ >> simp[fVars_def]
QED     
  
Theorem cont_vinsth:
cont (vinsth vσ th) = vinst_cont vσ (cont th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[cont_def,vinsth_def]
QED
  
Theorem sfv_vinst_cont_SUBSET_MONO:
wfvmap Σ vσ ∧ sfv s ⊆ ct ∧ ct ⊆ FDOM vσ ⇒
sfv (sinst vσ s) ⊆ vinst_cont vσ ct
Proof
simp[vinst_cont_def] >> rw[] >>
simp[SUBSET_DEF] >>
qspecl_then [‘s’,‘vσ’] assume_tac $ cj 2 tfv_sinst >>
rw[] >>
‘ cstt vσ ∧ sfv s ⊆ FDOM vσ ∧ no_bound vσ ’
 by (gs[SUBSET_DEF,wfvmap_def] >>
    metis_tac[wfcod_no_bound]) >> Cases_on ‘x’ >>
gs[] >>
simp[ofFMAP_def,PULL_EXISTS] >>
first_x_assum $ irule_at Any >> gs[SUBSET_DEF]
QED   


Theorem ffv_vinst_cont_SUBSET_MONO:
wfvmap Σ vσ ∧ ffv f ⊆ ct ∧ ct ⊆ FDOM vσ ⇒
ffv (finst vσ f) ⊆ vinst_cont vσ ct
Proof
simp[vinst_cont_def] >> rw[] >>
simp[SUBSET_DEF] >>
qspecl_then [‘f’,‘vσ’] assume_tac $ ffv_finst >>
rw[] >>
‘ cstt vσ ∧ ffv f ⊆ FDOM vσ ∧ no_bound vσ ’
 by (gs[SUBSET_DEF,wfvmap_def] >>
    metis_tac[wfcod_no_bound]) >> Cases_on ‘x’ >>
gs[] >>
simp[ofFMAP_def,PULL_EXISTS] >>
first_x_assum $ irule_at Any >> gs[SUBSET_DEF]
QED   

      

Theorem PfDrv_slfv_SUBSET_cont:
wfsigaxs Σ axs ∧
PfDrv Σ axs (Γ,A,f) ⇒ Uof fVslfv ({f} ∪ A) ⊆ Γ
Proof
rw[] >> gs[Uof_SUBSET] >> rw[] (* 2 *)
>- (irule SUBSET_TRANS >> qexists ‘ffv a’ >>
   simp[fVslfv_SUBSET_ffv] >>
   irule PfDrv_concl_ffv_SUBSET >>
    metis_tac[]) >>
irule SUBSET_TRANS >> qexists ‘ffv a’ >>
simp[fVslfv_SUBSET_ffv] >>
irule PfDrv_assum_ffv_SUBSET >>
metis_tac[]
QED
      



Theorem IMAGE_fVrn_fVrwinst_vinst_fVar:
     wfsigaxs Σ axs ∧
     PfDrv Σ axs th ∧ wfvmap (FST Σ) vσ ∧
     uniqifn uσ2 (thfVars th) ∧
     uniqifn uσ1 (FDOM uσ1) ∧
     IMAGE (vinst_fVar vσ) (thfVars th) = FDOM uσ1 ∧
     FDOM uσ2 = thfVars th ∧
     cont th = FDOM vσ ∧
     cont (vinsth vσ th) = FDOM hσ ⇒
     IMAGE
          (fVrn (fVrwinst vσ uσ1 hσ (uσ2:string # sort list |-> string)) ∘ vinst_fVar (o_vmap hσ vσ) ∘
           fVrn uσ2) (FDOM uσ2) ⊆
     IMAGE (vinst_fVar hσ) (IMAGE (fVrn uσ1) (FDOM uσ1))          
Proof
simp[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
Cases_on ‘x'’ >> rename [‘(P,sl)’] >>
simp[fVrn_def,vinst_fVar_def,FDOM_fVrnwinst] >>
‘∃x. (uσ2 ' (P,sl),MAP (sinst (o_vmap hσ vσ)) sl) =
                 vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 x) ∧ x ∈ thfVars th’
 by (qexists ‘(P,sl)’ >>
    simp[fVrn_def,vinst_fVar_def,FDOM_fVrnwinst]) >>
    ‘(∃x. (uσ2 ' (P,sl),MAP (sinst (o_vmap hσ vσ)) sl) =
                 vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 x) ∧ x ∈ thfVars th) ⇔ T’ by metis_tac[] >>
simp[] >> Cases_on ‘x’ >>
pop_assum (K all_tac) >>
‘uniqifn uσ2 (FDOM uσ2) ’ by metis_tac[] >>
‘(q,r) ∈ FDOM uσ2’ by metis_tac[] >>
drule_all_then assume_tac
(FAPPLY_fVrnwinst  |> INST_TYPE [alpha |-> “:string”]) >> gs[] >>
qexists ‘(vinst_fVar vσ (q,r))’ >>
simp[vinst_fVar_def,fVrn_def] >>
‘(q,MAP (sinst vσ) r) ∈ FDOM uσ1’
 by
 (qpat_x_assum ‘_ = FDOM uσ1’ (assume_tac o GSYM) >>
  simp[] >>
  qexists ‘(q,r)’ >> simp[vinst_fVar_def]) >> gs[]>>
simp[vinst_fVar_def] >>
gs[fVrn_def,vinst_fVar_def] >> 
simp[MAP_EQ_f,MAP_MAP_o] >> rw[] >>
irule $ GSYM $ cj 2 inst_o_vmap >>
qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
simp[] >> simp[cont_vinsth] >> 
‘sfv e ⊆ cont th’
 suffices_by
 (rw[] >> irule sfv_vinst_cont_SUBSET_MONO >>
 gs[] >> metis_tac[]) >>
irule SUBSET_TRANS >>
Cases_on ‘th’ >> Cases_on ‘r'’ >>
rename [‘(Γ,A,f)’] >>
qexists ‘Uof fVslfv ({f} ∪ A)’ >>
simp[cont_def] >> rw[] (* 2 *)
>- (simp[SUBSET_DEF,IN_Uof,IN_fVslfv,PULL_EXISTS] >>
   gs[IN_thfVars] >> TRY (metis_tac[])) >>
irule PfDrv_slfv_SUBSET_cont >>
metis_tac[]
QED

     
Theorem ex_SUBSET_ofFMAP:
∀a. a ∈ A ∧ a ∈ FDOM σ ∧ X ⊆ f (σ ' a) ⇒ X ⊆ ofFMAP f σ A
Proof
rw[SUBSET_DEF,ofFMAP_def,PULL_EXISTS] >>
metis_tac[]
QED



Theorem FAPPLY_o_fVmap1':
fv ∈ FDOM σ1 ⇒ o_fVmap σ2 σ1 ' fv = fVinst σ2 (σ1 ' fv)
Proof
Cases_on ‘fv’ >> metis_tac[FAPPLY_o_fVmap1]
QED


Theorem FAPPLY_plainfV_bmap:
∀i. i < LENGTH r ⇒
    (mk_bmap (REVERSE (MAP Bound (REVERSE (COUNT_LIST (LENGTH r)))))) ' i = Bound i
Proof
rw[] >> simp[rich_listTheory.MAP_REVERSE] >>
‘i < LENGTH (MAP Bound (COUNT_LIST (LENGTH r)))’
 by simp[rich_listTheory.LENGTH_COUNT_LIST] >> 
drule_then assume_tac FAPPLY_mk_bmap >> gs[] >>
gs[EL_MAP] >> irule rich_listTheory.EL_COUNT_LIST >>
simp[]
QED

Theorem tprpl_fix:
(∀t bmap.
(∀i. i ∈ FDOM bmap ⇒ bmap ' i = Bound i) ⇒
 tprpl bmap t = t) ∧
(∀s bmap.
(∀i. i ∈ FDOM bmap ⇒ bmap ' i = Bound i) ⇒
 sprpl bmap s = s)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tprpl_def,MAP_fix]
QED

Theorem fprpl_fix:
(∀f bmap.
(∀i. i ∈ FDOM bmap ⇒ bmap ' i = Bound i) ⇒
 fprpl bmap f = f)
Proof
Induct_on ‘f’ >> gs[fprpl_def,MAP_fix,tprpl_fix] >>
rw[] >>
first_x_assum irule >>
simp[FDOM_shift_bmap] >> rw[] >>
drule_then assume_tac FAPPLY_shift_bmap >>
first_x_assum $ qspecl_then [‘1’] assume_tac >>
‘1 + x = x + 1’ by simp[] >>
gs[] >>simp[tshift_def]
QED
 
Theorem fVinst_plainfV:
fv ∈ FDOM fσ ⇒
fVinst fσ (plainfV fv) = fσ ' fv
Proof
Cases_on ‘fv’ >> rw[plainfV_def,fVinst_def]  >>
irule fprpl_fix >> simp[FDOM_mk_bmap,rich_listTheory.LENGTH_COUNT_LIST] >>
rw[FAPPLY_plainfV_bmap]
QED



Theorem fVrn_fVrwinst:
(P:string,sl) ∈ FDOM uσ2 ∧ uniqifn uσ2 (FDOM uσ2) ⇒ 
fVrn
(fVrwinst vσ uσ1 hσ uσ2)
(vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P,sl))) =
(uσ1 ' (vinst_fVar vσ (P,sl)),
 MAP (sinst (o_vmap hσ vσ)) sl)
Proof
rw[fVrn_def,vinst_fVar_def] >>
gs[FDOM_fVrnwinst,vinst_fVar_def] (* 2 *)
>- (Cases_on ‘x’ >>
gs[FDOM_fVrnwinst,vinst_fVar_def,fVrn_def] >>
‘(P,sl) = (q,r)’
 by (irule uniqifn_INJ >> metis_tac[]) >>
gs[] >>
drule_all_then assume_tac
               (FAPPLY_fVrnwinst |> INST_TYPE [alpha |-> “:string”])>>
gs[fVrn_def,vinst_fVar_def]) >>
first_x_assum $ qspecl_then [‘(P,sl)’] assume_tac>>
gs[vinst_fVar_def,fVrn_def]
QED


Theorem ofFMAP_differ_2_SUBSET_lemma:
(∀a.  a ∈ A ∧ a ∈ FDOM σ1 ⇒
 ∃b. b ∈ B ∧ b ∈ FDOM σ2 ∧ σ1 ' a = σ2 ' b) 
⇒ ofFMAP f σ1 A ⊆ ofFMAP f σ2 B
Proof
simp[SUBSET_DEF,ofFMAP_def]  >>
metis_tac[]
QED





Theorem vinst_case_SUBSET_lemma:
  wfsigaxs Σ axs ∧
  PfDrv Σ axs (Γ,A,f) ∧
  wfvmap (FST Σ) vσ ∧
  cont (Γ,A,f) = FDOM vσ ∧
  wfvmap (FST Σ) hσ ∧
  wfcfVmap Σ fσ ∧
  thfVars
  (vinst_cont hσ (vinst_cont vσ Γ),
   IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A)),
   finst hσ (ffVrn uσ1 (finst vσ f))) =
  FDOM fσ
  ∧
  cont (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM hσ ∧
  uniqifn uσ1 (FDOM uσ1)∧
  thfVars (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM uσ1∧
  uniqifn uσ2 (thfVars (Γ,A,f))∧
  FDOM uσ2 = thfVars (Γ,A,f) ⇒
  ∀a. a = f ∨ a ∈ A ⇒ 
      ofFMAP ffv (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
             (fVars (finst (o_vmap hσ vσ) (ffVrn uσ2 a)))
             ⊆
             ofFMAP ffv fσ
             (fVars (finst hσ (ffVrn uσ1 (finst vσ a))))
Proof
  rw[] (* 2 *)
  >- (irule ofFMAP_differ_2_SUBSET_lemma >>
      simp[fVars_finst,PULL_EXISTS,
           FDOM_o_fVmap,FDOM_rn2fVmap,
           FDOM_fVrnwinst] >>
      ‘∀x. x ∈ fVars (ffVrn uσ2 a) ⇒
           ∃x'.
             x' ∈ fVars (ffVrn uσ1 (finst vσ a)) ∧
             vinst_fVar hσ x' ∈ FDOM fσ ∧
             o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)) '
                     (vinst_fVar (o_vmap hσ vσ) x) =
             fσ ' (vinst_fVar hσ x')’
        suffices_by metis_tac[] >> rw[] >>
      gs[thfVars_def,IMAGE_IMAGE] >>
      ‘{finst hσ (ffVrn uσ1 (finst vσ a))} ∪
       IMAGE (finst hσ ∘ ffVrn uσ1 ∘ finst vσ) A  =
       IMAGE  (finst hσ ∘ ffVrn uσ1 ∘ finst vσ) ({a} ∪ A) ’      by (simp[Once EXTENSION] >> metis_tac[]) >>
      pop_assum SUBST_ALL_TAC >>
      gs[Uof_IMAGE] >> 
      gs[fVars_ffVrn,fVars_finst,PULL_EXISTS] >>
      qexists ‘x'’ >>
      Cases_on ‘x'’ >>
      simp[] >>
      ‘vinst_fVar hσ (fVrn uσ1 (vinst_fVar vσ (q,r))) ∈ FDOM fσ’
        by
        (qpat_x_assum ‘_ = FDOM fσ’ (assume_tac o GSYM) >>
         simp[IN_Uof,fVars_finst,fVars_ffVrn,PULL_EXISTS]>>
         metis_tac[]) >> simp[] >>
      ‘(vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (q,r))) ∈
       FDOM (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))’
        by (simp[FDOM_rn2fVmap,FDOM_fVrnwinst] >>
            qexists ‘(q,r)’ >> simp[IN_Uof] >>
            metis_tac[]) >> simp[] >>
      drule_then assume_tac FAPPLY_o_fVmap1' >>
      gs[] >> gs[FDOM_rn2fVmap] >>
      drule_then assume_tac FAPPLY_rn2fVmap >>
      simp[] >>
      ‘(fVrn (fVrwinst vσ uσ1 hσ uσ2)
        (vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (q,r)))) =
       (uσ1 ' (vinst_fVar vσ (q,r)),MAP (sinst (o_vmap hσ vσ)) r)’
        by (irule fVrn_fVrwinst >> simp[] >>
            gs[IN_Uof] >> metis_tac[]) >> simp[] >>
      ‘(uσ1 ' (vinst_fVar vσ (q,r)),MAP (sinst (o_vmap hσ vσ)) r) =
       (vinst_fVar hσ (fVrn uσ1 (vinst_fVar vσ (q,r))))’
        by
        (simp[vinst_fVar_def,fVrn_def] >>
         ‘(q,MAP (sinst vσ) r) ∈ FDOM uσ1’
           by (qpat_x_assum ‘_ = FDOM uσ1’
               (assume_tac o GSYM) >>
               simp[IN_Uof] >>
               qexists ‘finst vσ a’ >>
               simp[fVars_finst] >> qexists ‘(q,r)’ >>
               simp[vinst_fVar_def]) >>
         simp[] >> simp[vinst_fVar_def,fVrn_def] >>
         simp[MAP_MAP_o,MAP_EQ_f] >>
         rw[] >> irule $ GSYM sinst_o_vmap >>
         qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
         qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
         simp[] >> simp[cont_vinsth] >> 
         ‘sfv e ⊆ cont (Γ,A,a) ’
           suffices_by
           (rw[] >> simp[cont_def] >>
            irule sfv_vinst_cont_SUBSET_MONO >>
            gs[cont_def] >> metis_tac[]) >>
         irule SUBSET_TRANS >>
         qexists ‘Uof fVslfv ({a} ∪ A)’ >>
         simp[cont_def] >> rw[] (* 2 *)
         >- (simp[SUBSET_DEF,IN_Uof,IN_fVslfv,PULL_EXISTS] >>
             gs[IN_thfVars,cont_def] >> TRY (metis_tac[])) >>
         irule PfDrv_slfv_SUBSET_cont >>
         metis_tac[]) >> 
      ‘(uσ1 ' (vinst_fVar vσ (q,r)),MAP (sinst (o_vmap hσ vσ)) r) ∈ FDOM fσ’
        by simp[] >>
      drule_then assume_tac fVinst_plainfV >>
      simp[]) >>
  irule ofFMAP_differ_2_SUBSET_lemma >>
  simp[fVars_finst,PULL_EXISTS,
       FDOM_o_fVmap,FDOM_rn2fVmap,
       FDOM_fVrnwinst] >>
  ‘∀x. x ∈ fVars (ffVrn uσ2 a) ⇒
       ∃x'.
         x' ∈ fVars (ffVrn uσ1 (finst vσ a)) ∧
         vinst_fVar hσ x' ∈ FDOM fσ ∧
         o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)) '
                 (vinst_fVar (o_vmap hσ vσ) x) =
         fσ ' (vinst_fVar hσ x')’
    suffices_by metis_tac[] >> rw[] >>
  gs[thfVars_def,IMAGE_IMAGE] >>
  ‘{finst hσ (ffVrn uσ1 (finst vσ f))} ∪
   IMAGE (finst hσ ∘ ffVrn uσ1 ∘ finst vσ) A  =
   IMAGE  (finst hσ ∘ ffVrn uσ1 ∘ finst vσ) ({f} ∪ A) ’      by (simp[Once EXTENSION] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  gs[Uof_IMAGE] >> 
  gs[fVars_ffVrn,fVars_finst,PULL_EXISTS] >>
  qexists ‘x'’ >>
  Cases_on ‘x'’ >>
  simp[] >>
  ‘vinst_fVar hσ (fVrn uσ1 (vinst_fVar vσ (q,r))) ∈ FDOM fσ’
    by
    (qpat_x_assum ‘_ = FDOM fσ’ (assume_tac o GSYM) >>
     simp[IN_Uof,fVars_finst,fVars_ffVrn,PULL_EXISTS]>>
     metis_tac[]) >> simp[] >>
  ‘(vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (q,r))) ∈
   FDOM (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))’
    by (simp[FDOM_rn2fVmap,FDOM_fVrnwinst] >>
        qexists ‘(q,r)’ >> simp[IN_Uof] >>
        metis_tac[]) >> simp[] >>
  drule_then assume_tac FAPPLY_o_fVmap1' >>
  gs[] >> gs[FDOM_rn2fVmap] >>
  drule_then assume_tac FAPPLY_rn2fVmap >>
  simp[] >>
  ‘(fVrn (fVrwinst vσ uσ1 hσ uσ2)
    (vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (q,r)))) =
   (uσ1 ' (vinst_fVar vσ (q,r)),MAP (sinst (o_vmap hσ vσ)) r)’
    by (irule fVrn_fVrwinst >> simp[] >>
        gs[IN_Uof] >> metis_tac[]) >> simp[] >>
  ‘(uσ1 ' (vinst_fVar vσ (q,r)),MAP (sinst (o_vmap hσ vσ)) r) =
   (vinst_fVar hσ (fVrn uσ1 (vinst_fVar vσ (q,r))))’
    by
    (simp[vinst_fVar_def,fVrn_def] >>
     ‘(q,MAP (sinst vσ) r) ∈ FDOM uσ1’
       by (qpat_x_assum ‘_ = FDOM uσ1’
           (assume_tac o GSYM) >>
           simp[IN_Uof] >> 
           qexists ‘finst vσ a’ >>
           simp[fVars_finst] >> rw[] (* 2 *)
           >- (disj2_tac >> metis_tac[]) >>
           qexists ‘(q,r)’ >>
           simp[vinst_fVar_def]) >>
     simp[] >> simp[vinst_fVar_def,fVrn_def] >>
     simp[MAP_MAP_o,MAP_EQ_f] >>
     rw[] >> irule $ GSYM sinst_o_vmap >>
     qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
     qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
     simp[] >> simp[cont_vinsth] >> 
     ‘sfv e ⊆ cont (Γ,A,f) ’
       suffices_by
       (rw[] >> simp[cont_def] >>
        irule sfv_vinst_cont_SUBSET_MONO >>
        gs[cont_def] >> metis_tac[]) >>
     irule SUBSET_TRANS >>
     qexists ‘Uof fVslfv ({f} ∪ A)’ >>
     simp[cont_def] >> rw[] (* 2 *)
     >- (simp[SUBSET_DEF,IN_Uof,IN_fVslfv,PULL_EXISTS] >>
         gs[IN_thfVars,cont_def] >> TRY (metis_tac[])) >>
     irule PfDrv_slfv_SUBSET_cont >>
     metis_tac[]) >> 
  ‘(uσ1 ' (vinst_fVar vσ (q,r)),MAP (sinst (o_vmap hσ vσ)) r) ∈ FDOM fσ’
    by simp[] >>
  drule_then assume_tac fVinst_plainfV >>
  simp[]
QED     





               
Theorem ofFMAP_SUBSET_UNION_lemma:
ofFMAP f σ1 A ⊆ ofFMAP g σ2 C ∧
ofFMAP f σ1 B ⊆ ofFMAP g σ2 D ⇒
ofFMAP f σ1 (A ∪ B) ⊆ ofFMAP g σ2 (C ∪ D)
Proof
rw[] >> gs[ofFMAP_def,SUBSET_DEF]>>
metis_tac[]
QED
        
Theorem ofFMAP_Uof_SUBSET_lemma2:
 (∀a. a ∈ s1 ⇒
 ∃b. b ∈ s2 ∧ ofFMAP f σ1 (g a) ⊆ ofFMAP f σ2 (g b)) ⇒ ofFMAP f σ1 (Uof g s1) ⊆ ofFMAP f σ2 (Uof g s2)
Proof
gs[SUBSET_DEF,ofFMAP_def,Uof_def,PULL_EXISTS] >>
rw[] >>metis_tac[]
QED



Theorem vinsth_case_SUBSET:
wfsigaxs Σ axs ∧
PfDrv Σ axs (Γ,A,f) ∧
wfvmap (FST Σ) vσ ∧
cont (Γ,A,f) = FDOM vσ ∧
wfvmap (FST Σ) hσ ∧
     wfcfVmap Σ fσ ∧
     thfVars
       (vinst_cont hσ (vinst_cont vσ Γ),
        IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A)),
        finst hσ (ffVrn uσ1 (finst vσ f))) =
     FDOM fσ
   ∧
     cont (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM hσ ∧
     uniqifn uσ1 (FDOM uσ1)∧
     thfVars (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM uσ1∧
     uniqifn uσ2 (thfVars (Γ,A,f))∧
     FDOM uσ2 = thfVars (Γ,A,f) ⇒
vinst_cont (o_vmap hσ vσ) Γ ∪
        ofFMAP ffv (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
          (Uof fVars
             ({finst (o_vmap hσ vσ) (ffVrn uσ2 f)} ∪
              IMAGE (finst (o_vmap hσ vσ)) (IMAGE (ffVrn uσ2) A))) ⊆
        vinst_cont hσ (vinst_cont vσ Γ) ∪
        ofFMAP ffv fσ
          (Uof fVars
             ({finst hσ (ffVrn uσ1 (finst vσ f))} ∪
              IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A))))
Proof
rw[] (* 2 *)
>- (‘vinst_cont (o_vmap hσ vσ) Γ ⊆
    vinst_cont hσ (vinst_cont vσ Γ)’
   suffices_by simp[SUBSET_DEF] >>
   simp[SUBSET_DEF,vinst_cont_def,ofFMAP_def,
        PULL_EXISTS,FDOM_o_vmap] >> rw[] >>
   Cases_on ‘a’ >>        
   drule_then assume_tac FAPPLY_o_vmap >>
   gs[] >>
   qspecl_then [‘(vσ ' (q,r))’,‘hσ’] assume_tac
   $ cj 1 tfv_sinst >>
   ‘cstt hσ ∧ tfv (vσ ' (q,r)) ⊆ FDOM hσ ∧ no_bound hσ’ by (gs[wfvmap_def] >> reverse (rw[]) (* 2 *)
      >- metis_tac[wfvmap_def,wfcod_no_bound] >>
      qpat_x_assum ‘_ = FDOM hσ’
       (assume_tac o GSYM) >> simp[] >>
      ‘(vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = vinsth vσ (Γ,A,f)’ by gs[vinsth_def] >>
      simp[] >> 
     irule IN_cont_FAPPLY_SUBSET_cont_vinst >>
     simp[cont_def]) >>
   gs[] >> Cases_on ‘x’ >> rgs[] >>
   gs[cont_def] >>
   first_assum $ irule_at Any >>
   first_assum $ irule_at Any >> simp[] >>
   gs[vinst_cont_def] >>
   qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
   simp[ofFMAP_def] >>
   metis_tac[]) >>
‘ofFMAP ffv (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
          (Uof fVars
             ({finst (o_vmap hσ vσ) (ffVrn uσ2 f)} ∪
              IMAGE (finst (o_vmap hσ vσ)) (IMAGE (ffVrn uσ2) A))) ⊆
        ofFMAP ffv fσ
          (Uof fVars
             ({finst hσ (ffVrn uσ1 (finst vσ f))} ∪
              IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A))))’
   suffices_by gs[SUBSET_DEF] >>
simp[Uof_UNION,Uof_Sing] >>
irule ofFMAP_SUBSET_UNION_lemma >> rw[] (* 2 *)
>- (irule vinst_case_SUBSET_lemma >>
   metis_tac[]) >>
irule ofFMAP_Uof_SUBSET_lemma2 >>
simp[IMAGE_IMAGE,PULL_EXISTS] >> rw[] >>
qexists ‘x'’ >> simp[] >>
irule vinst_case_SUBSET_lemma >>
metis_tac[]
QED

Definition wffVsl_def:
wffVsl Σf sl ⇔
∃vl. wfvl Σf vl False ∧ vl2sl vl = sl ∧ ALL_DISTINCT vl ∧ okvnames vl
End

        
Theorem Pf2Pf0_vinst_lemma1:
∀Γ A f. PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ∧
        wfvmap (FST Σ) vσ ∧
        cont (Γ,A,f) = FDOM vσ ∧ wfvmap (FST Σ) hσ ∧
        wffVmap Σ fσ ∧
        thfVars
          (vinst_cont hσ (vinst_cont vσ Γ),
           IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A)),
           finst hσ (ffVrn uσ1 (finst vσ f))) =
        FDOM fσ ∧
        cont (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM hσ ∧
        uniqifn uσ1 (FDOM uσ1) ∧
        thfVars (vinst_cont vσ Γ,IMAGE (finst vσ) A,finst vσ f) = FDOM uσ1 ∧
        uniqifn uσ2 (thfVars (Γ,A,f)) ∧
        FDOM uσ2 = thfVars (Γ,A,f) ⇒
        ∀a. a = f ∨ a ∈ A ⇒
    fVinst fσ (finst hσ (ffVrn uσ1 (finst vσ a))) =
    fVinst (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
     (finst (o_vmap hσ vσ) (ffVrn uσ2 a))
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >> rename [‘(Σf,Σp,Σe)’] >>
rw[] (* 2 *)
>- (‘fVinst (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
          (finst (o_vmap hσ vσ) (ffVrn uσ2 a)) =
    fVinst fσ (fVinst (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))
               (finst (o_vmap hσ vσ) (ffVrn uσ2 a)))’
     by (irule $ GSYM fVar_prpl_o_fVmap >>
        first_x_assum $ irule_at Any >> 
        gs[wfsigaxs_def,wfsig_def,wffsig_def] >>
        irule wffVmap_rn2fVmap1 >>
        simp[FDOM_fVrnwinst] >>
        cheat (*wf of rn*)) >>
    simp[] >>
    ‘ffv a ⊆ FDOM vσ’
     by (qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
         gs[cont_def] >>
         irule SUBSET_TRANS >>
         qexists ‘Uof ffv ({a} ∪ A)’ >> rw[] (* 2 *)
         >- (simp[SUBSET_DEF,Uof_def] >> metis_tac[]) >>
         irule PfDrv_ffv_SUBSET_cont >>
         qexistsl [‘axs’,‘(Σf,Σp,Σe)’] >>
         gs[wfsigaxs_def,wfsig_def]) >>
    ‘(fVinst (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))
             (finst (o_vmap hσ vσ) (ffVrn uσ2 a))) =
      ffVrn (fVrwinst vσ uσ1 hσ uσ2) (finst (o_vmap hσ vσ) (ffVrn uσ2 a))’
      by (irule $ GSYM ffVrn_fVinst >>
         rw[] >> irule $ GSYM wff_subfm_fVar_LENGTH >>
         first_assum $ irule_at Any >>
         qexists ‘(Σf,Σp,Σe)’ >>
         irule wff_finst >> gs[wfsigaxs_def,wfsig_def] >>
         ‘wfvmap Σf (o_vmap hσ vσ)’
           by (rw[wfvmap_def] (* 2 *)
           >- (irule o_vmap_cstt >> gs[wfvmap_def] >>
               simp[complete_FDOM_is_cont] >> rw[] >>
               TRY (metis_tac[wfcod_no_bound]) (* 2 *)
               >- (qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
                  qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
                  gs[] >> gs[GSYM vinsth_def] >>
                  irule IN_cont_FAPPLY_SUBSET_cont_vinst >>
                  gs[]) >>
               metis_tac[PfDrv_cont_is_cont]) >>
           irule wfcod_o_vmap >>
           gs[wfvmap_def] >> rw[] >>
           TRY (metis_tac[wfcod_no_bound]) (* 2 *)
           >- (qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
                  qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
                  gs[] >> gs[GSYM vinsth_def] >>
                  irule IN_cont_FAPPLY_SUBSET_cont_vinst >>
                  gs[]) >>
           gs[wffsig_def]) >>
         drule_then assume_tac wfvmap_presname >> simp[] >>
         gs[wfvmap_def] >> simp[ffv_ffVrn,FDOM_o_vmap] >>
         ‘wff (Σf,Σp,Σe) (ffVrn uσ2 a)’
           by cheat (*done if have wf rn but can be proved directly*) >>
         simp[]) >>
    simp[] >> AP_TERM_TAC >> irule Pf2Pf0_vinst_lemma >>
    gs[] >> gs[SUBSET_thfVars] >> rw[] (* 2 *)
    >- (qpat_x_assum ‘_ = FDOM uσ1’ (assume_tac o GSYM) >>
       simp[thfVars_def] >> irule SUBSET_one_Uof >>
       qexists ‘finst vσ a’ >> simp[] >>
       simp[fVars_finst]) >>
    qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
    gs[cont_def] >>
    irule ffv_vinst_cont_SUBSET_MONO >> simp[] >>
    metis_tac[]) >>
‘fVinst (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
 (finst (o_vmap hσ vσ) (ffVrn uσ2 a)) =
 fVinst fσ (fVinst (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))
            (finst (o_vmap hσ vσ) (ffVrn uσ2 a)))’
  by (irule $ GSYM fVar_prpl_o_fVmap >>
      first_x_assum $ irule_at Any >> 
      gs[wfsigaxs_def,wfsig_def,wffsig_def] >>
      cheat (*wf of rn*)) >>
simp[] >>
‘ffv a ⊆ FDOM vσ’
  by (qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
      gs[cont_def] >>
      irule SUBSET_TRANS >>
      qexists ‘Uof ffv ({f} ∪ A)’ >> rw[] (* 2 *)
      >- (simp[SUBSET_DEF,Uof_def] >> metis_tac[]) >>
      irule PfDrv_ffv_SUBSET_cont >>
      qexistsl [‘axs’,‘(Σf,Σp,Σe)’] >>
      gs[wfsigaxs_def,wfsig_def]) >>
‘(fVinst (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))
  (finst (o_vmap hσ vσ) (ffVrn uσ2 a))) =
 ffVrn (fVrwinst vσ uσ1 hσ uσ2) (finst (o_vmap hσ vσ) (ffVrn uσ2 a))’
  by (irule $ GSYM ffVrn_fVinst >>
      rw[] >> irule $ GSYM wff_subfm_fVar_LENGTH >>
      first_assum $ irule_at Any >>
      qexists ‘(Σf,Σp,Σe)’ >>
      irule wff_finst >> gs[wfsigaxs_def,wfsig_def] >>
      ‘wfvmap Σf (o_vmap hσ vσ)’
        by (rw[wfvmap_def] (* 2 *)
            >- (irule o_vmap_cstt >> gs[wfvmap_def] >>
                simp[complete_FDOM_is_cont] >> rw[] >>
                TRY (metis_tac[wfcod_no_bound]) (* 2 *)
                >- (qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
                    qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
                    gs[] >> gs[GSYM vinsth_def] >>
                    irule IN_cont_FAPPLY_SUBSET_cont_vinst >>
                    gs[]) >>
                metis_tac[PfDrv_cont_is_cont]) >>
            irule wfcod_o_vmap >>
            gs[wfvmap_def] >> rw[] >>
            TRY (metis_tac[wfcod_no_bound]) (* 2 *)
            >- (qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
                qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
                gs[] >> gs[GSYM vinsth_def] >>
                irule IN_cont_FAPPLY_SUBSET_cont_vinst >>
                gs[]) >>
            gs[wffsig_def]) >>
      drule_then assume_tac wfvmap_presname >> simp[] >>
      gs[wfvmap_def] >> simp[ffv_ffVrn,FDOM_o_vmap] >>
      ‘wff (Σf,Σp,Σe) (ffVrn uσ2 a)’
        by cheat (*done if have wf rn but can be proved directly*) >>
      simp[]) >>
simp[] >> AP_TERM_TAC >> irule Pf2Pf0_vinst_lemma >>
gs[] >> gs[SUBSET_thfVars] >> rw[] (* 2 *)
>- (qpat_x_assum ‘_ = FDOM uσ1’ (assume_tac o GSYM) >>
    simp[thfVars_def] >> irule SUBSET_one_Uof >>
    qexists ‘finst vσ a’ >> simp[] >>
    simp[fVars_finst]) >>
qpat_x_assum ‘_ = FDOM hσ’ (assume_tac o GSYM) >>
gs[cont_def] >>
irule ffv_vinst_cont_SUBSET_MONO >> simp[] >>
metis_tac[]
QED   
      



Theorem main_vinsth_case:
 wfsigaxs Σ axs ∧
   Pf Σ axs pf ∧
   (Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ⇒
   ∀th.
     MEM th pf ⇒
     ∀vσ fσ uσ.
       wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
       thfVars (vinsth vσ (uniqify uσ th)) ⊆ FDOM fσ ∧
       cont th ⊆ FDOM vσ ∧ uniqifn uσ (thfVars th) ⇒
       Pf0Drv Σ aths (insth fσ vσ (uniqify uσ th)))∧
   MEM th pf ∧
   wfvmap (FST Σ) vσ ∧
   cont th ⊆ FDOM vσ ∧
   Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ∧
   wfvmap (FST Σ) vσ' ∧
   wfcfVmap Σ fσ ∧
   thfVars (vinsth vσ' (uniqify uσ (vinsth vσ th))) ⊆ FDOM fσ ∧
   cont (vinsth vσ th) ⊆ FDOM vσ' ∧
   uniqifn uσ (thfVars (vinsth vσ th)) ⇒
   Pf0Drv Σ aths (insth fσ vσ' (uniqify uσ (vinsth vσ th)))
Proof
rpt strip_tac >> gs[] >>
first_x_assum $ drule_then assume_tac >>
rename [‘cont (vinsth vσ th) ⊆ FDOM hσ’] >>
drule_all_then assume_tac
vinsth_case_precise_maps_ex >>
pop_assum strip_assume_tac >> gs[] >>
qpat_x_assum ‘wfvmap (FST Σ) vσ’ (K all_tac) >>
qpat_x_assum ‘FDOM vσ1 ⊆ FDOM vσ’ (K all_tac) >>
qpat_x_assum ‘wfvmap (FST Σ) hσ’ (K all_tac) >>
qpat_x_assum ‘wfcfVmap Σ fσ’ (K all_tac) >>
qpat_x_assum ‘thfVars (vinsth hσ (uniqify uσ (vinsth vσ th))) ⊆ FDOM fσ’ (K all_tac) >>
qpat_x_assum ‘cont (vinsth vσ th) ⊆ FDOM hσ’
(K all_tac) >>
qpat_x_assum ‘uniqifn uσ (thfVars (vinsth vσ th))’
(K all_tac) >>
pop_assum (K all_tac) >>
rename [‘Pf0Drv Σ aths (insth fσ hσ (uniqify uσ1 (vinsth vσ th)))’] >>
‘∃uσ2:string # sort list |-> string. uniqifn uσ2 (thfVars th) ∧
       FDOM uσ2 = (thfVars th)’
  by cheat >> 
first_x_assum
(qspecl_then
[‘o_vmap hσ vσ’,
‘o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))’,
‘uσ2’] assume_tac) >>
‘Pf0Drv Σ aths
          (insth (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
             (o_vmap hσ vσ) (uniqify uσ2 th))’
 by             
 (first_x_assum irule >>
 simp[FDOM_o_fVmap,FDOM_rn2fVmap,FDOM_fVrnwinst,
      FDOM_o_vmap] >>
 ‘wfvmap (FST Σ) (o_vmap hσ vσ)’
  by (rw[wfvmap_def] (* 2 *)
     >- (irule o_vmap_cstt >>
        rw[] (* 6 *)
        >- (‘tfv (vσ ' x) ⊆ cont (vinsth vσ th)’
             suffices_by metis_tac[] >>
           irule IN_cont_FAPPLY_SUBSET_cont_vinst>>
           simp[])
        >- (simp[complete_FDOM_is_cont] >>
           irule Pf_cont_is_cont >>
           Cases_on ‘th’ >> Cases_on ‘r’ >>
           gs[cont_def] >> metis_tac[])
        >- gs[wfvmap_def]
        >- gs[wfvmap_def]
        >> metis_tac[wfvmap_def,wfcod_no_bound]) >>
     irule wfcod_o_vmap >>
     gs[wfvmap_def] >>
     Cases_on ‘Σ’ >> Cases_on ‘r’ >>
     gs[wfsigaxs_def,wfsig_def,wffsig_def] >>
     rw[] >>
     ‘tfv (vσ ' x) ⊆ cont (vinsth vσ th)’
      suffices_by metis_tac[] >>
     irule IN_cont_FAPPLY_SUBSET_cont_vinst >>
     simp[]) >> simp[] >>
 ‘wfcfVmap Σ (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))’
   by
   (rw[wfcfVmap_def] (* 2 *)
   >- (Cases_on ‘Σ’ >> Cases_on ‘r’ >>
      irule wffVmap_o_fVmap >>
      gs[wfsigaxs_def,wfsig_def,wffsig_def] >>
      gs[wfcfVmap_def] >> cheat
      (*need wffVmap of rn2fVmap*)) >>
   irule cfVmap_o_fVmap >> gs[wfcfVmap_def] >>
   simp[FDOM_rn2fVmap,FDOM_fVrnwinst] >>
   gs[thfVars_vinsth,thfVars_uniqify] >>
   simp[ofFMAP_fVars_rn2fVmap,FDOM_fVrnwinst] >>
   simp[IMAGE_IMAGE] >>
   ‘IMAGE
       (fVrn (fVrwinst vσ uσ1 hσ uσ2) ∘ vinst_fVar (o_vmap hσ vσ) ∘ fVrn uσ2)
       (FDOM uσ2) ⊆ IMAGE (vinst_fVar hσ) (IMAGE (fVrn uσ1) (FDOM uσ1))’
    suffices_by simp[] >>
   irule IMAGE_fVrn_fVrwinst_vinst_fVar >>
   simp[] >> qexistsl [‘axs’,‘th’,‘Σ’] >>
   simp[] >> metis_tac[PfDrv_def]) >>
 simp[] >>
 simp[thfVars_vinsth,thfVars_uniqify,IMAGE_IMAGE])>>
qpat_x_assum ‘_ ⇒ _’ (K all_tac) >>
Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘(Γ,A,f)’] >>
gs[uniqify_def,insth_def,vinsth_def,fVinsth_def] >>
drule_then assume_tac Pf0Drv_cont_SUBSET_cong >>
first_x_assum irule >>
‘vinst_cont (o_vmap hσ vσ) Γ ∪
        ofFMAP ffv (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
          (Uof fVars
             ({finst (o_vmap hσ vσ) (ffVrn uσ2 f)} ∪
              IMAGE (finst (o_vmap hσ vσ)) (IMAGE (ffVrn uσ2) A))) ⊆
        vinst_cont hσ (vinst_cont vσ Γ) ∪
        ofFMAP ffv fσ
          (Uof fVars
             ({finst hσ (ffVrn uσ1 (finst vσ f))} ∪
              IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A))))’
 by (irule vinsth_case_SUBSET >>
    simp[cont_def] >> metis_tac[PfDrv_def]) >>
 simp[]  >>
 ‘fVinst (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2)))
          (finst (o_vmap hσ vσ) (ffVrn uσ2 f)) =
        fVinst fσ (finst hσ (ffVrn uσ1 (finst vσ f)))’
  by (irule $ GSYM Pf2Pf0_vinst_lemma1 >>
     simp[] >>
     qexistsl [‘A’,‘axs’,‘f’,‘Γ’,‘Σ’] >> simp[] >>
     metis_tac[PfDrv_def,wfcfVmap_def]) >> simp[]>>
 ‘IMAGE (fVinst (o_fVmap fσ (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))))
          (IMAGE (finst (o_vmap hσ vσ)) (IMAGE (ffVrn uσ2) A)) =
        IMAGE (fVinst fσ)
          (IMAGE (finst hσ) (IMAGE (ffVrn uσ1) (IMAGE (finst vσ) A)))’
  by (rw[IMAGE_IMAGE]>>
     irule IMAGE_eq_lemma >>
     rw[] >> irule $ GSYM Pf2Pf0_vinst_lemma1 >>
     metis_tac[PfDrv_def,wfcfVmap_def]) >> simp[] >>
 rw[] (* 5 *)
 >- (irule vinst_cont_wf >>
  first_x_assum $ irule_at Any >>
   gs[wfvmap_def] >> rw[] >>
   ‘PfDrv Σ axs (Γ,A,f)’ by metis_tac[PfDrv_def] >>
   drule_then assume_tac PfDrv_vinsth >>
   first_x_assum $ qspecl_then [‘vσ’] assume_tac>>
   gs[wfvmap_def] >> irule PfDrv_cont_wf' >>
   first_assum $ irule_at Any >>
   Cases_on ‘Σ’ >> Cases_on ‘r’ >>
   rename [‘(Σf,Σp,Σe)’] >> simp[]>>
   gs[vinsth_def] >>
   first_assum $ irule_at Any >>
   metis_tac[wfsigaxs_def])
>- (irule wffVmap_ofFMAP_var_wf >>
    Cases_on ‘Σ’ >> Cases_on ‘r’ >>
    rename [‘(Σf,Σp,Σe)’] >> simp[]>>
    metis_tac[wfcfVmap_def])
>- (simp[vinst_cont_def] >>
   irule ofFMAP_FINITE >>
   simp[tfv_FINITE] >>
   rw[]     >>
   irule ofFMAP_FINITE >>
  simp[ffv_FINITE] >>
  metis_tac[PfDrv_cont_FINITE,cont_def])
>- (irule ofFMAP_FINITE >>  simp[ffv_FINITE] >>
    irule Uof_FINITE_lemma >>
    simp[fVars_FINITE,IMAGE_IMAGE] >>
    irule IMAGE_FINITE >>
    metis_tac[Pf_assum_FINITE,assum_def]) >>
simp[Uof_UNION,Uof_Sing,ofFMAP_UNION] >>
rpt $ irule_at Any UNION_is_cont >>
simp[ofFMAP_ffv_is_cont,vinst_cont_is_cont]
QED   
   

Theorem gen_precise_maps_ex1:
wfsigaxs Σ axs ∧ PfDrv Σ axs th ∧ wfvmap (FST Σ) hσ ∧
     wfcfVmap Σ fσ ∧ thfVars (vinsth hσ (uniqify uσ th)) ⊆ FDOM fσ ∧
     cont th ⊆ FDOM hσ ∧ uniqifn uσ (thfVars th) ⇒
     ∃uσ1 hσ1 fσ1.
       wfvmap (FST Σ) hσ1 ∧ wfcfVmap Σ fσ1 ∧
       thfVars (vinsth hσ1 (uniqify uσ1 th)) = FDOM fσ1 ∧
       cont th = FDOM hσ1 ∧ uniqifn uσ1 (thfVars th) ∧
       thfVars th = FDOM uσ1 ∧
       insth fσ hσ (uniqify uσ th) = insth fσ1 hσ1 (uniqify uσ1 th)
Proof
metis_tac[PfDrv_def,gen_precise_maps_ex]
QED       




Theorem Pf0Drv_gen1:
  Pf0Drv Σ aths th ∧ wfs (FST Σ) s ∧ sfv s ⊆ cont th ∧
     (x,s) ∉ genavds th ⇒
     Pf0Drv Σ aths (gen (x,s) th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[cont_def] >>
metis_tac[Pf0Drv_gen]
QED
        





   
Theorem tinst_FUPDATE_as_trename:
(∀tm σ n s nn.
   (nn,s) ∉ FDOM σ ∧
  (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ⇒
  tinst (σ |+ ((n,s),Var nn (sinst σ s))) tm =
  tinst σ (trename (n,s) nn tm)) ∧
(∀st σ n s nn.
   (nn,s) ∉ FDOM σ ∧
  (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ⇒
  sinst (σ |+ ((n,s),Var nn (sinst σ s))) st =
  sinst σ (srename (n,s) nn st))  
Proof
ho_match_mp_tac better_tm_induction >>
gs[tinst_def,trename_alt,MAP_MAP_o,MAP_EQ_f,
   PULL_EXISTS] >>
rw[] (* 4 *) >> TRY (metis_tac[]) >>
rw[] (* 3 *)
>- (‘srename (n,s) nn st = st’
      by (irule $ cj 2 trename_fix >>
          metis_tac[]) >> simp[] >>
   irule $ cj 2 fmap_fv_inst_eq>>
   rw[fmap_EXT]) >> 
gs[] >>
‘srename (n,s) nn st = st’
  by (irule $ cj 2 trename_fix >>
      metis_tac[]) >> simp[] >>
simp[FAPPLY_FUPDATE_THM] >>
‘¬(s0 = n ∧ st = s)’ by metis_tac[] >> simp[]      
QED





   
Theorem finst_FUPDATE_as_frename:
(∀f σ n s nn.
   (nn,s) ∉ FDOM σ ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
  finst (σ |+ ((n,s),Var nn (sinst σ s))) f =
  finst σ (frename (n,s) nn f))
Proof
Induct_on ‘f’ >>
gs[finst_def,frename_alt,MAP_MAP_o,MAP_EQ_f,
   PULL_EXISTS] >> rw[] >> TRY (metis_tac[])
>> metis_tac[tinst_FUPDATE_as_trename]
QED





Theorem ffVrn_fabs:
∀f i v.
ffVrn uσ (fabs v i f) = fabs v i (ffVrn uσ f)
Proof
Induct_on ‘f’ >> gs[ffVrn_def,fabs_def] >>
rw[fabs_def]
QED
        
Theorem ffVrn_mk_FALL:
ffVrn uσ (mk_FALL n s f) =  mk_FALL n s (ffVrn uσ f)
Proof
rw[mk_FALL_def,abst_def,ffVrn_def,ffVrn_fabs]
QED


Theorem uniqify_gen:
uniqify uσ (gen v th) = gen v (uniqify uσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> rename [‘(Γ,A,f)’]>>
Cases_on ‘v’ >> rename [‘(n,s)’] >>
gs[uniqify_def,gen_def,ffVrn_mk_FALL]
QED 

(*    

Definition gthrename_def:
gthrename (n,s) nn (Γ,A,f) =
(Γ DELETE (n,s) ∪ {(nn,s)},A,
 frename (n,s) nn f)
End 
*)

  
Theorem vinsth_gen:
PfDrv Σ axs (Γ,A,f)  ∧ wfsigaxs Σ axs ∧
sfv s ⊆ Γ ∧ wfvmap (FST Σ) vσ ∧ 
FDOM vσ = cont (gen (x,s) (Γ,A,f)) ∧
(∀s. (nn,s) ∉ ofFMAP tfv vσ (FDOM vσ)) ∧
(x,s) ∉ genavds (Γ,A,f) ⇒
vinsth vσ (gen (x,s) (Γ,A,f) ) =
gen (nn,sinst vσ s)
(vinsth (vσ |+ ((x,s),Var nn (sinst vσ s))) (Γ,A,f) )
Proof
gs[vinsth_def,gen_def] >>
reverse (rw[]) (* 3 *)
>- (simp[mk_FALL_def,abst_def] >>
irule $ GSYM finst_fabs >>
simp[cont_def] >>
drule_all_then assume_tac PfDrv_concl_ffv_SUBSET >>
‘ffv f ∪ sfv s DELETE (x,s) ⊆ Γ DELETE (x,s)’
 by (gs[SUBSET_DEF] >> metis_tac[]) >>
simp[] >> gs[NOTIN_genavds] >>
rw[] >> gs[SUBSET_DEF] >> TRY (metis_tac[]) (* 2 *)
>> (gs[ofFMAP_def,cont_def] >> metis_tac[]))
>- (irule IMAGE_eq_lemma >> rw[] >>
   irule fmap_ffv_finst_eq >>
   simp[FDOM_FUPDATE,cont_def] >>
   gs[NOTIN_genavds] >>
   drule_all_then assume_tac PfDrv_assum_ffv_SUBSET>>
   gs[] >> rw[] (* 2 *)
   >- (‘x' ≠ (x,s)’ by metis_tac[] >>
      simp[FAPPLY_FUPDATE_THM]) >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
gs[vinst_cont_def] >>
irule $ iffLR SUBSET_ANTISYM_EQ >> rw[] (* 2 *)
>- (‘(nn,sinst vσ s) ∉ ofFMAP tfv vσ (Γ DELETE (x,s))’
    by gs[ofFMAP_def,cont_def] >>
   ‘ofFMAP tfv vσ (Γ DELETE (x,s)) ⊆
        ofFMAP tfv (vσ |+ ((x,s),Var nn (sinst vσ s))) Γ’ suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
irule ofFMAP_differ_2_SUBSET_lemma >>
simp[cont_def,FAPPLY_FUPDATE_THM] >> rw[] >>
qexists ‘a’ >> simp[]) >>
gs[SUBSET_DEF,ofFMAP_def,cont_def,PULL_EXISTS] >>
rw[] (* 2 *)
>- (gs[FAPPLY_FUPDATE_THM] >>
qspecl_then [‘s’,‘vσ’] assume_tac $ cj 2 tfv_sinst >>
‘cstt vσ ∧ sfv s ⊆ FDOM vσ ∧ no_bound vσ’
by (gs[wfvmap_def,SUBSET_DEF] >>
   metis_tac[tm_tree_WF,wfcod_no_bound]) >>
gs[] >> Cases_on ‘x'’ >> gs[] >>
qexists ‘(n0,st0)’ >> simp[] >>
CCONTR_TAC >> gs[]>>metis_tac[tm_tree_WF]) >>
gs[FAPPLY_FUPDATE_THM] >> metis_tac[]
QED

Theorem vinsth_gen1:
PfDrv Σ axs th  ∧ wfsigaxs Σ axs ∧
sfv s ⊆ cont th ∧ wfvmap (FST Σ) vσ ∧ 
FDOM vσ = cont (gen (x,s) th) ∧
(∀s. (nn,s) ∉ ofFMAP tfv vσ (FDOM vσ)) ∧
(x,s) ∉ genavds th ⇒
vinsth vσ (gen (x,s) th ) =
gen (nn,sinst vσ s)
(vinsth (vσ |+ ((x,s),Var nn (sinst vσ s))) th )
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[cont_def] >>
metis_tac[vinsth_gen] 
QED

 

        
 


Theorem fVinsth_gen:
PfDrv Σ axs th ∧ wfsigaxs Σ axs ∧
(v ∉ ofFMAP ffv fσ (FDOM fσ) ∪ genavds th) ∧
FDOM fσ = thfVars th ⇒
fVinsth fσ (gen v th) = gen v (fVinsth fσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> 
rename [‘(Γ,A,f)’] >> Cases_on ‘v’ >>
rename [‘(gen (n,s) (Γ,A,f))’] >>
gs[gen_def,fVinsth_def,mk_FALL_def] >>
simp[abst_def,fVinst_def] >>
strip_tac >>
‘fVinst fσ (fabs (n,s) 0 f) = fabs (n,s) 0 (fVinst fσ f)’ by
(irule fVar_prpl_fabs1 >>
gs[ofFMAP_def,thfVars_def] >> rw[] (* 3 *)
>- metis_tac[]
>- (gs[NOTIN_genavds] >>
   drule_all_then assume_tac PfDrv_concl_ffv_SUBSET>>
   gs[SUBSET_DEF] >> metis_tac[]) >>
gs[NOTIN_genavds,IN_fVslfv] >>
metis_tac[]) >> simp[] >>
irule $ iffLR  SUBSET_ANTISYM_EQ >> rw[] (* 3 *)
>- gs[SUBSET_DEF]
>- (rw[Uof_UNION,Uof_Sing,fVars_def,fVars_fabs] >>
   ‘(n,s) ∉ ofFMAP ffv fσ (fVars f ∪ Uof fVars A)’
    suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
   gs[thfVars_def,Uof_UNION,Uof_Sing]) >>
simp[Uof_UNION,Uof_Sing,fVars_def,fVars_fabs] >>
‘(n,s) ∉ ofFMAP ffv fσ (fVars f ∪ Uof fVars A)’
    suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
   gs[thfVars_def,Uof_UNION,Uof_Sing]   
QED   


Theorem ffv_ffVrn1:
ffv o  (ffVrn uσf) = ffv
Proof
rw[FUN_EQ_THM,ffv_ffVrn]
QED

Theorem slfv_SND_fVrn:
(slfv ∘ SND ∘ fVrn uσ) = slfv o SND
Proof
 rw[FUN_EQ_THM] >> Cases_on ‘x’ >>Cases_on ‘x'’ >>
 rw[slfv_def,fVrn_def]
QED   
  
Theorem slfv_fVrn:
slfv (SND (fVrn uσ fv)) = slfv (SND fv)
Proof
‘(slfv ∘ SND ∘ fVrn uσ) fv = (slfv o SND) fv’
 by REWRITE_TAC[slfv_SND_fVrn] >>
gs[]
QED


Theorem genavds_uniqify:
genavds (uniqify uσ th) = genavds th
Proof 
Cases_on ‘th’ >> Cases_on ‘r’ >>
simp[genavds_def,uniqify_def,cont_def,concl_def,
assum_def,Uof_UNION,Uof_Sing,Uof_IMAGE,ffv_ffVrn1,
 fVars_ffVrn,slfv_SND_fVrn] >>
‘Uof (slfv ∘ SND) (Uof (fVars ∘ ffVrn uσ) q') =
 Uof (slfv ∘ SND) (Uof fVars q')’
 by (irule $ iffLR SUBSET_ANTISYM_EQ >> rw[] (*2 *)
    >- (rw[SUBSET_DEF,IN_Uof_Uof] >>
       gs[fVars_ffVrn,slfv_SND_fVrn] >>
       gs[slfv_fVrn] >>
       metis_tac[]) >>
    rw[SUBSET_DEF,IN_Uof_Uof,fVars_ffVrn,PULL_EXISTS,
      slfv_fVrn]) >>
 simp[]
QED       
             
         
Theorem fVars_mk_FALL:
fVars (mk_FALL n s b) = fVars b
Proof
rw[mk_FALL_def,abst_def,fVars_fabs,fVars_def]
QED
         
Theorem thfVars_gen:
thfVars (gen v th) = thfVars th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘(Γ,A,f)’] >> Cases_on ‘v’ >>
gs[gen_def]>> gs[thfVars_def,Uof_UNION,Uof_Sing,fVars_mk_FALL]
QED

Theorem wfsigaxs_def1:
 wfsigaxs Σ axs ⇔
 wfsig Σ ∧ ∀ax. ax ∈ axs ⇒ wff Σ ax
Proof
Cases_on ‘Σ’ >> Cases_on ‘r’ >>
metis_tac[wfsigaxs_def]
QED 

        
Theorem concl_vinsth:
concl (vinsth σ th) = finst σ (concl th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[concl_def,vinsth_def]
QED

Theorem assum_vinsth:
assum (vinsth σ th) = IMAGE (finst σ) (assum th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[assum_def,vinsth_def]
QED

Theorem ofFMAP_BIGUNION:
ofFMAP f σ (BIGUNION ss) = BIGUNION {ofFMAP f σ s| s ∈ ss}
Proof 
rw[Once EXTENSION,ofFMAP_def,PULL_EXISTS] >>
metis_tac[]
QED



(*        
Theorem Uof_sfv_SND_vinst_cont:
Uof (sfv ∘ SND) (vinst_cont σ Γ) =
 vinst_cont σ (Uof (sfv ∘ SND) Γ)
Proof
 simp[Uof_def,vinst_cont_def,ofFMAP_UNION,
      ofFMAP_BIGUNION]  >>
 AP_TERM_TAC >>
 rw[Once EXTENSION,PULL_EXISTS] >>
 rw[EQ_IMP_THM](* 2 *)
 >- gs[ofFMAP_def] >>
    qexists ‘a’ >> simp[] >> 
        
Theorem genavds_vinsth:
genavds (vinsth σ th) = vinst_cont σ (genavds th)
Proof
simp[genavds_def,cont_vinsth,Uof_Sing,Uof_UNION,
     vinst_cont_UNION,concl_vinsth,assum_vinsth,
     fVars_finst,Uof_IMAGE] >>
‘Uof (sfv ∘ SND) (vinst_cont σ (cont th)) =
 vinst_cont σ (Uof (sfv ∘ SND) (cont th))’
 simp[Uof_def,vinst_cont_def,ofFMAP_UNION,
      ofFMAP_BIGUNION]    
Cases_on ‘’
*)

Theorem MEM_SUBSET_slfv:
∀e l. MEM e l ⇒ sfv e ⊆ slfv l
Proof
gs[slfv_def,SUBSET_DEF,Uof_def] >> metis_tac[]
QED           

Theorem vinst_fVar_eq:
∀fv.
slfv (SND fv) ⊆ FDOM σ1 ∧
slfv (SND fv) ⊆ FDOM σ2 ∧
(∀v. v ∈ slfv (SND fv) ⇒ σ1 ' v = σ2 ' v) 
⇒ vinst_fVar σ1 fv = vinst_fVar σ2 fv
Proof
rw[] >> Cases_on ‘fv’ >> rename [‘(P,sl)’] >>
gs[vinst_fVar_def,MAP_EQ_f] >> rw[] >>
irule $ cj 2 fmap_fv_inst_eq_alt >>
drule_then assume_tac MEM_SUBSET_slfv >>
gs[SUBSET_DEF] >> metis_tac[]
QED


         
Theorem IMAGE_vinst_fVar_thfVars_eq:
Uof (slfv o SND) fvs ⊆ FDOM vσ1 ∧
Uof (slfv o SND) fvs ⊆ FDOM vσ2 ∧
(∀v. v ∈ Uof (slfv o SND) fvs ⇒ vσ1 ' v = vσ2 ' v) ⇒
IMAGE (vinst_fVar vσ1) fvs =
IMAGE (vinst_fVar vσ2) fvs
Proof
rw[]>> irule IMAGE_eq_lemma >>
rw[] >> irule vinst_fVar_eq >>
rw[] (* 3 *)
>- (first_x_assum irule >>
   gs[IN_Uof] >> metis_tac[])
>> (irule SUBSET_TRANS >>
   first_x_assum $ irule_at Any >>
   gs[SUBSET_DEF,Uof_def,PULL_EXISTS] >>
   metis_tac[])
QED   
        
        

Theorem Uof_slfv_SND_thfVars_uniqify:
Uof (slfv ∘ SND) (thfVars (uniqify uσ th)) =
Uof (slfv ∘ SND) (thfVars th)
Proof
simp[GSYM SUBSET_ANTISYM_EQ] >> rw[] (* 2 *)
>- (rw[Uof_SUBSET] >> gs[thfVars_uniqify] >>
   simp[SUBSET_DEF,Uof_def,PULL_EXISTS] >>
   Cases_on ‘x’ >> gs[fVrn_def] >>
   Cases_on ‘(q,r) ∈ FDOM uσ’ >> gs[] (* 2 *)
   >> (rw[] >> qexists ‘(q,r)’ >> simp[])) >>
rw[Uof_SUBSET] >> gs[thfVars_uniqify] >>
simp[SUBSET_DEF,Uof_def,PULL_EXISTS] >>
Cases_on ‘a’ >> gs[] >>
rw[] >> qexists ‘(q,r)’ >> gs[fVrn_def] >>
Cases_on ‘(q,r) ∈ FDOM uσ’ >> gs[]
QED
   
Theorem Uof_fVslfv:
Uof fVslfv ({f} ∪ A) =  Uof (slfv ∘ SND) (thfVars (Γ,A,f))
Proof
rw[thfVars_def,fVslfv_def] >>
irule $ iffLR SUBSET_ANTISYM_EQ >> rw[Uof_SUBSET]
(* 3 *)
>- (simp[fVslfv_def] >>
   irule Uof_SUBSET_MONO >>
   gs[Uof_def,SUBSET_DEF,PULL_EXISTS] >>
   metis_tac[])
>- (simp[fVslfv_def] >>
   irule Uof_SUBSET_MONO >>
   gs[Uof_def,SUBSET_DEF,PULL_EXISTS] >>
   metis_tac[]) >>
gs[IN_Uof,Uof_def,SUBSET_DEF] (* 2 *)
>> (gs[fVslfv_def,IN_Uof] >> metis_tac[])
QED

Theorem thfVars_SUBSET:
PfDrv Σ axs th ∧ wfsigaxs Σ axs ⇒
Uof (slfv ∘ SND) (thfVars th) ⊆ cont th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[cont_def] >> gs[GSYM Uof_fVslfv] >> 
metis_tac[PfDrv_slfv_SUBSET_cont]
QED



Theorem thfVars_SUBSET1:
PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ⇒
Uof (slfv ∘ SND) (thfVars (Γ,A,f)) ⊆ Γ
Proof
metis_tac[thfVars_SUBSET,cont_def]
QED 
           
Theorem NOTIN_genavds_SUBSET_thfVars:
PfDrv Σ axs th ∧ wfsigaxs Σ axs ∧
(x,s) ∉ genavds th ⇒
 Uof (slfv ∘ SND) (thfVars th) ⊆ (cont th) DELETE (x,s)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘(Γ,A,f)’] >> 
rw[cont_def] >>
‘Uof (slfv ∘ SND) (thfVars (Γ,A,f)) ⊆ Γ’
 by (irule thfVars_SUBSET1 >> metis_tac[]) >>
gs[genavds_def,cont_def,concl_def,assum_def] >>
gs[SUBSET_DEF,thfVars_def]
QED


Theorem NOTIN_genavds_assum_SUBSET_DELETE:
PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ∧
(x,s) ∉ genavds (Γ,A,f) ⇒
 Uof ffv A ⊆ Γ DELETE (x,s)
Proof
rw[] >>
drule_then assume_tac PfDrv_assum_ffv_SUBSET >>
gs[Uof_SUBSET] >> rw[] >>
first_x_assum $ drule_all_then assume_tac >>
gs[NOTIN_genavds] >>
‘(x,s) ∉ ffv a’ suffices_by
(gs[SUBSET_DEF] >> metis_tac[]) >>
metis_tac[]  
QED
        

Theorem concl_uniqify:
concl (uniqify uσ th) = ffVrn uσ (concl th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rw[] >> simp[uniqify_def,concl_def]
QED



Theorem concl_uniqify:
concl (uniqify uσ th) = ffVrn uσ (concl th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rw[] >> simp[uniqify_def,concl_def]
QED        


Theorem assum_uniqify:
assum (uniqify uσ th) = IMAGE (ffVrn uσ) (assum th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rw[] >> simp[uniqify_def,assum_def]
QED
           
Theorem NOTIN_Uof_lemma:
(∀a. x ∈ f a ⇒ P a) ∧
(∀a. a ∈ A ⇒ ¬ P a) ⇒ x ∉ Uof f A
Proof
rw[Uof_def] >> metis_tac[]
QED

Theorem fVslfv_finst_ffVrn:
fVslfv (finst vσ (ffVrn uσ f)) =
fVslfv (finst vσ f)
Proof
rw[fVslfv_def] >> irule $ iffLR SUBSET_ANTISYM_EQ >>
rw[Uof_SUBSET] (* 2 *)
>- (gs[fVars_finst,fVars_ffVrn] >>
Cases_on ‘x'’ >> gs[fVrn_def,vinst_fVar_def] >>
Cases_on ‘(q,r) ∈ FDOM uσ ’ >> gs[vinst_fVar_def]
 (* 2 *)
>> (rw[SUBSET_DEF,Uof_def,PULL_EXISTS] >>
   qexists ‘(q,r)’ >> simp[vinst_fVar_def])) >>
gs[fVars_finst] >> Cases_on ‘x’  >>
gs[vinst_fVar_def] >>
simp[SUBSET_DEF,PULL_EXISTS,fVars_ffVrn] >>
rw[] >> simp[Uof_def,PULL_EXISTS] >>
qexists ‘(q,r)’ >> simp[vinst_fVar_def,fVrn_def] >>
Cases_on ‘(q,r) ∈ FDOM uσ’ >> gs[vinst_fVar_def]
QED
 


Theorem fVslfv_finst:
wfvmap Σ σ ∧ ffv f ⊆ FDOM σ ⇒
fVslfv (finst σ f) = vinst_cont σ (fVslfv f)
Proof
rw[fVslfv_def] >>
irule $ iffLR SUBSET_ANTISYM_EQ >>
simp[Uof_SUBSET] >> rw[] (* 2 *)
>- (gs[fVars_finst] >> Cases_on ‘x’ >>
   gs[vinst_fVar_def] >>
   simp[SUBSET_DEF,IN_slfv',PULL_EXISTS,ofFMAP_def,
        MEM_MAP] >> rw[] >>
   qspecl_then [‘y’,‘σ’]
               assume_tac $ cj 2 tfv_sinst>>
   ‘cstt σ ∧ sfv y ⊆ FDOM σ ∧ no_bound σ’
     by (gs[wfvmap_def] >>
        drule_then assume_tac wfcod_no_bound >>
        simp[] >>
        irule SUBSET_TRANS >>
        first_x_assum $ irule_at Any >>
        irule SUBSET_TRANS >>
        irule_at Any fVslfv_SUBSET_ffv >>
        irule MEM_fVsl_SUBSET_fVslfv >>
        metis_tac[]) >>
   gs[] >> Cases_on ‘x’ >> gs[] >>
   ‘(n0,st0) ∈ fVslfv f’
     by (simp[IN_fVslfv] >> metis_tac[]) >>
   ‘(n0,st0) ∈ ffv f’
     by metis_tac[fVslfv_SUBSET_ffv,SUBSET_DEF] >>
   simp[vinst_cont_def,ofFMAP_def,PULL_EXISTS] >>
   qexists ‘(n0,st0)’ >> simp[] >>
   simp[GSYM fVslfv_def] >>
   gs[SUBSET_DEF]) >>
simp[SUBSET_DEF,vinst_cont_def,GSYM fVslfv_def,IN_fVslfv,PULL_EXISTS,ofFMAP_def] >>
rw[] >> simp[fVars_finst,PULL_EXISTS] >>
qexistsl [‘P’,‘MAP (sinst σ) sl’,‘sinst σ s'’,‘(P,sl)’] >> simp[vinst_fVar_def,MEM_MAP,PULL_EXISTS] >>
qexists ‘s'’ >> simp[] >>
qspecl_then [‘s'’,‘σ’] assume_tac $ cj 2 tfv_sinst >>
‘cstt σ ∧ sfv s' ⊆ FDOM σ ∧ no_bound σ’
 by (gs[wfvmap_def] >>
    drule_then assume_tac wfcod_no_bound >>
        simp[] >>
        irule SUBSET_TRANS >>
        first_x_assum $ irule_at Any >>
        irule SUBSET_TRANS >>
        irule_at Any fVslfv_SUBSET_ffv >>
        irule MEM_fVsl_SUBSET_fVslfv >>
        metis_tac[]) >> gs[] >>
Cases_on ‘x’ >> simp[] >>
Cases_on ‘a’ >> metis_tac[]
QED 



Theorem DRESTRICT_FUPDATE_id:
x ∉ FDOM σ ⇒ DRESTRICT (σ |+ (x,y)) (FDOM σ) = σ
Proof
rw[fmap_EXT,FDOM_DRESTRICT,FAPPLY_FUPDATE_THM,
   DRESTRICT_FDOM] >>
rw[EXTENSION] >> metis_tac[]
QED 

Theorem Uof_slfv_SND_fVslfv:
Uof (slfv ∘ SND) (thfVars (Γ,A,f)) =
Uof fVslfv ({f} ∪ A)
Proof
simp[thfVars_def,Once EXTENSION,PULL_EXISTS,
     IN_Uof_Uof] >>
simp[IN_Uof,Uof_UNION,Uof_Sing] >>
simp[fVslfv_def,IN_Uof] >> metis_tac[]
QED     

Theorem NOTIN_genavds_SUBSET_fVslfv:   
PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ∧ (x,s) ∉ genavds (Γ,A,f) ⇒
∀f0.f0 = f ∨ f0 ∈ A ⇒ fVslfv f0 ⊆ Γ DELETE (x,s)
Proof
strip_tac >>
drule_all_then assume_tac
               NOTIN_genavds_SUBSET_thfVars >>
gs[Uof_slfv_SND_fVslfv] >>
gs[Uof_UNION,Uof_Sing,Uof_SUBSET,cont_def]
QED


Theorem Uof_sfv_SND_ofFMAP_SUBSET:
  Uof (sfv ∘ SND) (ofFMAP ffv fσ A) ⊆
  ofFMAP ffv fσ (FDOM fσ)
Proof
  rw[Uof_SUBSET] >>
  gs[ofFMAP_def] >>
  simp[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
  qexists ‘a'’ >> simp[] >>
  Cases_on ‘a’ >> gs[] >>
  metis_tac[sfv_ffv,SUBSET_DEF]
QED  



(*     
        
Theorem ffv_fVinst_SUBSET:
∀f σ. ffv (fVinst σ f) ⊆ ffv f ∪ ofFMAP ffv σ (fVars f)
Proof
Induct_on ‘f’ >> gs[ffv_thm,fVinst_def,fVars_def,
 ofFMAP_UNION] (* 3 *)
>- (gs[SUBSET_DEF] >> metis_tac[])
>- (rw[] (* 2 *)
   >- gs[SUBSET_DEF] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
rw[] (* 3 *)
>- simp[ofFMAP_Sing] >> ffv_fprpl   

Theorem genavds_insth_SUBSET_lemma:
  Uof ffv ({f} ∪ A) ⊆ Γ ⇒
  genavds
          (insth fσ vσ (uniqify uσ (Γ,A,f))) ⊆
          ofFMAP ffv fσ (FDOM fσ) ∪
        genavds
          (vinsth vσ (uniqify uσ (Γ,A,f)))
Proof
rw[genavds_def] (* 3 *) 
>- (simp[insth_def] >>
   simp[uniqify_def,vinsth_def,fVinsth_def,
        cont_def,concl_def,assum_def,
        Uof_UNION] >> rw[] (* 2 *)
   >- (gs[SUBSET_DEF] >> metis_tac[]) >>
   ‘Uof (sfv ∘ SND)
          (ofFMAP ffv fσ
             (Uof fVars {finst vσ (ffVrn uσ f)} ∪
              Uof fVars (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)))) ⊆
        ofFMAP ffv fσ (FDOM fσ)’
    suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
    simp[Uof_sfv_SND_ofFMAP_SUBSET])
>- simp[insth_def] >>
   simp[uniqify_def,vinsth_def,fVinsth_def,
        cont_def,concl_def,assum_def,
        Uof_UNION] >> rw[] >>
   simp[IMAGE_IMAGE] ffv_fVinst    
   


         cont_fVinsth cont_vinsth
*)
                  
Theorem NOTIN_Uof_lemma2:
(∀a. a ∈ A ⇒ x ∉ f a) ⇒ x ∉ Uof f A
Proof
metis_tac[IN_Uof]
QED

Theorem insth_uniqify_gen:
PfDrv Σ axs (Γ,A,f) ∧ wfsigaxs Σ axs ∧
wfs (FST Σ) s ∧
thfVars (vinsth vσ (uniqify uσ (gen (x,s) (Γ,A,f)))) = FDOM fσ ∧
wfvmap (FST Σ) vσ ∧ sfv s ⊆ Γ ∧
FDOM vσ = Γ DELETE (x,s) ∧
(x,s) ∉ genavds (Γ,A,f) ∧ 
(∀s0. (nn,s0) ∉ Γ ∪ ofFMAP ffv fσ (FDOM fσ) ∪
 ofFMAP tfv vσ (FDOM vσ)) ⇒
(insth fσ vσ (uniqify uσ (gen (x,s) (Γ,A,f)))) =
gen (nn,sinst vσ s) (insth fσ (vσ |+ ((x,s),Var nn (sinst vσ s))) (uniqify uσ (Γ,A,f)))
Proof
simp[uniqify_gen] >> simp[insth_def] >> rw[] >>
qspecl_then [‘(uniqify uσ (Γ,A,f))’] assume_tac
(Q.GENL [‘th’] vinsth_gen1) >>
‘vinsth vσ (gen (x,s) (uniqify uσ (Γ,A,f))) =
        gen (nn,sinst vσ s)
          (vinsth (vσ |+ ((x,s),Var nn (sinst vσ s))) (uniqify uσ (Γ,A,f)))’
 by (first_x_assum irule >> simp[] >>
    simp[genavds_uniqify,cont_uniqify,cont_def] >>
    rw[] >-
    simp[uniqify_def,gen_def,cont_def] >>
    metis_tac[PfDrv_uniqify]) >>
simp[] >>
irule fVinsth_gen >> 
simp[PULL_EXISTS] >> qexistsl [‘axs’,‘Σ’] >>
simp[] >> gs[thfVars_vinsth,thfVars_gen] >>
‘wfvmap (FST Σ) (vσ |+ ((x,s),Var nn (sinst vσ s)))’
  by (rw[wfvmap_def] (* 2 *)
     >- (irule FUPDATE_cstt >>
        simp[sort_of_def] >>
        gs[complete_FDOM_is_cont] >>
        gs[wfvmap_def] >>
        rw[] (* 3 *)
        >- (gs[NOTIN_genavds,SUBSET_DEF]>>
           metis_tac[])
        >- (irule is_cont_DELETE >>
           gs[NOTIN_genavds,SUBSET_DEF]>>
           metis_tac[PfDrv_cont_is_cont,cont_def])>>
        gs[NOTIN_genavds,SUBSET_DEF]>>
         metis_tac[]) >>
     irule FUPDATE_wfcod >> gs[wft_def,wfvmap_def]>>
     irule $ cj 2 wft_tinst >>
     simp[] >> Cases_on ‘Σ’ >> Cases_on ‘r’ >>
     gs[wfsigaxs_def1,wfsig_def] >>
     gs[SUBSET_DEF,NOTIN_genavds]>>
     metis_tac[tm_tree_WF]) >>
 reverse (rw[]) (* 3 *)
 >- (irule PfDrv_vinsth  >>
    simp[cont_uniqify,cont_def] >> rw[]
    >- gs[SUBSET_DEF] >>
    irule PfDrv_uniqify >> metis_tac[])
 >- (qpat_x_assum ‘_ = FDOM fσ’ (assume_tac o GSYM)>>
    simp[] >> irule IMAGE_vinst_fVar_thfVars_eq >>
    simp[FDOM_FUPDATE] >>
    gs[Uof_slfv_SND_thfVars_uniqify] >>
    drule_all_then assume_tac 
    NOTIN_genavds_SUBSET_thfVars >>
    gs[cont_def] >> rw[] (* 2 *)
    >- (gs[SUBSET_DEF] >>
       first_x_assum $ drule_then assume_tac >>
       gs[FAPPLY_FUPDATE_THM]) >>
    gs[SUBSET_DEF] >> metis_tac[]) >>
simp[genavds_def,cont_vinsth,concl_vinsth,
     assum_vinsth,cont_uniqify,concl_uniqify,
     assum_uniqify,IMAGE_IMAGE,assum_def,
     concl_def,cont_def,Uof_UNION,Uof_IMAGE,
     Uof_Sing] >>
simp[IMAGE_IMAGE,assum_vinsth] >> rw[] (* 4 *)
>- (gs[Uof_def,PULL_EXISTS] >> rw[] >>
   Cases_on ‘e’ >> rename [‘(n0,s0)’] >>
   Cases_on ‘(n0,s0) ∈ sfv (SND (q,r)) ’ >> gs[] >>
   simp[vinst_cont_def,ofFMAP_def] >>
   rw[PULL_FORALL] >>
   Cases_on ‘(q,r) ∈ s'’ >> gs[] >>
   rw[] >> Cases_on ‘a = (x,s)’ >> gs[] (* 3 *)
   >- metis_tac[tm_tree_WF]
   >- metis_tac[vsort_tfv_closed,tm_tree_WF] >>
   CCONTR_TAC >> gs[] >>
   ‘a ∈ FDOM vσ’ by gs[] >>
   gs[FAPPLY_FUPDATE_THM] >>
   ‘(n0,s0) ∈ ofFMAP tfv vσ (Γ DELETE (x,s))’
    suffices_by metis_tac[] >>
   qpat_x_assum ‘∀s0. _’ (K all_tac) >>
   simp[ofFMAP_def] >>
   metis_tac[vsort_tfv_closed])
>- (simp[Uof_def,PULL_EXISTS,ffv_finst_ffVrn] >>
   rw[] >> Cases_on ‘e ∈ A’ >> gs[] >>
   ‘ffv e ⊆ Γ DELETE (x,s)’
    by
      (drule_all_then assume_tac
       NOTIN_genavds_assum_SUBSET_DELETE >>
       gs[Uof_SUBSET]) >>
   ‘(finst (vσ |+ ((x,s),Var nn (sinst vσ s))) e) =
    (finst vσ e)’
    by (irule fmap_ffv_finst_eq >>
       simp[FDOM_FUPDATE] >> rw[] (* 2 *)
        >- (‘x'∈ FDOM vσ’ by gs[SUBSET_DEF] >>
        gs[FAPPLY_FUPDATE_THM]) >>
        gs[SUBSET_DEF]) >> gs[] >>
   qspecl_then [‘e’,‘vσ’] assume_tac ffv_finst >>
   gs[] >>
   ‘cstt vσ ∧ no_bound vσ’ by
     (gs[wfvmap_def] >> metis_tac[wfcod_no_bound]) >> gs[] >>
   rw[] >> Cases_on ‘(n0,st0) ∈ ffv e’ >> gs[] >>
   CCONTR_TAC >> 
   ‘(nn,sinst vσ s) ∈ ofFMAP tfv vσ (Γ DELETE (x,s))’
    suffices_by metis_tac[] >>
   qpat_x_assum ‘∀s0. _ ∧ _’ (K all_tac) >>
   simp[ofFMAP_def,PULL_EXISTS] >>
   gs[] >> gs[SUBSET_DEF] >> metis_tac[])
>- (simp[GSYM fVslfv_def,fVslfv_finst_ffVrn] >>
   drule_then assume_tac fVslfv_finst >>
   first_x_assum $ qspecl_then [‘f’] assume_tac >>
   gs[FDOM_FUPDATE] >>
   drule_then assume_tac PfDrv_concl_ffv_SUBSET >>
   first_x_assum $ drule_then assume_tac >>
   ‘ffv f ⊆ (x,s) INSERT Γ DELETE (x,s)’
     by (Cases_on ‘(x,s) ∈ Γ’ (* 2 *)
         >> (gs[SUBSET_DEF] >> metis_tac[])) >>
   gs[] >>
   drule_then
   assume_tac NOTIN_genavds_SUBSET_fVslfv >>
   first_x_assum $ qspecl_then [‘x’,‘s’,‘f’]
   assume_tac >> gs[] >>
   ‘vinst_cont (DRESTRICT
   (vσ |+ ((x,s),Var nn (sinst vσ s)))
   (FDOM vσ)) (fVslfv f) =
   vinst_cont (vσ |+ ((x,s),Var nn (sinst vσ s))) (fVslfv f)’
   by (irule vinst_cont_DRESTRICT >>
      simp[FDOM_FUPDATE]) >>
   ‘(x,s)∉ FDOM vσ’ by gs[] >>
   gs[DRESTRICT_FUPDATE_id] >>
   pop_assum (assume_tac o GSYM) >> gs[] >>
   ‘(x,s) ∉ (fVslfv f)’
     by (gs[SUBSET_DEF] >> metis_tac[]) >>
   simp[vinst_cont_def,PULL_EXISTS,
        ofFMAP_def] >> rw[] >>
   Cases_on ‘a ∈ Γ’ >> gs[] >>
   Cases_on ‘a = (x,s)’ >> gs[] >>
   Cases_on ‘a ∈ fVslfv f’ >> gs[] >>
   gs[SUBSET_DEF] >>
   first_x_assum $ drule_then assume_tac >>
   CCONTR_TAC >> gs[] >>
   ‘(nn,sinst vσ s) ∈ 
   ofFMAP tfv vσ (Γ DELETE (x,s))’
   suffices_by metis_tac[] >>
   qpat_x_assum ‘∀s. _ ∧ _’ (K all_tac) >>
   simp[ofFMAP_def] >> metis_tac[]) >>
irule NOTIN_Uof_lemma2 >>
simp[IN_Uof,PULL_EXISTS] >> rw[] >> 
‘(nn,sinst vσ s) ∉
Uof (slfv o SND)
(fVars (finst (vσ |+ ((x,s),Var nn (sinst vσ s))) (ffVrn uσ
   a')))’ suffices_by
 (rw[] >> CCONTR_TAC >> gs[]>>
 ‘(nn,sinst vσ s) ∈
        Uof (slfv ∘ SND)
          (fVars (finst (vσ |+ ((x,s),Var nn (sinst vσ s))) (ffVrn uσ a')))’ suffices_by metis_tac[] >>
 qpat_x_assum ‘_ ∉ _’ (K all_tac) >>
 simp[IN_Uof] >> metis_tac[]) >>
pop_assum (K all_tac) >> 
simp[GSYM fVslfv_def,fVslfv_finst_ffVrn] >>
   drule_then assume_tac fVslfv_finst >>
   first_x_assum $ qspecl_then [‘a'’] assume_tac >>
   gs[FDOM_FUPDATE] >>
   drule_all_then assume_tac
                  PfDrv_assum_ffv_SUBSET >>
   ‘ffv a' ⊆ (x,s) INSERT Γ DELETE (x,s)’
     by (Cases_on ‘(x,s) ∈ Γ’ (* 2 *)
         >> (gs[SUBSET_DEF] >> metis_tac[])) >>
   gs[] >>
   drule_then
   assume_tac NOTIN_genavds_SUBSET_fVslfv >>
   first_x_assum $ qspecl_then [‘x’,‘s’,‘a'’]
   assume_tac >> gs[] >>
   ‘vinst_cont (DRESTRICT
   (vσ |+ ((x,s),Var nn (sinst vσ s)))
   (FDOM vσ)) (fVslfv a') =
   vinst_cont (vσ |+ ((x,s),Var nn (sinst vσ s))) (fVslfv a')’
   by (irule vinst_cont_DRESTRICT >>
      simp[FDOM_FUPDATE]) >>
   ‘(x,s)∉ FDOM vσ’ by gs[] >>
   gs[DRESTRICT_FUPDATE_id] >>
   pop_assum (assume_tac o GSYM) >> gs[] >>
   ‘(x,s) ∉ (fVslfv a')’
     by (gs[SUBSET_DEF] >> metis_tac[]) >>
   simp[vinst_cont_def,PULL_EXISTS,
        ofFMAP_def] >> rw[] >>
   Cases_on ‘a ∈ Γ’ >> gs[] >>
   Cases_on ‘a = (x,s)’ >> gs[] >>
   Cases_on ‘a ∈ fVslfv a'’ >> gs[] >>
   gs[SUBSET_DEF] >>
   first_x_assum $ drule_then assume_tac >>
   CCONTR_TAC >> gs[] >>
   ‘(nn,sinst vσ s) ∈ 
   ofFMAP tfv vσ (Γ DELETE (x,s))’
   suffices_by metis_tac[] >>
   qpat_x_assum ‘∀s. _ ∧ _’ (K all_tac) >>
   simp[ofFMAP_def] >> metis_tac[]
QED     
             
   


Theorem cont_gen:
cont (gen v th) = cont th DELETE v
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
Cases_on ‘v’ >> 
simp[gen_def,cont_def]
QED
   



Theorem wfvmap_FUPDATE:
wfvmap Σf vσ ∧ is_cont (FDOM vσ) ∧
v ∉ FDOM vσ ∧ wft Σf t ∧
sort_of t = sinst vσ (SND v) ⇒
wfvmap Σf (vσ |+ (v,t))
Proof
reverse (rw[wfvmap_def]) (* 2 *)
>- (gs[wfcod_def] >> rw[] (* 2 *)
    >- simp[FAPPLY_FUPDATE_THM] >>
    ‘(n,s) ≠ v’ by metis_tac[] >>
    simp[FAPPLY_FUPDATE_THM]) >>
reverse (rw[cstt_def,FAPPLY_FUPDATE_THM]) (* 2 *)
>- (‘(n,s) ≠ v’ by metis_tac[] >> simp[] >>
   ‘sfv s ⊆ FDOM vσ’ by (gs[is_cont_def] >> metis_tac[]) >>
   ‘sinst (vσ |+ (v,t)) s = sinst vσ s’
     by (irule $ GSYM update_inst_lemma >>
        gs[SUBSET_DEF] >> metis_tac[]) >>
   gs[cstt_def]) >>
gs[] >>   
irule $ update_inst_lemma >> simp[tm_tree_WF] 
QED
        


Theorem sfv_sinst_SUBSET_vinst_cont:
cstt vσ ∧ sfv s ⊆ ct ∧ ct ⊆ FDOM vσ ∧ v ∉ FDOM vσ ∧
(∀v. v ∈ FDOM vσ ⇒ ¬is_bound (vσ ' v)) ⇒
sfv (sinst vσ s) ⊆ vinst_cont (vσ |+ (v,t)) ct
Proof
rw[] >> simp[] >>
drule_then assume_tac $ cj 2 tfv_tinst >>
first_x_assum $ qspecl_then [‘s’] assume_tac >> gs[] >>
‘sfv s ⊆ FDOM vσ’ by (irule SUBSET_TRANS >> metis_tac[]) >>
gs[] >>
simp[SUBSET_DEF,PULL_EXISTS,vinst_cont_def,ofFMAP_def] >>
rw[] >> Cases_on ‘x’ >> simp[] >> gs[] >>
qexists ‘(n0,st0)’ >> simp[] >>
‘(n0,st0) ∈ FDOM vσ’ by (gs[SUBSET_DEF] >> metis_tac[]) >>
‘v ≠ (n0,st0)’ by metis_tac[] >> simp[] >>
simp[FAPPLY_FUPDATE_THM] >> gs[SUBSET_DEF]
QED



Theorem sfv_sinst_SUBSET_vinst_cont:
cstt vσ ∧ sfv s ⊆ FDOM vσ ∧ sfv s ⊆ ct ∧ v ∉ FDOM vσ ∧
(∀v. v ∈ FDOM vσ ⇒ ¬is_bound (vσ ' v)) ⇒
sfv (sinst vσ s) ⊆ vinst_cont (vσ |+ (v,t)) ct
Proof
rw[] >> simp[] >>
drule_then assume_tac $ cj 2 tfv_tinst >>
first_x_assum $ qspecl_then [‘s’] assume_tac >> gs[] >>
simp[SUBSET_DEF,PULL_EXISTS,vinst_cont_def,ofFMAP_def] >>
rw[] >> Cases_on ‘x’ >> simp[] >> gs[] >>
qexists ‘(n0,st0)’ >> simp[] >>
‘(n0,st0) ∈ FDOM vσ’ by (gs[SUBSET_DEF] >> metis_tac[]) >>
‘v ≠ (n0,st0)’ by metis_tac[] >> simp[] >>
simp[FAPPLY_FUPDATE_THM] >> gs[SUBSET_DEF]
QED
        



Theorem thm_cong:
cont th1 = cont th2 ∧ assum th1 = assum th2 ∧ concl th1 = concl th2 ⇒ th1 = th2
Proof
Cases_on ‘th1’ >> Cases_on ‘th2’ >>
Cases_on ‘r’ >> Cases_on ‘r'’ >>
gs[cont_def,assum_def,concl_def]
QED


Theorem insth_uniqify_components:
insth fσ vσ (uniqify uσ (Γ,A,f)) =
(vinst_cont vσ Γ ∪
    ofFMAP ffv fσ
      (Uof fVars
         ({finst vσ (ffVrn uσ f)} ∪
          IMAGE (finst vσ) (IMAGE (ffVrn uσ) A))),
    IMAGE (fVinst fσ)
      (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)),
    fVinst fσ (finst vσ (ffVrn uσ f)))
Proof
simp[uniqify_def,insth_def,vinsth_def,fVinsth_def]
QED

Theorem cont_insth_uniqify:
cont (insth fσ vσ (uniqify uσ (Γ,A,f))) =
vinst_cont vσ Γ ∪
    ofFMAP ffv fσ
      (Uof fVars
         ({finst vσ (ffVrn uσ f)} ∪
          IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)))
Proof
simp[insth_uniqify_components,cont_def] 
QED          



Theorem assum_insth_uniqify:
assum (insth fσ vσ (uniqify uσ (Γ,A,f))) =
IMAGE (fVinst fσ)
      (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A))
Proof
simp[insth_uniqify_components,assum_def] 
QED


Theorem concl_insth_uniqify:
concl (insth fσ vσ (uniqify uσ (Γ,A,f))) =
fVinst fσ (finst vσ (ffVrn uσ f))
Proof
simp[insth_uniqify_components,concl_def] 
QED

        
Theorem main_gen_case:
   wfsigaxs Σ axs ∧ PfDrv Σ axs (Γ,A,f) ∧
   wfs (FST Σ) s ∧ sfv s ⊆ Γ ∧
   (x,s) ∉ genavds (Γ,A,f) ∧
   wfvmap (FST Σ) vσ ∧
   wfcfVmap Σ fσ ∧
   thfVars (vinsth vσ (uniqify uσ (gen (x,s) (Γ,A,f)))) ⊆ FDOM fσ ∧
   cont (gen (x,s) (Γ,A,f)) ⊆ FDOM vσ ∧
   uniqifn uσ (thfVars (gen (x,s) (Γ,A,f))) ∧
   (∀vσ fσ uσ.
          wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
          thfVars (vinsth vσ (uniqify uσ (Γ,A,f))) ⊆ FDOM fσ ∧
          cont (Γ,A,f) ⊆ FDOM vσ ∧ uniqifn uσ (thfVars (Γ,A,f)) ⇒
          Pf0Drv Σ aths (insth fσ vσ (uniqify uσ (Γ,A,f)))) ⇒
   Pf0Drv Σ aths (insth fσ vσ (uniqify uσ (gen (x,s) (Γ,A,f))))
Proof   
  rw[] >> drule_all_then assume_tac PfDrv_gen >>
  drule_then assume_tac gen_precise_maps_ex1 >>
  first_x_assum $ qspecl_then
  [‘uσ’,‘(gen (x,s) (Γ,A,f))’,‘vσ’,‘fσ’]
  assume_tac >> gs[]  >>
  qpat_x_assum ‘wfvmap (FST Σ) vσ’ (K all_tac) >>
  qpat_x_assum ‘wfcfVmap Σ fσ’ (K all_tac) >>
  qpat_x_assum ‘thfVars (vinsth vσ (uniqify uσ (gen (x,s) (Γ,A,f)))) ⊆ FDOM fσ’ (K all_tac) >>
  qpat_x_assum ‘FDOM hσ1 ⊆ FDOM vσ’ (K all_tac) >>
  qpat_x_assum ‘uniqifn uσ (FDOM uσ1)’ (K all_tac)>>
  pop_assum (K all_tac) >>
  rename [‘(insth fσ vσ (uniqify uσ (gen (x,s) (Γ,A,f))))’] >>
  ‘∃nn. (nn,s) ∉ ofFMAP tfv vσ (FDOM vσ) ∪
               ofFMAP ffv fσ (FDOM fσ)’ by cheat >>
  first_x_assum $ qspecl_then
  [‘vσ |+ ((x,s),Var nn (sinst vσ s))’,‘fσ’,‘uσ’] assume_tac >>
  gs[] >>
  ‘insth fσ vσ (uniqify uσ (gen (x,s) (Γ,A,f))) =
     gen (nn,sinst vσ s)
       (insth fσ (vσ |+ ((x,s),Var nn (sinst vσ s))) (uniqify uσ (Γ,A,f)))’
   by (irule insth_uniqify_gen >>
      simp[PULL_EXISTS] >>
      qexistsl [‘axs’,‘Σ’] >> simp[] >>
      gs[cont_gen,cont_def] >> cheat) >>
  simp[] >> irule Pf0Drv_gen1 >>
  reverse (rw[]) (* 4 *)
  >- (first_x_assum irule >> simp[cont_def] >> rw[] (* 4 *)
     >- cheat
     >- (gs[cont_gen,cont_def,SUBSET_DEF,EXTENSION] >>
        metis_tac[])
     >- gs[thfVars_gen] >>
     irule wfvmap_FUPDATE >> simp[sort_of_def,wft_def] >>
     drule_then assume_tac PfDrv_cont_is_cont >>
     gs[cont_gen,cont_def] >>
     qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
     simp[] >> irule wfs_sinst1 >>
     gs[wfvmap_def] >>
     gs[wfsigaxs_def1] >> Cases_on ‘Σ’ >>
     Cases_on ‘r’ >> gs[wfsig_def])
  >- (irule wfs_sinst1 >> gs[wfvmap_def] >>
     gs[wfsigaxs_def1] >> Cases_on ‘Σ’ >>
     Cases_on ‘r’ >> gs[wfsig_def])
  >- (simp[cont_insth_uniqify] >>
      ‘sfv (sinst vσ s) ⊆
       vinst_cont (vσ |+ ((x,s),Var nn (sinst vσ s))) Γ’
       suffices_by simp[SUBSET_DEF] >>
      irule sfv_sinst_SUBSET_vinst_cont >> simp[] >>
      gs[wfvmap_def,cont_gen,cont_def] >> rw[] (* 3 *)
      >- metis_tac[wfcod_no_bound,no_bound_not_bound]
      >- (qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
         simp[]) >>
      qpat_x_assum ‘_ = FDOM vσ’ (assume_tac o GSYM) >>
      simp[] >> gs[SUBSET_DEF] >> simp[tm_tree_WF]) >>
  qabbrev_tac ‘vσ1 = (vσ |+ ((x,s),Var nn (sinst vσ s)))’ >>
  simp[insth_uniqify_components] >>
  simp[NOTIN_genavds,concl_def,cont_def,assum_def,
       PULL_EXISTS] >> rw[] (* 5 *)
  >-( gs[vinst_cont_def] >>
     ‘ofFMAP tfv vσ1 Γ = ofFMAP tfv vσ Γ ∪ tfv (Var nn (sinst vσ s))’ by cheat >>
     gs[] (* 3 *) >- cheat (*nn  not in range*)
     >- simp[tm_tree_WF] >>
     metis_tac[tm_tree_WF,vsort_tfv_closed])
  >- cheat (*nn not in range fσ*)
  >- cheat (* x not in assum*)
  >- (‘(P,sl) ∈ fVars (finst vσ1 (ffVrn uσ f)) ∪ fVars (fVinst fσ (finst vσ1 (ffVrn uσ f)))’ by simp[] >>
     pop_assum mp_tac >> REWRITE_TAC[fVars_fVinst] >>
     rw[] (* 2 *)
     >- (gvs[fVars_finst,fVars_ffVrn,
            vinst_fVar_def,fVrn_def] >>
        Cases_on ‘x''’ >> gs[fVrn_def] >> 
        ‘(q,r) ∈ FDOM uσ’ by cheat >> gs[] >>
        gvs[vinst_fVar_def,MEM_MAP]>>
        ‘(x,s) ∉ sfv y’ by cheat >>
        qspecl_then [‘y’,‘vσ1’] assume_tac $ cj 2 tfv_tinst>>
        ‘cstt vσ1 ∧ sfv y ⊆ FDOM vσ1 ∧ (∀v. v ∈ FDOM vσ1 ⇒ ¬is_bound (vσ1 ' v))’  by cheat >> gs[] >>
        rw[] >> Cases_on ‘(n0,st0) ∈ sfv y’ >> gs[] >>
        ‘(x,s) ≠ (n0,st0)’ by metis_tac[] >>
        simp[Abbr‘vσ1’] >> simp[FAPPLY_FUPDATE_THM] >>
        (*nn not in range of vσ*) cheat) >>
     ‘(nn,sinst vσ s) ∉ ofFMAP ffv fσ (FDOM fσ)’
      by cheat >>
     strip_tac >>
     qpat_x_assum ‘(nn,sinst vσ s) ∉ ofFMAP ffv fσ (FDOM fσ)’
     mp_tac >> simp[] >>
     gvs[ofFMAP_def,PULL_EXISTS] >>
     qexists ‘a’ >> simp[] >>
     ‘fVslfv (fσ ' a) ⊆ ffv (fσ ' a)’
      by simp[fVslfv_SUBSET_ffv] >>
     gs[SUBSET_DEF] >>
     first_x_assum irule >> simp[IN_fVslfv,PULL_EXISTS] >>
     metis_tac[]) >>
  cheat
QED        
     
        
        
        


Theorem ffVrn_NEG:
(ffVrn uσ (NEG f)) = NEG (ffVrn uσ f)
Proof
rw[NEG_def,ffVrn_def]
QED

Theorem finst_NEG:
finst σ (NEG f) = NEG (finst σ f)
Proof
rw[finst_def,NEG_def]
QED


Theorem fVinst_NEG:
fVinst σ (NEG f) = NEG (fVinst σ f)
Proof
rw[fVinst_def,NEG_def]
QED


                
Theorem main_double_neg_lemma:
  Pf0Drv Σ aths (insth fσ vσ (uniqify uσ (Γ,A ∪ {NEG f},False))) ⇒
  Pf0Drv Σ aths (insth fσ vσ (uniqify uσ (Γ,A,f)))
Proof
  simp[insth_def,uniqify_def,fVinsth_def,vinsth_def]
  >> rw[] >>
  irule Pf0Drv_double_neg >>
  ‘(vinst_cont vσ Γ ∪
    ofFMAP ffv fσ
    (Uof fVars
     ({finst vσ (ffVrn uσ False)} ∪
      (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A) ∪
       {finst vσ (ffVrn uσ (NEG f))}))),
    IMAGE (fVinst fσ) (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)) ∪
          {fVinst fσ (finst vσ (ffVrn uσ (NEG f)))},
    fVinst fσ (finst vσ (ffVrn uσ False))) =
   (vinst_cont vσ Γ ∪
    ofFMAP ffv fσ
    (Uof fVars
     ({finst vσ (ffVrn uσ f)} ∪
      IMAGE (finst vσ) (IMAGE (ffVrn uσ) A))),
    IMAGE (fVinst fσ) (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)) ∪
          {NEG (fVinst fσ (finst vσ (ffVrn uσ f)))},False)’ suffices_by metis_tac[] >>
  rw[] (* 3 *)
  >- (gs[finst_def,ffVrn_def] >>
      ‘(Uof fVars
        ({False} ∪
         (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A) ∪
          {finst vσ (ffVrn uσ (NEG f))}))) =
       (Uof fVars
        ({finst vσ (ffVrn uσ f)} ∪ IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)))’ suffices_by metis_tac[]>>
      simp[Uof_UNION,Uof_Sing,fVars_def] >>
      simp[fVars_NEG,finst_NEG,ffVrn_NEG] >>
      metis_tac[UNION_COMM])
  >- simp[finst_NEG,ffVrn_NEG,fVinst_NEG] >>
  simp[fVinst_def,finst_def,ffVrn_def]     
QED
 

Theorem ofFMAP_tfv_vinst_cont:
  ofFMAP tfv σ s = vinst_cont σ s
Proof
  simp[ofFMAP_def,vinst_cont_def]
QED

Theorem thfVars_assume:
thfVars (assume f) = fVars f
Proof
rw[thfVars_def,assume_def,Uof_Sing]
QED 
        
(*Theorem insth_uniqify_mp:
(insth fσ vσ (uniqify uσ (Γ1 ∪ Γ2,A1 ∪ A2,f2))) =
()
(insth fσ vσ (uniqify uσ (Γ1 ∪ Γ2,A1 ∪ A2,f2)))
*)


(*        
Definition TRUE_def:
TRUE = Pred "T" []
End
*)

        
Definition exFfmap_def:
exFfmap σ fvs =
FUN_FMAP
(λfv. if fv ∈ FDOM σ then σ ' fv else False)
(FDOM σ ∪ fvs)
End

Definition MP0_def:
MP0 (Γ1,A1,IMP f1 f2) (Γ2,A2,f3) =
(Γ1 ∪ Γ2, A1 ∪ A2,f2)
End 


Theorem Pf0Drv_MP0:
Pf0Drv Σ aths (Γ1,A1,IMP ϕ ψ) ∧ Pf0Drv Σ aths (Γ2,A2,ϕ) ⇒
Pf0Drv Σ aths (MP0 (Γ1,A1,IMP ϕ ψ) (Γ2,A2,ϕ))
Proof
simp[MP0_def] >> rw[] >>
irule Pf0Drv_mp >> metis_tac[]
QED


(*                

Definition cfVmap_def:
cfVmap (fvs:string # sort list -> bool) (fm:form) =
FUN_FMAP (λfv. fm) fvs
End

(*trivial aug*)
Definition tvaug_def:
tvaug fσ fvs = FUNION fσ (cfVmap fvs False)
End
*)


        
        


(*
Theorem mp_case_lemma:
∀Γ1 Γ2 A1 A2 f1 f2.
wfvmap (FST Σ) hσ ∧
wfcfVmap Σ fσ ∧
thfVars (vinsth hσ (uniqify uσ (Γ1 ∪ Γ2,A1 ∪ A2,f2))) = FDOM fσ ∧
Γ1 ∪ Γ2 = FDOM hσ ∧
uniqifn uσ (thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2)) ∧
thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2) = FDOM uσ ⇒
∃hσ1 fσ1 uσ1 hσ2 fσ2 uσ2.
 wfvmap (FST Σ) hσ1 ∧
 wfcfVmap Σ fσ1 ∧
 thfVars
 (vinsth hσ1 (uniqify uσ1 (Γ1,A1,IMP f1 f2))) ⊆ FDOM fσ1 ∧
 Γ1 ⊆ FDOM hσ1 ∧
 uniqifn uσ1 (thfVars (Γ1,A1,IMP f1 f2)) ∧
 wfvmap (FST Σ) hσ2 ∧
 wfcfVmap Σ fσ2 ∧
 thfVars
 (vinsth hσ2 (uniqify uσ2 (Γ2,A2,f1))) ⊆ FDOM fσ2 ∧
 Γ2 ⊆ FDOM hσ2 ∧
 uniqifn uσ2 (thfVars (Γ2,A2,f1)) ∧
insth fσ hσ (uniqify uσ (Γ1 ∪ Γ2,A1 ∪ A2,f2)) =
MP0 (insth fσ1 hσ1 (uniqify uσ1 (Γ1,A1,IMP f1 f2)))
(insth fσ2 hσ2 (uniqify uσ2 (Γ2,A2,f1)))
Proof
cheat
QED
*)
(*
Theorem MP0_insth_unqify:
MP0 (insth fσ hσ ())
*)

Definition is_imp_def:
is_imp (IMP f1 f2) = T ∧
is_imp _ = F
End

Definition dest_imp_def:
dest_imp (IMP f1 f2) = (f1,f2)
End        

Theorem Pf0Drv_MP0':
Pf0Drv Σ aths th1 ∧ Pf0Drv Σ aths th2 ∧
is_imp (concl th1) ∧ concl th2 = FST (dest_imp (concl th1)) ⇒
Pf0Drv Σ aths (MP0 th1 th2)
Proof
rw[] >> Cases_on ‘th1’ >> Cases_on ‘r’ >> gs[concl_def] >>
Cases_on ‘r'’ >> gs[is_imp_def,dest_imp_def] >>
Cases_on ‘th2’ >> Cases_on ‘r’ >> gs[concl_def] >>
irule Pf0Drv_MP0 >> simp[]
QED 


Theorem concl_insth_uniqify:
concl (insth fσ vσ (uniqify uσ th)) =
instf fσ vσ (ffVrn uσ (concl th))
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> simp[concl_def,uniqify_def,insth_def,
 fVinsth_def,vinsth_def,instf_def]
QED 

Theorem ffVrn_is_imp:
is_imp (ffVrn uσ f) ⇔ is_imp f
Proof
Induct_on ‘f’ >> gs[is_imp_def,ffVrn_def] >> rw[is_imp_def]
QED
        
Theorem uniqifn_inst_EX:
∀(uσ:α # β |-> string) δ s.
FINITE δ ∧ uniqifn uσ s ∧ FDOM uσ ∩ δ = {} ⇒
∃uσ1. uniqifn uσ1 (s ∪ δ) ∧ FDOM uσ1 = FDOM uσ ∪ δ ∧
 (∀x. x ∈ FDOM uσ ⇒ uσ1 ' x = uσ ' x)
Proof 
Induct_on ‘FINITE’ >> rw[] (* 2 *)
>- metis_tac[] >>
‘e ∉ FDOM uσ ∧ FDOM uσ ∩ δ = {}’
 by (gs[EXTENSION]>> metis_tac[]) >>
‘FDOM uσ ∩ δ = {}’ by (gs[EXTENSION]>> metis_tac[]) >>
first_x_assum $ drule_all_then strip_assume_tac >>
qabbrev_tac ‘used = FRANGE uσ1’ >>
‘FINITE used’ by simp[Abbr‘used’] >>
‘∃a. a ∉ used’ by (irule $ iffLR NOT_IN_FINITE >> simp[])>>
qexists ‘uσ1 |+ (e,a)’ >>
rw[] (* 3 *)
>- (gs[uniqifn_def] >> rw[] (* 9 *)
   >- (gs[SUBSET_DEF] >> metis_tac[])
   >- (gs[FAPPLY_FUPDATE_THM,AllCaseEqs()] >> rw[] (* 2 *)
       >- (‘(P2,sl2) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       ‘uσ1 ' (P2,sl2) ∈ FRANGE uσ1’
         by (REWRITE_TAC[FRANGE_DEF] >> simp[] >>
            gs[SUBSET_DEF] >> metis_tac[]) >>
       gs[Abbr‘used’]) >>
       ‘(P1,sl1) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       ‘uσ1 ' (P1,sl1) ∈ FRANGE uσ1’
         by (REWRITE_TAC[FRANGE_DEF] >> simp[] >>
            gs[SUBSET_DEF] >> metis_tac[]) >>
       gs[Abbr‘used’])
    >- (‘(P1,sl1) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
        simp[FAPPLY_FUPDATE_THM] >>
        ‘¬(P1 = P2 ∧ sl1 = sl2)’ by metis_tac[] >> simp[]>>
         ‘uσ1 ' (P1,sl1) ∈ FRANGE uσ1’
         by (REWRITE_TAC[FRANGE_DEF] >> simp[] >>
            gs[SUBSET_DEF] >> metis_tac[]) >>
       gs[Abbr‘used’] >> metis_tac[])
    >- (‘(P1,sl1) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       ‘(P2,sl2) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       ‘e ∉ FDOM uσ1’ by simp[] >>
       simp[FAPPLY_FUPDATE_THM] >>
       ‘(P1,sl1) ≠ e ∧ (P2,sl2) ≠ e’ by metis_tac[] >>
       simp[])
    >- (‘(P2,sl2) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       simp[FAPPLY_FUPDATE_THM] >>
       ‘¬(P2 = P1 ∧ sl2 = sl1)’ by metis_tac[] >>
       simp[] >>
       ‘uσ1 ' (P2,sl2) ∈ FRANGE uσ1’
         by (REWRITE_TAC[FRANGE_DEF] >> simp[] >>
            gs[SUBSET_DEF] >> metis_tac[]) >>
       gs[Abbr‘used’] >> metis_tac[])
    >- (‘(P2,sl2) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       simp[FAPPLY_FUPDATE_THM] >>
       ‘¬(P2 = P1 ∧ sl2 = sl1)’ by metis_tac[] >>
       simp[] >>
       ‘uσ1 ' (P2,sl2) ∈ FRANGE uσ1’
         by (REWRITE_TAC[FRANGE_DEF] >> simp[] >>
            gs[SUBSET_DEF] >> metis_tac[]) >>
       gs[Abbr‘used’] >> metis_tac[])
    >- (‘(P1,sl1) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       ‘(P2,sl2) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       ‘e ∉ FDOM uσ1’ by simp[] >>
       simp[FAPPLY_FUPDATE_THM] >>
       ‘(P1,sl1) ≠ e ∧ (P2,sl2) ≠ e’ by metis_tac[] >>
       simp[])
   >- (‘(P1,sl1) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
      simp[FAPPLY_FUPDATE_THM] >>
      ‘¬(P1 = P2 ∧ sl1 = sl2)’ by metis_tac[] >>
      simp[] >>
      ‘uσ1 ' (P1,sl1) ∈ FRANGE uσ1’
         by (REWRITE_TAC[FRANGE_DEF] >> simp[] >>
            gs[SUBSET_DEF] >> metis_tac[]) >>
       gs[Abbr‘used’] >> metis_tac[]) >>
    simp[] >>
    ‘(P1,sl1) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       ‘(P2,sl2) ∈ FDOM uσ1’
        by (simp[] >> gs[SUBSET_DEF] >> metis_tac[]) >>
       ‘e ∉ FDOM uσ1’ by simp[] >>
       simp[FAPPLY_FUPDATE_THM] >>
       ‘(P1,sl1) ≠ e ∧ (P2,sl2) ≠ e’ by metis_tac[] >>
       simp[])
>- (rw[EXTENSION]>> metis_tac[])  >>
‘x ≠ e’ by metis_tac[] >>
simp[FAPPLY_FUPDATE_THM]
QED

Definition agrees_on_def:
agrees_on σ1 σ2 s ⇔
s ⊆ FDOM σ1 ∧ s ⊆ FDOM σ2 ∧
∀a. a ∈ s ⇒ σ1 ' a = σ2 ' a
End




 
Theorem agrees_on_ofFMAP:
agrees_on σ1 σ2 s ⇒ ofFMAP f σ1 s = ofFMAP f σ2 s
Proof
rw[ofFMAP_def,agrees_on_def] >>
simp[EXTENSION] >> gs[SUBSET_DEF] >> metis_tac[]
QED


Theorem agrees_on_SUBSET:
agrees_on σ1 σ2 s ∧ s0 ⊆ s ⇒ agrees_on σ1 σ2 s0
Proof
rw[agrees_on_def,SUBSET_DEF]
QED                
        

Theorem agrees_on_ffVrn:
agrees_on uσ1 uσ2 (fVars f) ⇒
ffVrn uσ1 f = ffVrn uσ2 f
Proof
rw[] >> irule ffVrn_eq1 >>
gs[agrees_on_def,SUBSET_DEF,EXTENSION] >>
metis_tac[]
QED


Theorem agrees_on_finst:
agrees_on vσ1 vσ2 (ffv f) ⇒
finst vσ1 f = finst vσ2 f
Proof
rw[] >> irule fmap_ffv_finst_eq >>
gs[agrees_on_def,SUBSET_DEF,EXTENSION] >>
metis_tac[]
QED


Theorem agrees_on_fVinst:
agrees_on fσ1 fσ2 (fVars f) ⇒
fVinst fσ1 f = fVinst fσ2 f
Proof
rw[] >> irule fVars_DRESTRICT_fVinst_eq0 >>
gs[agrees_on_def,SUBSET_DEF,EXTENSION] >>
metis_tac[]
QED        
        
Theorem uniqify_cong:
∀uσ1 uσ2 th.
agrees_on uσ1 uσ2 (thfVars th) ⇒
uniqify uσ1 th = uniqify uσ2 th
Proof
rw[] >> Cases_on ‘th’ >> Cases_on ‘r’ >> simp[uniqify_def] >>
‘agrees_on uσ1 uσ2 (fVars r')’
 by (irule agrees_on_SUBSET >>
    first_x_assum $ irule_at Any >>
    metis_tac[SUBSET_thfVars]) >>
drule_then assume_tac agrees_on_ffVrn >> simp[] >>
irule IMAGE_eq_lemma >> rw[] >>
irule agrees_on_ffVrn >>
irule agrees_on_SUBSET >>
qexists ‘(thfVars (q,q',r'))’ >>
simp[] >> irule $ cj 2 SUBSET_thfVars >> simp[] 
QED


Theorem vinsth_cong:
∀vσ1 vσ2 th.
Uof ffv ({concl th} ∪ assum th) ⊆ cont th ∧
agrees_on vσ1 vσ2 (cont th) ⇒
vinsth vσ1 th = vinsth vσ2 th
Proof
rw[] >> Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘(Γ,A,f)’] >>
gs[vinsth_def,cont_def,concl_def,assum_def] >>
rw[] (* 3 *)
>- (gs[vinst_cont_def] >> metis_tac[agrees_on_ofFMAP])
>- (irule IMAGE_eq_lemma >> rw[] >>
   irule agrees_on_finst >> irule agrees_on_SUBSET >>
   qexists ‘Γ’ >> simp[] >> gs[Uof_SUBSET,Uof_UNION]) >>
irule agrees_on_finst >> irule agrees_on_SUBSET >>
qexists ‘Γ’ >> simp[] >> gs[Uof_SUBSET,Uof_UNION]    
QED            



Theorem fVinsth_cong:
∀fσ1 fσ2 th.
agrees_on fσ1 fσ2 (thfVars th) ⇒
fVinsth fσ1 th = fVinsth fσ2 th
Proof
rw[] >> Cases_on ‘th’ >> Cases_on ‘r’ >>
rename [‘(Γ,A,f)’] >>
gs[fVinsth_def,cont_def,concl_def,assum_def] >>
rw[] (* 3 *)
>- (gs[thfVars_def] >>
   ‘ofFMAP ffv fσ1 (Uof fVars ({f} ∪ A)) =
    ofFMAP ffv fσ2 (Uof fVars ({f} ∪ A))’
    suffices_by metis_tac[] >>
   irule agrees_on_ofFMAP >> simp[])
>- (irule IMAGE_eq_lemma >> rw[] >> 
   irule agrees_on_fVinst >> irule agrees_on_SUBSET >>
   qexists ‘(thfVars (Γ,A,f))’ >> simp[] >>
   irule $ cj 2 SUBSET_thfVars >> simp[]) >>
irule agrees_on_fVinst >> irule agrees_on_SUBSET >>
qexists ‘(thfVars (Γ,A,f))’ >> simp[] >>
metis_tac[SUBSET_thfVars]
QED                

Definition mp_match:
mp_match th1 th2 ⇔
is_imp (concl th1) ∧
     concl th2 = FST (dest_imp (concl th1))
End     


Theorem uniqify_mp_match:
mp_match th1 th2 ⇒
mp_match (uniqify uσ th1) (uniqify uσ th2)
Proof
Cases_on ‘th1’ >> Cases_on ‘th2’ >>
Cases_on ‘r’ >> Cases_on ‘r'’ >>
rename [‘mp_match (Γ1,A1,phi) (Γ2,A2,psi)’] >>
simp[mp_match,concl_def] >> Cases_on ‘phi’ >>
simp[is_imp_def,dest_imp_def,uniqify_def,concl_def,ffVrn_def]
QED


Theorem vinsth_mp_match:
mp_match th1 th2 ⇒
mp_match (vinsth vσ th1) (vinsth vσ th2)
Proof
Cases_on ‘th1’ >> Cases_on ‘th2’ >>
Cases_on ‘r’ >> Cases_on ‘r'’ >>
rename [‘mp_match (Γ1,A1,phi) (Γ2,A2,psi)’] >>
simp[mp_match,concl_def] >> Cases_on ‘phi’ >>
simp[is_imp_def,dest_imp_def,vinsth_def,concl_def,finst_def]
QED


Theorem fVinsth_mp_match:
mp_match th1 th2 ⇒
mp_match (fVinsth fσ th1) (fVinsth fσ th2)
Proof
Cases_on ‘th1’ >> Cases_on ‘th2’ >>
Cases_on ‘r’ >> Cases_on ‘r'’ >>
rename [‘mp_match (Γ1,A1,phi) (Γ2,A2,psi)’] >>
simp[mp_match,concl_def] >> Cases_on ‘phi’ >>
simp[is_imp_def,dest_imp_def,fVinsth_def,
     concl_def,fVinst_def]
QED
        
        


        
Theorem insth_uniqify_mp_match:
mp_match th1 th2 ⇒
mp_match (insth fσ vσ (uniqify uσ th1)) (insth fσ vσ (uniqify uσ th2))
Proof
rw[] >> simp[insth_def] >> irule fVinsth_mp_match >>
irule vinsth_mp_match >> irule uniqify_mp_match >> simp[] 
QED


Theorem Pf0Drv_mp_match_MP0:
mp_match th1 th2 ∧ Pf0Drv Σ aths th1 ∧ Pf0Drv Σ aths th2 ⇒
Pf0Drv Σ aths (MP0 th1 th2)
Proof
simp[mp_match] >> metis_tac[Pf0Drv_MP0']
QED
        
Theorem insth_uniqify_mp:
mp_match th1 th2 ⇒
Pf0Drv Σ axs (insth fσ vσ (uniqify uσ th1)) ∧
Pf0Drv Σ axs (insth fσ vσ (uniqify uσ th2)) ⇒
Pf0Drv Σ axs (MP0 (insth fσ vσ (uniqify uσ th1))
(insth fσ vσ (uniqify uσ th2)))
Proof
metis_tac[Pf0Drv_mp_match_MP0,insth_uniqify_mp_match]
QED


Theorem insth_concl_is_imp:
is_imp (concl th) ⇒ is_imp (concl (insth fσ hσ th))
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> simp[insth_def,concl_def] >>
gs[fVinsth_def,vinsth_def] >>
Cases_on ‘r'’ >>
gs[finst_def,fVinst_def,concl_def,is_imp_def] 
QED        


Theorem uniqify_concl_is_imp:
is_imp (concl th) ⇒ is_imp (concl (uniqify uσ th))
Proof
Cases_on ‘th’ >>
Cases_on ‘r’ >> simp[uniqify_def,concl_def] >>
Cases_on ‘r'’ >> gs[ffVrn_def,is_imp_def] 
QED
           

         

Theorem ofFMAP_EMPTY_iff:
ofFMAP f σ s = {} ⇔
 ∀a. a ∈ s ∩ FDOM σ ⇒ f (σ ' a) = {}
Proof 
rw[ofFMAP_def] >> rw[EQ_IMP_THM] (* 3 *)
>> (gs[EXTENSION] >> metis_tac[])
QED
      

Theorem insth_unqify_MP0:
is_imp (concl th1) ∧ mp_match th1 th2 ∧
(∀fv. fv ∈ fVars (FST (dest_imp (concl th1))) DIFF
(Uof fVars ({SND (dest_imp (concl th1))} ∪ assum th1 ∪ assum th2)) ⇒
 ffv (fσ ' (vinst_fVar hσ (fVrn uσ fv))) = {}) ⇒
(insth fσ hσ (uniqify uσ (MP0 th1 th2))) =
MP0 (insth fσ hσ (uniqify uσ th1))
(insth fσ hσ (uniqify uσ th2))    
Proof
Cases_on ‘th1’ >> Cases_on ‘th2’ >>
Cases_on ‘r’ >> Cases_on ‘r'’ >> gs[] >>
rename [‘MP0 (Γ1,A1,f) (Γ2,A2,g)’] >>
gs[concl_def,is_imp_def] >> rw[] >>
Cases_on ‘f’ >> gs[is_imp_def] >>
rename [‘IMP f1 f2’] >> gs[MP0_def] >>
Cases_on ‘(insth fσ hσ (uniqify uσ (Γ1,A1,IMP f1 f2)))’ >>
Cases_on ‘(insth fσ hσ (uniqify uσ (Γ2,A2,g)))’ >>
Cases_on ‘r’ >> Cases_on ‘r'’ >>
‘is_imp (concl (insth fσ hσ (uniqify uσ (Γ1,A1,IMP f1 f2))))’
 by (irule insth_concl_is_imp >>
    irule uniqify_concl_is_imp >> simp[is_imp_def,concl_def])
     >>
Cases_on ‘(concl
             (insth fσ hσ
                (uniqify uσ (Γ1,A1,IMP f1 f2))))’ >>
gs[is_imp_def] >> gs[concl_def] >>
rename [‘(Γ1',A1',IMP f1' f2')’] >>
gs[dest_imp_def,assum_def] >> 
rename
[‘insth fσ hσ (uniqify uσ (Γ2,A2,g)) = (Γ2',A2',g')’]>>
simp[MP0_def] >>
gvs[] >>
irule thm_cong >> simp[cont_def,assum_def,concl_def] >> 
rw[] (* 3 *)
>- gs[insth_uniqify_components,concl_def,
      fVinst_def, ffVrn_def,finst_def]
>- gs[insth_uniqify_components,concl_def,assum_def,
      fVinst_def, ffVrn_def,finst_def] >>
gs[insth_uniqify_components,concl_def,cont_def,
      fVinst_def, ffVrn_def,finst_def] >>
pop_assum (K all_tac) >>
pop_assum (K all_tac) >>
pop_assum (assume_tac o GSYM) >> simp[] >>
pop_assum (K all_tac) >>
pop_assum (K all_tac) >>
pop_assum (K all_tac) >>
pop_assum (K all_tac) >>
pop_assum (assume_tac o GSYM) >> simp[] >>
pop_assum (K all_tac) >>
simp[vinst_cont_UNION] >>
‘ofFMAP ffv fσ
          (Uof fVars
             ({finst hσ (ffVrn uσ f2)} ∪
              (IMAGE (finst hσ) (IMAGE (ffVrn uσ) A1) ∪
               IMAGE (finst hσ) (IMAGE (ffVrn uσ) A2)))) =
ofFMAP ffv fσ
          (Uof fVars
             ({IMP (finst hσ (ffVrn uσ f1))
                 (finst hσ (ffVrn uσ f2))} ∪
              IMAGE (finst hσ) (IMAGE (ffVrn uσ) A1))) ∪
ofFMAP ffv fσ
           (Uof fVars
              ({finst hσ (ffVrn uσ g)} ∪
               IMAGE (finst hσ) (IMAGE (ffVrn uσ) A2)))’
 suffices_by (simp[EXTENSION] >> metis_tac[]) >>
simp[GSYM ofFMAP_UNION] >>
‘g = f1’ by gs[mp_match,concl_def,dest_imp_def] >> gs[] >>
simp[ofFMAP_UNION,Uof_UNION,Uof_Sing,ofFMAP_Sing,fVars_def]>>
simp[fVars_finst,fVars_ffVrn] >>
‘(fVars f1) = (fVars f1 DIFF Uof fVars ({f2} ∪ A1 ∪ A2)) ∪
 (fVars f1 ∩ Uof fVars ({f2} ∪ A1 ∪ A2))’
 by (simp[EXTENSION] >> metis_tac[]) >>
‘ofFMAP ffv fσ
          (IMAGE (vinst_fVar hσ)
             (IMAGE (fVrn uσ) (fVars f1))) ∪
        ofFMAP ffv fσ
          (IMAGE (vinst_fVar hσ)
             (IMAGE (fVrn uσ) (fVars f2))) ∪
        ofFMAP ffv fσ
          (Uof fVars
             (IMAGE (finst hσ) (IMAGE (ffVrn uσ) A1))) ∪
        (ofFMAP ffv fσ
           (IMAGE (vinst_fVar hσ)
              (IMAGE (fVrn uσ) (fVars f1))) ∪
         ofFMAP ffv fσ
           (Uof fVars
              (IMAGE (finst hσ) (IMAGE (ffVrn uσ) A2)))) =
ofFMAP ffv fσ
          (Uof fVars
             (IMAGE (finst hσ) (IMAGE (ffVrn uσ) A1))) ∪
ofFMAP ffv fσ
          (Uof fVars
             (IMAGE (finst hσ) (IMAGE (ffVrn uσ) A2))) ∪
ofFMAP ffv fσ
          (IMAGE (vinst_fVar hσ)
             (IMAGE (fVrn uσ) (fVars f1))) ∪
        ofFMAP ffv fσ
          (IMAGE (vinst_fVar hσ)
             (IMAGE (fVrn uσ) (fVars f2)))’ 
 by (rw[EXTENSION] >> metis_tac[]) >>
pop_assum SUBST_ALL_TAC >>
pop_assum SUBST_ALL_TAC >>
simp[ofFMAP_UNION] >>
‘ofFMAP ffv fσ
           (IMAGE (vinst_fVar hσ)
              (IMAGE (fVrn uσ)
                 (fVars f1 DIFF
                  Uof fVars ({f2} ∪ A1 ∪ A2)))) = {} ∧
ofFMAP ffv fσ
           (IMAGE (vinst_fVar hσ)
              (IMAGE (fVrn uσ)
                 (fVars f1 ∩ Uof fVars ({f2} ∪ A1 ∪ A2)))) ⊆
ofFMAP ffv fσ
          (Uof fVars
             (IMAGE (finst hσ) (IMAGE (ffVrn uσ) A1))) ∪
        ofFMAP ffv fσ
          (Uof fVars
             (IMAGE (finst hσ) (IMAGE (ffVrn uσ) A2))) ∪
ofFMAP ffv fσ
          (IMAGE (vinst_fVar hσ)
             (IMAGE (fVrn uσ) (fVars f2)))’
suffices_by (gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
reverse (rw[]) (* 2 *)
>- (simp[GSYM ofFMAP_UNION] >> irule ofFMAP_SUBSET_MONO >>
   irule SUBSET_TRANS >>
   qexists
   ‘IMAGE (vinst_fVar hσ)
              (IMAGE (fVrn uσ)
                 (Uof fVars ({f2} ∪ A1 ∪ A2)))’ >>
   rw[] >>
   simp[SUBSET_DEF,Uof_def,PULL_EXISTS] >> rw[] (* 3 *)
   >- metis_tac[]
   >- (disj1_tac >> disj1_tac >>
      qexists ‘e’  >> simp[fVars_finst,fVars_ffVrn]) >>
   disj1_tac >> disj2_tac >>
   qexists ‘e’  >> simp[fVars_finst,fVars_ffVrn]) >>
simp[] >> irule $ iffRL ofFMAP_EMPTY_iff >> 
rw[] >> first_x_assum irule >> simp[]
QED


        
Theorem SUBMAP_agrees_on:
σ1 ⊑ σ2 ⇒ agrees_on σ1 σ2 (FDOM σ1)
Proof
rw[agrees_on_def,SUBMAP_DEF,SUBSET_DEF]
QED



        
Theorem insth_unqify_MP0':
(is_imp (concl th1) ∧ mp_match th1 th2 ∧
Uof ffv ({concl th1} ∪ assum th1) ⊆ cont th1 ∧
Uof ffv ({concl th2} ∪ assum th2) ⊆ cont th2 ∧
let extras = fVars (FST (dest_imp (concl th1))) DIFF
(Uof fVars ({SND (dest_imp (concl th1))} ∪ assum th1 ∪ assum th2)) in 
(∀fv. fv ∈ extras ⇒
 ffv (fσ ' (vinst_fVar hσ (fVrn uσ fv))) = {}) ∧
FDOM uσ1 = thfVars th1 ∧
FDOM uσ2 = thfVars th2 ∧
uσ1 ⊑ uσ ∧ uσ2 ⊑ uσ ∧
FDOM hσ1 = cont th1 ∧ FDOM hσ2 = cont th2 ∧ 
hσ1 ⊑ hσ ∧ hσ2 ⊑ hσ ∧
fσ1 ⊑ fσ ∧ fσ2 ⊑ fσ ∧
FDOM fσ1 = thfVars (vinsth hσ1 (uniqify uσ1 th1)) ∧
FDOM fσ2 = thfVars (vinsth hσ2 (uniqify uσ2 th2))) ⇒
(insth fσ hσ (uniqify uσ (MP0 th1 th2))) =
MP0 (insth fσ1 hσ1 (uniqify uσ1 th1))
(insth fσ2 hσ2 (uniqify uσ2 th2))    
Proof
rw[] >>
‘(insth fσ1 hσ1 (uniqify uσ1 th1)) =
 (insth fσ hσ (uniqify uσ th1)) ∧
 (insth fσ2 hσ2 (uniqify uσ2 th2)) =
 (insth fσ hσ (uniqify uσ th2))’
 suffices_by
  (rw[] >> irule insth_unqify_MP0 >> simp[] >> rw[]) >>
rw[] (* 2 *)
>- (‘uniqify uσ1 th1 = uniqify uσ th1’
     by (irule uniqify_cong >>
        qpat_x_assum ‘FDOM uσ1 = thfVars th1’
        (assume_tac o GSYM) >> simp[] >>
        irule SUBMAP_agrees_on >>
        simp[]) >>
   simp[] >>
   simp[insth_def] >>
   ‘(vinsth hσ1 (uniqify uσ th1)) =
   (vinsth hσ (uniqify uσ th1))’
    by (irule vinsth_cong >> reverse (rw[]) (* 2 *)
        >- (simp[cont_uniqify] >>
           qpat_x_assum ‘FDOM hσ1 = cont th1’
        (assume_tac o GSYM) >> simp[] >>
        irule SUBMAP_agrees_on >>
        simp[]) >> cheat) >> simp[] >>
   irule fVinsth_cong >> gs[] >>
   qpat_x_assum ‘FDOM fσ1 = _’ (assume_tac o GSYM) >>
   simp[] >> irule SUBMAP_agrees_on >> simp[]) >> 
‘uniqify uσ2 th2 = uniqify uσ th2’
     by (irule uniqify_cong >>
        qpat_x_assum ‘FDOM uσ2 = thfVars th2’
        (assume_tac o GSYM) >> simp[] >>
        irule SUBMAP_agrees_on >>
        simp[]) >>
   simp[] >>
   simp[insth_def] >>
   ‘(vinsth hσ2 (uniqify uσ th2)) =
   (vinsth hσ (uniqify uσ th2))’
    by (irule vinsth_cong >> reverse (rw[]) (* 2 *)
        >- (simp[cont_uniqify] >>
           qpat_x_assum ‘FDOM hσ2 = cont th2’
        (assume_tac o GSYM) >> simp[] >>
        irule SUBMAP_agrees_on >>
        simp[]) >> cheat) >> simp[] >>
   irule fVinsth_cong >> gs[] >>
   qpat_x_assum ‘FDOM fσ2 = _’ (assume_tac o GSYM) >>
   simp[] >> irule SUBMAP_agrees_on >> simp[]
QED


Theorem wff_wfvl_mk_FALLL:
wfvl Σf vl False ⇒ wff (Σf,Σp,Σe) (mk_FALLL vl False)
Proof
Induct_on ‘LENGTH vl’ >> rw[mk_FALLL_def,wff_False] >>
Cases_on ‘vl’ >>gs[] >>
first_x_assum $ qspecl_then [‘t’] assume_tac >>gs[] >>
gs[wfvl_alt] >> Cases_on ‘h’ >> 
simp[mk_FALLL_def] >>
irule $ cj 6 wff_rules >> gs[] >>
simp[fVslfv_mk_FALLL] >> metis_tac[]
QED

        

            
Theorem wfcfVmap_inst_EX:
∀fσ δ.
 FINITE δ ∧
 (∀fv. fv ∈ δ ⇒ wffV (FST Σ) fv) ∧
 wfcfVmap Σ fσ ∧ FDOM fσ ∩ δ = ∅ ⇒
 ∃fσ1.
   wfcfVmap Σ fσ1 ∧ FDOM fσ1 = FDOM fσ ∪ δ ∧
   fσ ⊑ fσ1 ∧
   ∀fv. fv ∈ δ ⇒ ffv (fσ1 ' fv) = {}
Proof
Induct_on ‘FINITE’ >> rw[] (* 2 *)
>- (qexists ‘fσ’ >> simp[]) >>
‘FDOM fσ ∩ δ = {}’ by (gs[EXTENSION] >> metis_tac[]) >>
‘e ∉ FDOM fσ’ by (gs[EXTENSION] >> metis_tac[]) >>
‘(∀fv. fv ∈ δ ⇒ wffV (FST Σ) fv)’ by metis_tac[] >>
first_x_assum $ drule_all_then assume_tac >> 
gs[] >> qexists ‘fσ1 |+ (e,False)’ >>
rw[] (* 5 *)
>- (gs[wfcfVmap_def,wffVmap_def,cfVmap_def] >>
   rw[] (* 6 *)
   >- (simp[FAPPLY_FUPDATE_THM] >>
      last_x_assum $ qspecl_then [‘(P,sl)’] assume_tac >>
      gs[wffV_def] >>
      qpat_x_assum ‘_ = sl’ (assume_tac o GSYM) >> 
      simp[GSYM mk_FALLL_False] >>
      Cases_on ‘Σ’ >> Cases_on ‘r’ >>
      irule wff_wfvl_mk_FALLL >> gs[])
   >- (gs[FAPPLY_FUPDATE_THM] >>
      ‘(P,sl) ≠ e’ by metis_tac[] >> simp[])
   >- (gs[FAPPLY_FUPDATE_THM] >>
      ‘(P,sl) ≠ e’ by metis_tac[] >> simp[]) 
   >- simp[FAPPLY_FUPDATE_THM,is_cfm_def] >>
   gs[FAPPLY_FUPDATE_THM] >>
   ‘(P,sl) ≠ e’ by metis_tac[] >> simp[])
>- (gs[EXTENSION] >> metis_tac[])
>- (‘e ∉ FDOM fσ1’ by (gs[EXTENSION] >> metis_tac[]) >>
    gs[SUBMAP_DEF,FAPPLY_FUPDATE_THM] >> rw[]) >>
simp[FAPPLY_FUPDATE_THM] >> rw[]    
QED   

            
Theorem uniqifn_DISJOINT_IMAGE_DISJOINT:
uniqifn uσb (s1 ∪ s2) ∧ s1 ∩ s2 = {} ⇒
IMAGE (vinst_fVar hσ ∘ fVrn uσb) s1 ∩
IMAGE (vinst_fVar hσ ∘ fVrn uσb) s2 = {}
Proof
rw[] >>
‘(∀fv. fv ∈ IMAGE (vinst_fVar hσ ∘ fVrn uσb) s2 ⇒
 fv ∉ IMAGE (vinst_fVar hσ ∘ fVrn uσb) s1) ∧
 (∀fv. fv ∈ IMAGE (vinst_fVar hσ ∘ fVrn uσb) s1 ⇒
 fv ∉ IMAGE (vinst_fVar hσ ∘ fVrn uσb) s2)’
 suffices_by (simp[Once EXTENSION] >>
metis_tac[]) >> rpt strip_tac (* 2 *)
>> (gs[] >>
Cases_on ‘x’ >>Cases_on ‘x'’ >> gs[fVrn_def] >>
‘(q,r) ∈ FDOM uσb ∧ (q',r') ∈ FDOM uσb’
 by (gs[uniqifn_def,SUBSET_DEF] >> metis_tac[]) >>
gs[vinst_fVar_def,vinst_fVar_def] >>
‘(q,r) ≠ (q',r')’ by (gs[EXTENSION] >>
metis_tac[]) >>
drule_then assume_tac $ iffLR uniqifn_def >>
pop_assum mp_tac >> simp[] >> disj2_tac >>
first_x_assum $ irule_at Any >> simp[] >> gs[]) 
QED
 


Theorem wffV_wffVsl:
wffV Σf (P,sl) ⇔ wffVsl Σf sl
Proof
rw[wffVsl_def,wffV_def]
QED

Theorem wffV_sinst_wffV:
wffV Σf fv ∧
     (∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧ wfvmap Σf σ ⇒ wffV Σf (vinst_fVar σ fv)
Proof
Cases_on ‘fv’ >> simp[wffV_wffVsl,vinst_fVar_def] >>
rw[] >> irule wffVsl_sinst >>
gs[wfvmap_def]
QED

Theorem wffV_fVrn:
wffV Σ fv ⇒ wffV Σ (fVrn uσ fv)
Proof
Cases_on ‘fv’ >> simp[wffV_wffVsl,fVrn_def] >>
rw[wffV_wffVsl]
QED


Theorem main_mp_case:
 wfsigaxs Σ axs ∧
      Pf Σ axs pf ∧
      Pf Σ axs pf' ∧
      MEM (Γ1,A1,IMP f1 f2) pf ∧
      MEM (Γ2,A2,f1) pf' ∧
      Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ∧
      (∀vσ' fσ' uσ'.
        wfvmap (FST Σ) vσ' ∧ wfcfVmap Σ fσ' ∧
        thfVars (vinsth vσ' (uniqify uσ' (Γ2,A2,f1))) ⊆ FDOM fσ' ∧
        Γ2 ⊆ FDOM vσ' ∧ uniqifn uσ' (thfVars (Γ2,A2,f1)) ⇒
        Pf0Drv Σ aths (insth fσ' vσ' (uniqify uσ' (Γ2,A2,f1)))) ∧
      (∀vσ' fσ' uσ'.
        wfvmap (FST Σ) vσ' ∧ wfcfVmap Σ fσ' ∧
        thfVars (vinsth vσ' (uniqify uσ' (Γ1,A1,IMP f1 f2))) ⊆ FDOM fσ' ∧
        Γ1 ⊆ FDOM vσ' ∧ uniqifn uσ' (thfVars (Γ1,A1,IMP f1 f2)) ⇒
        Pf0Drv Σ aths (insth fσ' vσ' (uniqify uσ' (Γ1,A1,IMP f1 f2)))) ∧
      PfDrv Σ axs (Γ1 ∪ Γ2,A1 ∪ A2,f2) ∧
      wfvmap (FST Σ) hσ ∧
      wfcfVmap Σ fσ ∧
      thfVars (vinsth hσ (uniqify uσ (Γ1 ∪ Γ2,A1 ∪ A2,f2))) = FDOM fσ ∧
      Γ1 ∪ Γ2 = FDOM hσ ∧
      uniqifn uσ (thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2)) ∧
      thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2) = FDOM uσ ⇒
        Pf0Drv Σ aths (insth fσ hσ (uniqify uσ (FDOM hσ,A1 ∪ A2,f2)))
Proof
rpt strip_tac >>
‘(FDOM hσ,A1 ∪ A2,f2) = MP0 (Γ1,A1,IMP f1 f2) (Γ2,A2,f1)’
 by simp[MP0_def] >>
simp[] >>
qabbrev_tac ‘extras =
fVars f1 DIFF
(Uof fVars ({f2} ∪ A1 ∪ A2))’ >>
‘FINITE extras’ by
simp[Abbr ‘extras’,fVars_FINITE] >>
‘FDOM uσ ∩ extras = {}’
 by (qpat_x_assum ‘_ = FDOM uσ’ (assume_tac o GSYM) >>
    simp[Abbr‘extras’] >>
    REWRITE_TAC[MP0_def] >>
    simp[thfVars_def,Uof_Sing,Uof_UNION] >>
    simp[EXTENSION] >> metis_tac[]) >> 
‘∃uσb.
uniqifn uσb ((thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2)) ∪ extras) ∧
FDOM uσb = ((thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2)) ∪ extras) ∧
uσ ⊑ uσb’
 by (qspecl_then [‘uσ’,‘extras’,
                 ‘(thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2))’]
    assume_tac uniqifn_inst_EX >>
    gs[] >>
    qexists ‘uσ1’ >> simp[] >>
    simp[SUBMAP_DEF]) >>
‘∃fσb.
 wfcfVmap Σ fσb ∧
 FDOM fσb = IMAGE ((vinst_fVar hσ) o fVrn uσb)
                  ((Uof fVars ({f2} ∪ A1 ∪ A2)) ∪ extras) ∧
 fσ ⊑ fσb ∧
 ∀fv. fv ∈ extras ⇒ ffv (fσb ' (vinst_fVar hσ (fVrn uσb fv))) = {}’ by
  (qspecl_then [‘fσ’,‘IMAGE (vinst_fVar hσ ∘ fVrn uσb) extras’] assume_tac wfcfVmap_inst_EX >>
 ‘(∀fv. fv ∈ IMAGE (vinst_fVar hσ ∘ fVrn uσb) extras ⇒ wffV (FST Σ) fv)’
   by (simp[PULL_EXISTS] >>
   rw[] >> irule wffV_sinst_wffV >>
   Cases_on ‘Σ’ >> Cases_on ‘r’ >>
   gs[wfsigaxs_def1,wfsig_def] >>
   irule wffV_fVrn >>
   irule wff_wffV' >> rename [‘(Σf,Σp,Σe)’] >>
   qexistsl [‘f1’,‘Σe’,‘Σp’] >> rw[] (* 2 *)
   >- gs[Abbr‘extras’] >>
   irule PfDrv_concl_wff >>
   qexistsl [‘A2’,‘axs’,‘Γ2’] >>
   simp[wfsigaxs_def1,wfsig_def] >>
   metis_tac[PfDrv_def]) >> 
 ‘IMAGE (vinst_fVar hσ ∘ fVrn uσb)
            (Uof fVars ({f2} ∪ A1 ∪ A2)) 
  ∩ IMAGE (vinst_fVar hσ ∘ fVrn uσb) extras = {}’
  by (irule uniqifn_DISJOINT_IMAGE_DISJOINT >>
     ‘thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2) = Uof fVars ({f2} ∪ A1 ∪ A2)’ by (gs[thfVars_def,Uof_def,EXTENSION] >>
       metis_tac[]) >> gs[]) >>
  gs[] >>
  ‘FDOM fσ = IMAGE (vinst_fVar hσ ∘ fVrn uσb) (Uof fVars ({f2} ∪ A1 ∪ A2))’
   by (qpat_x_assum ‘_ = FDOM fσ’ (assume_tac o GSYM) >>
      simp[] >>
      simp[thfVars_vinsth,thfVars_uniqify] >>
      qpat_x_assum ‘_ = FDOM uσ’ (assume_tac o GSYM) >>
      simp[] >>
      REWRITE_TAC[MP0_def,IMAGE_IMAGE] >>
      ‘thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2) = Uof fVars ({f2} ∪ A1 ∪ A2)’ by (gs[thfVars_def,Uof_def,EXTENSION] >>
       metis_tac[]) >> simp[] >>
      simp[GSYM IMAGE_IMAGE] >>
      AP_TERM_TAC >>
      irule IMAGE_eq_lemma >>
      gs[SUBMAP_DEF] >> rw[] >> Cases_on ‘a’ >>
      simp[fVrn_def]) >> gs[] >>
  qexists ‘fσ1’ >> gs[PULL_EXISTS]) >>       
‘(insth fσ hσ (uniqify uσ (MP0 (Γ1,A1,IMP f1 f2) (Γ2,A2,f1)))) =
 (insth fσb hσ (uniqify uσb (MP0 (Γ1,A1,IMP f1 f2) (Γ2,A2,f1))))’ 
  by (‘(uniqify uσ (MP0 (Γ1,A1,IMP f1 f2) (Γ2,A2,f1))) =
      (uniqify uσb (MP0 (Γ1,A1,IMP f1 f2) (Γ2,A2,f1)))’
      by (irule uniqify_cong >>
      ‘(thfVars (MP0 (Γ1,A1,IMP f1 f2) (Γ2,A2,f1))) =
       FDOM uσ’
       by (REWRITE_TAC[MP0_def] >> simp[]) >> simp[] >>
      irule SUBMAP_agrees_on >> simp[]) >> 
     simp[] >> simp[insth_def] >>
     irule fVinsth_cong >>
     ‘(thfVars
             (vinsth hσ (uniqify uσb (MP0 (Γ1,A1,IMP f1 f2) (Γ2,A2,f1))))) =
      FDOM fσ’
       by
        (pop_assum (assume_tac o GSYM) >> simp[] >>
        REWRITE_TAC[MP0_def] >> simp[]) >>
     simp[] >> irule SUBMAP_agrees_on >> simp[]) >>
simp[] >>
dep_rewrite.DEP_REWRITE_TAC[insth_unqify_MP0] >>
simp[concl_def,mp_match,is_imp_def,dest_imp_def] >> rw[]
(* 2 *)
>- (first_x_assum irule >> gs[assum_def] >>
   simp[Abbr‘extras’]) >>
irule Pf0Drv_MP0' >>
simp[concl_insth_uniqify,dest_imp_def,fVinst_def,finst_def,ffVrn_def,is_imp_def,dest_imp_def,concl_def] >> rw[] (* 2 *)
>- (simp[concl_def,mp_match,is_imp_def,dest_imp_def] >>
rw[] >>
   simp[ffVrn_def,instf_def,fVinst_def,finst_def,is_imp_def])
>- (simp[concl_def,mp_match,is_imp_def,dest_imp_def] >>
rw[] >>
   simp[ffVrn_def,instf_def,fVinst_def,finst_def,is_imp_def]>> simp[dest_imp_def])   
>- (first_x_assum irule >>
   simp[] >> rw[] (* 3 *)
   >- (simp[thfVars_vinsth,thfVars_uniqify,IMAGE_IMAGE] >>
      simp[Excl "IMAGE_UNION",GSYM IMAGE_UNION] >>
      irule IMAGE_SUBSET >>
      simp[thfVars_def,Uof_UNION,Uof_Sing,fVars_def,
           Abbr‘extras’] >>
      simp[SUBSET_DEF] >> metis_tac[])
   >- (qpat_x_assum ‘Γ1 ∪ Γ2 = FDOM hσ’
       (assume_tac o GSYM) >> simp[]) >>
   irule uniqifn_SUBSET >>
   first_x_assum $ irule_at Any >>
   qpat_x_assum ‘_ = FDOM uσ’ (assume_tac o GSYM) >>
   simp[thfVars_def,Abbr‘extras’,Uof_UNION,Uof_Sing,
        fVars_def] >> simp[SUBSET_DEF] >> metis_tac[]) >>
first_x_assum irule >> simp[] >> rw[] (* 3 *)
>- (simp[thfVars_vinsth,thfVars_uniqify,IMAGE_IMAGE] >>
    simp[Excl "IMAGE_UNION",GSYM IMAGE_UNION] >>
    irule IMAGE_SUBSET >>
    simp[thfVars_def,Uof_UNION,Uof_Sing,fVars_def,
         Abbr‘extras’] >>
    simp[SUBSET_DEF] >> metis_tac[])
>- (qpat_x_assum ‘Γ1 ∪ Γ2 = FDOM hσ’
    (assume_tac o GSYM) >> simp[]) >>
irule uniqifn_SUBSET >>
first_x_assum $ irule_at Any >>
qpat_x_assum ‘_ = FDOM uσ’ (assume_tac o GSYM) >>
simp[thfVars_def,Abbr‘extras’,Uof_UNION,Uof_Sing,
     fVars_def] >> simp[SUBSET_DEF] >> metis_tac[]
QED     
       
     
    


Theorem fVslfv_ffVrn:
fVslfv (ffVrn uσ f) = fVslfv f
Proof
Induct_on ‘f’ >> gs[fVslfv_alt,ffVrn_def] >>
rw[] >> simp[EXTENSION,IN_fVslfv,IN_slfv',fVars_def]
QED
           
Theorem wff_ffVrn:
∀f. wff Σ f ⇒ wff Σ (ffVrn uσ f)
Proof
Induct_on ‘wff’ >> simp[ffVrn_def,wff_False] >> rw[] (* 6 *)
>- (simp[ffVrn_def,EQ_def] >> rw[GSYM EQ_def] >>
   irule $ cj 2 wff_rules >>
   simp[])
>- (irule $ cj 3 wff_rules >> simp[])
>- simp[wff_IMP]
>- (irule $ cj 5 wff_rules >> simp[])
>- (irule $ cj 5 wff_rules >> simp[]) >>
simp[ffVrn_mk_FALL] >> irule $ cj 6 wff_rules >>
simp[] >> simp[ffv_ffVrn,fVslfv_ffVrn] >> metis_tac[]
QED


Theorem inst_eff_finst:
(∀v. v ∈ ffv f ⇒ inst_eff σ1 v = inst_eff σ v) ⇒
finst σ f = finst σ1 f
Proof
Induct_on ‘f’ >>
gs[finst_def,inst_eff_def,MAP_EQ_f,PULL_EXISTS] (* 3 *)
>- (rw[] >> irule $ cj 1 inst_eff_tinst >> metis_tac[])
>- (rw[] >> irule $ cj 2 inst_eff_tinst >> metis_tac[]) >>
rw[] >- (irule $ cj 2 inst_eff_tinst >> metis_tac[]) >>
irule $ cj 1 inst_eff_tinst >> metis_tac[]
QED

        
Theorem wff_finst1:
(∀fsym. isfsym Σf fsym ⇒
            sfv (fsymout Σf fsym) ⊆
            BIGUNION
              {tfv (Var n s) |
               MEM (n,s) (fsymin Σf fsym)}) ⇒
         ∀σ. wff (Σf,Σp,Σe) f ∧ wfvmap Σf σ ⇒
             wff (Σf,Σp,Σe) (finst σ f)
Proof
strip_tac >>
completeInduct_on ‘form_size f’ >>
rw[] >> gs[wfvmap_def] >>
drule_then assume_tac cstt_EXT1 >>
first_x_assum $ qspecl_then [‘ffv f’] assume_tac>>
gs[] >>
‘(finst σ f) = (finst σ1 f)’
 by (irule inst_eff_finst >> metis_tac[]) >>
   (*by (irule $ cj 1 inst_eff_finst >> metis_tac[]) >>*)
simp[] >>
irule $ wff_finst >> simp[] >>
‘gcont (ffv f) = ffv f’
    by metis_tac[gcont_of_cont,ffv_is_cont] >>
gs[] >>
simp[wfcod_def,PULL_EXISTS] >>
(*‘presname σ1 ’ by wfvmap_presname *)
‘∀n s. (n,s) ∈ ffv f ⇒ wft Σf (σ1 ' (n,s))’ by
(rw[] >> first_x_assum $ drule_then assume_tac >>
gs[inst_eff_def] >>
Cases_on ‘(n,s) ∈ FDOM σ’ (* 2 *) >> simp[] 
>- gs[wfcod_def] >>
simp[wft_def] >>
irule wfs_sinst1 >> simp[] >>
metis_tac[wff_wfs]) >> simp[] >>
irule wfvmap_presname >> qexists ‘Σf’ >>
simp[wfvmap_def,wfcod_def]
QED 
                

Theorem ffVrn_frpl:
∀f i t. ffVrn uσ (frpl i t f) = frpl i t (ffVrn uσ f)
Proof
Induct_on ‘f’ >> gs[ffVrn_def,frpl_def] >>
rw[frpl_def]
QED 

Theorem uniqify_spec:
is_fall (concl th) ⇒ uniqify uσ (spec t th) = spec t (uniqify uσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> simp[concl_def] >>
Cases_on ‘r'’ >> gs[is_fall_def] >>
simp[spec_def,uniqify_def,ffVrn_def] >>
simp[ffVrn_frpl,substb_def]
QED
           


Theorem finst_frpl:
∀f i t σ.
     (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ∧
     (∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = ∅) ⇒
     finst σ (frpl i t f) = frpl i (tinst σ t) (finst σ f)
Proof
Induct_on ‘f’ >>
gs[finst_def,frpl_def,MAP_MAP_o,PULL_EXISTS,
   MAP_EQ_f,PULL_EXISTS] >> rw[] >> TRY (metis_tac[sinst_srpl1])
QED   


Theorem tfv_tinst_vinst_cont:
(∀t σ.
        cstt σ ∧ tfv t ⊆ FDOM σ ∧ (∀v. v ∈ FDOM σ ⇒ ¬is_bound (σ ' v)) ⇒
        tfv (tinst σ t) = vinst_cont σ (tfv t)) ∧
     ∀s σ.
       cstt σ ∧ sfv s ⊆ FDOM σ ∧ (∀v. v ∈ FDOM σ ⇒ ¬is_bound (σ ' v)) ⇒
       sfv (sinst σ s) = vinst_cont σ (sfv s)
Proof       
rw[] (* 2 *)
>- (drule_all_then assume_tac $ cj 1 tfv_tinst >>
   simp[EXTENSION] >>
   Cases_on ‘x’ >> simp[vinst_cont_def,ofFMAP_def,pairTheory.EXISTS_PROD,PULL_EXISTS] >> metis_tac[SUBSET_DEF]) >>
drule_all_then assume_tac $ cj 2 tfv_tinst >>
   simp[EXTENSION] >>
   Cases_on ‘x’ >> simp[vinst_cont_def,ofFMAP_def,pairTheory.EXISTS_PROD,PULL_EXISTS] >> metis_tac[SUBSET_DEF]
QED      



(*
Theorem ffv_finst_vinst_cont:
(∀t σ.
        cstt σ ∧ tfv t ⊆ FDOM σ ∧ (∀v. v ∈ FDOM σ ⇒ ¬is_bound (σ ' v)) ⇒
        ffv (finst σ f) = vinst_cont σ (tfv t)) ∧
     ∀s σ.
       cstt σ ∧ sfv s ⊆ FDOM σ ∧ (∀v. v ∈ FDOM σ ⇒ ¬is_bound (σ ' v)) ⇒
       sfv (sinst σ s) = vinst_cont σ (sfv s)
Proof       
rw[] (* 2 *)
>- (drule_all_then assume_tac $ cj 1 tfv_tinst >>
   simp[EXTENSION] >>
   Cases_on ‘x’ >> simp[vinst_cont_def,ofFMAP_def,pairTheory.EXISTS_PROD,PULL_EXISTS] >> metis_tac[SUBSET_DEF]) >>
drule_all_then assume_tac $ cj 2 tfv_tinst >>
   simp[EXTENSION] >>
   Cases_on ‘x’ >> simp[vinst_cont_def,ofFMAP_def,pairTheory.EXISTS_PROD,PULL_EXISTS] >> metis_tac[SUBSET_DEF]
QED
*)


Theorem wff_FALL_no_vbound:
wff Σ (FALL s b) ⇒
∀n0 s0. (n0,s0) ∈ ffv b ⇒ sbounds s0 = {}
Proof        
rw[] >> ‘(n0,s0) ∈ ffv (FALL s b)’ by simp[ffv_def] >>
metis_tac[wff_no_vbound]
QED
                      
Theorem vinsth_spec:
wfsigaxs Σ axs ∧ PfDrv Σ axs th ∧ wfvmap (FST Σ) vσ ∧
tfv t ⊆ FDOM vσ ∧
is_fall (concl th) ⇒ vinsth vσ (spec t th) = spec (tinst vσ t) (vinsth vσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> simp[concl_def] >>
Cases_on ‘r'’ >> gs[is_fall_def] >>
simp[spec_def,vinsth_def,vinst_cont_UNION] >>
simp[substb_def] >> strip_tac >>
dep_rewrite.DEP_REWRITE_TAC[finst_frpl] >>
gs[wfvmap_def] >> 
‘(∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅)’
 by (drule_all_then assume_tac PfDrv_concl_wff >>
    metis_tac[wff_FALL_no_vbound]) >> simp[] >>
    rw[] (* 3 *)
>- metis_tac[]
>- metis_tac[wfcod_no_bound,no_bound_def] >>
‘vinst_cont vσ (tfv t) = tfv (tinst vσ t)’
 suffices_by metis_tac[] >>
irule $ GSYM $ cj 1 tfv_tinst_vinst_cont >> simp[] >>
metis_tac[wfcod_no_bound,no_bound_not_bound]
QED
    
 


Theorem fVinst_frpl:
∀f t i.
wffVmap (Σf,Σg,Σe) fσ ∧ wffsig Σf ∧ tbounds t = {} ∧
       (∀P sl tl. fVar P sl tl ∈ subfm f ⇒ LENGTH sl = LENGTH tl) ⇒
fVinst fσ (frpl i t f) = frpl i t (fVinst fσ f)
Proof
rw[] >> drule_then assume_tac frpl_fprpl >> simp[] >>
irule fVinst_fprpl >> metis_tac[]
QED

 
Theorem fVinsth_spec:
wffVmap Σ fσ ∧ wffsig (FST Σ) ∧ wft (FST Σ) t ∧
wfsigaxs Σ axs ∧ PfDrv Σ axs th ∧ 
is_fall (concl th) ⇒
fVinsth fσ (spec t th) = spec t (fVinsth fσ th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> Cases_on ‘r'’ >>
gs[is_fall_def,concl_def] >>
simp[spec_def,fVinsth_def,fVinst_def,Uof_UNION,Uof_Sing,
 fVars_def,fVars_frpl,substb_def] >>
rw[] (* 2 *)
>- (simp[EXTENSION] >> metis_tac[]) >>
irule fVinst_frpl >> rw[] (* 3 *)
>- (drule_all_then assume_tac PfDrv_concl_wff >>
   irule wff_subfm_fVar_LENGTH >>
   first_x_assum $ irule_at Any >> simp[subfm_def] >>
   metis_tac[])
>- metis_tac[wft_no_bound] >>
Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[] >> metis_tac[]
QED      
   


Theorem wff_ffVrn:
wffsig (FST Σ) ∧ wff Σ f ⇒ wff Σ (ffVrn uσ f)
Proof
rw[] >>
‘(ffVrn uσ f) = ffVrn (DRESTRICT uσ (fVars f)) f’
 by (irule ffVrn_eq >> simp[DRESTRICT_DRESTRICT]) >>
simp[] >>  
dep_rewrite.DEP_REWRITE_TAC[ffVrn_fVinst] >>
drule_then assume_tac wff_subfm_fVar_LENGTH >> rw[](* 2 *)
>- metis_tac[] >>
Cases_on ‘Σ’ >> Cases_on ‘r’ >> irule wff_fVinst >>
gs[wffsig_def] >>
irule wffVmap_rn2fVmap >> simp[FDOM_DRESTRICT] >>
rw[] >>
drule_then assume_tac wff_wffV >>
gs[wffV_def] >> first_x_assum $ drule_then assume_tac >>
gs[wffV_def] >> metis_tac[]
QED


Theorem ofFMAP_ffv_FINITE:
FINITE (ofFMAP ffv σ s)
Proof
rw[ofFMAP_def,ffv_FINITE]>> gs[ffv_FINITE] >>
‘{ffv (σ ' a) | a | a ∈ FDOM σ ∧ a ∈ s} =
 IMAGE ffv (FRANGE (DRESTRICT σ s))’
 by (simp[EXTENSION,FRANGE_DEF,DRESTRICT_DEF,AllCaseEqs()] >>
 metis_tac[]) >>
 simp[]
QED  


Theorem ofFMAP_tfv_FINITE:
FINITE (ofFMAP tfv σ s)
Proof
rw[ofFMAP_def,tfv_FINITE]>> gs[tfv_FINITE] >>
‘{tfv (σ ' a) | a | a ∈ FDOM σ ∧ a ∈ s} =
 IMAGE tfv (FRANGE (DRESTRICT σ s))’
 by (simp[EXTENSION,FRANGE_DEF,DRESTRICT_DEF,AllCaseEqs()] >>
 metis_tac[]) >>
 simp[]
QED  
     

Theorem vinst_cont_FINITE:
FINITE (vinst_cont σ ct)
Proof
rw[vinst_cont_def,ofFMAP_tfv_FINITE]
QED 

   

Theorem thfVars_add_cont1:
thfVars (add_cont1 (n,s) th) = thfVars th
Proof 
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[thfVars_def,add_cont1_def]
QED


   
Theorem cont_add_cont1:
cont (add_cont1 (n,s) th) =
{(n,s)} ∪ sfv s ∪ cont th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[add_cont1_def,cont_def]
QED

Theorem uniqify_refl:
uniqify uσ (refl t) = refl t
Proof
simp[refl_def,uniqify_def,EQ_def,ffVrn_def]
QED

Theorem vinsth_refl:
tfv t ⊆ FDOM vσ ∧ wfvmap Σf vσ ⇒
vinsth vσ (refl t) = refl (tinst vσ t)
Proof
simp[refl_def,vinsth_def,finst_EQ] >>
rw[] >> irule $ GSYM $ cj 1 tfv_tinst_vinst_cont >>
metis_tac[wfvmap_def,wfcod_no_bound,no_bound_not_bound]
QED          

Theorem fVinsth_refl:
fVinsth fσ (refl t) = refl t
Proof
simp[refl_def,fVinsth_def,EQ_def,
  ffVrn_def,fVars_def,Uof_Sing,fVinst_def,ofFMAP_EMPTY]
QED  

             
Theorem thfVars_EQ:
thfVars (Γ,A,EQ t1 t2) = Uof fVars A
Proof
simp[thfVars_def,Uof_UNION,Uof_Sing,fVars_EQ]
QED 


Theorem ffVrn_EQ:
ffVrn uσ (EQ t1 t2) = EQ t1 t2
Proof
rw[ffVrn_def,EQ_def]
QED
    
Theorem UCIth_alt:
UCIth Σ th =
       {insth fσ vσ (uniqify uσ th) |
        (fσ,vσ,uσ) |
        uniqifn uσ (thfVars th) ∧
        IMAGE (λ(P,sl). (uσ ' (P,sl),MAP (sinst vσ) sl)) (thfVars th) ⊆ FDOM fσ ∧
        wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧ cont th ⊆ FDOM vσ}
Proof
cheat
QED


Theorem ffVrn_IFF:
ffVrn uσ (IFF f1 f2) = IFF (ffVrn uσ f1) (ffVrn uσ f2)
Proof
simp[ffVrn_def,IFF_def,CONJ_def,NEG_def]
QED


Theorem finst_IFF:
finst σ (IFF f1 f2) = IFF (finst σ f1) (finst σ f2)
Proof
simp[finst_def,IFF_def,CONJ_def,NEG_def]
QED


Theorem fVinst_IFF:
fVinst fσ (IFF f1 f2) = IFF (fVinst fσ f1) (fVinst fσ f2)
Proof
simp[fVinst_def,IFF_def,CONJ_def,NEG_def]
QED        
        
Theorem IFF_eq_eq:
IFF f1 f2 = IFF f3 f4 ⇔ f1 = f3 ∧ f2 = f4
Proof
simp[IFF_def,CONJ_def,NEG_def] >> metis_tac[]
QED       
        

Theorem fVars_IFF:
fVars (IFF f1 f2) = fVars f1 ∪ fVars f2
Proof
simp[IFF_def,CONJ_def,NEG_def,fVars_def] >>
simp[EXTENSION] >> metis_tac[]
QED

        
Theorem cfVmap_alt:
cfVmap σ ⇔
 ∀P sl. (P,sl) ∈ FDOM σ ⇒ is_cfm (σ ' (P,sl))
Proof
cheat
QED 


Theorem concl_fv_IN_thfVars_fVcong:
(P,sl) ∈ thfVars (fVcong eqthl P sl)
Proof
simp[fVcong_def,thfVars_def,Uof_UNION,Uof_Sing,fVars_IFF,
      fVars_def]
QED        
    
Theorem main:
 wfsigaxs Σ axs ⇒
 ∀pf. Pf Σ axs pf ⇒
      Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ⇒
      ∀th. MEM th pf ⇒
 ∀vσ fσ uσ. wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
           thfVars (vinsth vσ (uniqify uσ th)) ⊆ FDOM fσ ∧
           cont th ⊆ FDOM vσ ∧ uniqifn uσ (thfVars th) ⇒
           Pf0Drv Σ aths (insth fσ vσ (uniqify uσ th))
Proof
strip_tac >>
Induct_on ‘Pf’ >> rw[] >> TRY (metis_tac[]) (* 16 *)
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
        by (first_x_assum irule >> rw[] >>
           irule wffVmap_no_vbound >>
           metis_tac[wfcfVmap_def]) >>
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
     (* irule wff_fVinst >> *)
   cheat)
>~ [‘MEM (Γ1,A1,IMP f1 f2) pf’]
>- (gs[cont_def] >>
   first_x_assum $ drule_then assume_tac >>
   last_x_assum $ drule_then assume_tac >> gs[cont_def] >>
   drule_then assume_tac gen_precise_maps_ex1 >>
   ‘PfDrv Σ axs (Γ1 ∪ Γ2,A1 ∪ A2,f2)’
     by (irule PfDrv_mp >> metis_tac[PfDrv_def]) >>
   first_x_assum $ drule_then assume_tac >>
   gs[cont_def]>>
   first_x_assum $ drule_all_then strip_assume_tac >>
   qpat_x_assum ‘Γ1 ⊆ FDOM vσ’ (K all_tac) >>
   qpat_x_assum ‘Γ2 ⊆ FDOM vσ’ (K all_tac) >>
   qpat_x_assum ‘thfVars (vinsth vσ (uniqify uσ (Γ1 ∪ Γ2,A1 ∪ A2,f2))) ⊆ FDOM fσ’ (K all_tac) >>
   qpat_x_assum ‘wfvmap (FST Σ) vσ’ (K all_tac) >>
   qpat_x_assum ‘wfcfVmap Σ fσ’ (K all_tac) >>
   qpat_x_assum ‘uniqifn uσ (thfVars (Γ1 ∪ Γ2,A1 ∪ A2,f2))’
   (K all_tac) >>
   simp[] >> pop_assum (K all_tac) >>
   rename
   [‘(insth fσ hσ (uniqify uσ (FDOM hσ,A1 ∪ A2,f2)))’] >>
   metis_tac[main_mp_case])
>~ [‘uniqifn uσ (thfVars (gen (x,s) (Γ,A,f)))’]
>- (irule main_gen_case >> simp[] >>
   metis_tac[PfDrv_def])
>~ [‘(spec t (Γ,A,FALL (sort_of t) f))’]
>- (gs[] >>
   first_x_assum $ drule_then assume_tac >>
   first_x_assum $ qspecl_then [‘vσ’,‘fσ’,‘uσ’] assume_tac >>
   gs[cont_def] >>
   dep_rewrite.DEP_REWRITE_TAC[uniqify_spec] >>
   simp[concl_def,is_fall_def] >>
   gs[spec_def,cont_def] >>
   simp[insth_def] >>
   dep_rewrite.DEP_REWRITE_TAC[vinsth_spec] >>
   ‘PfDrv Σ axs (Γ,A,FALL (sort_of t) f)’
    by metis_tac[PfDrv_def] >>
   drule_then assume_tac PfDrv_uniqify >> gs[] >>
   rw[] (* 2 *)
   >- simp[is_fall_def,concl_def,uniqify_def,ffVrn_def] >>
   dep_rewrite.DEP_REWRITE_TAC[fVinsth_spec] >>
   simp[] >> rw[] (* 6 *)
   >- gs[wfcfVmap_def]
   >- (Cases_on ‘Σ’ >> Cases_on ‘r’ >>
      gs[wfsigaxs_def1,wfsig_def,wffsig_def])
   >- (irule wft_tinst1 >>
      Cases_on ‘Σ’ >> Cases_on ‘r’ >>
      gs[wfsigaxs_def1,wfsig_def,wffsig_def,wfvmap_def])
   >- (irule PfDrv_vinsth >>
      simp[cont_uniqify,cont_def])
   >- simp[concl_def,uniqify_def,vinsth_def,
           finst_def,ffVrn_def,is_fall_def] >>
   irule Pf0Drv_spec >> rw[] (* 4 *)
   >- simp[uniqify_def,vinsth_def,fVinsth_def,concl_def,
           finst_def,ffVrn_def,fVinst_def,is_fall_def]
   >- (simp[uniqify_def,vinsth_def,fVinsth_def,concl_def,
           finst_def,ffVrn_def,fVinst_def,is_fall_def,
           dest_forall_def] >>
      irule cstt_sort_of_tinst' >>
      gs[wfvmap_def] >>
      metis_tac[wfcod_no_bound,wft_not_bound])
   >- (irule wft_tinst1 >>
      Cases_on ‘Σ’ >> Cases_on ‘r’ >>
      gs[wfsigaxs_def1,wfsig_def,wffsig_def,wfvmap_def]) >>
   simp[GSYM insth_def] >> first_x_assum irule >>
   reverse (rw[]) (* 2 *)
   >- gs[thfVars_def,Uof_UNION,Uof_Sing,fVars_def,
         substb_def,fVars_frpl] >>
   gs[thfVars_vinsth,thfVars_uniqify,
      thfVars_def,Uof_UNION,Uof_Sing,fVars_def,
         substb_def,fVars_frpl])
>~ [‘MEM (Γ,A,False) pf’]
>- (gs[cont_def] >>
   ‘Pf0Drv Σ aths (insth fσ vσ (uniqify uσ (Γ,A,False)))’
     by (first_x_assum irule >> simp[cont_def] >>
        rw[] (* 2 *)
        >- (gs[thfVars_vinsth,thfVars_uniqify] >>
           gs[thfVars_def,Uof_UNION,Uof_Sing,fVars_def]) >>
        gs[thfVars_def,Uof_UNION,Uof_Sing,fVars_def] >>
        irule uniqifn_SUBSET >>
        first_x_assum $ irule_at Any >> simp[]) >>
   gs[insth_def,uniqify_def,vinsth_def,fVinsth_def,
      finst_def,ffVrn_def,fVinst_def,Uof_UNION,Uof_Sing,
      fVars_def] >>
   drule_then assume_tac Pf0Drv_fromBot >>
   first_x_assum $ qspecl_then [‘fVinst fσ (finst vσ (ffVrn uσ f))’] assume_tac >>
   ‘vinst_cont vσ Γ ∪
           ofFMAP ffv fσ (Uof fVars (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A))) ∪
           ffv (fVinst fσ (finst vσ (ffVrn uσ f))) ⊆ vinst_cont vσ (Γ ∪ ffv f) ∪
           ofFMAP ffv fσ
             (fVars (finst vσ (ffVrn uσ f)) ∪
              Uof fVars (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)))’
    by (simp[vinst_cont_UNION,ofFMAP_UNION] >> rw[] (* 3 *)
       >- (simp[SUBSET_DEF] >> metis_tac[])
       >- (simp[SUBSET_DEF] >> metis_tac[]) >>
       ‘ffv (finst vσ (ffVrn uσ f)) ∪ ffv (fVinst fσ (finst vσ (ffVrn uσ f))) ⊆
       vinst_cont vσ Γ ∪ vinst_cont vσ (ffv f) ∪
        (ofFMAP ffv fσ (fVars (finst vσ (ffVrn uσ f))) ∪
         ofFMAP ffv fσ (Uof fVars (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A))))’ suffices_by (gs[SUBSET_DEF] >> metis_tac[])>>
        dep_rewrite.DEP_REWRITE_TAC[ffv_fVinst] >>
        dep_rewrite.DEP_REWRITE_TAC[ffv_finst_alt] >>
        REWRITE_TAC[vinst_cont_def,ffv_ffVrn] >>
        gs[wfvmap_def] >> rw[] (* 4 *)
        >- metis_tac[wfcod_no_bound]
        >- metis_tac[wffVmap_no_vbound,wfcfVmap_def]
        >- (gs[SUBSET_DEF] >> metis_tac[]) >>
        gs[SUBSET_DEF,ofFMAP_def] >> metis_tac[]) >>
    irule Pf0Drv_cont_SUBSET_cong >>
    rpt $ irule_at Any EQ_REFL >>
    first_x_assum $ irule_at Any >> reverse (rw[]) (* 6 *)
    >- (first_x_assum irule >> rw[] (* 2 *)
        >- (irule fVinst_cfVmap_is_cfm >>
           gs[wfcfVmap_def,thfVars_def,Uof_UNION,Uof_Sing])
           >>
        Cases_on ‘Σ’ >> Cases_on ‘r’ >> irule wff_fVinst >>
        gs[wfcfVmap_def] >> strip_tac (* 2 *)
        >- gs[wfsigaxs_def1,wfsig_def,wffsig_def,
              wfvmap_def] >>
        irule wff_finst >>
        gs[wfsigaxs_def1,wfsig_def,wffsig_def,
              wfvmap_def] >>
        gs[ffv_ffVrn] >> rw[] (* 2 *)
        >- metis_tac[wfvmap_def,wfvmap_presname] >>
        irule wff_ffVrn >>
        gs[wfsigaxs_def1,wfsig_def,wffsig_def,wfvmap_def])
    >- (irule UNION_is_cont >>
       simp[vinst_cont_is_cont,ofFMAP_ffv_is_cont])
    >- simp[ofFMAP_ffv_FINITE]
    >- simp[vinst_cont_FINITE]
    >- (irule wffVmap_ofFMAP_var_wf >>
       first_x_assum $ irule_at Any >>
       Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[wfcfVmap_def] >>
       metis_tac[]) >>
    irule wfvmap_IN_ofMAP_wfs >>
    gs[vinst_cont_def] >>
    first_x_assum $ irule_at Any >>
    Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[])
>~ [‘(disch a th)’]
>- (gs[] >>
   Cases_on ‘th’ >> Cases_on ‘r’ >>
   rename [‘(Γ,A,f)’] >> gs[disch_def,cont_def] >>
   first_x_assum $ drule_then assume_tac >>
   ‘Pf0Drv Σ aths (insth fσ vσ (uniqify uσ (Γ,A,f)))’
    by (first_x_assum irule >>
       gs[cont_def,thfVars_vinsth,thfVars_uniqify] >>
       gs[thfVars_def,Uof_UNION,Uof_Sing,fVars_def] >>
       rw[] (* 2 *)
       >- (gs[SUBSET_DEF,Uof_def] >> metis_tac[]) >>
       irule uniqifn_SUBSET >>
       first_x_assum $ irule_at Any >>
       gs[SUBSET_DEF,Uof_def] >> metis_tac[]) >>
   gs[uniqify_def,insth_def,fVinsth_def,vinsth_def] >>
   drule_then assume_tac Pf0Drv_disch >>
   first_x_assum $ qspecl_then
   [‘fVinst fσ (finst vσ (ffVrn uσ a))’] assume_tac >>
   gs[disch_def] >>
   ‘vinst_cont vσ Γ ∪
           ofFMAP ffv fσ
             (Uof fVars
                ({finst vσ (ffVrn uσ f)} ∪
                 IMAGE (finst vσ) (IMAGE (ffVrn uσ) A))) ∪
           ffv (fVinst fσ (finst vσ (ffVrn uσ a))) ⊆
    vinst_cont vσ (Γ ∪ ffv a) ∪
           ofFMAP ffv fσ
             (Uof fVars
                ({finst vσ (ffVrn uσ (IMP a f))} ∪
                 IMAGE (finst vσ) (IMAGE (ffVrn uσ) (A DELETE a))))’
     by (simp[vinst_cont_UNION] >> rw[] (* 3 *)
        >- (simp[SUBSET_DEF] >> metis_tac[])
        >- (simp[Uof_UNION,Uof_Sing] >>
           simp[SUBSET_DEF,Uof_def,ofFMAP_def,
                ffVrn_def,finst_def,fVars_def] >>
           metis_tac[]) >>
        ‘ffv (finst vσ (ffVrn uσ a)) ∪
         ffv (fVinst fσ (finst vσ (ffVrn uσ a))) ⊆
         vinst_cont vσ Γ ∪ vinst_cont vσ (ffv a) ∪
        ofFMAP ffv fσ
          (Uof fVars
             ({finst vσ (ffVrn uσ (IMP a f))} ∪
              IMAGE (finst vσ) (IMAGE (ffVrn uσ) (A DELETE a))))’ suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
         dep_rewrite.DEP_REWRITE_TAC[ffv_fVinst] >>
         dep_rewrite.DEP_REWRITE_TAC[ffv_finst_alt] >>
        REWRITE_TAC[vinst_cont_def,ffv_ffVrn] >>
        gs[wfvmap_def] >> rw[] (* 4 *)
        >- metis_tac[wfcod_no_bound]
        >- metis_tac[wffVmap_no_vbound,wfcfVmap_def]
        >- (gs[SUBSET_DEF] >> metis_tac[]) >>
        gs[SUBSET_DEF,ofFMAP_def,fVars_finst,
           Uof_UNION,Uof_Sing,ffVrn_def,fVars_def] >>
         metis_tac[]) >>
    ‘IMAGE (fVinst fσ) (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)) DELETE
           fVinst fσ (finst vσ (ffVrn uσ a)) ⊆
    IMAGE (fVinst fσ)
             (IMAGE (finst vσ) (IMAGE (ffVrn uσ) (A DELETE a)))’ by (simp[SUBSET_DEF] >> metis_tac[]) >>
    simp[fVinst_def,finst_def,ffVrn_def] >>
    irule Pf0Drv_cont_assum_SUBSET_cong >>
    irule_at Any EQ_REFL >>
    simp[PULL_EXISTS] >>
    qexistsl [‘vinst_cont vσ Γ ∪
        ofFMAP ffv fσ
          (Uof fVars
             ({finst vσ (ffVrn uσ f)} ∪ IMAGE (finst vσ) (IMAGE (ffVrn uσ) A))) ∪
        ffv (fVinst fσ (finst vσ (ffVrn uσ a)))’,
   ‘IMAGE (fVinst fσ) (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A)) DELETE
        fVinst fσ (finst vσ (ffVrn uσ a))’] >>
    reverse (rw[]) (* 14 *)
    >- (first_x_assum irule >>  rw[] (* 2 *)
       >- (irule fVinst_cfVmap_is_cfm >>
          gs[wfcfVmap_def,thfVars_def,Uof_UNION,Uof_Sing,
             ffVrn_def,finst_def,fVars_def]) >>
       Cases_on ‘Σ’ >> Cases_on ‘r’ >> irule wff_fVinst >>
        gs[wfcfVmap_def] >> strip_tac (* 2 *)
        >- gs[wfsigaxs_def1,wfsig_def,wffsig_def,
              wfvmap_def] >>
        irule wff_finst >>
        gs[wfsigaxs_def1,wfsig_def,wffsig_def,
              wfvmap_def] >>
        gs[ffv_ffVrn] >> rw[] (* 2 *)
        >- metis_tac[wfvmap_def,wfvmap_presname] >>
        irule wff_ffVrn >>
        gs[wfsigaxs_def1,wfsig_def,wffsig_def,wfvmap_def])
    >- (simp[ofFMAP_UNION,GSYM vinst_cont_def,
            vinst_cont_UNION] >>
       ‘ffv (finst vσ (ffVrn uσ a)) ∪
         ffv (fVinst fσ (finst vσ (ffVrn uσ a))) ⊆
         vinst_cont vσ Γ ∪ vinst_cont vσ (ffv a) ∪
        ofFMAP ffv fσ
          (Uof fVars
             ({IMP (finst vσ (ffVrn uσ a)) (finst vσ (ffVrn uσ f))} ∪
              IMAGE (finst vσ) (IMAGE (ffVrn uσ) (A DELETE a))))’ suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
         dep_rewrite.DEP_REWRITE_TAC[ffv_fVinst] >>
         dep_rewrite.DEP_REWRITE_TAC[ffv_finst_alt] >>
        REWRITE_TAC[vinst_cont_def,ffv_ffVrn] >>
        gs[wfvmap_def] >> rw[] (* 4 *)
        >- metis_tac[wfcod_no_bound]
        >- metis_tac[wffVmap_no_vbound,wfcfVmap_def]
        >- (gs[SUBSET_DEF] >> metis_tac[]) >>
        gs[SUBSET_DEF,ofFMAP_def,fVars_finst,
           Uof_UNION,Uof_Sing,ffVrn_def,fVars_def] >>
         metis_tac[])
    >- (simp[Uof_UNION,Uof_Sing,fVars_def,ofFMAP_def,
        SUBSET_DEF] >> simp[Uof_def] >> metis_tac[])
    >- (simp[vinst_cont_UNION] >> simp[SUBSET_DEF] >>
       metis_tac[])
    >- cheat (*simp[wfsigaths_def] wf of aths *)
    >- (simp[Uof_SUBSET,PULL_EXISTS] >> cheat)
    >- (irule UNION_is_cont >>
       simp[ofFMAP_ffv_is_cont,ofFMAP_tfv_is_cont,
            vinst_cont_def])
    >- simp[ofFMAP_ffv_FINITE]
    >- simp[ofFMAP_tfv_FINITE,vinst_cont_def]
    >- cheat (*A is finite*)
    >- (irule wffVmap_ofFMAP_var_wf >>
       Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[] >>
       metis_tac[wfcfVmap_def])
    >- (gs[vinst_cont_def] >>
       irule wfvmap_IN_ofMAP_wfs >>
       Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[] >>
       metis_tac[])
    >- (irule fVinst_cfVmap_is_cfm >>
          gs[wfcfVmap_def,thfVars_def,Uof_UNION,Uof_Sing,
             ffVrn_def,finst_def,fVars_def] >>
       gs[Uof_def,fVars_finst,fVars_ffVrn,SUBSET_DEF,PULL_EXISTS] >> metis_tac[])>>
       Cases_on ‘Σ’ >> Cases_on ‘r’ >> irule wff_fVinst >>
        gs[wfcfVmap_def] >> strip_tac (* 2 *)
        >- gs[wfsigaxs_def1,wfsig_def,wffsig_def,
              wfvmap_def] >>
        irule wff_finst >>
        gs[wfsigaxs_def1,wfsig_def,wffsig_def,
              wfvmap_def] >>
        gs[ffv_ffVrn] >> rw[] (* 3 *)
        >- metis_tac[wfvmap_def,wfvmap_presname]
        >- (‘ffv x'' ⊆ Γ’
             suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
           irule PfDrv_assum_ffv_SUBSET >>
           qexistsl [‘A’,‘axs’,‘f’,‘(q,q',r')’] >>
           gs[wfsigaxs_def1] >> gs[wfsig_def] >>
           metis_tac[PfDrv_def]) >> 
        irule wff_ffVrn >>
        gs[wfsigaxs_def1,wfsig_def,wffsig_def,wfvmap_def] >>
        irule PfDrv_assum_wff >>
        gs[wfsigaxs_def1,wfsig_def] >>
        metis_tac[PfDrv_def])
>~ [‘(add_cont1 (n,s) th)’]
>- (gs[]>>
   first_x_assum $ drule_then assume_tac >>
   ‘Pf0Drv Σ aths (insth fσ vσ (uniqify uσ th))’
    by (first_x_assum irule >>
       gs[thfVars_vinsth,thfVars_uniqify,thfVars_add_cont1,
          cont_add_cont1]) >>
    Cases_on ‘th’ >> Cases_on ‘r’ >>
    gs[uniqify_def,add_cont1_def,insth_def,
       vinsth_def,fVinsth_def] >>
    irule Pf0Drv_cont_SUBSET_cong >>
    rpt (irule_at Any EQ_REFL) >>
    first_x_assum $ irule_at Any >> rw[] (* 6 *)
    >- (gs[vinst_cont_def] >>
       irule wfvmap_IN_ofMAP_wfs >>
       Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[] >>
       metis_tac[])
    >- (irule wffVmap_ofFMAP_var_wf >>
       Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[] >>
       metis_tac[wfcfVmap_def])
    >- simp[vinst_cont_def,ofFMAP_tfv_FINITE]
    >- simp[ofFMAP_ffv_FINITE]
    >- (irule UNION_is_cont >>
       simp[ofFMAP_ffv_is_cont,ofFMAP_tfv_is_cont,
            vinst_cont_def]) >>
    simp[vinst_cont_UNION] >> simp[SUBSET_DEF] >>
    metis_tac[])
>~ [‘refl t’]
>- (gs[uniqify_refl] >> simp[insth_def] >>
   ‘vinsth vσ (refl t) = refl (tinst vσ t)’
    by (irule vinsth_refl >> gs[cont_def,refl_def] >>
       metis_tac[]) >>
   simp[] >> simp[fVinsth_refl] >>
   irule Pf0Drv_refl >> rw[] (* 2 *)
   >- (dep_rewrite.DEP_REWRITE_TAC[tsname_tinst] >>
      simp[] >> metis_tac[wfvmap_presname,wft_not_bound]) >>
   irule wft_tinst1 >> gs[wfsigaxs_def1,wfvmap_def] >>
   Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[wfsig_def])
>~ [‘(Γ,A,EQ t2 t1)’]
>- (gs[cont_def] >>
   rpt (first_x_assum $ drule_then assume_tac) >>
   gs[cont_def] >>
   gs[thfVars_EQ] >>
   first_x_assum $ qspecl_then [‘uσ’] assume_tac >>
   gs[thfVars_EQ,thfVars_uniqify,thfVars_vinsth] >>
   gs[insth_def,uniqify_def,vinsth_def,fVinsth_def,Uof_UNION,Uof_Sing,fVars_EQ] >>
   gs[ffVrn_EQ,finst_EQ,fVars_EQ,fVinst_EQ] >>
   irule Pf0Drv_sym >> simp[])
>~ [‘(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)’]
>- (gs[cont_def,thfVars_EQ,thfVars_vinsth,thfVars_uniqify,
      Uof_UNION] >>
   first_x_assum $ drule_then assume_tac >>
   first_x_assum $ qspecl_then [‘vσ’,‘fσ’,‘uσ’] assume_tac>>
   gs[cont_def,thfVars_EQ] >>
   ‘uniqifn uσ (Uof fVars A2) ∧ uniqifn uσ (Uof fVars A1)’
    by (rw[] >> irule uniqifn_SUBSET >>
       first_x_assum $ irule_at Any>> simp[]) >>
   gs[] >>
   first_x_assum $ drule_then assume_tac >>
   first_x_assum $ qspecl_then [‘vσ’,‘fσ’,‘uσ’] assume_tac>>
   gs[cont_def,thfVars_EQ] >>
   gs[insth_def,fVinsth_def,vinsth_def,uniqify_def] >>
   gs[fVinst_EQ,finst_EQ,ffVrn_EQ] >>
   drule_then assume_tac Pf0Drv_trans >>
   first_x_assum $ drule_then assume_tac >>
   gs[Uof_UNION,Uof_Sing,fVars_EQ] >>
   ‘vinst_cont vσ Γ1 ∪
           ofFMAP ffv fσ (Uof fVars (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A1))) ∪
           (vinst_cont vσ Γ2 ∪
            ofFMAP ffv fσ
              (Uof fVars (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A2)))) =
    vinst_cont vσ (Γ1 ∪ Γ2) ∪
           ofFMAP ffv fσ
             (Uof fVars (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A1)) ∪
              Uof fVars (IMAGE (finst vσ) (IMAGE (ffVrn uσ) A2)))’ by (simp[vinst_cont_UNION,ofFMAP_UNION] >>
         simp[EXTENSION] >> metis_tac[]) >> gs[])
>~ [‘(ffv ax,∅,ax)’]   
>- (rw[Pf0Drv_def] >> irule_at Any Pf0_AX >>
   gs[Uof_SUBSET,PULL_EXISTS] >>
   first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >>
   first_assum irule >> gs[UCIth_alt] >>
   gs[ax2th_def] >> first_assum $ irule_at Any >>
   irule_at Any EQ_REFL >>
   gs[] >> simp[SUBSET_DEF] >>
   simp[PULL_EXISTS,thfVars_def,Uof_Sing] >>
   rw[] >> first_x_assum irule >>
   simp[thfVars_def,vinsth_def,Uof_Sing] >>
   rw[fVars_finst,vinst_fVar_def] >>
   Cases_on ‘x'’ >>  gs[] >>
   simp[thfVars_vinsth,thfVars_uniqify,PULL_EXISTS] >>
   qexists ‘(q,r)’ >>
   simp[vinst_fVar_def,fVrn_def,thfVars_def,Uof_Sing] >>
   ‘(q,r) ∈ FDOM uσ’
    by (gs[uniqifn_def,thfVars_def,Uof_Sing] >>
       gs[SUBSET_DEF] >> metis_tac[]) >>
   simp[vinst_fVar_def])
>~ [‘MEM th (FLAT (map2list (LENGTH sl − 1) Pfs))’]
>- (gs[MEM_FLAT,MEM_map2list] >>
   ‘LENGTH sl ≠ 0’ by simp[] >>
    ‘n0 < LENGTH sl’ by simp[] >>
    first_x_assum $ drule_then assume_tac >> gs[]) 
>~ [‘(fVcong (map2list (LENGTH sl − 1) eqths) P sl)’] >>
qabbrev_tac
‘eqths1 = λn. (insth fσ vσ (uniqify uσ (eqths n)))’ >>
qabbrev_tac
‘eqthl1 = map2list (LENGTH sl - 1) eqths1’ >>
qabbrev_tac ‘eqthl = (map2list (LENGTH sl − 1) eqths)’ >>
‘insth fσ vσ (uniqify uσ (fVcong eqthl P sl)) =
    fcong eqthl1 (MAP (sinst vσ) sl)
    (fσ ' (uσ ' (P,sl),MAP (sinst vσ) sl))’
 by (simp[fVcong_def,fcong_def] >>
    irule thm_cong >> rw[] (* 3 *)
    >- (simp[insth_uniqify_components,concl_def,ffVrn_IFF] >>
    simp[ffVrn_IFF,finst_IFF,fVinst_IFF,IFF_eq_eq] >>
    simp[ffVrn_def,finst_def,fVinst_def] >>
    ‘(P,sl) ∈ FDOM uσ’ by cheat >> simp[] >>
    simp[fVinst_def] >>
    ‘(uσ ' (P,sl),MAP (sinst vσ) sl) ∈ FDOM fσ’ by cheat >>
    simp[] >>
    ‘(MAP (tinst vσ) (Rofeqthl eqthl)) = (Rofeqthl eqthl1) ∧
    (MAP (tinst vσ) (Lofeqthl eqthl)) = (Lofeqthl eqthl1)’
     suffices_by metis_tac[] >>
    cheat)
    >- (simp[assum_def,insth_uniqify_components] >>
       (*IMAGE comm with union?*) cheat) >>
    simp[cont_def,insth_uniqify_components] >>
    simp[Uof_UNION,Uof_Sing,fVars_finst,
         fVars_ffVrn,fVars_IFF,fVars_def] >>
    ‘(P,sl) ∈ FDOM uσ’ by cheat >>
    simp[fVrn_def,vinst_fVar_def,ofFMAP_UNION,ofFMAP_Sing]>>
    ‘(uσ ' (P,sl),MAP (sinst vσ) sl) ∈ FDOM fσ’
     by cheat >> simp[ofFMAP_Sing] >>
    ‘vinst_cont vσ (Uof cont (set eqthl)) ∪
     ofFMAP ffv fσ
           (Uof fVars
              (IMAGE (finst vσ) (IMAGE (ffVrn uσ) (Uof assum (set eqthl))))) =
     Uof cont (set eqthl1)’
     suffices_by (rw[EXTENSION] >> metis_tac[]) >>
    irule $ iffLR SUBSET_ANTISYM_EQ >> rw[] (* 3 *)
    >- (simp[vinst_cont_def,ofFMAP_SUBSET] >>
       simp[IN_Uof,PULL_EXISTS,Abbr‘eqthl’,
           MEM_map2list,SUBSET_DEF,Abbr‘eqthl1’,
           Abbr‘eqths1’] >>
       rw[] >> qexists ‘n0’ >> simp[] >>
       Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
       gs[cont_def] >>
       rename [‘(Γ,A,f)’] >>
       ‘Γ ⊆ FDOM vσ’ by cheat >>
       simp[insth_uniqify_components,cont_def] >>
       disj1_tac >> simp[vinst_cont_def,ofFMAP_def] >>
       gs[SUBSET_DEF] >> metis_tac[])
    >- (simp[vinst_cont_def,ofFMAP_SUBSET] >>
       simp[IN_Uof,PULL_EXISTS,Abbr‘eqthl’,
           MEM_map2list,SUBSET_DEF,Abbr‘eqthl1’,
           Abbr‘eqths1’] >>
       rw[] >> qexists ‘n0’ >> simp[] >>
       Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
       gs[cont_def] >>
       rename [‘(Γ,A,f)’] >>
       gs[assum_def] >>
       simp[insth_uniqify_components,cont_def] >>
       disj2_tac >> simp[Uof_UNION,Uof_Sing] >>
       simp[ofFMAP_def,PULL_EXISTS] >>
       qexists ‘a’ >> simp[] >>
       disj2_tac >> simp[IN_Uof,PULL_EXISTS] >>
       metis_tac[]) >>
    simp[Uof_SUBSET,
        IN_Uof,PULL_EXISTS,Abbr‘eqthl’,
           MEM_map2list,SUBSET_DEF,Abbr‘eqthl1’,
           Abbr‘eqths1’,vinst_cont_def,ofFMAP_def] >>
    rw[] >>
    Cases_on ‘eqths n’ >> Cases_on ‘r’ >>
    gs[cont_def,insth_uniqify_components] (* 2 *)
    >- (gvs[vinst_cont_def,ofFMAP_def] >>
       disj1_tac >> qexistsl [‘a’,‘n’] >> simp[cont_def]) >>
    ‘∃t1 t2. r' = EQ t1 t2’ by cheat >>
    gs[Uof_UNION,Uof_Sing,ffVrn_EQ,finst_EQ,fVars_EQ] >>
    disj2_tac >>
    gvs[ofFMAP_def,IN_Uof] >>
    qexistsl [‘a’,‘x''’,‘n’] >> simp[assum_def]) >>
simp[] >> simp[Abbr‘eqthl1’] >>
qspecl_then [‘Σ’,‘(MAP (sinst vσ) sl)’,‘eqths1’]
assume_tac $ GEN_ALL Pf0Drv_cong >> gs[] >>
first_x_assum irule >>
rw[] (* 4 *)
>- (* indeed need choice*)
   (‘∀n.
          n < LENGTH sl ⇒
          is_EQ (concl (eqths1 n)) ∧ Pf0Drv Σ aths (eqths1 n) ∧
          sort_of (Leq (concl (eqths1 n))) = EL n (MAP (sinst vσ) sl)’
   by (gen_tac >> strip_tac >>
       first_x_assum $ drule_then strip_assume_tac >>
       first_x_assum $ drule_then assume_tac >>
       first_x_assum $ qspecl_then [‘vσ’,‘fσ’,‘uσ’]
       assume_tac >>
       gs[] >>
       ‘Pf0Drv Σ aths (eqths1 n)’ by cheat >> simp[] >>
       simp[Abbr‘eqths1’] >>
       gs[is_EQ_def] >>
       Cases_on ‘eqths n’ >> Cases_on ‘r’ >>
       gs[concl_def] >> 
       simp[insth_uniqify_components,concl_def,ffVrn_EQ,
       finst_EQ,fVinst_EQ] >> rw[] (* 2 *)
       >- metis_tac[] >>
       gs[Leq_Req_EQ,sort_of_def] >>
       dep_rewrite.DEP_REWRITE_TAC[cstt_sort_of_tinst'] >>
       simp[EL_MAP] >> gs[wfvmap_def] >>
       rw[] >- metis_tac[wfcod_no_bound]>>
       ‘PfDrv Σ axs (q,q',EQ t1 t2)’
        by metis_tac[PfDrv_def] >>
       drule_all_then assume_tac PfDrv_concl_wff >>
       ‘wfsig Σ’ by gs[wfsigaxs_def1] >>
       Cases_on ‘Σ’ >> Cases_on ‘r’ >> gs[wff_EQ] >>
       metis_tac[wft_not_bound]) >>
       cheat)
>- (gs[MEM_MAP] >> irule wfs_sinst1 >>
   gs[wfsigaxs_def1] >> Cases_on ‘Σ’ >> Cases_on ‘r’ >>
   gs[wfvmap_def,wfsig_def])
>- (gs[wfcfVmap_def,cfVmap_alt] >>
   first_x_assum irule >>
   gs[thfVars_vinsth,thfVars_uniqify] >>
   gs[SUBSET_DEF] >> first_x_assum irule >>
   simp[PULL_EXISTS] >> qexists ‘(P,sl)’ >>
   simp[concl_fv_IN_thfVars_fVcong] >>
   ‘(P,sl) ∈ FDOM uσ’   
    by (gs[uniqifn_def,SUBSET_DEF] >>
        first_x_assum irule >>
        simp[concl_fv_IN_thfVars_fVcong]) >>
   simp[fVrn_def,vinst_fVar_def]) >>
‘(P,sl) ∈ FDOM uσ’   
    by (gs[uniqifn_def,SUBSET_DEF] >>
        first_x_assum irule >>
        simp[concl_fv_IN_thfVars_fVcong]) >>
‘(uσ ' (P,sl),MAP (sinst vσ) sl) ∈ FDOM fσ’
 by (gs[thfVars_vinsth,thfVars_uniqify,SUBSET_DEF] >>
    first_x_assum irule >> simp[PULL_EXISTS] >>
    qexists ‘(P,sl)’ >>
    simp[concl_fv_IN_thfVars_fVcong,
         fVrn_def,vinst_fVar_def]) >>
gs[wfcfVmap_def,wffVmap_def]
QED
         
 
val _ = export_theory();

