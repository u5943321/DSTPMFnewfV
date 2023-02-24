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


Theorem Uof_IMAGE:
Uof f (IMAGE g s) = Uof (f o g) s
Proof
rw[Uof_def,Once EXTENSION] >> metis_tac[]
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
        

Theorem ofFMAP_Uof_SUBSET_lemma:
(∀a. a ∈ A ⇒ ofFMAP f σ (g a) ⊆ B) ⇒
ofFMAP f σ (Uof g A) ⊆ B
Proof
rw[ofFMAP_def,SUBSET_DEF,IN_Uof,PULL_EXISTS] >>
first_x_assum $ drule_then assume_tac >>
metis_tac[]
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

Theorem ofFMAP_SUBSET:
ofFMAP f σ A ⊆ B ⇔ ∀a. a ∈ A ∧ a ∈ FDOM σ ⇒ f (σ ' a) ⊆ B
Proof        
rw[ofFMAP_def,SUBSET_DEF] >> metis_tac[]
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


Theorem IMAGE_eq_lemma:
(∀a. a ∈ A ⇒ f1 a = f2 a) ⇒ IMAGE f1 A = IMAGE f2 A
Proof
rw[Once EXTENSION] >> metis_tac[]
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

Theorem PfDrv_fVinsth:
∀th.
PfDrv Σ axs th ∧
wffVmap Σ fσ ∧ thfVars th ⊆ FDOM fσ ⇒
PfDrv Σ axs (fVinsth fσ th)
Proof
rw[PfDrv_def] >>
drule_all_then assume_tac Pf_fVinsth >>
first_x_assum $ irule_at Any >> simp[]
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
        

Theorem PfDrv_concl_wff:
wfsigaxs Σ axs ⇒
∀th. PfDrv Σ axs (Γ,A,f) ⇒ wff Σ f
Proof
metis_tac[PfDrv_wff,concl_def]
QED


Theorem PfDrv_assum_wff:
wfsigaxs Σ axs ⇒
∀th. PfDrv Σ axs (Γ,A,f) ⇒
∀a. a ∈ A ⇒ wff Σ a
Proof
metis_tac[PfDrv_wff,assum_def]
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
    by (irule uniqifn_ex >> cheat)  >>
  assume_tac (Pf2Pf0_fVinsth_lemma |> SPEC_ALL |> Q.GEN ‘f’) >>
  last_x_assum $ drule_then assume_tac >>
  first_x_assum $ qspecl_then [‘vσ’,‘(o_fVmap σ
                                      (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT
                                                                   (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))’,
                               ‘uσf’] assume_tac >> gs[] >>
  ‘cont th ⊆ cont (fVinsth fσ th)’
    by simp[cont_fVinsth] >>
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
           gs[wffsig_def] >>
           cheat (*  wffVmap (Σf,Σp,Σe) (rn2fVmap uσ)
           *)) >> simp[] >>
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
      
Theorem IN_thfVars:
∀fv. fv ∈ thfVars (Γ,A,f) ⇔
     ∃a. (a = f ∨ a ∈ A) ∧ fv ∈ fVars a
Proof
 simp[thfVars_def,IN_Uof]
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


Theorem uniqifn_INJ:
uniqifn (σ:string # sort list |-> string) s ∧ fv1 ∈ s ∧ fv2 ∈ s ∧
σ ' fv1 = σ ' fv2 ⇒ fv1 = fv2
Proof
rw[uniqifn_def] >>
Cases_on ‘fv1’ >> Cases_on ‘fv2’ >>
simp[] >> metis_tac[]
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

   
   
      ‘ofFMAP fVars (rn2fVmap (fVrwinst vσ uσ1 hσ uσ2))
          (IMAGE (vinst_fVar (o_vmap hσ vσ) ∘ fVrn uσ2) (thfVars th)) ⊆
        FDOM fσ’
      
 
   Pf2Pf0_vinst_lemma  >>
   
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


>- (rw[Pf0Drv_def] >> irule_at Any Pf0_AX >>
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
   pop_assum SUBST_ALL_TAC >>
   simp[vinst_fVar_def])
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

