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
 uniqifn uσf (FDOM uσ ∪ FDOM fσ) ∧ fVars f ⊆ FDOM fσ ⇒
Uof ffv
          (IMAGE
             (fVinst σ ∘
              $' (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
             (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f))) ⊆
        vinst_cont vσ (ffv f) ∪ vinst_cont vσ (ofFMAP ffv fσ (fVars f)) ∪
        ofFMAP ffv σ (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f))))
Proof
simp[Uof_SUBSET,PULL_EXISTS] >> rw[] >>
gs[] >> Cases_on ‘x'’ >> rename [‘(P,sl)’] >>
‘(P,sl) ∈ FDOM (o_fVmap (rn2fVmap uσ) fσ)’
 by (simp[FDOM_o_fVmap] >> gs[SUBSET_DEF]) >>
drule_then assume_tac FAPPLY_vinst_fVmap_fVmap_fVrn >>
first_x_assum $ qspecl_then [‘vσ’,‘uσf’] assume_tac >>
‘(FDOM uσ ∪ FDOM fσ) ⊆ FDOM uσf’ by metis_tac[uniqifn_def] >>
qpat_x_assum ‘(P,sl) ∈ FDOM (o_fVmap (rn2fVmap uσ) fσ)’ (K all_tac) >>
gs[] >> gs[FDOM_o_fVmap,FDOM_rn2fVmap] >>
‘(FDOM fσ ∪ FDOM uσ) = (FDOM uσ ∪ FDOM fσ)’ by simp[UNION_COMM] >> gs[] >>
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
                              
Theorem fVinst_subset_lemma:
ffv f ⊆ Γ ⇒
vinst_cont vσ Γ ∪
   (ofFMAP ffv
      (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
      (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) ∪
    ofFMAP ffv
      (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
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
>- ‘ofFMAP ffv
     (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
     (IMAGE (vinst_fVar vσ ∘ fVrn uσf) (fVars f)) ⊆
   vinst_cont vσ (ffv f) ∪   
   vinst_cont vσ (ofFMAP ffv fσ (fVars f)) ∪
   ofFMAP ffv σ (IMAGE (vinst_fVar vσ) (fVars (ffVrn uσ (fVinst fσ f))))’
   suffices_by cheat(gs[SUBSET_DEF] >> metis_tac[]) >>
   irule SUBSET_TRANS >>
   irule_at Any ofFMAP_ffv_o_fVmap >> rw[] (* 2 *)
   >- simp[FDOM_vinst_fVmap,FDOM_fVmap_fVrn,FDOM_o_fVmap,
           FDOM_rn2fVmap,UNION_OVER_INTER,Uof_UNION,IMAGE_IMAGE] >>
      rw[] (* 2 *)
      >- (simp[SUBSET_DEF,IN_Uof,PULL_EXISTS,ofFMAP_Uof] >> rw[] >>
         ‘x'' = x'’ by cheat >> gs[] >>
         simp[vinst_cont_def,IN_Uof,ofFMAP_Uof,PULL_EXISTS] >>
         ‘(vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) '
              (vinst_fVar vσ (fVrn uσf x'))) =
          finst vσ ((o_fVmap (rn2fVmap uσ) fσ) ' x') ’
          by (irule FAPPLY_vinst_fVmap_fVmap_fVrn1 >>
          simp[FDOM_o_fVmap,FDOM_rn2fVmap] >> cheat) >>
         gs[] >> Cases_on ‘x'’>>
         drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
         Cases_on ‘x ∈ ffv (finst vσ (fVinst (rn2fVmap uσ) (fσ ' (q,r))))’
         (* 2 *)
         >- (‘x ∈ ffv (finst vσ (ffVrn uσ (fσ ' (q,r)))) ’ by cheat >>
            ‘ffv (finst vσ (ffVrn uσ (fσ ' (q,r)))) =
             ffv (finst vσ (fσ ' (q,r)))’ by cheat >>
            gs[] >>
            disj1_tac >> disj2_tac >>
            qspecl_then [‘(fσ ' (q,r))’,‘vσ’] assume_tac ffv_finst >>
            ‘cstt vσ ∧ ffv (fσ ' (q,r)) ⊆ FDOM vσ ∧ no_bound vσ’
             by cheat >>
            gs[] >> Cases_on ‘x’ >> gs[] >>
            qexistsl [‘(n0,st0)’,‘(q,r)’] >> simp[] >> cheat)
         >- (disj2_tac >>
            qspecl_then [‘(finst vσ (fVinst (rn2fVmap uσ) (fσ ' (q,r))))’,‘σ’]
            assume_tac ffv_fVinst >>
            ‘x ∈
             ofFMAP ffv σ
             (FDOM σ ∩ fVars (finst vσ (fVinst (rn2fVmap uσ) (fσ ' (q,r)))))’
             by cheat >>
            gs[ofFMAP_def] >>
            ‘ x' ∈ fVars (ffVrn uσ (fσ ' (q,r)))’ by cheat >>
            gs[fVars_ffVrn] >> simp[PULL_EXISTS] >>
            qexists ‘x'''’ >> simp[] >> cheat)) >>
        (*can choose FDOM fσ = FDOM uσ*) cheat
   (*need fVars f ⊆ FDOM fσ*)
   ‘fVars f ⊆ FDOM fσ’ by cheat >>
   last_x_assum (qspecl_then [‘x'’] assume_tac) >> gs[SUBSET_DEF]
           
   this subgoal does nott exist since 
  (FDOM σ DIFF
          FDOM (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
   empty,  σ contains everything by assumption.                  
   simp[Uof_SUBSET,PULL_EXISTS,FDOM_vinst_fVmap,
        FDOM_fVmap_fVrn,FDOM_o_fVmap,FDOM_rn2fVmap] >> rw[] >>
   simp[SUBSET_DEF] >> rw[] >>
   disj2_tac >> simp[PULL_EXISTS,ofFMAP_def] >>
   simp[fVars_ffVrn,PULL_EXISTS] >>
   qexists ‘x'’ >>   
           
             
   
      


Theorem main:
 ∀pf. Pf Σ axs pf ⇒
      Uof (UCIth Σ) (IMAGE ax2th axs) ⊆ aths ⇒
      ∀th. MEM th pf ⇒
 ∀vσ fσ uσ. wfvmap (FST Σ) vσ ∧ wfcfVmap Σ fσ ∧
           thfVars (vinsth vσ th) ⊆ FDOM fσ ∧
           cont th ⊆ FDOM vσ ∧ uniqifn uσ (thfVars th) ⇒
           Pf0Drv Σ aths (insth fσ vσ (uniqify uσ th))
Proof         
Induct_on ‘Pf’ >> rw[] >> TRY (metis_tac[]) (* 16 *)
>~ [‘(insth fσ' vσ (uniqify uσ (fVinsth fσ th)))’] (* M-h M-p *)
>- gs[] >> rename [‘wfcfVmap Σ σ’] >>
   ‘∃uσf:string # sort list |-> string. uniqifn uσf (FDOM fσ ∪ FDOM uσ)’
     by cheat >> 
   qspecl_then [‘σ’,‘Σp’,‘Σf’,‘Σe’,‘vσ’,‘uσf’,‘fσ’] assume_tac
    (Pf2Pf0_fVinsth_lemma |> GEN_ALL)   
(* uniqifn_ex *)
   qspecl_then [‘σ’,‘Σp’,‘Σf’,‘Σe’,‘vσ’,‘uσf’,‘fσ’] assume_tac
    (Pf2Pf0_fVinsth_lemma |> GEN_ALL)   
   Pf0Drv_cont_SUBSET
   (Pf2Pf0_fVinsth_lemma |> GEN_ALL)

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

