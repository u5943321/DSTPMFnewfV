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
           
             
   
      

(*
Theorem fVinst_lemma:
∀f fσ uσ vσ σ uσf.
   uniqifn uσf (fVars f) ∧ fVars f ⊆ FDOM fσ ∧ fVars (fVinst fσ 
Proof        
*)

                

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
>- gs[] >> rename [‘wfcfVmap Σ σ’] >>
    Cases_on ‘Σ’ >> Cases_on ‘r’ >> rename [‘(Σf,Σp,Σe)’] >>
   ‘∃uσf:string # sort list |-> string.
      uniqifn uσf (thfVars th)’
     by cheat >>
   assume_tac (Pf2Pf0_fVinsth_lemma |> SPEC_ALL |> Q.GEN ‘f’) >>
   last_x_assum $ drule_then assume_tac >>
   first_x_assum $ qspecl_then [‘vσ’,‘(o_fVmap σ
                 (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT
                 (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))’,
                 ‘uσf’] assume_tac >> gs[] >>
   ‘cont th ⊆ cont (fVinsth fσ th)’ by cheat >>
   ‘Pf0Drv (Σf,Σp,Σe)  aths
          (insth
             (o_fVmap σ
                (vinst_fVmap vσ
                   (fVmap_fVrn
                      (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
             vσ (uniqify uσf th))’
     by first_x_assum irule >>
        simp[FDOM_o_fVmap,FDOM_vinst_fVmap,FDOM_fVmap_fVrn,FDOM_DRESTRICT,
             INTER_UNION]   >>
        simp[thfVars_vinsth,thfVars_uniqify] >> rw[] (* 3 *)
        >- (gs[SUBSET_DEF] >> metis_tac[])
        >- (gs[SUBSET_DEF] >> metis_tac[]) >>
        rw[wfcfVmap_def] (* 2 *)
        >- irule wffVmap_o_fVmap >>
           gs[wfcfVmap_def,wfsigaxs_def,wffsig_def,wfsig_def] >>
           irule wffVmap_vinst_fVmap >>
           gs[wffsig_def] >>
           drule_then assume_tac wfvmap_presname >> gs[] >>
           simp[FDOM_fVmap_fVrn,FDOM_DRESTRICT,FDOM_o_fVmap,
                INTER_UNION,FDOM_rn2fVmap]
           ‘alluniq (IMAGE (fVrn uσf) (FDOM fσ))’
            by (irule uniqifn_alluniq0 >> cheat)
            (*choose uσf uniqify whole dom*) >>
           simp[] >> 
           ‘wffVmap (Σf,Σp,Σe)
          (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)’
           by cheat (*lemma*) >> simp[] >>
           simp[BIGUNION_SUBSET,PULL_EXISTS] >> rw[] (* 2 *)
           ‘uniqifn uσf (FDOM fσ)’ by cheat >>
          qspecl_then [‘uσf’,‘(DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))’]
          assume_tac FAPPLY_fVmap_fVrn1 >>
          gs[FDOM_DRESTRICT,FDOM_o_fVmap,FDOM_rn2fVmap,INTER_UNION] >>
          simp[DRESTRICT_DEF,FDOM_o_fVmap,FDOM_rn2fVmap,FDOM_rn2fVmap] >>
          Cases_on ‘x’ >> drule_then assume_tac FAPPLY_o_fVmap1 >>
          gs[] >>
          ‘(fVinst (rn2fVmap uσ) (fσ ' (q,r))) = ffVrn uσ (fσ ' (q,r))’
           by (irule $ GSYM ffVrn_fVinst >> cheat) >>
          gs[ffv_ffVrn] >> cheat (*need eq thfVars th = FDOM fσ*)
          cheat
          irule cfVmap_o_fVmap >> gs[wfcfVmap_def] >>
          simp[FDOM_vinst_fVmap,FDOM_fVmap_fVrn,FDOM_DRESTRICT,FDOM_o_fVmap,
          FDOM_rn2fVmap,INTER_UNION] >>
          simp[ofFMAP_SUBSET,PULL_EXISTS,FDOM_vinst_fVmap,
          FDOM_fVmap_fVrn,FDOM_DRESTRICT,FDOM_o_fVmap,
          FDOM_rn2fVmap,INTER_UNION] >> rw[] >>
          ‘x'' = x'’ by cheat >> gs[] >>
          Cases_on ‘x'’  >>
          qspecl_then [‘(q,r)’,‘uσf’,‘vσ’,‘(DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))’] assume_tac (FAPPLY_vinst_fVmap_fVmap_fVrn1 |> Q.GEN ‘fv’) >>
          gs[ofFMAP_SUBSET,PULL_EXISTS,FDOM_vinst_fVmap,
          FDOM_fVmap_fVrn,FDOM_DRESTRICT,FDOM_o_fVmap,
          FDOM_rn2fVmap,INTER_UNION] >>
          ‘(q,r) ∈ FDOM uσf ∧ uniqifn uσf (FDOM fσ)’ by cheat >>
          gs[] >>
          simp[fVars_finst] >>
          ‘(DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ) ' (q,r)) =
           (o_fVmap (rn2fVmap uσ) fσ) ' (q,r)’ by cheat >>
          gs[] >>
          ‘(o_fVmap (rn2fVmap uσ) fσ ' (q,r)) = ffVrn uσ (fσ ' (q,r))’
           by cheat >>
          gs[fVars_ffVrn] >> cheat
          
          
ffVrn_fVinst 
          fVinst_ffVrn
          drule_then assume_tac FAPPLY_fVmap_fVrn1 >>
          

        

        
        rename [‘(Σf,Σp,Σe)’] 
        ‘thfVars (vinsth vσ (fVinsth fσ th))  ’             
               
   ‘wffVmap Σ
          (o_fVmap σ
             (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf))) ’
     by Cases_on ‘Σ’ >> Cases_on ‘r’ >> irule wffVmap_o_fVmap >>
        gs[] >> gs[wfsigaxs_def,wfcfVmap_def,wffsig_def,wfsig_def] >>
        irule wffVmap_vinst_fVmap >>
        simp[wffsig_def,FDOM_fVmap_fVrn,FDOM_o_fVmap,FDOM_rn2fVmap] >>
        simp[GSYM IMAGE_UNION,Excl "IMAGE_UNION"] >>
        ‘FDOM uσf = (thfVars th ∪ thfVars (fVinsth fσ th))’ by cheat >>
        ‘BIGUNION
          {ffv (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf ' (P,sl)) ∪ slfv sl |
           (P,sl) |
           (∃x. (P,sl) = fVrn uσf x ∧ x ∈ FDOM uσf)} ⊆ FDOM vσ’
         simp[SUBSET_DEF,PULL_EXISTS] >> reverse (rw[]) (* 4 *)
         >- Cases_on ‘x'’ >> gs[fVrn_def]>>
            cheat
         >- Cases_on ‘x'’ >> gs[fVrn_def]>>
            cheat
         >- gs[] >>
            ‘uniqifn uσf (FDOM (o_fVmap (rn2fVmap uσ) fσ))’   by cheat >>
            drule_then assume_tac FAPPLY_fVmap_fVrn1 >>
            first_x_assum $ qspecl_then [‘x'’] assume_tac >>
            gs[FDOM_o_fVmap,FDOM_rn2fVmap] >>
            Cases_on ‘x' ∈ FDOM fσ’ (* 2 *)
            >- Cases_on ‘x'’ >> drule_then assume_tac FAPPLY_o_fVmap1 >>
               gs[] >> ‘(fVinst (rn2fVmap uσ) (fσ ' (q'',r))) =
                        ffVrn uσ (fσ ' (q'',r))’ by cheat >> gs[] >>
               gs[ffv_ffVrn] >> cheat >>
           Cases_on ‘x'’ >> drule_then assume_tac FAPPLY_o_fVmap2 >>
           ‘x ∈ slfv r’ by cheat >>
           cheat >>
        gs[] >>
        ‘(fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf ' (fVrn uσf x')) = (o_fVmap (rn2fVmap uσ) fσ) ' x'’
            
        
        
   
   qspecl_then [‘σ’,‘Σp’,‘Σf’,‘Σe’,‘vσ’,‘uσf’,‘fσ’] assume_tac
    (Pf2Pf0_fVinsth_lemma |> GEN_ALL)  >>
     
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

