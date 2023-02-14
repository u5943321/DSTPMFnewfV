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
 (∀s. MEM s sl ⇒ wfs (FST Σ) s) ⇒
 Pf0 Σ aths (FLAT (map2list (LENGTH sl - 1) Pf0s)  ++
 [fcong (map2list (LENGTH sl - 1) eqths) sl b])   
 ) ∧
[~vinsth:]
  (∀pf th vσ.
     Pf0 Σ aths pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ∧
     presname vσ ∧
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
    Pf0 Σ aths pf ∧ MEM (Γ,A,False) pf ∧ wff Σ f ⇒
    Pf0 Σ aths (pf ++ [(Γ ∪ ffv f,A,f)])) ∧
[~assume:]
  (∀c:form. wff Σ c ⇒ Pf0 Σ aths [assume c]) ∧
[~mp:]
  (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
     Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧
     MEM (Γ1,A1,IMP f1 f2) pf1 ∧
     MEM (Γ2,A2,f1) pf2 ⇒
     Pf0 Σ aths (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2, A1 ∪ A2,f2)])) ∧     
[~disch:]
  (∀pf th a.
     Pf0 Σ aths pf ∧ MEM th pf ∧ wff Σ a ⇒
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
     Pf0 Σ aths (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) 
End

    

Definition Pf0Drv_def:
  Pf0Drv Σ aths th ⇔ ∃pf0. Pf0 Σ aths pf0 ∧ MEM th pf0
End

(*    
Inductive Pf0:
[~AX:]
(∀ath. ath ∈ aths ⇒ Pf0 Σ aths [ath]) ∧
[~cong:]
(∀sl b Pf0s eqths.
 (∀n. n < LENGTH sl ⇒
     Pf0 Σ aths (Pf0s n) ∧ MEM (eqths n) (Pf0s n)) ∧
 wff Σ (FALLL sl b) ∧ is_cfm b ∧
 wfabsap (FST Σ) sl
         (Lofeqthl (map2list (LENGTH sl - 1) eqths)) ⇒
 Pf0 Σ aths (FLAT (map2list (LENGTH sl - 1) Pf0s)  ++
 [fcong (map2list (LENGTH sl - 1) eqths) sl b])   
 ) ∧
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
[~refl:]
  (∀t.
     wft (FST Σ) t ⇒ Pf0 Σ aths [refl t]) ∧
[~sym:]
  (∀Γ A pf t1 t2.
     Pf0 Σ aths pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
     Pf0 Σ aths (pf ++ [(Γ,A,EQ t2 t1)])) ∧
[~trans:]
  (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
     Pf0 Σ aths pf1 ∧ Pf0 Σ aths pf2 ∧
     MEM (Γ1,A1,EQ t1 t2) pf1 ∧ MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
     Pf0 Σ aths (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
[~vinsth:]
  (∀pf th vσ.
     Pf0 Σ aths pf ∧ MEM th pf ∧ wfvmap (FST Σ) vσ ⇒
     Pf0 Σ aths (pf ++ [vinsth vσ th]))
End



Definition Pf0Drv_def:
  Pf0Drv Σ aths th ⇔ ∃pf0. Pf0 Σ aths pf0 ∧ MEM th pf0
End          

Theorem Pf0Drv_wf:
  Pf0Drv Σ aths (Γ,A,f) ⇒
  wff Σ f ∧ (∀a. a ∈ A ⇒ wff Σ a) ∧
  (∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s)
Proof
cheat
QED  
 

Theorem Pf0Drv_cfm:
  Pf0Drv Σ aths (Γ,A,f) ⇒ is_cfm f ∧ (∀a. a ∈ A ⇒ is_cfm a)
Proof
cheat
QED


  

        
Theorem Pf0Drv_undisch:
  Pf0Drv Σ aths (Γ,A,IMP f1 f2) ⇒ Pf0Drv Σ aths (Γ,A ∪ {f1},f2)
Proof
  rw[Pf0Drv_def] >>
  drule_all_then assume_tac Pf0_wf >> gs[wff_IMP_iff] >>
  rev_drule_then assume_tac Pf0_assume >>
  first_x_assum (qspecl_then [‘aths’] assume_tac) >>
  ‘is_cfm f1’ by
  (‘is_cfm (IMP f1 f2)’ by
   (irule $ cj 1 Pf0Drv_cfm >>
    gs[Pf0Drv_def] >> metis_tac[]) >>
  gs[is_cfm_def])>> gs[] >>
  gs[assume_def] >>
  rev_drule_then assume_tac Pf0_mp >>
  rpt (first_x_assum $ drule_then assume_tac) >>
  first_x_assum $ qspecl_then [‘ffv f1’,‘{f1}’] assume_tac >>
  gs[] >> first_x_assum $ irule_at Any >> 
  ‘Γ ∪ ffv f1 = Γ’ suffices_by rw[] >> cheat
QED  



             
Theorem add_cont1:
  Pf0Drv Σ aths th ⇒
  ∀n s. wfs (FST Σ) s ⇒ Pf0Drv Σ aths (add_cont1 (n,s) th)
Proof
  (*rw[Pf0Drv_def] >>
  ‘wft (FST Σ) (Var n s)’ by simp[wft_def] >>
  drule_then assume_tac Pf0_refl >>
  gs[refl_def] >>
  ‘wff Σ (EQ (Var n s) (Var n s))’ by cheat >>
  drule_all_then assume_tac Pf0_disch >>
  first_x_assum (qspecl_then [‘aths’] assume_tac) >>
  Cases_on ‘th’ >> Cases_on ‘r’ >>
  rename [‘MEM (Γ,A,f) pf’] >> 
  gs[disch_def] >>
  Cases_on ‘EQ (Var n s) (Var n s) ∈ A’ >> gs[] (*2*)
  >- (‘Pf0Drv Σ aths
      (Γ ∪ ffv (EQ (Var n s) (Var n s)),
       (A DELETE EQ (Var n s) (Var n s)) ∪
       {EQ (Var n s) (Var n s)}, f)’
     by (irule undisch >> simp[Pf0Drv_def] >>
     qpat_x_assum ‘Pf0 _ _ (_ ++ _)’ assume_tac >>
     first_x_assum $ irule_at Any >> gs[]) >>
     ‘A DELETE EQ (Var n s) (Var n s) ∪ {EQ (Var n s) (Var n s)} = A’ by (rw[EXTENSION] >> metis_tac[]) >>
     gs[] >> simp[add_cont1_def]  >>
     gs[ffv_EQ] >>
     ‘Γ ∪ ({(n,s)} ∪ sfv s) = {(n,s)} ∪ sfv s ∪ Γ’
      by metis_tac[UNION_COMM] >> gs[] >>
     gs[Pf0Drv_def] >> first_x_assum $ irule_at Any >>
     simp[]) >>
  qpat_x_assum ‘Pf0 _ _ (_ ++ _)’ assume_tac >>
  drule_then assume_tac Pf0_mp >>
  qpat_x_assum ‘Pf0 _ _ [(_,{},_)]’ assume_tac >>
  first_x_assum $ drule_then assume_tac >>
  gs[ffv_EQ] >>
  first_x_assum
  (qspecl_then [‘Γ ∪ ({(n,s)} ∪ sfv s)’,
                ‘A DELETE EQ (Var n s) (Var n s)’,
                ‘f’] assume_tac) >>
  gs[] >>
  ‘A DELETE EQ (Var n s) (Var n s) = A’
    by (rw[EXTENSION] >> metis_tac[]) >>
  gs[] >>
  first_x_assum $ irule_at Any >>
  simp[add_cont1_def] >> disj2_tac >>
  rw[Once EXTENSION] >> metis_tac[] *) cheat
QED


Definition add_cont_def:
  add_cont ct (Γ,A,f) = (ct ∪ Γ,A,f)
End  
        
        
Theorem add_cont0:          
 ∀vs. FINITE vs ⇒
      (∀n s. (n,s) ∈ vs ⇒ wfs (FST Σ) s) ∧ Pf0Drv Σ aths th ⇒
      Pf0Drv Σ aths (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) vs) th)
Proof      
 (* Induct_on ‘vs’ >> rw[Uof_EMPTY,add_cont_EMPTY] >>
 ‘Pf0Drv Σ aths (add_cont (Uof (λ(n,s). {(n,s)} ∪ sfv s) vs) th)’ by metis_tac[] >>
 ‘(e INSERT vs) = {e} ∪ vs’ by 
 rw[Once INSERT_SING_UNION] >>
 pop_assum SUBST_ALL_TAC >> rw[Uof_Sing,Uof_UNION] >>
 rw[add_cont_UNION] >>
 drule_then assume_tac add_cont1 >>
 Cases_on ‘e’ >> gs[] >> gs[add_cont1_add_cont] >>
 first_x_assum irule >> metis_tac[] *) cheat
QED

Theorem add_cont:
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
irule add_cont0 >> simp[] >> metis_tac[]
QED





Theorem double_neg:
Pf0Drv Σ aths (Γ,A ∪ {NEG f},False) ⇒
Pf0Drv Σ aths (Γ,A,f)
Proof
rw[Pf0Drv_def] >>
drule_all_then assume_tac Pf0_double_neg >>
first_x_assum $ irule_at Any >> simp[]
QED


Theorem mp:
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
 


Theorem Pf0Drv_SUBSET_ffv:
Pf0Drv Σ aths (Γ,A,f) ⇒ Uof ffv ({f} ∪ A) ⊆ Γ
Proof
metis_tac[Pf0Drv_def,cont_SUBSET_ffv]
QED

Theorem Pf0Drv_concl_SUBST:
Pf0Drv Σ aths (Γ,A,f) ⇒ ffv f ⊆ Γ
Proof
rw[] >> drule_all_then assume_tac Pf0Drv_SUBSET_ffv >>
gs[Uof_UNION,Uof_Sing]
QED


Theorem Pf0Drv_assum_SUBSET:
Pf0Drv Σ aths (Γ,A,f) ⇒
(∀a. a ∈ A ⇒ ffv a ⊆ Γ)
Proof
rw[] >> drule_all_then assume_tac Pf0Drv_SUBSET_ffv >>
gs[Uof_UNION,Uof_Sing,Uof_SUBSET] 
QED


        
Theorem add_assum:
∀s th. FINITE s ⇒
    (∀ϕ. ϕ ∈ s ⇒ wff Σ ϕ) ∧
    Pf0Drv Σ aths th ⇒ Pf0Drv Σ aths (add_assum s th)
Proof
 Induct_on ‘FINITE’ >> gs[add_assum_EMPTY] >>
 rw[] >>
 ‘Pf0Drv Σ aths (add_assum s th)’ by metis_tac[] >>
 qpat_x_assum ‘ ∀th.
          (∀ϕ. ϕ ∈ s ⇒ wff Σ ϕ) ∧ Pf0Drv Σ aths th ⇒
          Pf0Drv Σ aths (add_assum s th)’ (K all_tac)>>
 Cases_on ‘th’ >> Cases_on ‘r’ >>
 gs[add_assum_def] >>
 drule_then assume_tac Pf0Drv_disch >>
 ‘wff Σ e’ by metis_tac[] >>
 first_x_assum $ drule_then assume_tac >>
 gs[disch_def] >>
 drule_then assume_tac undisch >>
 gs[add_assum_def,Uof_UNION,Uof_Sing,Uof_INSERT] >>
 ‘q' ∪ s DELETE e ∪ {e} = q' ∪ (e INSERT s)’
  by (gs[EXTENSION] >> metis_tac[]) >>
 ‘q ∪ (ffv e ∪ Uof ffv s) = q ∪ Uof ffv s ∪ ffv e’
  by  (gs[EXTENSION] >> metis_tac[]) >>
 gs[]
QED  

 
 
Theorem contrapos0:
Pf0Drv Σ aths (Γ1,A1,IMP ϕ ψ) ⇒
Pf0Drv Σ aths (Γ1,A1 DELETE ϕ DELETE NEG ψ,IMP (NEG ψ) (NEG ϕ))
Proof
rw[] >>
drule_then assume_tac undisch >>
‘wff Σ (NEG ψ)’ by cheat >>
drule_then assume_tac Pf0_assume >>
first_x_assum $ qspecl_then [‘aths’] assume_tac >>
‘Pf0Drv Σ aths (assume (NEG ψ))’
 by (simp[Pf0Drv_def] >> first_x_assum $ irule_at Any >>
    simp[]) >>
gs[assume_def,NEG_def] >>
drule_all_then assume_tac mp >>
gs[GSYM NEG_def,UNION_ASSOC] >>
‘ffv ψ ⊆ Γ1’ by metis_tac[Pf0Drv_concl_SUBST] >>
‘ffv ψ ∪ Γ1 = Γ1’
 by (gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
gs[] >>
‘wff Σ ϕ’ by cheat >>
drule_all_then assume_tac Pf0Drv_disch >>
gs[disch_def] >> gs[GSYM NEG_def] >>
drule_then assume_tac Pf0Drv_disch>>
first_x_assum $ rev_drule_then assume_tac >>
gs[disch_def] >>
‘Γ1 ∪ ffv ϕ ∪ ffv (NEG ψ) = Γ1’ by cheat >> gs[]>>
‘{NEG ψ} ∪ A1 ∪ {ϕ} DELETE ϕ DELETE NEG ψ = A1 DELETE ϕ DELETE NEG ψ’
 by (rw[EXTENSION] >> metis_tac[]) >>
gs[] 
QED



 
Theorem contrapos:
Pf0Drv Σ aths (Γ1,A1,IMP ϕ ψ) ⇒
Pf0Drv Σ aths (Γ1,A1,IMP (NEG ψ) (NEG ϕ))
Proof
rw[] >>
drule_then assume_tac contrapos0 >>
Cases_on ‘ϕ ∈ A1’ >> Cases_on ‘NEG ψ ∈ A1’ (* 4 *) >>
cheat
QED
                      
                
Theorem EX_E:
  Pf0Drv Σ aths (G1,A1,EX n s b) ∧
  (a,s) ∉ G2 ∧ substb (Var a s) b ∉ A2 ∧
  Pf0Drv Σ aths (G2 ∪ {(a,s)},A2 ∪ {substb (Var a s) b},f) ∧
  (a,s) ∉ Uof (sfv ∘ SND) G2 ∧ (a,s) ∉ Uof ffv (A2 ∪ {f}) ∧
  (a,s) ∉ Uof (slfv ∘ SND) (Uof fVars (A2 ∪ {f})) ⇒
  Pf0Drv Σ aths (G1 ∪ G2,A1 ∪ A2,f)
Proof
  rw[] >> irule double_neg >> rw[GSYM UNION_ASSOC] >>
  irule mp >>
  qexists ‘FALL s (NEG b)’ >>
  rw[] (* 2 *)
  >- (rw[GSYM NEG_def] >> gs[EX_def]) >>
  ‘wff Σ (substb (Var a s) b)’ by cheat >>
  drule_all_then assume_tac Pf0Drv_disch >>
  ‘(disch (substb (Var a s) b)
             (G2 ∪ {(a,s)},A2 ∪ {substb (Var a s) b},f)) =
  (G2 ∪ {(a,s)},A2, IMP (substb (Var a s) b) f)’
   by (rw[disch_def] (* 2 *)
      >- (‘ffv (substb (Var a s) b) ⊆ G2 ∪ {(a,s)}’
          suffices_by
          (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
          qpat_x_assum ‘Pf0Drv Σ aths (G2 ∪ {(a,s)},A2 ∪ {substb (Var a s) b},f)’ assume_tac >>
          drule_then assume_tac Pf0Drv_SUBSET_ffv >>
          gs[Uof_UNION,Uof_Sing]) >>
      gs[EXTENSION] >> metis_tac[]) >> gs[] >>
   irule undisch >>
   drule_then assume_tac contrapos >>
   drule_then assume_tac undisch >>
   cheat (*fabs_frpl*)
QED   



Theorem Pf0Drv_cont_SUBSET:
  Pf0Drv Σ aths (Γ0,A,f) ∧ FINITE Γ ∧ Γ0 ⊆ Γ ∧ is_cont Γ ∧
  (∀n s. (n,s) ∈ Γ ⇒ wfs (FST Σ) s) ⇒
  Pf0Drv Σ aths (Γ,A,f)
Proof
  rw[] >> drule_then assume_tac add_cont >> gs[] >>
  first_x_assum $ drule_all_then assume_tac >>
  gs[add_cont_def] >>
  ‘Γ ∪ Γ0 = Γ’ by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[])>>
  gs[]
QED
*)
        
val _ = export_theory();

