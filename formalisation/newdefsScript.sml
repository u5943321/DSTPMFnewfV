open HolKernel Parse boolLib bossLib;

val _ = new_theory "newdefs";


Definition cont_def:
cont (Γ:string # sort -> bool,A:form -> bool,f:form) = Γ
End

        
Definition assum_def:
assum (Γ:string # sort -> bool,A:form -> bool,f:form) = A
End


Definition concl_def:
concl (Γ:string # sort -> bool,A:form -> bool,f:form) = f
End        


Definition thfVars_def:
thfVars (ct,asm,f) = Uof fVars ({f} ∪ asm)
End

(*
Definition vinst_fVar_def:
vinst_fVar vσ (P,sl) = (P,MAP (sinst vσ) sl)
End
*)        

Definition genavds_def:
  genavds th = (Uof (sfv o SND) (cont th)) ∪
               (Uof ffv (assum th)) ∪                      
               Uof (slfv o SND)
               (Uof fVars ({concl th} ∪ assum th))           
End   

        

Definition map2list:
  map2list 0 f = [f 0] ∧
  map2list (SUC n) f = (map2list n f) ++ [f (n+1)]
End  
        
Definition Lofeqths_def:
  Lofeqthl eqthl  = (MAP (FST o dest_eq o concl) eqthl)
End

Definition Rofeqths_def:
  Rofeqthl eqthl  = (MAP (SND o dest_eq o concl) eqthl)
End
          

    

    
(*connectives*)



Definition NEG_def:
  NEG f = IMP f False
End

Definition DISJ_def:
  DISJ f1 f2 = IMP (NEG f1) f2
End

Definition CONJ_def:
  CONJ f1 f2 = NEG (IMP f1 (NEG f2))
End

Definition True_def:
  True = NEG False
End          

Definition IFF_def:
  IFF f1 f2 = CONJ (IMP f1 f2) (IMP f2 f1)
End               

Definition EX_def:
  EX s b = NEG (FALL s (NEG b))
End



Theorem ffv_IFF:
ffv (IFF f1 f2) = ffv f1 ∪ ffv f2
Proof
rw[IFF_def,ffv_def,CONJ_def,NEG_def] >>
gs[EXTENSION] >> metis_tac[]
QED
        

(*instantiation*)


Definition vinst_cont_def:
vinst_cont σ Γ = ofFMAP tfv σ Γ
End
        
Definition vinsth_def:
  vinsth σ (Γ,A,f) = (vinst_cont σ Γ,IMAGE (finst σ) A,finst σ f)
End


Definition fVinsth_def:
  fVinsth σf (ct,asm,f) =
  (ct ∪ ofFMAP ffv σf (Uof fVars ({f} ∪ asm)), 
  IMAGE (fVinst σf) asm,fVinst σf f)
End

Definition insth_def:      
  insth σf σv th = fVinsth σf (vinsth σv th)
End
        


Definition instf_def:      
  instf σf σv f = fVinst σf (finst σv f)
End

        

(*concrete*)

Definition is_cfm_def:
is_cfm False = T ∧
(is_cfm (IMP f1 f2) = (is_cfm f1 ∧ is_cfm f2)) ∧
is_cfm (fVar _ _ _) = F ∧
is_cfm (Pred _ _) = T ∧
is_cfm (FALL s b) = is_cfm b
End

Definition is_cth:
is_cth (Γ,A,f) ⇔ is_cfm f ∧ (∀a. a ∈ A ⇒ is_cfm f)
End        
   
Definition cfVmap_def:
 cfVmap σ ⇔
 ∀P sl. (P,sl) ∈ FDOM σ ⇒ is_cfm (σ ' (P,sl))
End 

Definition wfcfVmap_def:
  wfcfVmap Σ fσ ⇔  wffVmap Σ fσ ∧ cfVmap fσ
End  


        
Definition wfvmap_def:
wfvmap Σ vσ ⇔ cstt vσ ∧ wfcod Σ vσ
End

(*th funcions*)



               

Definition spec_def:
  spec t (Γ,A,FALL s b) = (Γ ∪ tfv t,A,substb t b)
End


Definition gen_def:
gen (n,s) (Γ,A,f) = (Γ DELETE (n,s),A,mk_FALL n s f)
End

Definition assume_def:
  assume f = (ffv f,{f},f)
End

Definition refl_def:
refl t = (tfv t,{},EQ t t)
End
         
Definition sym_def:
sym (Γ,A,Pred "=" [t1;t2]) = (Γ,A,Pred "=" [t2;t1])
End
 

Definition disch_def:
  disch a (Γ,A,f) = (Γ ∪ ffv a,A DELETE a,IMP a f)
End
       

     
Definition fVcong_def:
fVcong eqthl P sl =
(Uof cont (set eqthl),Uof assum (set eqthl),
 IFF (fVar P sl (Lofeqthl eqthl))
     (fVar P sl (Rofeqthl eqthl)))
End

        
            

Definition fcong_def:
fcong eqthl sl b =
(Uof cont (set eqthl) ∪ ffv b,Uof assum (set eqthl),
 IFF (fprpl (mk_bmap (REVERSE (Lofeqthl eqthl))) b)
     (fprpl (mk_bmap (REVERSE (Rofeqthl eqthl))) b))
End        

Definition add_assum_def:
add_assum s (Γ,A,f) = (Γ ∪ Uof ffv s, A ∪ s,f)
End


Theorem add_assum_EMPTY:
add_assum {} th = th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >> gs[add_assum_def,Uof_EMPTY]
QED        


Definition add_cont_def:
  add_cont ct (Γ,A,f) = (ct ∪ Γ,A,f)
End  
                

Definition add_cont1_def:
  add_cont1 (n,s) (Γ,A,f) = ({(n,s)} ∪ sfv s ∪ Γ,A,f)
End



Definition undisch_def:
undisch (Γ,A,IMP f1 f2) = (Γ,A ∪ {f1},f2)
End


Theorem is_cont_DELETE:
    is_cont ct ∧ (∀n s. (n,s) ∈ ct ⇒ v ∉ sfv s) ⇒
    is_cont (ct DELETE v)
Proof    
  rw[is_cont_def] >> gs[SUBSET_DEF] >> metis_tac[]
QED  
        

Theorem EMPTY_is_cont:
is_cont {}
Proof
rw[is_cont_def]
QED

Theorem add_cont_EMPTY:
add_cont {} th = th
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
rw[add_cont_def]
QED        
         
Theorem cont_decompose:
∀ct. FINITE ct ∧ is_cont ct ⇒
     let s = IMAGE (λ(n,s). {(n,s)} ∪ sfv s) ct
     in
     FINITE s ∧ BIGUNION s = ct ∧
         (∀ct0. ct0 ∈ s ⇒ is_cont ct0)
Proof
rw[] >>(* qexists ‘IMAGE (λ(n,s). {(n,s)} ∪ sfv s) ct’ >>*)
rw[] (* 2 *)
>- (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
   >- (Cases_on ‘x'’ >> gs[] >>
       metis_tac[is_cont_def,SUBSET_DEF]) >>
   Cases_on ‘x’ >> gs[] >> qexists ‘(q,r)’ >> simp[]) >>
Cases_on ‘x’ >> simp[] >> rw[is_cont_def] (* 2 *)
>- gs[SUBSET_DEF] >>
gs[SUBSET_DEF] >>  rw[] >> metis_tac[vsort_tfv_closed]
QED
   
Theorem add_cont_UNION:
add_cont (c1 ∪ c2) th = add_cont c1 (add_cont c2 th)
Proof
Cases_on ‘th’ >> Cases_on ‘r’ >>
gs[add_cont_def,UNION_ASSOC]
QED

Theorem add_cont1_add_cont:
add_cont1 (n,s) = add_cont ({(n,s)} ∪ sfv s)
Proof
simp[FUN_EQ_THM] >> rw[] >> Cases_on ‘x’ >>
Cases_on ‘r’ >> rw[add_cont_def,add_cont1_def]
QED

Theorem BIGUNION_IMAGE_Uof:
BIGUNION (IMAGE f s) = Uof f s
Proof
rw[Uof_def,IMAGE_DEF]
QED 
        
        
                
(*        
        
Definition cinstsf_def:
  cinstsf Σ f = {instf fσ vσ f | (fσ,vσ) | IMAGE (λ(P,sl). (P, MAP (sinst vσ) sl)) (fVars f) ⊆ FDOM fσ ∧ wfvmap (FST Σ) vσ ∧ wffVmap Σ fσ ∧ ffv f ⊆ FDOM vσ}
End    
         

Definition cinststh_def:
  cinststh Σ th = {insth fσ vσ th | (fσ,vσ) | IMAGE (λ(P,sl). (P, MAP (sinst vσ) sl)) (thfVars th) ⊆ FDOM fσ ∧ wfvmap (FST Σ) vσ ∧ wffVmap Σ fσ ∧ cont th ⊆ FDOM vσ}
End            
*)        



Theorem LENGTH_map2list:
∀n.LENGTH (map2list n f) = n + 1
Proof
Induct_on ‘n’ >> gs[map2list]
QED

Theorem EL_map2list:
  ∀n m. m ≤ n ⇒ EL m (map2list n f) = f m
Proof  
Induct_on ‘n’ >> simp[map2list] >>
rw[] >> Cases_on ‘m ≤ n’ >> gs[] (* 2 *)
>- (first_x_assum $ drule_then (assume_tac o GSYM) >>
   simp[] >> 
   irule rich_listTheory.EL_APPEND1 >>
   simp[LENGTH_map2list]) >>
‘m = SUC n’ by simp[] >> gs[] >>
‘LENGTH (map2list n f) ≤ SUC n’ by simp[LENGTH_map2list] >>
drule_then assume_tac rich_listTheory.EL_APPEND2 >>
gs[] >> simp[LENGTH_map2list,arithmeticTheory.ADD1]
QED 

   
Theorem LENGTH_LRofeqthl:
LENGTH (Lofeqthl l) = LENGTH l ∧
LENGTH (Rofeqthl l) = LENGTH l
Proof
rw[Lofeqths_def,Rofeqths_def]
QED

Theorem ffv_NEG:
ffv (NEG f) = ffv f
Proof
rw[ffv_def,NEG_def]
QED

Theorem Uof_lemma_classic:
Uof ffv ({False} ∪ (A ∪ {NEG f})) = Uof ffv ({f} ∪ A)
Proof
rw[Uof_def,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 5 *)
>> gs[ffv_def,ffv_NEG]
>- metis_tac[]
>- metis_tac[]
>- (qexists ‘NEG e’ >> simp[ffv_NEG]) >>
metis_tac[]
QED





Theorem wfabsap_Lofeqthl_sl_NONNIL:
wfabsap Σf sl (Lofeqthl (map2list f l)) ⇒ sl ≠ []
Proof
rw[] >> drule_then assume_tac wfabsap_LENGTH >>
CCONTR_TAC >> gs[] >>
gs[Lofeqths_def] >> 
‘LENGTH (map2list f l) = LENGTH []’ by simp[] >> 
gs[LENGTH_map2list]
QED



Theorem MEM_map2list:
MEM th (map2list n eqths) ⇔ ∃n0. n0 ≤ n ∧ th = eqths n0
Proof
rw[MEM_EL,EL_map2list,LENGTH_map2list,GSYM arithmeticTheory.LE_LT1,EQ_IMP_THM] (* 2 *)
>> (first_assum $ irule_at Any >>
   metis_tac[EL_map2list])
QED   
   
            
Theorem dest_eq_EQ:
 dest_eq (EQ t1 t2) = (t1,t2)
Proof
 rw[dest_eq_def,EQ_def]  
QED

Theorem MEM_Lofeqthl_map2list:
 (∀n0. n0 ≤ n ⇒ is_EQ (concl (eqths n0))) ⇒
 (MEM t (Lofeqthl (map2list n eqths)) ⇔
 ∃n0 Γ A t1 t2.
   n0 ≤ n ∧ eqths n0 = (Γ,A,EQ t1 t2) ∧
   t = t1)
Proof
 rw[EQ_IMP_THM,Lofeqths_def,MEM_MAP,
    MEM_map2list,PULL_EXISTS] >>
 first_x_assum $ drule_then assume_tac >>
 gs[is_EQ_def] >> first_assum $ irule_at Any >>
 gs[dest_eq_EQ,concl_def] (* 2 *)
 >- (Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
    simp[] >> gs[concl_def] >> metis_tac[]) >>
 gs[EQ_def]
QED      


Theorem MEM_Rofeqthl_map2list:
 (∀n0. n0 ≤ n ⇒ is_EQ (concl (eqths n0))) ⇒
 (MEM t (Rofeqthl (map2list n eqths)) ⇔
 ∃n0 Γ A t1 t2.
   n0 ≤ n ∧ eqths n0 = (Γ,A,EQ t1 t2) ∧
   t = t2)
Proof
 rw[EQ_IMP_THM,Rofeqths_def,MEM_MAP,
    MEM_map2list,PULL_EXISTS] >>
 first_x_assum $ drule_then assume_tac >>
 gs[is_EQ_def] >> first_assum $ irule_at Any >>
 gs[dest_eq_EQ,concl_def] (* 2 *)
 >- (Cases_on ‘eqths n0’ >> Cases_on ‘r’ >>
    simp[] >> gs[concl_def] >> metis_tac[]) >>
 gs[EQ_def]
QED      
         
Theorem IN_Uof:
x ∈ Uof f A ⇔ ∃a. a ∈ A ∧ x ∈ f a
Proof
rw[Uof_def] >> metis_tac[]
QED






Theorem fVars_vinst:
∀f. fVars (finst vσ f) = IMAGE (vinst_fVar vσ) (fVars f)
Proof
Induct_on ‘f’ >> gs[vinst_fVar_def,finst_def,fVars_def]
QED        

           
Theorem instf_fVinst_finst:
 instf fσ vσ = fVinst fσ ∘ finst vσ
Proof
rw[FUN_EQ_THM,instf_def]
QED

Theorem insth_instf:
  insth fσ vσ (Γ,A,f) =
  (vinst_cont vσ Γ ∪
   ofFMAP ffv fσ
   (Uof (IMAGE (vinst_fVar vσ) o fVars) ({f} ∪ A)),
  IMAGE (instf fσ vσ) A,
  instf fσ vσ f)
Proof  
 rw[insth_def,fVinsth_def,vinsth_def,instf_def,
    IMAGE_IMAGE,instf_fVinst_finst] >>
 rw[Uof_UNION,Uof_Sing,fVars_vinst] >>
 ‘Uof fVars (IMAGE (finst vσ) A) =
  Uof (IMAGE (vinst_fVar vσ) ∘ fVars) A’
  suffices_by metis_tac[] >>
 rw[Once EXTENSION,IN_Uof,PULL_EXISTS,fVars_vinst]
QED



Theorem vinst_cont_EMPTY:        
vinst_cont σv ∅ = ∅ 
Proof
rw[vinst_cont_def,ofFMAP_EMPTY]
QED


Theorem vinst_cont_UNION:
vinst_cont σ (s1 ∪ s2) = vinst_cont σ s1 ∪ vinst_cont σ s2
Proof
rw[vinst_cont_def,ofFMAP_UNION]
QED



(*uniqification*)        
Definition uniqifn_def:
  uniqifn uσ fVs ⇔
    fVs ⊆ FDOM uσ ∧
    ∀P1 P2 sl1 sl2. (P1,sl1) ∈ fVs ∧ (P2,sl2) ∈ fVs ∧
     (P1,sl1) ≠ (P2,sl2) ⇒ uσ ' (P1,sl1) ≠ uσ ' (P2,sl2)
End    


Definition alluniq_def:
alluniq fVs ⇔
∀P1 P2 sl1 sl2. (P1,sl1) ∈ fVs ∧ (P2,sl2) ∈ fVs ∧ sl1 ≠ sl2 ⇒ P1 ≠ P2
End


Theorem alluniq_EMPTY:
alluniq {}
Proof
rw[alluniq_def]
QED        

Theorem uniqifn_SUBSET:
uniqifn uσ A ∧ B ⊆ A ⇒ uniqifn uσ B
Proof
rw[uniqifn_def] >> gs[SUBSET_DEF] >> metis_tac[]
QED


Definition ffVrn_def:
(ffVrn uσ (fVar P sl tl) =
if (P,sl) ∈ FDOM uσ then fVar (uσ ' (P,sl)) sl tl else fVar P sl tl) ∧
ffVrn uσ (IMP f1 f2) =
IMP (ffVrn uσ f1) (ffVrn uσ f2) ∧
ffVrn uσ (FALL s b) =
FALL s (ffVrn uσ b) ∧
ffVrn uσ (Pred p tl) = Pred p tl ∧
ffVrn uσ False = False
End


Definition fVrn_def:
fVrn uσ (P,sl) = if (P,sl) ∈ FDOM uσ then (uσ ' (P,sl),sl)
else (P,sl)
End

        

             

Theorem fVars_ffVrn:
∀f. fVars (ffVrn uσ f) = IMAGE (fVrn uσ) (fVars f)
Proof
Induct_on ‘f’ >> gs[fVars_def,ffVrn_def,fVrn_def] >>
rw[fVars_def]
QED


          
Theorem uniqifn_alluniq0:
∀s. uniqifn uσ s ⇒ alluniq (IMAGE (fVrn uσ) s)
Proof
rw[] >>
irule $ iffRL alluniq_def >> rw[] >>
Cases_on ‘x’ >> Cases_on ‘x'’ >> gs[fVrn_def] >>
‘(q,r) ∈ FDOM uσ  ∧ (q',r') ∈ FDOM uσ ’
 by gs[uniqifn_def,SUBSET_DEF] >>
gs[] >>
gs[uniqifn_def]
QED

Theorem uniqifn_alluniq:
∀f. uniqifn uσ (fVars f) ⇒
    alluniq (fVars (ffVrn uσ f))
Proof
rw[fVars_ffVrn] >> metis_tac[uniqifn_alluniq0]
QED



Definition vinst_bmap_def:
vinst_bmap σ bmap =
FUN_FMAP (λi. tinst σ (bmap ' i))  (FDOM bmap)
End

Theorem FDOM_vinst_bmap:
FDOM (vinst_bmap σ bmap) = FDOM bmap
Proof
rw[vinst_bmap_def]
QED



Theorem FAPPLY_vinst_bmap:
i ∈ FDOM bmap  ⇒
(vinst_bmap σ bmap) ' i =  tinst σ (bmap ' i)
Proof
‘FINITE (FDOM bmap)’ by simp[] >> rw[] >>
drule_then assume_tac FUN_FMAP_DEF >> gs[] >>
first_x_assum $ drule_then assume_tac >> 
rw[vinst_bmap_def,FUN_FMAP_DEF]
QED
        
        
Theorem tinst_tprpl:
(∀tm bmap σ.
   tfv tm ⊆ FDOM σ ∧
   (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = {}) ∧
   (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
             tinst σ (tprpl bmap tm) =
       tprpl (vinst_bmap σ bmap) (tinst σ tm)) ∧
(∀st bmap σ.
   sfv st ⊆ FDOM σ ∧
   (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = {}) ∧
   (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
             sinst σ (sprpl bmap st) =
       sprpl (vinst_bmap σ bmap) (sinst σ st))       
Proof
ho_match_mp_tac better_tm_induction >>
gs[tinst_def,tprpl_def,MAP_MAP_o,MAP_EQ_f,
   FDOM_vinst_bmap] >>
rw[]
>- (rw[Once EQ_SYM_EQ] >> irule $ cj 1 tprpl_id >>
   ‘tbounds (σ ' (s0,st)) = {}’ suffices_by simp[] >>
   metis_tac[])
>- metis_tac[]
>- (first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (drule_then assume_tac FAPPLY_vinst_bmap >>
   gs[]) >>
(first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[])
QED
        

                



Theorem tshift_tinst:
(∀tm.
  (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
  tshift n (tinst σ tm) = tinst σ (tshift n tm)) ∧
(∀st.
  (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
  sshift n (sinst σ st) = sinst σ (sshift n st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tshift_def,tinst_def,MAP_MAP_o,MAP_EQ_f] >>
rw[] (* 4 *) >> TRY (metis_tac[]) >>
Cases_on ‘(s0,st) ∈ FDOM σ’ >> simp[] (* 2 *)
>- (irule $ cj 1 tshift_id >> metis_tac[]) >>
rw[tshift_def]
QED
                

                
Theorem shift_bmap_vinst_bmap:
(∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅) ⇒
(shift_bmap n (vinst_bmap σ bmap)) =
    (vinst_bmap σ (shift_bmap n bmap))
Proof    
rw[fmap_EXT,FDOM_shift_bmap,FDOM_vinst_bmap]    >>
‘(n + x') ∈ FDOM (shift_bmap n bmap)’ by simp[FDOM_shift_bmap] >>
drule_then assume_tac FAPPLY_vinst_bmap >>
simp[] >>
‘x' ∈ FDOM (vinst_bmap σ bmap)’
 by simp[FDOM_vinst_bmap] >>
drule_then assume_tac FAPPLY_shift_bmap >>
simp[] >>
rev_drule_then assume_tac FAPPLY_shift_bmap >>
simp[] >>
rev_drule_then assume_tac FAPPLY_vinst_bmap >> simp[] >>
irule $ cj 1 tshift_tinst >> metis_tac[]
QED


Theorem finst_fprpl:
∀f bmap σ.
   ffv f ⊆ FDOM σ ∧
   (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = {}) ∧
   (∀n s. (n,s) ∈ FDOM σ ⇒ tbounds (σ ' (n,s)) = ∅)⇒
finst σ (fprpl bmap f) =
fprpl (vinst_bmap σ bmap) (finst σ f)
Proof
Induct_on ‘f’ >> gs[finst_def,fprpl_def,MAP_EQ_f,
 MAP_MAP_o,PULL_EXISTS] (* 4 *)
>- (rw[] >> irule $ cj 1 tinst_tprpl >>
   simp[] >> gs[SUBSET_DEF] >>
   metis_tac[])
>- (rw[] (* 2 *)
   >> (first_x_assum irule >> metis_tac[]))
>- (rw[] (* 2 *)
   >- (irule $ cj 2 tinst_tprpl >> simp[] >>
      metis_tac[]) >>
   ‘(shift_bmap 1 (vinst_bmap σ bmap)) =
    (vinst_bmap σ (shift_bmap 1 bmap))’
     by metis_tac[shift_bmap_vinst_bmap] >>
   gs[] >> first_x_assum irule >>
   simp[] >> metis_tac[]) >>
rw[] >> irule $ cj 1 tinst_tprpl >>
   simp[] >> gs[SUBSET_DEF] >>
   metis_tac[]
QED      






Theorem vinst_bmap_alt:
vinst_bmap vσ bmap = FMAP_MAP (tinst vσ) bmap
Proof
rw[fmap_EXT,FDOM_vinst_bmap,FDOM_FMAP_MAP] >>
drule_then assume_tac FAPPLY_vinst_bmap >>
metis_tac[FAPPLY_FMAP_MAP]
QED



Definition vinst_fVmap_def:
vinst_fVmap vσ fσ =
 FUN_FMAP
 (λ(P,sl).
  finst vσ (fσ ' (CHOICE {(P0,sl0) | vinst_fVar vσ (P0,sl0) = (P,sl) ∧ (P0,sl0) ∈ FDOM fσ})))
(IMAGE (vinst_fVar vσ) (FDOM fσ))
End

Theorem FDOM_vinst_fVmap:
FDOM (vinst_fVmap vσ fσ) = (IMAGE (vinst_fVar vσ) (FDOM fσ))
Proof
rw[vinst_fVmap_def,FUN_FMAP_DEF]
QED


        
Theorem FAPPLY_vinst_fVmap:
∀P sl. (P,sl) ∈ FDOM fσ ∧ alluniq (FDOM fσ) ⇒
vinst_fVmap vσ fσ ' (vinst_fVar vσ (P,sl)) =
finst vσ (fσ ' (P,sl))
Proof
rw[vinst_fVar_def,vinst_fVmap_def] >>
‘FINITE (IMAGE (vinst_fVar vσ) (FDOM fσ))’
 by simp[] >>
‘(P,MAP (sinst vσ) sl) ∈ IMAGE (vinst_fVar vσ) (FDOM fσ)’ by
  (simp[IMAGE_DEF,vinst_fVar_def] >>
  qexists ‘(P,sl)’ >> simp[] >>
  rw[vinst_fVar_def]) >>
qspecl_then [‘(λ(P',sl').
               finst vσ
                 (fσ '
                  (CHOICE
                     {(P0,sl0) |
                      (P0 = P' ∧ MAP (sinst vσ) sl0 = sl') ∧
                      (P0,sl0) ∈ FDOM fσ})))’] assume_tac     
FUN_FMAP_DEF   >>
first_x_assum $ drule_then assume_tac >>
gs[PULL_EXISTS] >>
Cases_on ‘x’ >> rw[vinst_fVar_def] >>
‘{(P0,sl0) |
               (P0 = q ∧ MAP (sinst vσ) sl0 = MAP (sinst vσ) r) ∧
               (P0,sl0) ∈ FDOM fσ} = {(P,sl)}’ suffices_by simp[CHOICE_SING] >>
rw[Once EXTENSION,EQ_IMP_THM] (* 4 *)
>> (gs[vinst_fVar_def,alluniq_def] >>
   metis_tac[])
QED      
        


(*can strengthen assumption on σ is wf, vσ wf*)         
Theorem instf_fVinst:
∀f.  fVars f ⊆ FDOM σ ∧
     ffv (fVinst σ f) ⊆ FDOM vσ ∧
     wffVmap Σ σ ∧
     alluniq (FDOM σ) ∧
   (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = {}) ∧
   (∀n s. (n,s) ∈ FDOM vσ ⇒ tbounds (vσ ' (n,s)) = ∅) ⇒
  finst vσ (fVinst σ f) =
  instf (vinst_fVmap vσ σ) vσ f
Proof
Induct_on ‘f’ >> gs[fVinst_def,finst_def,instf_def,fVars_def] >>
reverse (rw[]) (* 5 *)
>- (first_x_assum irule >> simp[] >>
   metis_tac[])
>- (first_x_assum irule >> simp[] >>
   metis_tac[])
>- (first_x_assum irule >> simp[] >>
   metis_tac[])      
>- gs[FDOM_vinst_fVmap,vinst_fVar_def] >>
drule_all_then assume_tac FAPPLY_vinst_fVmap >>
simp[] >>
rw[GSYM vinst_fVar_def] >>
‘(mk_bmap (REVERSE (MAP (tinst vσ) l0))) =
 vinst_bmap vσ (mk_bmap (REVERSE l0))’
 by rw[GSYM rich_listTheory.MAP_REVERSE,
       mk_bmap_MAP,vinst_bmap_alt] >>
simp[] >> 
irule finst_fprpl  >> rw[] (* 2 *)
>- (drule_all_then assume_tac wffVmap_no_vbound >>
   simp[]) >>
qspecl_then [‘(σ ' (s,l))’,‘(mk_bmap (REVERSE l0))’]
assume_tac ffv_fprpl >>
‘ffv (fprpl (mk_bmap (REVERSE l0)) (σ ' (s,l))) =
        ffv (σ ' (s,l)) ∪
        BIGUNION
          {tfv (mk_bmap (REVERSE l0) ' i) |
           i |
           i ∈ FDOM (mk_bmap (REVERSE l0)) ∩ fbounds (σ ' (s,l))}’ suffices_by gs[Once EXTENSION,SUBSET_DEF] >>
first_x_assum irule >>  metis_tac[wffVmap_no_vbound]
QED


           

Definition o_fVmap_def:
o_fVmap σ2 σ1 =
FUN_FMAP
(λ(P,sl).
 if (P,sl) ∈ FDOM σ1 then fVinst σ2 (σ1 ' (P,sl)) else
 σ2 ' (P,sl)) (FDOM σ1 ∪ FDOM σ2)
End

Theorem FDOM_o_fVmap:
FDOM (o_fVmap σ2 σ1) = FDOM σ1  ∪ FDOM σ2
Proof
rw[o_fVmap_def,FUN_FMAP_DEF]
QED

             

Theorem FAPPLY_o_fVmap:
(P,sl) ∈ FDOM σ1 ∪ FDOM σ2 ⇒
(o_fVmap σ2 σ1) ' (P,sl) = if (P,sl) ∈ FDOM σ1 then
fVinst σ2 (σ1 ' (P,sl)) else σ2 ' (P,sl)
Proof
rw[o_fVmap_def,FUN_FMAP_DEF]
QED 



Theorem FAPPLY_o_fVmap1:
(P,sl) ∈ FDOM σ1 ⇒
(o_fVmap σ2 σ1) ' (P,sl) = fVinst σ2 (σ1 ' (P,sl)) 
Proof
rw[o_fVmap_def,FUN_FMAP_DEF]
QED



Theorem FAPPLY_o_fVmap2:
(P,sl) ∉ FDOM σ1 ∧ (P,sl) ∈ FDOM σ2 ⇒
(o_fVmap σ2 σ1) ' (P,sl) = σ2 ' (P,sl)
Proof
rw[o_fVmap_def,FUN_FMAP_DEF]
QED        
        

        
Definition subfm_def:
subfm False = {False} ∧
subfm (IMP f1 f2) = {IMP f1 f2} ∪ subfm f1 ∪ subfm f2 ∧
subfm (Pred p tl) = {Pred p tl} ∧
subfm (fVar P sl tl) = {fVar P sl tl} ∧
subfm (FALL s b) = {FALL s b} ∪ subfm b
End



Theorem FALLL_components:
∀sl b1 b2. FALLL sl b1 = FALLL sl b2 ⇒
b1 = b2
Proof
Induct_on ‘sl’ >> gs[FALLL_def]
QED
        

     
(*
Theorem wff_FALL_alt:
∀ b. wff (Σf,Σp) (FALL s b) ⇒
       wfs Σf s ∧
       ∀nn. (nn,s) ∉ ffv b ⇒
            wff (Σf,Σp) (substb (Var nn s) b) ∧
            FALL s b =
            mk_FALL nn s (substb (Var nn s) b)
Proof
Induct_on ‘b’ >> gs[F]
disch_tac >> gs[wff_FALL] >>

(substb (Var nn s) b)

Theorem wff_FALLL:
wff Σ (FALLL s b) ⇔
∃
*)


        
Theorem wff_FALL_alt:
  ∀f. wff (Σf,Σp,Σe) f ⇒
   ∀s b. f = (FALL s b) ⇒
  ∀nn. (nn,s) ∉ ffv b ⇒ 
  (FALL s b) = mk_FALL nn s (substb (Var nn s) b)
Proof
  Induct_on ‘wff’ >> rw[] >> gs[EQ_def] >>
  gs[mk_FALL_def,substb_def,abst_def] >>
  ‘fabs (nn,s') 0 (frpl 0 (Var nn s') b) = b’
    suffices_by metis_tac[] >>
  irule fabs_frpl >>
  simp[]
QED  

(*
Theorem wff_FALL_alt:
  ∀f. wff (Σf,Σp) f ⇒
   ∀s b. f = (FALL s b) ⇒
  ∀nn. (nn,s) ∉ ffv b ⇒ 
  (FALL s b) = mk_FALL nn s (substb (Var nn s) b)
Proof
  Induct_on ‘wff’ >> rw[] >>
  gs[mk_FALL_def,substb_def,abst_def] >>
  ‘fabs (nn,s') 0 (frpl 0 (Var nn s') b) = b’
    suffices_by metis_tac[] >>
  irule fabs_frpl >>
  simp[]
QED
*)
  
Theorem fVslfv_fabs:
fVslfv (fabs v i f) = fVslfv f
Proof
rw[fVslfv_def,fVars_fabs] 
QED

Definition vsfv_def:
vsfv vs = Uof (sfv o SND) vs
End


        
        
Definition wffsig_def:
wffsig Σf ⇔
(∀fsym.
     isfsym Σf fsym ⇒
     sfv (fsymout Σf fsym) ⊆
     BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)})
End     

Theorem FALLL_fbounds:
wffsig Σf ⇒
∀n sl b. LENGTH sl = n ⇒ wff (Σf,Σg,Σe) (FALLL sl b) ⇒
     fbounds b ⊆ count (LENGTH sl)
Proof
strip_tac >>
Induct_on ‘n’ >> rw[] (* 2 *)
>- (gs[FALLL_def] >>
   metis_tac[wff_fbounds]) >>
rw[] >> Cases_on ‘sl’ >> gs[] >>
gs[FALLL_def] >>
drule_then assume_tac wff_FALL_alt >>
first_x_assum (qspecl_then [‘h’,‘(FALLL t b)’] assume_tac) >> gs[] >>
‘∃nn. (nn,h) ∉ ffv (FALLL t b)’
 by metis_tac[ffv_FINITE,fresh_name_ex] >>
first_x_assum $ drule_then assume_tac >>
‘wff (Σf,Σg,Σe) (substb (Var nn h) (FALLL t b))’
 by (irule wff_spec >> gs[wffsig_def] >> simp[] >>
     simp[sort_of_def,wft_def] >> gs[] >>
     metis_tac[wff_FALL]) >>
gs[substb_def,frpl_FALLL] >>
first_x_assum $ (qspecl_then [‘(specsl 0 (Var nn h) t)’,‘(frpl n (Var nn h) b)’]) assume_tac >>
gs[LENGTH_specsl] >>
‘fabs (nn,h) n (frpl n (Var nn h) b) = b’
 by (irule fabs_frpl >> gs[ffv_FALLL,EXTENSION]) >>
qabbrev_tac ‘f1 = (frpl n (Var nn h) b)’ >>
qpat_x_assum ‘fabs (nn,h) n f1 = b’
(assume_tac o GSYM) >> gs[] >>
reverse (Cases_on ‘(nn,h) ∈ ffv f1’ (* 2 *))
>- (‘(fabs (nn,h) n f1) = f1’
    by (irule fabs_id >> simp[]) >>
gs[count_def,SUBSET_DEF] >> rw[] >>
first_x_assum $ drule_then assume_tac >> gs[]) >>  
qspecl_then [‘f1’,‘n’,‘nn’,‘h’] assume_tac
fbounds_fabs >>
‘fbounds (fabs (nn,h) n f1) = {n} ∪ fbounds f1’
  suffices_by
  (gs[Once EXTENSION,SUBSET_DEF,count_def] >>
  rw[] (* 2 *) >- simp[] >>
  first_x_assum $ drule_then assume_tac >> gs[])>>
first_x_assum irule >> simp[] >>
gs[ffv_FALLL] >>
‘fVslfv (fabs (nn,h) n f1) ⊆ ffv (fabs (nn,h) n f1)’
  by metis_tac[fVslfv_SUBSET_ffv] >>
‘(nn,h) ∉ fVslfv (fabs (nn,h) n f1)’
by (gs[SUBSET_DEF] >> metis_tac[]) >>
gs[fVslfv_fabs] >> reverse (rw[]) (* 2 *)
>- (drule_then assume_tac wff_no_vbound >>
   gs[ffv_FALLL] >>
   metis_tac[]) >>
CCONTR_TAC >> gs[] >>
‘(nn,h) ∈ ffv (fabs (nn,h) (LENGTH t) f1)’
 by (irule ill_formed_fabs_still_in >>
    metis_tac[])
QED    


  
                  

Theorem fVinst_fprpl:
  ∀ϕ σ bmap.
    wffVmap (Σf,Σg,Σe) σ ∧ wffsig Σf ∧
    (∀P sl tl. fVar P sl tl ∈ subfm ϕ ⇒
     LENGTH sl = LENGTH tl) ⇒
    fVinst σ (fprpl bmap ϕ) =
    fprpl bmap (fVinst σ ϕ)
Proof
  reverse (Induct_on ‘ϕ’)>>
  gs[fVinst_def,fprpl_def,subfm_def] >> reverse (rw[]) (* 2 *) >> gs[fprpl_def]
  >- (simp[fprpl_def] >>
     ‘(mk_bmap (REVERSE (MAP (tprpl bmap) l0))) =
      FMAP_MAP (tprpl bmap) (mk_bmap (REVERSE l0))’
      by (rw[GSYM rich_listTheory.MAP_REVERSE] >>
         simp[mk_bmap_MAP]) >>
     simp[] >>
     irule fprpl_FMAP_MAP >>
     gs[FDOM_mk_bmap] >> 
     drule_then assume_tac FALLL_fbounds >>
     ‘fbounds (σ ' (s,l)) ⊆ count (LENGTH l)’
      suffices_by simp[] >>
     first_x_assum irule >> gs[wffVmap_def] >>
     metis_tac[])
  >> metis_tac[]
QED  
        

(*
Theorem fVinst_fprpl:
  ∀ϕ σ bmap.
    wffVmap Σ σ ∧ wfsig Σ ∧
    (∀P sl tl. fVar P sl tl ∈ subfm ϕ ⇒
     LENGTH sl = LENGTH tl) ⇒
    fVinst σ (fprpl bmap ϕ) =
    fprpl bmap (fVinst σ ϕ)
Proof
  reverse (Induct_on ‘ϕ’)>>
  gs[fVinst_def,fprpl_def,subfm_def] >> reverse (rw[]) (* 2 *) >> gs[fprpl_def]
  >- (simp[fprpl_def] >>
     ‘(mk_bmap (REVERSE (MAP (tprpl bmap) l0))) =
      FMAP_MAP (tprpl bmap) (mk_bmap (REVERSE l0))’
      by (rw[GSYM rich_listTheory.MAP_REVERSE] >>
         simp[mk_bmap_MAP]) >>
     simp[] >>
     irule fprpl_FMAP_MAP >>
     gs[FDOM_mk_bmap] >>
     drule_then assume_tac FALLL_fbounds >>
     ‘fbounds (σ ' (s,l)) ⊆ count (LENGTH l)’
      suffices_by simp[] >>
     first_x_assum irule >> gs[wffVmap_def])
  >> metis_tac[]
QED  
*)  
        

Definition absapLs_def:
absapLs False = {} ∧
absapLs (Pred _ _) = {} ∧ 
absapLs (IMP f1 f2) = absapLs f1 ∪ absapLs f2∧
absapLs (FALL s b) = absapLs b ∧
absapLs (fVar P sl tl) = {(LENGTH sl,LENGTH tl)}
End

Theorem absapLs_fabs:
∀f i v. absapLs (fabs v i f) = absapLs f
Proof
Induct_on ‘f’ >> gs[absapLs_def,fabs_def]
QED


Theorem wff_absapLs_eq:
∀f. wff Σ f ⇒
    ∀n1 n2. (n1,n2) ∈ absapLs f ⇒ n1 = n2
Proof
Induct_on ‘wff’ >> gs[absapLs_def] >>
rw[] (* 5 *)
>- gs[absapLs_def,EQ_def]
>- metis_tac[]
>- metis_tac[]
>- metis_tac[wfabsap_LENGTH] >>
gs[mk_FALL_def,absapLs_def,absapLs_fabs,abst_def]  
QED

        
Theorem fVar_subfm_IN_absapLs:
∀f. ∀P sl tl. fVar P sl tl ∈ subfm f ⇒
    (LENGTH sl,LENGTH tl) ∈ absapLs f
Proof
Induct_on ‘f’ >> gs[subfm_def,absapLs_def]
>> metis_tac[]
QED


Theorem wff_subfm_fVar_LENGTH:
∀f. wff Σ f ⇒
    ∀P sl tl. fVar P sl tl ∈ subfm f ⇒
    LENGTH sl = LENGTH tl
Proof
rw[] >> 
drule_then assume_tac wff_absapLs_eq >>
first_x_assum irule >>
metis_tac[fVar_subfm_IN_absapLs]
QED


Theorem fVar_FALLL_inc:
∀l b f. f ∈ subfm b ⇒ f ∈ subfm (FALLL l b)
Proof
Induct_on ‘l’ >> gs[subfm_def,FALLL_def]
QED
                



     
Theorem fVar_prpl_o_fVmap:
∀f σ1 σ2.
wffsig Σf ∧
wffVmap (Σf,Σg,Σe) σ1 ∧ wffVmap (Σf,Σg,Σe) σ2 ⇒
fVinst σ2 (fVinst σ1 f) = fVinst (o_fVmap σ2 σ1) f
Proof
Induct_on ‘f’ >> gs[fVinst_def,FDOM_o_fVmap] >>
reverse (rw[]) (* 4 *)
>- gs[fVinst_def]
>- (drule_all_then assume_tac FAPPLY_o_fVmap2 >>
   simp[fVinst_def]) 
>- gs[] >>
drule_all_then assume_tac FAPPLY_o_fVmap1 >>
simp[] >>
irule fVinst_fprpl >>
first_x_assum $ irule_at Any >> simp[] >>
rw[] >>
gs[wffVmap_def] >>
first_x_assum $ drule_then assume_tac >>
‘fVar P sl tl ∈ subfm (FALLL l (σ1 ' (s,l)))’
 by (irule fVar_FALLL_inc >> simp[]) >>
irule wff_subfm_fVar_LENGTH >>
metis_tac[]
QED


Theorem fVar_prpl_o_fVmap1:
∀f σ1 σ2.
wffsig Σf ∧
(∀P sl. (P,sl) ∈ fVars f ∩ FDOM σ1 ⇒
 wff (Σf,Σp,Σe) (FALLL sl (σ1 ' (P,sl))))
∧ wffVmap (Σf,Σg,Σe) σ2 ⇒
fVinst σ2 (fVinst σ1 f) = fVinst (o_fVmap σ2 σ1) f
Proof
Induct_on ‘f’ >> gs[fVinst_def,FDOM_o_fVmap,fVars_def] >>
reverse (rw[]) (* 4 *) >> TRY (metis_tac[]) 
>- gs[fVinst_def]
>- (drule_all_then assume_tac FAPPLY_o_fVmap2 >>
   simp[fVinst_def])  >>
drule_all_then assume_tac FAPPLY_o_fVmap1 >>
simp[] >>
irule fVinst_fprpl >>
first_x_assum $ irule_at Any >> simp[] >>
rw[] >>
gs[wffVmap_def] >>
‘fVar P sl tl ∈ subfm (FALLL l (σ1 ' (s,l)))’
 by (irule fVar_FALLL_inc >> simp[]) >>
irule wff_subfm_fVar_LENGTH >>
metis_tac[]
QED

                
(*
Theorem fVar_prpl_o_fVmap:
∀f σ1 σ2.
wfsig Σ ∧
wffVmap Σ σ1 ∧ wffVmap Σ σ2 ⇒
fVinst σ2 (fVinst σ1 f) = fVinst (o_fVmap σ2 σ1) f
Proof
Induct_on ‘f’ >> gs[fVinst_def,FDOM_o_fVmap] >>
reverse (rw[]) (* 4 *)
>- gs[fVinst_def]
>- (drule_all_then assume_tac FAPPLY_o_fVmap2 >>
   simp[fVinst_def]) 
>- gs[] >>
drule_all_then assume_tac FAPPLY_o_fVmap1 >>
simp[] >>
irule fVinst_fprpl >>
first_x_assum $ irule_at Any >> simp[] >>
rw[] >>
gs[wffVmap_def] >>
first_x_assum $ drule_then assume_tac >>
‘fVar P sl tl ∈ subfm (FALLL l (σ1 ' (s,l)))’
 by (irule fVar_FALLL_inc >> simp[]) >>
irule wff_subfm_fVar_LENGTH >>
metis_tac[]
QED
*)

        
Theorem ofFMAP_SUBSET_MONO:
s1 ⊆ s2 ⇒ ofFMAP f σ s1 ⊆ ofFMAP f σ s2
Proof
gs[ofFMAP_def,SUBSET_DEF] >> metis_tac[]
QED
                       

Theorem ffv_finst_wfvmap:
∀f σ Σ.
       wfvmap Σ σ ∧ ffv f ⊆ FDOM σ ⇒
       ∀n st.
         (n,st) ∈ ffv (finst σ f) ⇔
         ∃n0 st0. (n0,st0) ∈ ffv f ∧ (n,st) ∈ tfv (σ ' (n0,st0))
Proof
rw[] >> irule ffv_finst >>
gs[wfvmap_def] >> gs[] >> metis_tac[wfcod_no_bound]
QED

        
Theorem IN_vsfv:
  x ∈ vsfv vs ⇔ ∃n s. (n,s)∈ vs ∧ x ∈ sfv s
Proof
  rw[vsfv_def,Uof_def,PULL_EXISTS] >>
  rw[EQ_IMP_THM] (* 2 *)
  >- (qexistsl [‘FST e’,‘SND e’] >> simp[]) >>
  qexists ‘(n,s)’ >> simp[]
QED

Theorem IN_Uof_Uof:
x ∈ Uof f1 (Uof f2 A) ⇔ ∃a e. a ∈ A ∧ e ∈ f2 a ∧ x ∈ f1 e
Proof
rw[Uof_def] >> metis_tac[]
QED

        
        
Theorem IN_genavds:
∀x th. x ∈ genavds (Γ,A,f) ⇔
       (∃n s. (n,s) ∈ Γ ∧ x ∈ sfv s) ∨
       (∃a. a ∈ A ∧ x ∈ ffv a) ∨
       (∃P sl s f0. (f0 = f ∨ f0 ∈ A) ∧ (P,sl) ∈ fVars f0 ∧
                    MEM s sl ∧ x ∈ sfv s)
Proof
rw[genavds_def,cont_def,concl_def,assum_def,Uof_UNION,Uof_Sing] >> rw[GSYM vsfv_def,GSYM fVslfv_def] >>
simp[IN_Uof_Uof] >>
Cases_on ‘x’ >> simp[IN_slfv,IN_fVslfv,IN_vsfv] >>
simp[IN_Uof,PULL_EXISTS] >> rw[EQ_IMP_THM] >>
TRY (metis_tac[]) (* 2 *)
>- (disj2_tac >> disj2_tac >>
Cases_on ‘e’ >> gs[] >> metis_tac[]) >>
disj2_tac >> disj2_tac >>
rpt (first_x_assum $ irule_at Any) >> simp[]
QED


Theorem NOTIN_genavds:
∀x th. x ∉ genavds (Γ,A,f) ⇔
       (∀n s. (n,s) ∈ Γ ⇒ x ∉ sfv s) ∧
       (∀a. a ∈ A ⇒ x ∉ ffv a) ∧
       (∀P sl s f0. (f0 = f ∨ f0 ∈ A) ∧ (P,sl) ∈ fVars f0 ∧
                    MEM s sl ⇒  x ∉ sfv s)
Proof
simp[IN_genavds] >>
rw[EQ_IMP_THM] >>
TRY (metis_tac[]) (* 2 *)
QED        


Theorem trpl_tprpl:
  (∀tm i new. trpl i new tm = tprpl (TO_FMAP [(i,new)]) tm)∧
  (∀st i new. srpl i new st = sprpl (TO_FMAP [(i,new)]) st)
Proof
  ho_match_mp_tac better_tm_induction >>
  gs[trpl_def,tprpl_def,MAP_EQ_f,FDOM_TO_FMAP] >>
  rpt strip_tac >> Cases_on ‘i = n’ (* 2 *)
  >- (pop_assum SUBST_ALL_TAC>> rw[TO_FMAP_SING]) >>
  simp[]
QED



Theorem frpl_fprpl:
  (∀f i new. tbounds new = {} ⇒
             frpl i new f = fprpl (TO_FMAP [(i,new)]) f)
Proof
  Induct_on ‘f’ >> 
  gs[frpl_def,fprpl_def,MAP_EQ_f,FDOM_TO_FMAP,trpl_tprpl] >>
  rw[] >>
  ‘(TO_FMAP [(i + 1,new)]) =(shift_bmap 1 (TO_FMAP [(i,new)])) ’ suffices_by metis_tac[] >>
  rw[fmap_EXT,FDOM_TO_FMAP,FDOM_shift_bmap,TO_FMAP_SING] >>
  ‘i ∈ FDOM (TO_FMAP [(i,new)])’ by simp[FDOM_TO_FMAP] >>
  drule_then assume_tac FAPPLY_shift_bmap >>
  ‘i + 1 = 1 + i’ by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  simp[] >> simp[TO_FMAP_SING] >>
  metis_tac[tshift_id]
QED

Theorem ffv_frpl:
  tbounds new = {} ∧
  (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ∧
  i ∈ fbounds f ⇒ ffv (frpl i new f) = ffv f ∪ tfv new
Proof
  rw[] >> drule_then assume_tac frpl_fprpl >>
  simp[] >>
  qspecl_then [‘f’,‘(TO_FMAP [(i,new)])’]
  assume_tac ffv_fprpl >>
  gs[FDOM_TO_FMAP] >>
  ‘BIGUNION
          {tfv (TO_FMAP [(i,new)] ' i') | i' | i' = i ∧ i' ∈ fbounds f}  = tfv new’
   by (rw[Once EXTENSION,EQ_IMP_THM] 
      >- gs[TO_FMAP_SING]
      >- gs[TO_FMAP_SING]) >>
   gs[] >> first_x_assum irule >> metis_tac[]
QED   


(*
Theorem ffv_frpl:
  ∀f i new. (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ∧
  i ∈ fbounds f ⇒ ffv (frpl i new f) = ffv f ∪ tfv new
Proof
  Induct_on ‘f’ >> not required, but should be provable
QED   
*)

               
Theorem frpl_id:
∀f i. i ∉ fbounds f ⇒ frpl i new f = f
Proof
Induct_on ‘f’ >> gs[fbounds_def,frpl_def,MEM_MAP,MAP_fix]
(* 3 *)
>- metis_tac[trpl_id]
>- (rw[] (* 2 *)
   >- metis_tac[trpl_id] >>
   first_x_assum (qspecl_then [‘i + 1’] assume_tac) >>
   gs[] >>
   metis_tac[]) >>
metis_tac[trpl_id]
QED   



Theorem ffv_frpl_SUBSET:
  tbounds new = {} ∧
  (∀n s. (n,s) ∈ ffv f ⇒ sbounds s = ∅) ⇒
  ffv (frpl i new f) ⊆ ffv f ∪ tfv new
Proof
  rw[] >>
  Cases_on ‘ i∈ fbounds f’ (* 2 *)
  >- (drule_all_then assume_tac ffv_frpl >> gs[]) >>
  drule_all_then assume_tac frpl_id >>
  simp[]
QED


Theorem wff_IMP:
  wff Σ (IMP f1 f2) ⇔ wff Σ f1 ∧ wff Σ f2
Proof
  rw[EQ_IMP_THM]
  >- gs[Once wff_cases,mk_FALL_def,EQ_def]
  >- gs[Once wff_cases,mk_FALL_def,EQ_def] >>
  Cases_on ‘Σ’ >> Cases_on ‘r’ >> irule wff_IMP >>
  simp[]
QED                          
         

Theorem wfvmap_IN_ofMAP_wfs:
wfvmap Σf vσ ∧ (n,s) ∈ ofFMAP tfv vσ vs ⇒
wfs Σf s
Proof
gs[wfvmap_def,ofFMAP_def,PULL_EXISTS] >> rw[]>>
gs[wfcod_def] >> Cases_on ‘a’ >>
metis_tac[wft_wfs]
QED        


Theorem ffv_finst_alt:
cstt σ ∧ ffv f ⊆ FDOM σ ∧ no_bound σ ⇒
ffv (finst σ f) = ofFMAP tfv σ (ffv f)
Proof           
rw[] >> drule_all_then assume_tac ffv_finst >>
simp[Once EXTENSION] >> rw[] >>
Cases_on ‘x’ >> simp[] >>
rw[ofFMAP_def,PULL_EXISTS] >> gs[SUBSET_DEF] >>
rw[EQ_IMP_THM] (* 2 *)
>- (first_x_assum $ irule_at Any >> metis_tac[]) >>
Cases_on ‘a’ >> metis_tac[]
QED

Theorem finst_o_vmap:
∀f σ1 σ2.
     ffv f ⊆ FDOM σ1 ∧ ffv (finst σ1 f) ⊆ FDOM σ2 ⇒
     finst σ2 (finst σ1 f) = finst (o_vmap σ2 σ1) f
Proof
Induct_on ‘f’ >> gs[ffv_thm,finst_def,MAP_MAP_o,MAP_EQ_f,MEM_MAP] (* 3 *)
>- (rw[] >> irule $ cj 1 inst_o_vmap >>
   gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[])
>- (rw[] >> irule $ cj 2 inst_o_vmap >> gs[SUBSET_DEF,PULL_EXISTS]) >>
rw[] (* 2 *)
>- (irule $ cj 2 inst_o_vmap >> gs[SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[]) >>
irule $ cj 1 inst_o_vmap >> gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[]
QED
    
Definition fVmap_fVrn_def:
fVmap_fVrn σ uσ =
FUN_FMAP (λ(P,sl). σ ' (CHOICE {(P0,sl) | uσ ' (P0,sl) = P ∧ (P0,sl) ∈ FDOM σ}))
(IMAGE (fVrn uσ) (FDOM σ))
End



        
Theorem FDOM_fVmap_fVrn:
FDOM (fVmap_fVrn σ uσ) = (IMAGE (fVrn uσ) (FDOM σ))
Proof
rw[fVmap_fVrn_def,FUN_FMAP_DEF]
QED

Theorem FAPPLY_fVmap_fVrn:
uniqifn uσ (FDOM σ) ⇒
∀P sl. (P,sl) ∈ FDOM σ ⇒
 (fVmap_fVrn σ uσ) ' (uσ ' (P,sl), sl) =
 σ ' (P,sl)
Proof
rw[fVmap_fVrn_def] >>
‘(P,sl) ∈ FDOM uσ’ by metis_tac[uniqifn_def,SUBSET_DEF] >>
‘FINITE (IMAGE (fVrn uσ) (FDOM σ))’ by simp[] >>
qspecl_then [‘(λ(P,sl).
               σ ' (CHOICE {(P0,sl) | uσ ' (P0,sl) = P ∧ (P0,sl) ∈ FDOM σ}))’,‘(IMAGE (fVrn uσ) (FDOM σ))’] assume_tac
FUN_FMAP_DEF >>
gs[PULL_EXISTS] >> first_x_assum $ drule_then assume_tac >>
gs[fVrn_def] >>
‘{(P0,sl') | uσ ' (P0,sl') = uσ ' (P,sl) ∧ (P0,sl') ∈ FDOM σ} = {(P,sl)}’
 by (rw[EXTENSION] >>
    Cases_on ‘x’ >> gs[uniqifn_def] >> metis_tac[]) >>
gs[]
QED 
        
Theorem uniqifn_FDOM_SUBSET:
uniqifn uσ fVs ⇒ fVs ⊆ FDOM uσ
Proof
gs[uniqifn_def]
QED


        
Theorem fVinst_ffVrn:
uniqifn uσ (FDOM σ) ⇒
∀f. fVars f ⊆ FDOM σ ⇒
fVinst (fVmap_fVrn σ uσ) (ffVrn uσ f) =
fVinst σ f
Proof           
strip_tac >> Induct_on ‘f’ >>
gs[fVinst_def,ffVrn_def,fVars_def] >> rw[] (* 2 *)
>- (rw[fVinst_def] (* 2 *) >- (AP_TERM_TAC >>
   drule_all_then assume_tac FAPPLY_fVmap_fVrn >>
   simp[]) >>
gs[FDOM_fVmap_fVrn] >>
first_x_assum $ qspecl_then [‘(s,l)’] assume_tac >>
gs[fVrn_def])      >>
metis_tac[SUBSET_DEF,uniqifn_def]
QED

(*
Theorem fVinst_ffVrn:
∀f. uniqifn uσ (fVars f) ∧ fVars f ⊆ FDOM σ ⇒
fVinst (fVmap_fVrn σ uσ) (ffVrn uσ f) =
fVinst σ f
Proof           
strip_tac >> Induct_on ‘f’ >>
gs[fVinst_def,ffVrn_def,fVars_def] >> rw[] (* 4 *)
>- (‘uniqifn uσ (fVars f)’ suffices_by metis_tac[] >>
   irule uniqifn_SUBSET >> last_x_assum $ irule_at Any >> simp[])
>- (‘uniqifn uσ (fVars f')’ suffices_by metis_tac[] >>
   irule uniqifn_SUBSET >> last_x_assum $ irule_at Any >> simp[])   
>- ‘fVmap_fVrn σ uσ ' (uσ ' (s,l),l) =
    fVmap_fVrn (DRESTRICT σ {(s,l)}) uσ ' (uσ ' (s,l),l)’
    rw[fVmap_fVrn_def]

(rw[fVinst_def] (* 2 *) >- (AP_TERM_TAC >>
   drule_all_then assume_tac FAPPLY_fVmap_fVrn >>
   simp[]) >>
gs[FDOM_fVmap_fVrn] >>
first_x_assum $ qspecl_then [‘(s,l)’] assume_tac >>
gs[fVrn_def])      >>
metis_tac[SUBSET_DEF,uniqifn_def]
QED
*)
        


Theorem uniqifn_ex:
∀fVs. FINITE fVs ⇒ ∃uσ:string # (sort list) |-> string. uniqifn uσ fVs ∧ FDOM uσ = fVs
Proof
Induct_on ‘FINITE’ >>
rw[] (* 2 *)
>- (qexists ‘FEMPTY’ >> simp[uniqifn_def]) >>
qexists ‘uσ |+ (e,variant (fromSet (IMAGE (λfV. uσ ' fV) (FDOM uσ))) "")’ >>
‘variant (fromSet (IMAGE (λfV. uσ ' fV) (FDOM uσ))) ""
 ∉ toSet (fromSet (IMAGE (λfV. uσ ' fV) (FDOM uσ)))’
by (simp[GSYM fIN_IN] >> simp[variant_NOT_fIN]) >>
‘FINITE (IMAGE (λfV. uσ ' fV) (FDOM uσ))’ by simp[] >>
drule_then assume_tac toSet_fromSet >> gs[] >>
rw[uniqifn_def] (* 3 *)
>> (rw[FAPPLY_FUPDATE_THM] >>
   gs[uniqifn_def,SUBSET_DEF] >> metis_tac[])
QED


(*        
Theorem uniqifn_ex:
∀fVs. FINITE fVs ⇒ ∃uσ:string # (sort list) |-> string. uniqifn uσ fVs 
Proof
Induct_on ‘FINITE’ >>
rw[] (* 2 *)
>- (qexists ‘FEMPTY’ >> simp[uniqifn_def]) >>
qexists ‘uσ |+ (e,variant (fromSet (IMAGE (λfV. uσ ' fV) (FDOM uσ))) "")’ >>
‘variant (fromSet (IMAGE (λfV. uσ ' fV) (FDOM uσ))) ""
 ∉ toSet (fromSet (IMAGE (λfV. uσ ' fV) (FDOM uσ)))’
by (simp[GSYM fIN_IN] >> simp[variant_NOT_fIN]) >>
‘FINITE (IMAGE (λfV. uσ ' fV) (FDOM uσ))’ by simp[] >>
drule_then assume_tac toSet_fromSet >> gs[] >>
rw[uniqifn_def] (* 4 *)
>- metis_tac[uniqifn_def]
>> (rw[FAPPLY_FUPDATE_THM] >>
   gs[uniqifn_def,SUBSET_DEF] >> metis_tac[])
QED
*)

Definition plainfV_def:
plainfV (P,sl) =
fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
End

(*        
Theorem fprpl_plainfV:
FDOM bmap = 
fprpl bmap (plainfV (P,sl)) =
fVar P sl (map2list (λi.)
*)        
        
Definition rn2fVmap_def:
rn2fVmap uσ =
FUN_FMAP (λfV. plainfV (fVrn uσ fV)) (FDOM uσ)
End
        
Theorem FDOM_rn2fVmap:
FDOM (rn2fVmap uσ) = FDOM uσ
Proof
rw[rn2fVmap_def]
QED

Theorem FAPPLY_rn2fVmap:
fV ∈ FDOM uσ ⇒ (rn2fVmap uσ) ' fV = plainfV (fVrn uσ fV)
Proof
rw[rn2fVmap_def] >>
qspecl_then [‘(λfV. plainfV (fVrn uσ fV))’,‘FDOM uσ’]
assume_tac FUN_FMAP_DEF >>
gs[]
QED



Theorem MAP_tprpl_mk_bmap_REVERSE:
MAP (tprpl (mk_bmap (REVERSE l0)) ∘ Bound)
          (REVERSE (COUNT_LIST (LENGTH l0))) =
        l0
Proof        
 irule LIST_EQ >> simp[] >>
    simp[rich_listTheory.LENGTH_COUNT_LIST] >>
 rw[] >>
 ‘x < LENGTH (REVERSE (COUNT_LIST (LENGTH l0)))’
  by simp[rich_listTheory.LENGTH_COUNT_LIST] >>
  drule_then assume_tac $ INST_TYPE [alpha |-> “:num”,beta |-> “:term” ] EL_MAP >> simp[] >>
  simp[tprpl_def,FDOM_mk_bmap] >>
  ‘EL x (REVERSE (COUNT_LIST (LENGTH l0))) < LENGTH l0’
   by (irule $ iffLR rich_listTheory.MEM_COUNT_LIST >>
      simp[MEM_EL] >> qexists ‘PRE (LENGTH l0 - x)’ >>
      simp[] >> rw[] (* 2 *)
      >- gs[rich_listTheory.LENGTH_COUNT_LIST] >>
      ‘ EL x (REVERSE (COUNT_LIST (LENGTH l0))) =
        EL (PRE (LENGTH (COUNT_LIST (LENGTH l0)) − x)) (COUNT_LIST (LENGTH l0))’ suffices_by gs[rich_listTheory.LENGTH_COUNT_LIST] >>
      irule EL_REVERSE >> simp[rich_listTheory.LENGTH_COUNT_LIST]) >>
  simp[] >>
  ‘(EL x (REVERSE (COUNT_LIST (LENGTH l0)))) < LENGTH (REVERSE l0)’
   by gs[LENGTH_REVERSE] >>
  drule_then assume_tac FAPPLY_mk_bmap >> gs[] >>
   drule_then assume_tac EL_REVERSE >> simp[] >>
   ‘(PRE (LENGTH l0 − EL x (REVERSE (COUNT_LIST (LENGTH l0))))) = x’ suffices_by metis_tac[] >>
    qpat_x_assum ‘x < LENGTH (COUNT_LIST (LENGTH l0))’
  assume_tac >>
 drule_then assume_tac EL_REVERSE >> simp[] >>
 simp[rich_listTheory.LENGTH_COUNT_LIST] >>
 ‘(PRE (LENGTH l0 − x)) < LENGTH l0’
  by gs[] >>
  drule_then assume_tac rich_listTheory.EL_COUNT_LIST >>
  simp[]
QED        

Theorem ffVrn_fVinst:
∀f.
(∀P sl tl. fVar P sl tl ∈ subfm f ⇒ LENGTH sl = LENGTH tl)⇒
 ffVrn uσ f = fVinst (rn2fVmap uσ) f
Proof
Induct_on ‘f’ >> gs[ffVrn_def,fVinst_def,subfm_def]>> rw[] >>
gs[FDOM_rn2fVmap,FAPPLY_rn2fVmap] >> TRY (metis_tac[]) >>
rw[fVrn_def,plainfV_def] >>
simp[fprpl_def] >> rw[MAP_MAP_o] >>
simp[MAP_tprpl_mk_bmap_REVERSE]
QED


Theorem wfvmap_presname:
 wfvmap Σ vσ ⇒ presname vσ
Proof
simp[wfvmap_def,presname_def] >> strip_tac >>
strip_tac >> strip_tac >>
‘¬is_bound (vσ ' v)’
 by (Cases_on ‘v’ >>
    metis_tac[wfcod_def,wft_not_bound]) >>
gs[] >> gs[cstt_def] >>
Cases_on ‘v’ >> gs[vsname_def] >>
Cases_on ‘r’ >> gs[sname_def] >>
first_x_assum $ drule_then assume_tac >>
gs[tsname_def,sname_def]
QED


(*here *)        

(*       
Theorem wfabsap_vl_ex:
∀n tl sl. LENGTH tl = n ∧ wfabsap Σ sl tl ⇒
     ∃vl σ. wfabsap Σ sl vl ∧ tl = MAP (tinst σ) vl
Proof
 Induct_on ‘n’ >- cheat >>
 rw[] >>
 Cases_on ‘sl’ >> Cases_on ‘tl’ >>
 gs[wfabsap_def] >>
 first_x_assum $ drule_all_then assume_tac >>
 gs[] >>
 qexistsl [‘(Var "" h) :: vl’,‘σ |+ (("",h),h')’] >>
 rw[wfabsap_def]


Theorem ok_abs_wff_fVar:
ok_abs sl ⇒ w
Proof

wff_FALL_alt
Theorem wff_FALL1:
wff Σ (FALL s b) ⇔
wft (FST Σ) s ∧
∀n. wff Σ (substb (Var n s) b)
Proof
            

Theorem wff_FALLL_plainfV:
∀n sl. LENGTH sl = n ∧ wfabsap Σf sl tl ⇒
       ∃f. wff Σ
       FALLL sl (plainfV (P,sl)) = mk_FALLL
       () (fVar P sl (MAP (λs. Var "" s) sl))
Proof
Induct_on ‘n’ >> rw[] (* 2 *)
>- (rw[rich_listTheory.COUNT_LIST_def,ok_abs_def,FALLL_def,plainfV_def] >>
   irule wff_fVar' >> simp[wfabsap_def]) >>
rw[] >> Cases_on ‘sl’  (* 2 *)
>- gs[] >>
gs[] >>        

Theorem wff_FALLL_plainfV:
∀n sl. LENGTH sl = n ∧ ok_abs sl ⇒
       wff Σ (FALLL sl (plainfV (P,sl)))
Proof
Induct_on ‘n’ >> rw[] (* 2 *)
>- (rw[rich_listTheory.COUNT_LIST_def,ok_abs_def,FALLL_def,plainfV_def] >>
   irule wff_fVar' >> simp[wfabsap_def]) >>
rw[] >> Cases_on ‘sl’  (* 2 *)
>- gs[] >>
gs[] >> 

   
Induct_on ‘sl’ (* 2 *)
>- (rw[rich_listTheory.COUNT_LIST_def,ok_abs_def,FALLL_def,plainfV_def] >>
   irule wff_fVar' >> simp[wfabsap_def]) >>
ok_abs_def   
   rw[]
gs[FALLL_def,ok_abs_def,plainfV_def,]         

Theorem wffVmap_rn2fVmap:
(∀P sl. (P,sl) ∈ FDOM uσ ⇒ ok_abs sl) ⇒ wffVmap Σ (rn2fVmap uσ)
Proof
rw[wffVmap_def,FDOM_rn2fVmap] >>
drule_then assume_tac FAPPLY_rn2fVmap >> gs[] >>
rw[fVrn_def,plainfV_def] >> cheat
QED
*)


Theorem fVinst_FALLL:
∀sl b. fVinst σ (FALLL sl b) = FALLL sl (fVinst σ b)
Proof
Induct_on ‘sl’ >> gs[fVinst_def,FALLL_def]
QED

Theorem wffVmap_o_fVmap:
∀σ1 σ2. wffsig Σf ∧ wffVmap (Σf,Σp,Σe) σ1 ∧ wffVmap (Σf,Σp,Σe) σ2 ⇒
        wffVmap (Σf,Σp,Σe) (o_fVmap σ2 σ1)
Proof
rw[wffVmap_def] >> gs[FDOM_o_fVmap] (* 2 *)
>- (drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
   gs[GSYM fVinst_FALLL] >> first_x_assum $ drule_then assume_tac >>
   irule wff_fVinst >> simp[wffVmap_def] >> gs[wffsig_def]) >>
Cases_on ‘(P,sl) ∈ FDOM σ1’ (* 2 *)
>- (drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
   gs[GSYM fVinst_FALLL] >> first_assum $ drule_then assume_tac >>
   irule wff_fVinst >> simp[wffVmap_def] >> gs[wffsig_def]) >>
drule_all_then assume_tac FAPPLY_o_fVmap2  >> gs[]
QED


Theorem wffVmap_fVmap_fVrn:
∀σ. wffVmap Σ σ ∧ uniqifn uσ (FDOM σ) ⇒
    wffVmap Σ (fVmap_fVrn σ uσ)
Proof
rw[wffVmap_def] >> gs[FDOM_fVmap_fVrn] >> Cases_on ‘x’ >>
drule_all_then assume_tac FAPPLY_fVmap_fVrn >>
simp[fVrn_def] >>
‘(q,r) ∈ FDOM uσ’by metis_tac[uniqifn_def,SUBSET_DEF] >> simp[] >>
first_assum $ drule_all_then assume_tac >>
gs[fVrn_def]
QED                


Theorem finst_FALLL:
∀sl b. finst vσ (FALLL sl b) =
 FALLL (MAP (sinst vσ) sl) (finst vσ b) 
Proof
Induct_on ‘sl’ >> gs[finst_def,FALLL_def]
QED

Theorem IN_slfv':
v ∈ slfv sl ⇔ ∃s0. MEM s0 sl ∧ v ∈ sfv s0
Proof
Cases_on ‘v’ >> rw[IN_slfv]
QED
        
Theorem wffVmap_vinst_fVmap:
∀σ. wffsig (FST Σ) ∧ wffVmap Σ σ ∧ alluniq (FDOM σ) ∧ wfvmap (FST Σ) vσ ∧
    presname vσ ∧
   BIGUNION  {ffv (σ ' (P,sl)) ∪ slfv sl | (P,sl) | (P,sl) ∈ FDOM σ} ⊆ FDOM vσ ⇒
        wffVmap Σ (vinst_fVmap vσ σ)
Proof
rw[wffVmap_def] >> gs[FDOM_vinst_fVmap] >>
Cases_on ‘x’ >>
drule_all_then assume_tac FAPPLY_vinst_fVmap >>
gs[] >> gs[vinst_fVar_def] >>
first_x_assum $ drule_all_then assume_tac >>
rw[GSYM finst_FALLL] >>
Cases_on ‘Σ’ >> Cases_on ‘r'’ >> gs[] >> irule wff_finst >>
gs[wffsig_def] >> gs[wfvmap_def] >>
gs[ffv_FALLL,SUBSET_DEF,PULL_EXISTS]  >>
gs[IN_slfv'] >> rw[] (* 2 *) >> metis_tac[]
QED                 
           

Theorem ffv_ffVrn:
ffv (ffVrn uσf f) = ffv f
Proof
Induct_on ‘f’ >> gs[ffVrn_def,ffv_thm] >> rw[]
QED


        


Theorem ofFMAP_SUBSET_ffv_fVinst:
∀f. (∀fv. fv ∈ FDOM σ ∩ fVars f ⇒ ∀n s. (n,s) ∈ ffv (σ ' fv) ⇒ sbounds s = {}) ⇒
   ofFMAP ffv σ (fVars f) ⊆ ffv (fVinst σ f)
Proof
Induct_on ‘f’ >> gs[fVars_def,ffv_def,fVinst_def,ofFMAP_UNION,ofFMAP_EMPTY]
(* 3 *)
>- (gs[SUBSET_DEF]>> metis_tac[])
>- (gs[SUBSET_DEF]>> metis_tac[]) >>
rw[ofFMAP_Sing] (* 2 *)
>- (drule_all_then assume_tac ffv_fprpl >> gs[]) >>
gs[ofFMAP_Sing_EMPTY]
QED




Theorem wffVmap_DRESTRICT:
wffVmap Σ σ ⇒ ∀s. wffVmap Σ (DRESTRICT σ s)
Proof
gs[wffVmap_def,DRESTRICT_DEF]
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



        
Theorem Pf2Pf0_fVinsth_lemma:
∀uσ. wffsig Σf ∧ wff (Σf,Σp,Σe) f ∧
     uniqifn uσf (FDOM fσ) ∧
     wffVmap (Σf,Σp,Σe) fσ ∧ fVars f ⊆ FDOM fσ ∧
     wfcfVmap (Σf,Σp,Σe) σ ∧ wfvmap Σf vσ ∧
     ffv f ∪ ffv (fVinst fσ f) ⊆ FDOM vσ
     ⇒
fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))) =
fVinst
(o_fVmap σ
 (vinst_fVmap vσ
  (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)))
       (finst vσ (ffVrn uσf f))
Proof
rw[] >>
‘wff (Σf,Σp,Σe) (fVinst fσ f)’
 by (irule wff_fVinst >> gs[wffsig_def]) >>
(* wff_subfm_fVar_LENGTH *) 
‘ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’
 by (irule ffVrn_fVinst >>
    rw[] >> irule wff_subfm_fVar_LENGTH >> metis_tac[]) >>
simp[] >>
‘wffVmap (Σf,Σp,Σe) (rn2fVmap uσ)’
 by cheat >>
‘fVinst (rn2fVmap uσ) (fVinst fσ f) =
 fVinst (o_fVmap (rn2fVmap uσ) fσ) f’
 by (irule fVar_prpl_o_fVmap >> rpt (first_x_assum $ irule_at Any)) >>
simp[] >>
‘fVinst (o_fVmap (rn2fVmap uσ) fσ) f =
 fVinst (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) f’
  by (irule fVars_DRESTRICT_fVinst_eq1 >> simp[]) >>   
‘uniqifn uσf (FDOM (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)))’
  by simp[DRESTRICT_DEF,FDOM_o_fVmap,FDOM_rn2fVmap,INTER_UNION] >>
‘(fVinst (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) f) =
 (fVinst (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf) (ffVrn uσf f))’    
  by (irule $ GSYM fVinst_ffVrn >>
     simp[FDOM_o_fVmap] >> gs[SUBSET_DEF,DRESTRICT_DEF,FDOM_o_fVmap,FDOM_rn2fVmap] ) >> simp[] >>
‘finst vσ
             (fVinst (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)
                (ffVrn uσf f)) =
 (instf
          (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf))
          vσ
          (ffVrn uσf f))’
 by (irule instf_fVinst >> simp[ffv_ffVrn] >>
    simp[FDOM_fVmap_fVrn,FDOM_o_fVmap,fVars_ffVrn,FDOM_rn2fVmap] >> rw[] (* 6 *)
    >- (gs[wfvmap_def] >>
       metis_tac[wfcod_no_bound,no_bound_def])
    >- metis_tac[wff_no_vbound]
    >- (gs[FDOM_o_fVmap,FDOM_rn2fVmap,DRESTRICT_DEF] >>
        rev_drule_all_then assume_tac uniqifn_alluniq0 >>
        gs[IMAGE_UNION,INTER_UNION])
    >- (gs[SUBSET_DEF,DRESTRICT_DEF,FDOM_o_fVmap,FDOM_rn2fVmap])
    >- (‘ffv (ffVrn uσ (fVinst fσ f)) ⊆ FDOM vσ’ suffices_by simp[] >>
       qpat_x_assum ‘ ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’ (K all_tac) >>
       gs[ffv_ffVrn]) >>
    irule_at Any wffVmap_fVmap_fVrn >>
    qexists ‘(Σf,Σp,Σe)’ >> 
    simp[FDOM_o_fVmap,FDOM_rn2fVmap,FDOM_DRESTRICT] >>
    irule wffVmap_DRESTRICT >> 
    irule_at Any wffVmap_o_fVmap >>
    first_x_assum $ irule_at Any >> simp[]) >>
simp[] >> rw[instf_def] >>
irule fVar_prpl_o_fVmap1 >> gs[wfcfVmap_def] >>
simp[FDOM_vinst_fVmap,fVars_finst,PULL_EXISTS,FDOM_fVmap_fVrn,
    FDOM_o_fVmap,FDOM_rn2fVmap,fVars_ffVrn,FDOM_DRESTRICT]  >>
‘∃Σe' Σf' Σg Σp'.
          (∀P sl x'.
             ((P,sl) = vinst_fVar vσ (fVrn uσf x') ∧ x' ∈ fVars f)  ⇒
             wff (Σf',Σp',Σe')
               (FALLL sl
                  (vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf) '
                   (vinst_fVar vσ (fVrn uσf x'))))) ∧ wffsig Σf' ∧
          wffVmap (Σf',Σg,Σe') σ’
  suffices_by metis_tac[] >>       
rpt (first_assum $ irule_at Any) >> qexists ‘Σp’ >> simp[] >>
‘wffVmap (Σf,Σp,Σe) (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf)’
 by (irule wffVmap_fVmap_fVrn >> simp[FDOM_o_fVmap] >>
     irule wffVmap_DRESTRICT >> 
    irule wffVmap_o_fVmap >> simp[]) >> simp[] >>
rw[] >>
Cases_on ‘x'’ >>
‘(vinst_fVmap vσ (fVmap_fVrn (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) uσf) '
              (vinst_fVar vσ (fVrn uσf (q,r)))) =
 finst vσ ((DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) ' (q,r)) ’
by (irule FAPPLY_vinst_fVmap_fVmap_fVrn >>
   simp[FDOM_o_fVmap,FDOM_rn2fVmap,FDOM_DRESTRICT] >> gs[uniqifn_def,SUBSET_DEF]) >>
simp[] >>
gs[fVrn_def,vinst_fVar_def] >>
‘(q,r) ∈ FDOM uσf’ by (gs[uniqifn_def,SUBSET_DEF] >> metis_tac[]) >>
gs[] >> gs[vinst_fVar_def] >>
‘(FALLL (MAP (sinst vσ) r)
             (finst vσ ((DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) ' (q,r)))) =
 finst vσ (FALLL r ((DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ)) ' (q,r)))’
 by simp[finst_FALLL] >>
 gs[] >>
irule wff_finst >>
gs[wffsig_def] >>
‘cstt vσ ∧ presname vσ ∧ wfcod Σf vσ’
 by metis_tac[wfvmap_def,wfvmap_presname] >> gs[] >>
‘wffVmap (Σf,Σp,Σe) (o_fVmap (rn2fVmap uσ) fσ)’
 by (irule wffVmap_o_fVmap >> simp[] >> gs[wffsig_def]) >>
‘wffVmap (Σf,Σp,Σe) (DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ))’
 by metis_tac[wffVmap_DRESTRICT] >> 
drule_then assume_tac $ iffLR wffVmap_def >>
gs[FDOM_o_fVmap,FDOM_DRESTRICT] >>
first_x_assum $ qspecl_then [‘q’,‘r’] assume_tac >>
reverse (rw[]) (* 2 *)
>- gs[SUBSET_DEF] >>
simp[ffv_FALLL] >>
‘(q,r) ∈ FDOM fσ’ by gs[SUBSET_DEF] >>
‘(DRESTRICT (o_fVmap (rn2fVmap uσ) fσ) (FDOM fσ) ' (q,r)) =
 (o_fVmap (rn2fVmap uσ) fσ) ' (q,r)’
  by simp[DRESTRICT_DEF,FDOM_o_fVmap,FDOM_rn2fVmap] >>
gs[] >>   
drule_then assume_tac FAPPLY_o_fVmap1 >>
simp[] >>
‘(fVinst (rn2fVmap uσ) (fσ ' (q,r))) = ffVrn uσ (fσ ' (q,r))’
by (irule $ GSYM ffVrn_fVinst >>
   rw[] >> irule $ GSYM wff_subfm_fVar_LENGTH >>
   qexists ‘P’ >>
   qpat_x_assum ‘wffVmap (Σf,Σp,Σe) fσ’ assume_tac >>
   gs[wffVmap_def] >>
   first_x_assum $ drule_then assume_tac >>
   first_x_assum $ irule_at Any >>
   metis_tac[fVar_FALLL_inc]) >>
simp[] >> simp[ffv_ffVrn] >>
rw[] (* 2 *)
>- (qspecl_then [‘f’] assume_tac fVslfv_SUBSET_ffv >>
    irule SUBSET_TRANS >> qexists ‘fVslfv f’ >>
    rw[] (* 2 *)
    >- (simp[SUBSET_DEF,IN_fVslfv,PULL_EXISTS]  >> metis_tac[]) >>
    irule SUBSET_TRANS >> metis_tac[]) >>
irule SUBSET_TRANS >> qexists ‘ffv (fVinst fσ f)’ >> simp[] >>    
irule SUBSET_TRANS >> qexists ‘ofFMAP ffv fσ (fVars f)’ >>
rw[] (* 2 *)
>- (rw[SUBSET_DEF,ofFMAP_def,PULL_EXISTS] >> metis_tac[]) >>
irule ofFMAP_SUBSET_ffv_fVinst >>
rw[] >> Cases_on ‘fv’ >> metis_tac[wffVmap_no_vbound]
QED


Theorem Pf2Pf0_fVinsth_lemma:
∀uσ. wffsig Σf ∧ wff (Σf,Σp,Σe) f ∧
     uniqifn uσf (FDOM fσ ∪ FDOM uσ) ∧
     wffVmap (Σf,Σp,Σe) fσ ∧ fVars f ⊆ FDOM fσ ∧
     wfcfVmap (Σf,Σp,Σe) σ ∧ wfvmap Σf vσ ∧
     ffv f ∪ ffv (fVinst fσ f) ⊆ FDOM vσ
     ⇒
fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))) =
fVinst (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
       (finst vσ (ffVrn uσf f))
Proof
rw[] >>
‘wff (Σf,Σp,Σe) (fVinst fσ f)’
 by (irule wff_fVinst >> gs[wffsig_def]) >>
(* wff_subfm_fVar_LENGTH *) 
‘ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’
 by (irule ffVrn_fVinst >>
    rw[] >> irule wff_subfm_fVar_LENGTH >> metis_tac[]) >>
simp[] >>
‘wffVmap (Σf,Σp,Σe) (rn2fVmap uσ)’
 by cheat >>
‘fVinst (rn2fVmap uσ) (fVinst fσ f) =
 fVinst (o_fVmap (rn2fVmap uσ) fσ) f’
 by (irule fVar_prpl_o_fVmap >> rpt (first_x_assum $ irule_at Any)) >>
simp[] >>
‘uniqifn uσf (FDOM (o_fVmap (rn2fVmap uσ) fσ))’
  by simp[FDOM_o_fVmap,FDOM_rn2fVmap] (*can choose it to be*) >>
‘(fVinst (o_fVmap (rn2fVmap uσ) fσ) f) =
 (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) (ffVrn uσf f))’    
  by (irule $ GSYM fVinst_ffVrn >>
     simp[FDOM_o_fVmap] >> gs[SUBSET_DEF]) >> simp[] >>
‘finst vσ
             (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)
                (ffVrn uσf f)) =
 (instf
          (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf))
          vσ
          (ffVrn uσf f))’
 by (irule instf_fVinst >> simp[ffv_ffVrn] >>
    simp[FDOM_fVmap_fVrn,FDOM_o_fVmap,fVars_ffVrn,FDOM_rn2fVmap] >> rw[] (* 6 *)
    >- (gs[wfvmap_def] >>
       metis_tac[wfcod_no_bound,no_bound_def])
    >- metis_tac[wff_no_vbound]
    >- (gs[FDOM_o_fVmap,FDOM_rn2fVmap] >>
        rev_drule_all_then assume_tac uniqifn_alluniq0 >>
        gs[IMAGE_UNION])
    >- (gs[SUBSET_DEF] >> metis_tac[])
    >- (‘ffv (ffVrn uσ (fVinst fσ f)) ⊆ FDOM vσ’ suffices_by simp[] >>
       qpat_x_assum ‘ ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’ (K all_tac) >>
       gs[ffv_ffVrn]) >>
    irule_at Any wffVmap_fVmap_fVrn >>
    simp[FDOM_o_fVmap,FDOM_rn2fVmap] >>
    irule_at Any wffVmap_o_fVmap >>
    first_x_assum $ irule_at Any >> simp[]) >>
simp[] >> rw[instf_def] >>
irule fVar_prpl_o_fVmap1 >> gs[wfcfVmap_def] >>
simp[FDOM_vinst_fVmap,fVars_finst,PULL_EXISTS,FDOM_fVmap_fVrn,
    FDOM_o_fVmap,FDOM_rn2fVmap,fVars_ffVrn]  >>
‘∃Σe' Σf' Σg Σp'.
          (∀P sl x'.
             ((P,sl) = vinst_fVar vσ (fVrn uσf x') ∧ x' ∈ fVars f)  ⇒
             wff (Σf',Σp',Σe')
               (FALLL sl
                  (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) '
                   (vinst_fVar vσ (fVrn uσf x'))))) ∧ wffsig Σf' ∧
          wffVmap (Σf',Σg,Σe') σ’
  suffices_by metis_tac[] >>       
rpt (first_assum $ irule_at Any) >> qexists ‘Σp’ >> simp[] >>
‘wffVmap (Σf,Σp,Σe) (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)’
 by (irule wffVmap_fVmap_fVrn >> simp[FDOM_o_fVmap] >>
    irule wffVmap_o_fVmap >> simp[]) >> simp[] >>
rw[] >>
Cases_on ‘x'’ >>
‘(vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) '
              (vinst_fVar vσ (fVrn uσf (q,r)))) =
 finst vσ ((o_fVmap (rn2fVmap uσ) fσ) ' (q,r)) ’
by (irule FAPPLY_vinst_fVmap_fVmap_fVrn >>
   simp[FDOM_o_fVmap,FDOM_rn2fVmap] >> gs[uniqifn_def,SUBSET_DEF]) >>
simp[] >>
gs[fVrn_def,vinst_fVar_def] >>
‘(q,r) ∈ FDOM uσf’ by (gs[uniqifn_def,SUBSET_DEF] >> metis_tac[]) >>
gs[] >> gs[vinst_fVar_def] >>
‘(FALLL (MAP (sinst vσ) r)
             (finst vσ (o_fVmap (rn2fVmap uσ) fσ ' (q,r)))) =
 finst vσ (FALLL r (o_fVmap (rn2fVmap uσ) fσ ' (q,r)))’
 by simp[finst_FALLL] >>
 gs[] >>
irule wff_finst >>
gs[wffsig_def] >>
‘cstt vσ ∧ presname vσ ∧ wfcod Σf vσ’
 by metis_tac[wfvmap_def,wfvmap_presname] >> gs[] >>
‘wffVmap (Σf,Σp,Σe) (o_fVmap (rn2fVmap uσ) fσ)’
 by (irule wffVmap_o_fVmap >> simp[] >> gs[wffsig_def]) >>
drule_then assume_tac $ iffLR wffVmap_def >>
gs[FDOM_o_fVmap] >>
first_x_assum $ qspecl_then [‘q’,‘r’] assume_tac >>
reverse (rw[]) (* 2 *)
>- gs[SUBSET_DEF] >>
simp[ffv_FALLL] >>
‘(q,r) ∈ FDOM fσ’ by gs[SUBSET_DEF] >>
drule_then assume_tac FAPPLY_o_fVmap1 >>
simp[] >>
‘(fVinst (rn2fVmap uσ) (fσ ' (q,r))) = ffVrn uσ (fσ ' (q,r))’
by (irule $ GSYM ffVrn_fVinst >>
   rw[] >> irule $ GSYM wff_subfm_fVar_LENGTH >>
   qexists ‘P’ >>
   qpat_x_assum ‘wffVmap (Σf,Σp,Σe) fσ’ assume_tac >>
   gs[wffVmap_def] >>
   first_x_assum $ drule_then assume_tac >>
   first_x_assum $ irule_at Any >>
   metis_tac[fVar_FALLL_inc]) >>
simp[] >> simp[ffv_ffVrn] >>
rw[] (* 2 *)
>- (qspecl_then [‘f’] assume_tac fVslfv_SUBSET_ffv >>
    irule SUBSET_TRANS >> qexists ‘fVslfv f’ >>
    rw[] (* 2 *)
    >- (simp[SUBSET_DEF,IN_fVslfv,PULL_EXISTS]  >> metis_tac[]) >>
    irule SUBSET_TRANS >> metis_tac[]) >>
irule SUBSET_TRANS >> qexists ‘ffv (fVinst fσ f)’ >> simp[] >>    
irule SUBSET_TRANS >> qexists ‘ofFMAP ffv fσ (fVars f)’ >>
rw[] (* 2 *)
>- (rw[SUBSET_DEF,ofFMAP_def,PULL_EXISTS] >> metis_tac[]) >>
irule ofFMAP_SUBSET_ffv_fVinst >>
rw[] >> Cases_on ‘fv’ >> metis_tac[wffVmap_no_vbound]
QED
        



Theorem Pf2Pf0_fVinsth_lemma:
∀uσ. wffsig Σf ∧ wff (Σf,Σp,Σe) f ∧
     uniqifn uσf (FDOM fσ ∪ FDOM uσ) ∧
     wffVmap (Σf,Σp,Σe) fσ ∧ fVars f ⊆ FDOM fσ ∧
     wfcfVmap (Σf,Σp,Σe) σ ∧ wfvmap Σf vσ ∧
     ffv f ∪ ffv (fVinst fσ f) ⊆ FDOM vσ
     ⇒
fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))) =
fVinst (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
       (finst vσ (ffVrn uσf f))
Proof
rw[] >>
‘wff (Σf,Σp,Σe) (fVinst fσ f)’
 by (irule wff_fVinst >> gs[wffsig_def]) >>
(* wff_subfm_fVar_LENGTH *) 
‘ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’
 by (irule ffVrn_fVinst >>
    rw[] >> irule wff_subfm_fVar_LENGTH >> metis_tac[]) >>
simp[] >>
‘wffVmap (Σf,Σp,Σe) (rn2fVmap uσ)’
 by cheat >>
‘fVinst (rn2fVmap uσ) (fVinst fσ f) =
 fVinst (o_fVmap (rn2fVmap uσ) fσ) f’
 by (irule fVar_prpl_o_fVmap >> rpt (first_x_assum $ irule_at Any)) >>
simp[] >>
‘uniqifn uσf (FDOM (o_fVmap (rn2fVmap uσ) fσ))’
  by simp[FDOM_o_fVmap,FDOM_rn2fVmap] (*can choose it to be*) >>
‘(fVinst (o_fVmap (rn2fVmap uσ) fσ) f) =
 (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) (ffVrn uσf f))’    
  by (irule $ GSYM fVinst_ffVrn >>
     simp[FDOM_o_fVmap] >> gs[SUBSET_DEF]) >> simp[] >>
‘finst vσ
             (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)
                (ffVrn uσf f)) =
 (instf
          (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf))
          vσ
          (ffVrn uσf f))’
 by (irule instf_fVinst >> simp[ffv_ffVrn] >>
    simp[FDOM_fVmap_fVrn,FDOM_o_fVmap,fVars_ffVrn,FDOM_rn2fVmap] >> rw[] (* 6 *)
    >- (gs[wfvmap_def] >>
       metis_tac[wfcod_no_bound,no_bound_def])
    >- metis_tac[wff_no_vbound]
    >- (gs[FDOM_o_fVmap,FDOM_rn2fVmap] >>
        rev_drule_all_then assume_tac uniqifn_alluniq0 >>
        gs[IMAGE_UNION])
    >- (gs[SUBSET_DEF] >> metis_tac[])
    >- (‘ffv (ffVrn uσ (fVinst fσ f)) ⊆ FDOM vσ’ suffices_by simp[] >>
       qpat_x_assum ‘ ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’ (K all_tac) >>
       gs[ffv_ffVrn]) >>
    irule_at Any wffVmap_fVmap_fVrn >>
    simp[FDOM_o_fVmap,FDOM_rn2fVmap] >>
    irule_at Any wffVmap_o_fVmap >>
    first_x_assum $ irule_at Any >> simp[]) >>
simp[] >> rw[instf_def] >>
irule fVar_prpl_o_fVmap1 >> gs[wfcfVmap_def] >>
simp[FDOM_vinst_fVmap,fVars_finst,PULL_EXISTS,FDOM_fVmap_fVrn,
    FDOM_o_fVmap,FDOM_rn2fVmap,fVars_ffVrn]  >>
‘∃Σe' Σf' Σg Σp'.
          (∀P sl x'.
             ((P,sl) = vinst_fVar vσ (fVrn uσf x') ∧ x' ∈ fVars f)  ⇒
             wff (Σf',Σp',Σe')
               (FALLL sl
                  (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) '
                   (vinst_fVar vσ (fVrn uσf x'))))) ∧ wffsig Σf' ∧
          wffVmap (Σf',Σg,Σe') σ’
  suffices_by metis_tac[] >>       
rpt (first_assum $ irule_at Any) >> qexists ‘Σp’ >> simp[] >>
‘wffVmap (Σf,Σp,Σe) (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)’
 by (irule wffVmap_fVmap_fVrn >> simp[FDOM_o_fVmap] >>
    irule wffVmap_o_fVmap >> simp[]) >> simp[] >>
rw[] >>
Cases_on ‘x'’ >>
‘(vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) '
              (vinst_fVar vσ (fVrn uσf (q,r)))) =
 finst vσ ((o_fVmap (rn2fVmap uσ) fσ) ' (q,r)) ’
by (irule FAPPLY_vinst_fVmap_fVmap_fVrn >>
   simp[FDOM_o_fVmap,FDOM_rn2fVmap] >> gs[uniqifn_def,SUBSET_DEF]) >>
simp[] >>
gs[fVrn_def,vinst_fVar_def] >>
‘(q,r) ∈ FDOM uσf’ by (gs[uniqifn_def,SUBSET_DEF] >> metis_tac[]) >>
gs[] >> gs[vinst_fVar_def] >>
‘(FALLL (MAP (sinst vσ) r)
             (finst vσ (o_fVmap (rn2fVmap uσ) fσ ' (q,r)))) =
 finst vσ (FALLL r (o_fVmap (rn2fVmap uσ) fσ ' (q,r)))’
 by simp[finst_FALLL] >>
 gs[] >>
irule wff_finst >>
gs[wffsig_def] >>
‘cstt vσ ∧ presname vσ ∧ wfcod Σf vσ’
 by metis_tac[wfvmap_def,wfvmap_presname] >> gs[] >>
‘wffVmap (Σf,Σp,Σe) (o_fVmap (rn2fVmap uσ) fσ)’
 by (irule wffVmap_o_fVmap >> simp[] >> gs[wffsig_def]) >>
drule_then assume_tac $ iffLR wffVmap_def >>
gs[FDOM_o_fVmap] >>
first_x_assum $ qspecl_then [‘q’,‘r’] assume_tac >>
reverse (rw[]) (* 2 *)
>- gs[SUBSET_DEF] >>
simp[ffv_FALLL] >>
‘(q,r) ∈ FDOM fσ’ by gs[SUBSET_DEF] >>
drule_then assume_tac FAPPLY_o_fVmap1 >>
simp[] >>
‘(fVinst (rn2fVmap uσ) (fσ ' (q,r))) = ffVrn uσ (fσ ' (q,r))’
by (irule $ GSYM ffVrn_fVinst >>
   rw[] >> irule $ GSYM wff_subfm_fVar_LENGTH >>
   qexists ‘P’ >>
   qpat_x_assum ‘wffVmap (Σf,Σp,Σe) fσ’ assume_tac >>
   gs[wffVmap_def] >>
   first_x_assum $ drule_then assume_tac >>
   first_x_assum $ irule_at Any >>
   metis_tac[fVar_FALLL_inc]) >>
simp[] >> simp[ffv_ffVrn] >>
rw[] (* 2 *)
>- (qspecl_then [‘f’] assume_tac fVslfv_SUBSET_ffv >>
    irule SUBSET_TRANS >> qexists ‘fVslfv f’ >>
    rw[] (* 2 *)
    >- (simp[SUBSET_DEF,IN_fVslfv,PULL_EXISTS]  >> metis_tac[]) >>
    irule SUBSET_TRANS >> metis_tac[]) >>
irule SUBSET_TRANS >> qexists ‘ffv (fVinst fσ f)’ >> simp[] >>    
irule SUBSET_TRANS >> qexists ‘ofFMAP ffv fσ (fVars f)’ >>
rw[] (* 2 *)
>- (rw[SUBSET_DEF,ofFMAP_def,PULL_EXISTS] >> metis_tac[]) >>
irule ofFMAP_SUBSET_ffv_fVinst >>
rw[] >> Cases_on ‘fv’ >> metis_tac[wffVmap_no_vbound]
QED

(*        
Theorem Pf2Pf0_fVinsth_lemma:
∀uσ. wffsig Σf ∧ wff (Σf,Σp,Σe) f ∧
     uniqifn uσf (FDOM fσ ∪ FDOM uσ) ∧
     wffVmap (Σf,Σp,Σe) fσ ∧ fVars f ⊆ FDOM fσ ∧
     wfcfVmap (Σf,Σp,Σe) σ ∧ wfvmap Σf vσ ∧
     fVars (finst vσ (fVinst fσ f)) ⊆ FDOM σ ∧
     ffv f ∪ ffv (fVinst fσ f) ⊆ FDOM vσ
     ⇒
fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))) =
fVinst (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
       (finst vσ (ffVrn uσf f))
Proof
rw[] >>
‘wff (Σf,Σp,Σe) (fVinst fσ f)’
 by (irule wff_fVinst >> gs[wffsig_def]) >>
(* wff_subfm_fVar_LENGTH *) 
‘ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’
 by (irule ffVrn_fVinst >>
    rw[] >> irule wff_subfm_fVar_LENGTH >> metis_tac[]) >>
simp[] >>
‘wffVmap (Σf,Σp,Σe) (rn2fVmap uσ)’
 by cheat >>
‘fVinst (rn2fVmap uσ) (fVinst fσ f) =
 fVinst (o_fVmap (rn2fVmap uσ) fσ) f’
 by (irule fVar_prpl_o_fVmap >> rpt (first_x_assum $ irule_at Any)) >>
simp[] >>
‘uniqifn uσf (FDOM (o_fVmap (rn2fVmap uσ) fσ))’
  by simp[FDOM_o_fVmap,FDOM_rn2fVmap] (*can choose it to be*) >>
‘(fVinst (o_fVmap (rn2fVmap uσ) fσ) f) =
 (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) (ffVrn uσf f))’    
  by (irule $ GSYM fVinst_ffVrn >>
     simp[FDOM_o_fVmap] >> gs[SUBSET_DEF]) >> simp[] >>
‘finst vσ
             (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)
                (ffVrn uσf f)) =
 (instf
          (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf))
          vσ
          (ffVrn uσf f))’
 by (irule instf_fVinst >> simp[ffv_ffVrn] >>
    simp[FDOM_fVmap_fVrn,FDOM_o_fVmap,fVars_ffVrn,FDOM_rn2fVmap] >> rw[] (* 6 *)
    >- (gs[wfvmap_def] >>
       metis_tac[wfcod_no_bound,no_bound_def])
    >- metis_tac[wff_no_vbound]
    >- (gs[FDOM_o_fVmap,FDOM_rn2fVmap] >>
        rev_drule_all_then assume_tac uniqifn_alluniq0 >>
        gs[IMAGE_UNION])
    >- (gs[SUBSET_DEF] >> metis_tac[])
    >- (‘ffv (ffVrn uσ (fVinst fσ f)) ⊆ FDOM vσ’ suffices_by simp[] >>
       qpat_x_assum ‘ ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’ (K all_tac) >>
       gs[ffv_ffVrn]) >>
    irule_at Any wffVmap_fVmap_fVrn >>
    simp[FDOM_o_fVmap,FDOM_rn2fVmap] >>
    irule_at Any wffVmap_o_fVmap >>
    first_x_assum $ irule_at Any >> simp[]) >>
simp[] >> rw[instf_def] >>
irule fVar_prpl_o_fVmap1 >> gs[wfcfVmap_def] >>
simp[FDOM_vinst_fVmap,fVars_finst,PULL_EXISTS,FDOM_fVmap_fVrn,
    FDOM_o_fVmap,FDOM_rn2fVmap,fVars_ffVrn]  >>
‘∃Σe' Σf' Σg Σp'.
          (∀P sl x'.
             ((P,sl) = vinst_fVar vσ (fVrn uσf x') ∧ x' ∈ fVars f)  ⇒
             wff (Σf',Σp',Σe')
               (FALLL sl
                  (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) '
                   (vinst_fVar vσ (fVrn uσf x'))))) ∧ wffsig Σf' ∧
          wffVmap (Σf',Σg,Σe') σ’
  suffices_by metis_tac[] >>       
rpt (first_assum $ irule_at Any) >> qexists ‘Σp’ >> simp[] >>
‘wffVmap (Σf,Σp,Σe) (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)’
 by (irule wffVmap_fVmap_fVrn >> simp[FDOM_o_fVmap] >>
    irule wffVmap_o_fVmap >> simp[]) >> simp[] >>
rw[] >>
Cases_on ‘x'’ >>
‘(vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) '
              (vinst_fVar vσ (fVrn uσf (q,r)))) =
 finst vσ ((o_fVmap (rn2fVmap uσ) fσ) ' (q,r)) ’
by (irule FAPPLY_vinst_fVmap_fVmap_fVrn >>
   simp[FDOM_o_fVmap,FDOM_rn2fVmap] >> gs[uniqifn_def,SUBSET_DEF]) >>
simp[] >>
gs[fVrn_def,vinst_fVar_def] >>
‘(q,r) ∈ FDOM uσf’ by cheat >> gs[] >> gs[vinst_fVar_def] >>
‘(FALLL (MAP (sinst vσ) r)
             (finst vσ (o_fVmap (rn2fVmap uσ) fσ ' (q,r)))) =
 finst vσ (FALLL r (o_fVmap (rn2fVmap uσ) fσ ' (q,r)))’
 by simp[finst_FALLL] >>
 gs[] >>
irule wff_finst >>
gs[wffsig_def] >>
‘cstt vσ ∧ presname vσ ∧ wfcod Σf vσ’
 by metis_tac[wfvmap_def,wfvmap_presname] >> gs[] >>
‘wffVmap (Σf,Σp,Σe) (o_fVmap (rn2fVmap uσ) fσ)’
 by (irule wffVmap_o_fVmap >> simp[] >> gs[wffsig_def]) >>
drule_then assume_tac $ iffLR wffVmap_def >>
gs[FDOM_o_fVmap] >>
first_x_assum $ qspecl_then [‘q’,‘r’] assume_tac >>
reverse (rw[]) (* 2 *)
>- gs[SUBSET_DEF] >>
simp[ffv_FALLL] >>
‘(q,r) ∈ FDOM fσ’ by gs[SUBSET_DEF] >>
drule_then assume_tac FAPPLY_o_fVmap1 >>
simp[] >>
‘(fVinst (rn2fVmap uσ) (fσ ' (q,r))) = ffVrn uσ (fσ ' (q,r))’
by cheat (*ffVrn_fVinst*) >>
simp[] >> simp[ffv_ffVrn] >>
rw[] (* 2 *)
>- (qspecl_then [‘f’] assume_tac fVslfv_SUBSET_ffv >>
    irule SUBSET_TRANS >> qexists ‘fVslfv f’ >>
    rw[] (* 2 *)
    >- (simp[SUBSET_DEF,IN_fVslfv,PULL_EXISTS]  >> metis_tac[]) >>
    irule SUBSET_TRANS >> metis_tac[]) >>
irule SUBSET_TRANS >> qexists ‘ffv (fVinst fσ f)’ >> simp[] >>    
irule SUBSET_TRANS >> qexists ‘ofFMAP ffv fσ (fVars f)’ >>
rw[] (* 2 *)
>- (rw[SUBSET_DEF,ofFMAP_def,PULL_EXISTS] >> metis_tac[]) >>
irule ofFMAP_SUBSET_ffv_fVinst >>
rw[] >> Cases_on ‘fv’ >> metis_tac[wffVmap_no_vbound]
QED


        
Theorem Pf2Pf0_fVinsth_lemma:
∀uσ. wffsig Σf ∧ wff (Σf,Σp,Σe) f ∧
     uniqifn uσf (FDOM fσ ∪ FDOM uσ) ∧
     wffVmap (Σf,Σp,Σe) fσ ∧ fVars f ⊆ FDOM fσ ∧
     wfcfVmap (Σf,Σp,Σe) σ ∧ wfvmap Σf vσ ∧
     fVars (finst vσ (fVinst fσ f)) ⊆ FDOM σ ∧
     ffv f ∪ ffv (fVinst fσ f) ⊆ FDOM vσ ∧ uniqifn uσ (fVars (fVinst fσ th))
     ⇒
fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))) =
fVinst (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
       (finst vσ (ffVrn uσf f))
Proof
rw[] >>
‘wff (Σf,Σp,Σe) (fVinst fσ f)’
 by (irule wff_fVinst >> gs[wffsig_def]) >>
(* wff_subfm_fVar_LENGTH *) 
‘ffVrn uσ (fVinst fσ f) = fVinst (rn2fVmap uσ) (fVinst fσ f)’
 by (irule ffVrn_fVinst >>
    rw[] >> irule wff_subfm_fVar_LENGTH >> metis_tac[]) >>
simp[] >>
‘wffVmap (Σf,Σp,Σe) (rn2fVmap uσ)’
 by cheat >>
‘fVinst (rn2fVmap uσ) (fVinst fσ f) =
 fVinst (o_fVmap (rn2fVmap uσ) fσ) f’
 by (irule fVar_prpl_o_fVmap >> rpt (first_x_assum $ irule_at Any)) >>
simp[] >>
‘uniqifn uσf (FDOM (o_fVmap (rn2fVmap uσ) fσ))’
  by simp[FDOM_o_fVmap,FDOM_rn2fVmap] (*can choose it to be*) >>
‘(fVinst (o_fVmap (rn2fVmap uσ) fσ) f) =
 (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) (ffVrn uσf f))’    
  by (irule $ GSYM fVinst_ffVrn >>
     simp[FDOM_o_fVmap] >> gs[SUBSET_DEF]) >> simp[] >>
‘finst vσ
             (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)
                (ffVrn uσf f)) =
 (instf
          (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf))
          vσ
          (ffVrn uσf f))’
 by (irule instf_fVinst >> simp[ffv_ffVrn] >>
    simp[FDOM_fVmap_fVrn,FDOM_o_fVmap,fVars_ffVrn,FDOM_rn2fVmap] >> rw[] (* 6 *)
    >- (gs[wfvmap_def] >>
       metis_tac[wfcod_no_bound,no_bound_def])
    >- metis_tac[wff_no_vbound]
    >- (gs[FDOM_o_fVmap,FDOM_rn2fVmap] >>
        rev_drule_all_then assume_tac uniqifn_alluniq0 >>
        gs[IMAGE_UNION])
    >- (gs[SUBSET_DEF] >> metis_tac[])
    >- (* gs[ffv_fVinst]  *) cheat >>
    irule_at Any wffVmap_fVmap_fVrn >>
    simp[FDOM_o_fVmap,FDOM_rn2fVmap] >>
    irule_at Any wffVmap_o_fVmap >>
    first_x_assum $ irule_at Any >> simp[]) >>
simp[] >> rw[instf_def] >>
irule fVar_prpl_o_fVmap >> gs[wfcfVmap_def] >>
rpt (first_assum $ irule_at Any) >>
irule wffVmap_vinst_fVmap >> simp[] >>
simp[FDOM_fVmap_fVrn,FDOM_o_fVmap,FDOM_rn2fVmap] >>
‘wffVmap (Σf,Σp,Σe) (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)’
 by (irule wffVmap_fVmap_fVrn >> simp[FDOM_o_fVmap] >>
    irule wffVmap_o_fVmap >> simp[]) >> simp[] >> 
(*‘BIGUNION
          {ffv (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf ' (P,sl)) ∪ slfv sl |
           (P,sl) |
           (P,sl) ∈ FDOM (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)} ⊆
        FDOM vσ’
 by simp[FDOM_o_fVmap,FDOM_rn2fVmap,FDOM_fVmap_fVrn] >>
    (* restrict fσ to fVars, uσ to (fVars (fVinst fσ th)),
        then as ffv f ⊆ FDOM vσ
    8.  ffv (fVinst fσ f) ⊆ FDOM vσ, should fine
       uniqifn uσ (fVars (fVinst fσ th))*)
*)
cheat
QED
*)

first_x_assum
‘(fVinst
          (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf))
          (finst vσ (ffVrn uσf f))
          ) = ’    

fVinst σ (finst vσ (ffVrn uσ (fVinst fσ f))) =
fVinst σ (finst vσ (fVinst (o_fVmap (rn2fVmap uσ) fσ) f)) =
fVinst σ (finst vσ
  (fVinst (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) (ffVrn uσf f))) =
(*FDOM (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf) all unique,since it is fVars in (ffVrn uσf f), already uniquenified *)
fVinst σ (instf
          (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf))
          vσ
          (ffVrn uσf f)) =
fVinst σ (fVinst
          (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf))
          (finst vσ (ffVrn uσf f))
          ) =
fVinst (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
       (finst vσ (ffVrn uσf f))


        

Definition fVrnwinst_def:
fVrwinst vσ uσ1 hσ uσ2 =
FUN_FMAP
(λ(P,sl).
  uσ1 '
      (vinst_fVar vσ (CHOICE
       {(P0,sl0) |
        (P,sl) =
        vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P0,sl0)) ∧
        (P0,sl0) ∈ FDOM uσ2})))
(IMAGE ((vinst_fVar (o_vmap hσ vσ)) o (fVrn uσ2)) (FDOM uσ2))
End


Theorem FDOM_fVrnwinst:
FDOM (fVrwinst vσ uσ1 hσ uσ2) =
(IMAGE ((vinst_fVar (o_vmap hσ vσ)) o (fVrn uσ2)) (FDOM uσ2))
Proof
rw[fVrnwinst_def,FUN_FMAP_DEF]
QED

Theorem FAPPLY_fVrnwinst:
uniqifn uσ2 (FDOM uσ2) ∧ (P:string,sl) ∈ FDOM uσ2 ⇒
fVrwinst vσ uσ1 hσ uσ2 '
         (vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P,sl))) =
uσ1 ' (vinst_fVar vσ (P,sl))
Proof
rw[] >> rw[fVrnwinst_def] >>
qspecl_then [‘ (λ(P,sl).
               uσ1 '
               (vinst_fVar vσ
                  (CHOICE
                     {(P0,sl0) |
                      (P,sl) = vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P0,sl0)) ∧
                      (P0,sl0) ∈ FDOM uσ2})))’,
              ‘(IMAGE (vinst_fVar (o_vmap hσ vσ) ∘ fVrn uσ2) (FDOM uσ2))’,‘(vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P,sl)))’]
 assume_tac (SRULE [PULL_FORALL] FUN_FMAP_DEF) >>
 gs[PULL_EXISTS] >>
 first_x_assum $ qspecl_then [‘(P,sl)’] assume_tac >>
 gs[] >>
 Cases_on ‘(vinst_fVar (o_vmap hσ vσ) (fVrn uσ2 (P,sl)))’ >>
 rw[] >>
 gs[fVrn_def] >> gs[vinst_fVar_def] >>
 ‘{(P0,sl0) |
               (q,r) =
               vinst_fVar (o_vmap hσ vσ)
                 (if (P0,sl0) ∈ FDOM uσ2 then (uσ2 ' (P0,sl0),sl0)
                  else (P0,sl0)) ∧ (P0,sl0) ∈ FDOM uσ2} =
 {(P,sl)}’
  by (rw[Once EXTENSION,EQ_IMP_THM] (* 2 *)
     >- (gs[] >> gs[vinst_fVar_def] >>
        gs[uniqifn_def] >> metis_tac[]) >>
     simp[vinst_fVar_def]) >>
gs[vinst_fVar_def]
QED
        

Theorem Pf2Pf0_vinst_lemma:
∀f. uniqifn uσ2 (FDOM uσ2) ∧ fVars f ⊆ FDOM uσ2 ∧
    IMAGE (vinst_fVar vσ) (fVars f) ⊆ FDOM uσ1 ∧
    ffv f ⊆ FDOM vσ ∧ ffv (finst vσ f) ⊆ FDOM hσ  ⇒
    finst hσ (ffVrn uσ1 (finst vσ f)) =
    ffVrn (fVrwinst vσ uσ1 hσ uσ2) (finst (o_vmap hσ vσ) (ffVrn uσ2 f))
Proof
Induct_on ‘f’ >>
gs[fVars_def,finst_def,ffVrn_def,MAP_MAP_o,MAP_EQ_f] (* 3 *)
>- (rw[] >> irule $ cj 1 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[])
>- (rw[] >> irule $ cj 2 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[]) >>
rw[] >> gs[FDOM_fVrnwinst,MAP_MAP_o,MAP_EQ_f] (* 12 *)
>- (rw[GSYM vinst_fVar_def] >> Cases_on ‘x’ >>
   ‘(q,r) = (s,l)’
     by (gs[vinst_fVar_def,fVrn_def,uniqifn_def] >>
     metis_tac[]) >> gs[] >>     
   irule $ GSYM FAPPLY_fVrnwinst >> simp[])
>- (rw[] >> irule $ cj 2 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[]) 
>- (rw[] >> irule $ cj 1 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[])
>- (first_x_assum $ qspecl_then [‘(s,l)’] assume_tac >>
   gs[vinst_fVar_def,fVrn_def])
>- (rw[] >> irule $ cj 2 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[]) 
>- (rw[] >> irule $ cj 1 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[]) 
>- gs[vinst_fVar_def]
>- (rw[] >> irule $ cj 2 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[]) 
>- (rw[] >> irule $ cj 1 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[]) 
>- (first_x_assum $ qspecl_then [‘(s,l)’] assume_tac >>
   gs[vinst_fVar_def,fVrn_def])
>- (rw[] >> irule $ cj 2 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[])  >>
(rw[] >> irule $ cj 1 inst_o_vmap >>
   gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[])
QED   

        
fVinst fσ (finst vσ (ffVrn uσ (finst σ f))) =
(* fVinst_ffVrn *)
fVinst fσ (finst vσ (ffVrn uσ (finst σ f)))



       
(*ffVrn_fVinst*)
fVinst fσ (finst vσ (fVinst (rn2fVmap uσ) (finst σ f))) =
(*instf_fVinst*)
fVinst fσ (instf (vinst_fVmap vσ (rn2fVmap uσ)) (finst σ f))=


        
fVinst fσ (finst vσ (instf (rn2fVmap uσ) σ f)) =

ffVrn_fVinst

        
       (rn2fVmap uσ)
fVinst (o_fVmap σ (vinst_fVmap vσ (fVmap_fVrn (o_fVmap (rn2fVmap uσ) fσ) uσf)))
       (finst vσ (ffVrn uσf f))        
      
(*        
  
Definition ext_fVmap_def:
ext_fVmap  

Definition fVar_eff_on_def:
fVar_eff σ (P,sl) = if (P,sl) ∈ FDOM σ then σ ' (P,sl) else fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
End
*)


Definition sl2vl:
sl2vl [] [] = [] ∧
sl2vl (n :: nl) (s :: sl) =
(n,s) :: sl2vl nl (specsl 0 (Var n s) sl)
End


(*redefine using inductive relation?*)        

Theorem wfabsap_CONS:
  wfabsap Σ sl tl ⇒
  ∀n s. (∀st n0 s0. MEM st sl ∧ (n0,s0) ∈ sfv s0 ⇒ (n,s) ∉ sfv s0) ∧
  
Theorem wfabsap_sl2vl:
∀tl sl.
wfabsap Σ sl tl ⇒
wfabsap Σ sl (MAP Var' (sl2vl [] sl)) ∧
∃σ. tl = MAP (tinst σ) (MAP Var' (sl2vl [] sl))
Proof
Induct_on ‘tl’ >- cheat >>
Cases_on ‘sl’ >- cheat >> gs[wfabsap_def] >> rw[] >>
first_x_assum $ drule_all_then assume_tac >> gs[] >>


        
Theorem wfabsap_sl2vl:
wfabsap sl tl ⇒ ∀nl. LENGTH nl = LENGTH sl ⇒
(∀n s. MEM (n,s) sl2vl ⇒
Proof

Theorem absvl_okabs:
∀l i. ok_abs

Theorem specsl_absvl:
∀vl i h.
 (∀m1 m2. m1 < m2 ∧ m2 < LENGTH vl ⇒
          ∀n s. (n, s) ∈ sfv (SND (EL m2 vl)) ⇒
              EL m1 vl ∉ sfv s) ∧
 (∀v n s. (MEM v vl ∨ v = h) ∧ (n,s) ∈ sfv (SND v) ⇒ sbounds s = {}) ∧
 (∀v sv. MEM v vl ∧ sv ∈ sfv (SND v) ⇒ h ∉ sfv (SND sv)) ∧
 ok_abs  ⇒
 (specsl i (Var' h) (MAP SND (absvl i h vl))) = MAP SND vl
Proof
Induct_on ‘vl’ >> gs[absvl_def,specsl_def] >>
rw[] >> Cases_on ‘h’ >> rw[absvl_def] >>
Cases_on ‘h'’ >> rw[specsl_def]
>- (qspecl_then [‘r’,‘i’,‘Var q' r'’,‘q'’,‘r'’] assume_tac
   (cj 2 trpl_tabs) >>
   ‘srpl i (Var q' r') (sabs (q',r') i r) =
    ssubst (q',r') (Var q' r') r’
    by (first_x_assum irule >> rw[] (* 3 *)
       >- (first_x_assum $ qspecl_then [‘(q,r)’,‘(n1,s1)’]
          assume_tac >> gs[])
       >- (first_x_assum irule >>
          qexistsl [‘n’,‘(q,r)’] >> simp[]) >>
       


(gs[] >> irule $ cj 2 wft_no_vbound >>
          first_x_assum $ irule_at Any >>
          last_x_assum $ qspecl_then [‘(q,r)’] assume_tac>>
          gs[] >> metis_tac[]) >>
       gs[] >>
       last_x_assum $ qspecl_then [‘(q,r)’] assume_tac>>
       gs[] >> metis_tac[wft_no_bound,MEMBER_NOT_EMPTY]) >>
    gs[] >> cheat) >>
first_x_assum $ qspecl_then [‘i+1’,‘(q',r')’] assume_tac >>
gs[] >> first_x_assum irule >> rw[] >>
first_x_assum $ qspecl_then [‘SUC m1’,‘SUC m2’] assume_tac >>
gs[] >> metis_tac[]
QED

        
Theorem specsl_absvl:
∀vl i h.
 (∀m1 m2. m1 < m2 ∧ m2 < LENGTH vl ⇒
          ∀n s. (n, s) ∈ sfv (SND (EL m2 vl)) ⇒
              EL m1 vl ∉ sfv s) ∧
 (∀v n s. (MEM v vl ∨ v = h) ∧ (n,s) ∈ sfv (SND v) ⇒ sbounds s = {})) ∧
 (∀v sv. MEM v vl ∧ sv ∈ sfv (SND v) ⇒ h ∉ sfv (SND sv)) ⇒
 (specsl i (Var' h) (MAP SND (absvl i h vl))) = MAP SND vl
Proof
Induct_on ‘vl’ >> gs[absvl_def,specsl_def] >>
rw[] >> Cases_on ‘h’ >> rw[absvl_def] >>
Cases_on ‘h'’ >> rw[specsl_def]
>- (qspecl_then [‘r’,‘i’,‘Var q' r'’,‘q'’,‘r'’] assume_tac
   (cj 2 trpl_tabs) >>
   ‘srpl i (Var q' r') (sabs (q',r') i r) =
    ssubst (q',r') (Var q' r') r’
    by (first_x_assum irule >> rw[] (* 3 *)
       >- (first_x_assum $ qspecl_then [‘(q,r)’,‘(n1,s1)’]
          assume_tac >> gs[])
       >- (gs[] >> irule $ cj 2 wft_no_vbound >>
          first_x_assum $ irule_at Any >>
          last_x_assum $ qspecl_then [‘(q,r)’] assume_tac>>
          gs[] >> metis_tac[]) >>
       gs[] >>
       last_x_assum $ qspecl_then [‘(q,r)’] assume_tac>>
       gs[] >> metis_tac[wft_no_bound,MEMBER_NOT_EMPTY]) >>
    gs[] >> cheat) >>
first_x_assum $ qspecl_then [‘i+1’,‘(q',r')’] assume_tac >>
gs[] >> first_x_assum irule >> rw[] >>
first_x_assum $ qspecl_then [‘SUC m1’,‘SUC m2’] assume_tac >>
gs[] >> metis_tac[]
QED

Theorem wfabsap_vl2sl:
 ∀vl. (∀m1 m2. m1 < m2 ∧ m2 < LENGTH vl ⇒
          ∀n s. n s ∈ sfv (SND (EL m2 vl)) ⇒
              EL m1 vl ∉ sfv s) ⇒
 wfabsap Σ (vl2sl vl) (MAP Var' vl)
Proof
 Induct_on ‘vl’ >> gs[wfabsap_def,vl2sl_def,vl2sl0_def] >>
 reverse (rw[])
 >- ‘(specsl 0 (Var' h) (MAP SND (absvl 0 h (vl2sl0 vl)))) =
     (MAP SND (vl2sl0 vl))’
     by irule specsl_absvl >> 
              
              

        

EVAL “vl2sl [("A",St "set" []);("B",St "set" []);
 ("f",St "fun" [Var "A" (St "set" []); Var "B" (St "set" [])])]”        
            
fun absvl i v [] = []
  | absvl i v ((n:string,s) :: t) = 
    (n,substs (v,Bound i) s) :: (absvl (i+1) v t)

fun vl2sl0 [] = []
  | vl2sl0 (v :: vs) = v :: absvl 0 v (vl2sl0 vs)

fun vl2sl vl = List.map #2 (vl2sl0 vl)


(*fresh name list*)    

         

Theorem wfabsap_alt:
∀n tl sl.
LENGTH tl = n ⇒ 
(wfabsap Σ sl tl ⇔
  let nl = 
  vl = sl2vl (REPLICATE (LENGTH sl) "") sl
  σ = TO_FMAP (ZIP )
  in wfabsap Σ sl (MAP Var' vl) ∧
     tl = MAP (tinst σ) (MAP Var' vl))
Proof
Induct_on ‘n’ >- cheat >>
reverse (Cases_on ‘sl’ >> Cases_on ‘tl’ ) >>
rw[wfabsap_def] >> rw[MAP_MAP_o,sl2vl,wfabsap_def] >- cheat >>
simp[sort_of_def]>>
Cases_on ‘wfs Σ h’ >> simp[] >> simp[LENGTH_specsl] >>
Cases_on ‘        (∀n0 s0 st. MEM st t ∧ (n0,s0) ∈ sfv st ⇒ sbounds s0 = ∅)’ >>
simp[] >>
‘ 
        wft Σ h' ∧ h = sort_of h' ∧
        wfabsap Σ (specsl 0 h' t)
          (MAP Var' (sl2vl (REPLICATE (LENGTH t) "") (specsl 0 h' t))) ∧
        t' =
        MAP (tinst σ ∘ Var')
          (sl2vl (REPLICATE (LENGTH t) "") (specsl 0 h' t)) ⇔
        (
         wft Σ (Var "" h) ∧
         wfabsap Σ (specsl 0 (Var "" h) t)
           (MAP Var'
              (sl2vl (REPLICATE (LENGTH t) "") (specsl 0 (Var "" h) t)))) ∧
        h' = σ ' ("",h) ∧
        t' =
        MAP (tinst σ ∘ Var')
          (sl2vl (REPLICATE (LENGTH t) "") (specsl 0 (Var "" h) t))’
suffices_by metis_tac[] >>
simp[wft_def] >> 

Induct_on ‘tl’ >- cheat >>
Cases_on ‘sl’ >- cheat >>
rw[wfabsap_def,MAP_MAP_o,sl2vl] >- cheat >>


             
                  
val _ = export_theory();

