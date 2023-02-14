open HolKernel Parse boolLib bossLib;

val _ = new_theory "Pf";


    

(*is concrete*)    
Definition is_cfm_def:
is_cfm False = T ∧
(is_cfm (IMP f1 f2) = (is_cfm f1 ∧ is_cfm f2)) ∧
is_cfm (fVar _ _ _) = F ∧
is_cfm (Pred _ _) = T ∧
is_cfm (FALL s b) = is_cfm b
End

Definition wffVmap_def:
  wffVmap Σ ε ⇔
  ∀P:string sl. (P,sl) ∈ FDOM ε ⇒
  (∀P1 sl1 tl1. fVar P1 sl1 tl1 ∈ subfm (ε ' (P,sl)) ⇒
  ok_abs sl1) ∧ wff Σ (FALLL sl (ε ' (P,sl))) 
End   

(*concrete fVmap *)      
Definition cfVmap_def:
 cfVmap σ ⇔
 ∀P sl. (P,sl) ∈ FDOM σ ⇒ is_cfm (σ ' (P,sl))
End 

Definition insts_of_def:
insts_of Σ f = {fVar_prpl ε f| ε | wffVmap Σ ε}
End


Definition fVar_prpl_def:
fVar_prpl ε False = False ∧
fVar_prpl ε (Pred p tl) = Pred p tl ∧
fVar_prpl ε (IMP f1 f2) = IMP (fVar_prpl ε f1)
                              (fVar_prpl ε f2) ∧
fVar_prpl ε (FALL s ϕ) = FALL s (fVar_prpl ε ϕ) ∧
fVar_prpl ε (fVar P sl tl) =
if (P,sl) ∈ FDOM ε ∧ ok_abs sl then
  fprpl (mk_bmap (REVERSE tl)) (ε ' (P,sl))
else fVar P sl tl
End


Definition fVar_thprpl_def:
  fVar_thprpl ε (ct,asm,f) =
  (ct ∪ (BIGUNION {ffv (ε ' fv) | (fv,f0) | (f0 ∈ asm ∨ f0 = f) ∧ fv ∈ freefVars f0 ∩ FDOM ε}) ,
  IMAGE (fVar_subst_def ε) asm,fVar_prpl ε f)
End

Definition Uof_def:
  Uof f s = BIGUNION {f e | e ∈ s}
End  


Definition thfVar_def:
thfVar (ct,asm,f) = Uof fVars ({f} ∪ asm)
End

     
Definition fVar_thprpl_def:
  fVar_thprpl σf (ct,asm,f) =
  (ct ∪ ofFMAP ffv σf (Uof fVars ({f} ∪ asm)), 
  IMAGE (fVar_prpl σf) asm,fVar_prpl σf f)
End        
      

        
Definition thinsts_of_def:
  thinsts_of th =
   {fVar_thprpl ε (tinst_thm σ th) | T }
End              

               
Definition EQ_def:
EQ t1 t2 = Pred "=" [t1;t2]
End 



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
  EX n s b = NEG (FALL s (NEG b))
End      


    
Definition fsstt_def:
  fsstt old new False = False ∧
  fsstt old new (Pred p tl) =
  Pred p (MAP (tsstt old new) tl) ∧
  fsstt old new (fVar p sl tl) =
  fVar p (MAP (ssstt old new) sl) (MAP (tsstt old new) tl) ∧
  fsstt old new (IMP f1 f2) =
  IMP (fsstt old new f1) (fsstt old new f2) ∧
  fsstt old new (FALL s b) =
  FALL (ssstt old new s) (fsstt old new b)
End

Definition specf_def:
  specf t (FALL s b) = substb t b
End


Definition spec_def:
  spec t (Γ,A,FALL s b) = (Γ ∪ tfv t,A,specf t (FALL s b))
End


Definition gen_def:
genth (n,s) (Γ,A,f) = (Γ DELETE (n,s),A,mk_FALL n s f)
End

Definition assume_def:
  assume f = (ffv f,{f},f)
End

Definition refl_def:
refl t = (tfv t,{},EQ t t)
End
        
Definition fvinst_def:
fvinst σf σv f = fVar_prpl σf (finst σv f)
End

        

        
          
Inductive Pf0:
[~AX:]
(∀ax. ax ∈ axs ⇒
      Pf0 Σ axs [(ffv ax,{},ax)]) ∧
[~FalseE1:]
  (∀Γ A pf f.
      Pf0 Σ axs pf ∧
      MEM (Γ,A ∪ {NEG f},False) pf ⇒
      Pf0 Σ axs (pf ++ [(Γ,A,f)])) ∧
[~FalseE2:]
  (∀Γ A pf f.
    Pf0 Σ axs pf ∧ wff Σ f ∧ is_cfm f ∧
    MEM (Γ,A,False) pf ⇒
    Pf0 Σ axs (pf ++ [(Γ ∪ ffv f,A,f)])) ∧
[~assume:]
  (∀c:form. wff Σ c ∧ is_cfm f ⇒
            Pf0 Σ axs [(ffv c,{c},c)]) ∧
[~mp:]
  (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
     Pf0 Σ axs pf1 ∧ Pf0 Σ axs pf2 ∧
     MEM (Γ1,A1,IMP f1 f2) pf1 ∧
     MEM (Γ2,A2,f1) pf2 ⇒
     Pf0 Σ axs (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2, A1 ∪ A2,f2)])) ∧
[~disch:]
  (∀Γ A pf f a.
     Pf0 Σ axs pf ∧ MEM (Γ,A,f) pf ∧
     wff Σ a ∧ is_cfm a ⇒
     Pf0 Σ axs (pf ++ [(Γ ∪ ffv a,A DELETE a,IMP a f)])) ∧
[~ALLI:]
  (∀Γ A pf f x s.
     Pf0 Σ axs pf ∧ 
     MEM (Γ,A,f) pf ∧
     wfs (FST Σ) s ∧ (sfv s) ⊆ Γ ∧
     (∀n0 s0. (n0,s0) ∈ Γ ⇒ (x,s) ∉ sfv s0) ∧
     wff Σ a ∧
     (∀a. a ∈ A ⇒ (x,s) ∉ ffv a) ⇒
     Pf0 Σ axs (pf ++ [(Γ DELETE (x,s),A,mk_FALL x s f)])) ∧
[~ALLE:]
  (∀Γ A pf s f t.
     Pf0 Σ axs pf ∧
     MEM (Γ,A,FALL s f) pf ∧
     wft (FST Σ) t ∧ sort_of t = s ⇒
     Pf0 Σ axs (pf ++ [(Γ ∪ tfv t,A,substb t f)])) ∧
[~refl:]
  (∀t.
     wft (FST Σ) t ⇒
     Pf0 Σ axs [(tfv t,{},EQ t t)]) ∧
[~sym:]
  (∀Γ A pf t1 t2.
     Pf0 Σ axs pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
     Pf0 Σ axs (pf ++ [(Γ,A,EQ t2 t1)])) ∧
[~trans:]
  (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
     Pf0 Σ axs pf1 ∧ Pf0 Σ axs pf2 ∧
     MEM (Γ1,A1,EQ t1 t2) pf1 ∧ MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
     Pf0 Σ axs (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
[~cong:]
  (Pf0 Σ axs pf ∧
   MEM (Γ,A,EQ t1 t2) pf ∧ wff Σ f ∧ is_cfm f ∧   
   (∀n s. (n,s) ∈ ffv f ⇒ t1 ∉ ssubtm s) ⇒
   Pf0 Σ axs (pf ++ [(Γ,A,IFF f (fsstt t1 t2 f))])
   )
End



Inductive Pf:
[~AX:]
(∀ax. ax ∈ axs ⇒
      Pf Σ axs [(ffv ax,{},ax)]) ∧
[~FalseE1:]
  (∀Γ A pf f.
      Pf Σ axs pf ∧
      MEM (Γ,A ∪ {NEG f},False) pf ⇒
      Pf Σ axs (pf ++ [(Γ,A,f)])) ∧
[~FalseE2:]
  (∀Γ A pf f.
    Pf Σ axs pf ∧ wff Σ f ∧
    MEM (Γ,A,False) pf ⇒
    Pf Σ axs (pf ++ [(Γ ∪ ffv f,A,f)])) ∧
[~assume:]
  (∀c:form. wff Σ c ⇒ Pf Σ axs [(ffv c,{c},c)]) ∧
[~mp:]
  (∀Γ1 Γ2 A1 A2 pf1 f1 pf2 f2.
     Pf Σ axs pf1 ∧ Pf Σ axs pf2 ∧
     MEM (Γ1,A1,IMP f1 f2) pf1 ∧
     MEM (Γ2,A2,f1) pf2 ⇒
     Pf Σ axs (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2, A1 ∪ A2,f2)])) ∧
[~disch:]
  (∀Γ A pf f a.
     Pf Σ axs pf ∧ MEM (Γ,A,f) pf ∧ wff Σ a ⇒
     Pf Σ axs (pf ++ [(Γ ∪ ffv a,A DELETE a,IMP a f)])) ∧
[~ALLI:]
  (∀Γ A pf f x s.
     Pf Σ axs pf ∧ 
     MEM (Γ,A,f) pf ∧
     wfs (FST Σ) s ∧ (sfv s) ⊆ Γ ∧
     (∀n0 s0. (n0,s0) ∈ Γ ⇒ (x,s) ∉ sfv s0) ∧
     wff Σ a ∧
     (∀a. a ∈ A ⇒ (x,s) ∉ ffv a) ⇒
     Pf Σ axs (pf ++ [(Γ DELETE (x,s),A,mk_FALL x s f)])) ∧
[~ALLE:]
  (∀Γ A pf s f t.
     Pf Σ axs pf ∧
     MEM (Γ,A,FALL s f) pf ∧
     wft (FST Σ) t ∧ sort_of t = s ⇒
     Pf Σ axs (pf ++ [(Γ ∪ tfv t,A,substb t f)])) ∧
[~refl:]
  (∀t.
     wft (FST Σ) t ⇒
     Pf Σ axs [(tfv t,{},EQ t t)]) ∧
[~sym:]
  (∀Γ A pf t1 t2.
     Pf Σ axs pf ∧ MEM (Γ,A,EQ t1 t2) pf ⇒
     Pf Σ axs (pf ++ [(Γ,A,EQ t2 t1)])) ∧
[~trans:]
  (∀Γ1 Γ2 A1 A2 pf1 pf2 t1 t2 t3.
     Pf Σ axs pf1 ∧ Pf Σ axs pf2 ∧
     MEM (Γ1,A1,EQ t1 t2) pf1 ∧ MEM (Γ2,A2,EQ t2 t3) pf2 ⇒
     Pf Σ axs (pf1 ++ pf2 ++ [(Γ1 ∪ Γ2,A1 ∪ A2,EQ t1 t3)])) ∧
[~fVar_prpl:]
  (∀Γ A f pf σ.
     Pf Σ axs pf ∧ wffVmap Σ σ ∧
     MEM (Γ,A,f) pf ∧ wff Σ f ⇒
     Pf Σ axs
        (pf ++ [fVar_thprpl Σ σ (Γ,A,f)])) ∧
[~inst_thm:]
 (Pf Σ axs pf ∧ cstt σ ∧ wfcod (FST Σ) σ ∧
  MEM (Γ,A,f) pf ⇒
  Pf Σ axs
     (pf ++ [(inst_cont σ Γ,IMAGE (finst σ) A,finst σ f)])
  )
End


Definition ofFMAP_def:
ofFMAP f fmap s = BIGUNION {f (fmap ' a) | a ∈ FDOM fmap ∩ s}
End
        

    


Theorem fbounds_FALLL:
∀sl b.
fbounds (FALLL sl b) = slbounds sl ∪
IMAGE (λi. i - LENGTH sl) (fbounds b DIFF (count (LENGTH sl)))
Proof
Induct_on ‘sl’ >>
simp[fbounds_def,FALLL_def,slbounds_def] >>
rw[] >> rw[GSYM UNION_ASSOC] >>
‘ IMAGE PRE
          (slbounds sl ∪
           IMAGE (λi. i − LENGTH sl) (fbounds b DIFF count (LENGTH sl)) DELETE
           0) =
        IMAGE PRE (slbounds sl DELETE 0) ∪
        IMAGE (λi. i − SUC (LENGTH sl))
          (fbounds b DIFF count (SUC (LENGTH sl)))’
 suffices_by metis_tac[] >>
‘ (λi. i − SUC (LENGTH sl)) =  PRE o (λi. i − (LENGTH sl))’
  by simp[FUN_EQ_THM] >>
simp[] >> simp[IMAGE_COMPOSE] >>
rw[Once $ GSYM IMAGE_UNION,Excl "IMAGE_UNION"] >>
AP_TERM_TAC >>
‘count (SUC (LENGTH sl)) = count (LENGTH sl) ∪
 {LENGTH sl}’
 by rw[count_def,EXTENSION] >>
simp[] >> simp[DIFF_UNION] >>  
‘0 ∉  IMAGE (λi. i − LENGTH sl)
          (fbounds b DIFF count (LENGTH sl) DIFF {LENGTH sl}) DELETE 0’
 by simp[] >>
 ‘slbounds sl DELETE 0 ∪
        IMAGE (λi. i − LENGTH sl)
          (fbounds b DIFF count (LENGTH sl) DIFF {LENGTH sl})
    =
  (slbounds sl ∪
        IMAGE (λi. i − LENGTH sl)
          (fbounds b DIFF count (LENGTH sl) DIFF {LENGTH sl})) DELETE 0
   ’
   by (rw[EXTENSION,EQ_IMP_THM]
      >- metis_tac[]
      >- metis_tac[]
      >- (gs[] >> disj2_tac >> qexists ‘i’ >>
         simp[]) >>
      simp[]) >>
simp[] >>
rw[Once EXTENSION,EQ_IMP_THM] (* 4 *)
>- metis_tac[] 
>- (disj2_tac >> qexists ‘i’ >> simp[] >>
   simp[])
>- simp[]   
>> disj2_tac >> qexists ‘i’ >> simp[]
QED
   
Theorem wff_FALLL_ok_abs:
wff Σ (FALLL sl b) ⇒ ok_abs sl
Proof
rw[ok_abs_def] >>
drule_then assume_tac wff_fbounds >>
gs[fbounds_FALLL] >>
gs[Once EXTENSION] >> gs[IN_slbounds] >>
rw[SUBSET_DEF] >>
CCONTR_TAC >>
‘n ≤ x’ by simp[] >>
‘∃a. x = a + n’ by (qexists ‘x - n’ >>  simp[]) >>
first_x_assum (qspecl_then [‘a’,‘n’] assume_tac) >>
gs[]
QED
        
                 
        
Definition ffVar_def:
ffVar (Pred _ _) = {} ∧
(ffVar (IMP f1 f2) = ffVar f1 ∪ ffVar f2)  ∧
ffVar False = {} ∧
ffVar (FALL s b) = ffVar b ∧
ffVar (fVar p vl _) = {(p,vl)}
End


Definition fVmap_fVs_def:
fVmap_fVs σ = BIGUNION {ffVar (σ ' (P:string,sl:sort list)) | (P,sl) | (P,sl) ∈ FDOM σ} 
End


Theorem ffVar_fprpl_ok_abs:
∀f bmap.
(∀P sl. (P,sl) ∈ ffVar f ⇒ ok_abs sl) ⇒
ffVar (fprpl bmap f) = ffVar f
Proof
Induct_on ‘f’ >> rw[ffVar_def,fprpl_def] (* 3 *)
>- metis_tac[]
>- metis_tac[] >>
metis_tac[ok_abs_slprpl]
QED

(*if f = fVar P [set] a , σ has (P,[set]) |-> Q(0->0)(0),
  then inst gives Q(a->a)(0), does not appear anywhere*)                
Theorem ffVar_fVar_prpl:
∀f σ. (∀P sl. (P,sl) ∈ FDOM σ ∩ freefVars f ⇒
     ∀P1 sl1. (P1,sl1) ∈ ffVar (σ ' (P,sl)) ⇒ ok_abs sl1) ⇒
ffVar (fVar_prpl σ f) ⊆ ffVar f ∪ fVmap_fVs (DRESTRICT σ (freefVars f))
Proof
rw[] >> reverse (Induct_on ‘f’) (* 5 *) 
>- (rw[fVar_prpl_def,freefVars_def,ffVar_def,fVmap_fVs_def] >>
   drule_then assume_tac ffVar_fprpl_ok_abs >> simp[] >>
   rw[SUBSET_DEF] >> simp[DRESTRICT_DEF])
>- (rw[fVar_prpl_def,freefVars_def,ffVar_def,fVmap_fVs_def] >>
   gs[fVmap_fVs_def] >> metis_tac[])
>- (rw[fVar_prpl_def,freefVars_def,ffVar_def,fVmap_fVs_def] (* 2 *)
    >- 
    (‘ffVar (fVar_prpl σ f) ⊆
        ffVar f ∪ fVmap_fVs (DRESTRICT σ (freefVars f))’
        by (first_x_assum irule >> metis_tac[] ) >>
        irule SUBSET_TRANS >> first_x_assum $ irule_at Any >>
        rw[] (* 2 *)
        >- (rw[SUBSET_DEF] >>
        rw[fVmap_fVs_def,SUBSET_DEF] >> disj2_tac >>
        rw[PULL_EXISTS] >>
        qexistsl [‘P’,‘sl’] >> gs[DRESTRICT_DEF]) >>
        rw[fVmap_fVs_def] >>
        rw[SUBSET_DEF] >> disj2_tac >> simp[PULL_EXISTS] >>
        qexistsl [‘P’,‘sl’] >> gs[DRESTRICT_DEF]) >>
     (‘ffVar (fVar_prpl σ f') ⊆
        ffVar f' ∪ fVmap_fVs (DRESTRICT σ (freefVars f'))’
        by (first_x_assum irule >> metis_tac[] ) >>
        irule SUBSET_TRANS >> first_x_assum $ irule_at Any >>
        rw[] (*3 *)
        >- (rw[SUBSET_DEF] >>
        rw[fVmap_fVs_def,SUBSET_DEF] >> disj2_tac >>
        rw[PULL_EXISTS] >>
        qexistsl [‘P’,‘sl’] >> gs[DRESTRICT_DEF]) >>
        rw[fVmap_fVs_def] >>
        rw[SUBSET_DEF] >> disj2_tac >> simp[PULL_EXISTS] >>
        qexistsl [‘P’,‘sl’] >> gs[DRESTRICT_DEF]) )
>> rw[fVar_prpl_def,freefVars_def,ffVar_def,fVmap_fVs_def]
QED
     

Theorem fVar_subfm_ffVar:
∀f P sl. (P,sl) ∈ ffVar f ⇔ ∃tl. fVar P sl tl ∈ subfm f
Proof
Induct_on ‘f’ >> gs[ffVar_def,subfm_def] >> metis_tac[]
QED


Theorem fVar_prpl_FALLL:
∀sl σ b. fVar_prpl σ (FALLL sl b) = FALLL sl (fVar_prpl σ b)
Proof
Induct_on ‘sl’ >> simp[fVar_prpl_def,FALLL_def]
QED
 
Theorem wffVmap_o_fVmap:
  (∀fsym.
    isfsym Σf fsym ⇒
    sfv (fsymout Σf fsym) ⊆
    BIGUNION {{(n,s)} ∪ sfv s | MEM (n,s) (fsymin Σf fsym)}) ∧
  wffVmap (Σf,Σp) σ1 ∧ wffVmap (Σf,Σp) σ2 ⇒
  wffVmap (Σf,Σp) (o_fVmap σ2 σ1)
Proof
  rw[wffVmap_def] >> gs[FDOM_o_fVmap] (* 4 *) 
  >- (first_x_assum $ drule_then assume_tac >>
     drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
     ‘(P1,sl1) ∈ ffVar (fVar_prpl σ2 (σ1 ' (P,sl)))’ by
      (simp[fVar_subfm_ffVar] >> metis_tac[]) >>
     ‘ffVar (fVar_prpl σ2 (σ1 ' (P,sl))) ⊆
      ffVar (σ1 ' (P,sl)) ∪ fVmap_fVs (DRESTRICT σ2 (freefVars (σ1 ' (P,sl))))’
      by (irule ffVar_fVar_prpl >> rw[] >>
         last_x_assum $ drule_then assume_tac >>
         gs[] >> first_x_assum irule >> 
         simp[GSYM fVar_subfm_ffVar] >> metis_tac[]) >>
     pop_assum mp_tac >> rw[SUBSET_DEF] >> first_x_assum $ drule_then assume_tac >>
     gs[] (* 2 *)
     >- (first_x_assum irule >> simp[GSYM fVar_subfm_ffVar] >> metis_tac[]) >>
     pop_assum mp_tac >> simp[fVmap_fVs_def] >>
     simp[PULL_EXISTS] >> simp[FDOM_DRESTRICT] >> rw[] >>
     last_x_assum $ drule_then assume_tac >> gs[] >>
     first_x_assum irule >>
     simp[GSYM fVar_subfm_ffVar] >> qexists ‘P1’ >>
     gs[DRESTRICT_DEF])
  >- (Cases_on ‘(P,sl) ∈ FDOM σ1’
      >- (qpat_x_assum ‘_ ∈ FDOM σ2’ (K all_tac) >>
         first_x_assum $ drule_then assume_tac >>
     drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
     ‘(P1,sl1) ∈ ffVar (fVar_prpl σ2 (σ1 ' (P,sl)))’ by
      (simp[fVar_subfm_ffVar] >> metis_tac[]) >>
     ‘ffVar (fVar_prpl σ2 (σ1 ' (P,sl))) ⊆
      ffVar (σ1 ' (P,sl)) ∪ fVmap_fVs (DRESTRICT σ2 (freefVars (σ1 ' (P,sl))))’
      by (irule ffVar_fVar_prpl >> rw[] >>
         last_x_assum $ drule_then assume_tac >>
         gs[] >> first_x_assum irule >> 
         simp[GSYM fVar_subfm_ffVar] >> metis_tac[]) >>
     pop_assum mp_tac >> rw[SUBSET_DEF] >> first_x_assum $ drule_then assume_tac >>
     gs[] (* 2 *)
     >- (first_x_assum irule >> simp[GSYM fVar_subfm_ffVar] >> metis_tac[]) >>
     pop_assum mp_tac >> simp[fVmap_fVs_def] >>
     simp[PULL_EXISTS] >> simp[FDOM_DRESTRICT] >> rw[] >>
     last_x_assum $ drule_then assume_tac >> gs[] >>
     first_x_assum irule >>
     simp[GSYM fVar_subfm_ffVar] >> qexists ‘P1’ >>
     gs[DRESTRICT_DEF]) >>
     drule_all_then assume_tac FAPPLY_o_fVmap2 >> gs[] >> metis_tac[])
 >- (first_x_assum $ drule_then assume_tac >> gs[] >>
    drule_then assume_tac FAPPLY_o_fVmap1 >> simp[] >>
    ‘(FALLL sl (fVar_prpl σ2 (σ1 ' (P,sl)))) =
     fVar_prpl σ2 (FALLL sl (σ1 ' (P,sl)))’ by simp[fVar_prpl_FALLL] >>
    simp[] >> irule wff_fVar_prpl >> simp[]) >>
 Cases_on ‘(P,sl) ∈ FDOM σ1’
 >- (qpat_x_assum ‘_ ∈ FDOM σ2’ (K all_tac) >>
    first_x_assum $ drule_then assume_tac >> gs[] >>
    drule_then assume_tac FAPPLY_o_fVmap1 >> simp[] >>
    ‘(FALLL sl (fVar_prpl σ2 (σ1 ' (P,sl)))) =
     fVar_prpl σ2 (FALLL sl (σ1 ' (P,sl)))’ by simp[fVar_prpl_FALLL] >>
    simp[] >> irule wff_fVar_prpl >> simp[]) >>
 drule_then assume_tac FAPPLY_o_fVmap2 >>
 first_x_assum $ drule_then assume_tac >> simp[]
QED 


Theorem EXTRA_ffv_fVar_prpl:        
∀f σ.
(∀P sl. (P,sl) ∈ freefVars f ∩ FDOM σ ⇒ ∀n s. (n,s) ∈ ffv (σ ' (P,sl)) ⇒ sbounds s = {}) ⇒
ffv f ∪ ffv (fVar_prpl σ f) = ffv f ∪ BIGUNION {ffv (σ ' (P,sl)) | (P,sl) | (P,sl) ∈ freefVars f ∩ FDOM σ}
Proof
Induct_on ‘f’ >> gs[ffv_thm,freefVars_def,fVar_prpl_def] (* 3 *)
>- (rw[] >>
   ‘ffv f ∪ ffv f' ∪ (ffv (fVar_prpl σ f) ∪ ffv (fVar_prpl σ f')) =
    (ffv f ∪ ffv (fVar_prpl σ f)) ∪ (ffv f' ∪ ffv (fVar_prpl σ f'))’
    by (rw[EXTENSION] >> metis_tac[]) >>
   ‘BIGUNION
          {ffv (σ ' (P,sl)) |
           (P,sl) |
           ((P,sl) ∈ freefVars f ∨ (P,sl) ∈ freefVars f') ∧ (P,sl) ∈ FDOM σ} =
    BIGUNION
              {ffv (σ ' (P,sl)) |
               (P,sl) |
               (P,sl) ∈ freefVars f ∧ (P,sl) ∈ FDOM σ} ∪
   BIGUNION
              {ffv (σ ' (P,sl)) |
               (P,sl) |
               (P,sl) ∈ freefVars f' ∧ (P,sl) ∈ FDOM σ}’
    by (rw[EXTENSION] >> metis_tac[]) >>
    simp[] >>
    ‘ffv f ∪ ffv f' ∪
        (BIGUNION
           {ffv (σ ' (P,sl)) |
            (P,sl) |
            (P,sl) ∈ freefVars f ∧ (P,sl) ∈ FDOM σ} ∪
         BIGUNION
           {ffv (σ ' (P,sl)) |
            (P,sl) |
            (P,sl) ∈ freefVars f' ∧ (P,sl) ∈ FDOM σ}) =
             (ffv f ∪ 
        BIGUNION
           {ffv (σ ' (P,sl)) |
            (P,sl) |
            (P,sl) ∈ freefVars f ∧ (P,sl) ∈ FDOM σ}) ∪
         (ffv f' ∪ BIGUNION
           {ffv (σ ' (P,sl)) |
            (P,sl) |
            (P,sl) ∈ freefVars f' ∧ (P,sl) ∈ FDOM σ})’
       by (rw[EXTENSION] >> metis_tac[]) >>
   simp[] >> metis_tac[])
>- (rw[] >>
   ‘ sfv s ∪ ffv f ∪ (sfv s ∪ ffv (fVar_prpl σ f)) =
     sfv s ∪ (ffv f ∪ ffv (fVar_prpl σ f))’
   by (rw[EXTENSION] >> metis_tac[]) >>
   simp[] >> rw[GSYM UNION_ASSOC] >> metis_tac[]) >>
rw[] (* 2 *)
>- (rw[GSYM UNION_ASSOC] >>
   ‘(BIGUNION {tfv t | MEM t l0} ∪ ffv (fprpl (mk_bmap (REVERSE l0)) (σ ' (s,l)))) =
    (BIGUNION {tfv t | MEM t l0} ∪
         BIGUNION
           {ffv (σ ' (P,sl)) | (P,sl) | (P = s ∧ sl = l) ∧ (P,sl) ∈ FDOM σ})’
   suffices_by metis_tac[] >>
   drule_then assume_tac ffv_fprpl >> simp[] >>
   simp[FDOM_mk_bmap] >>
   ‘BIGUNION
          {ffv (σ ' (P,sl)) | (P,sl) | (P = s ∧ sl = l) ∧ (P,sl) ∈ FDOM σ} =
    ffv (σ ' (s,l))’
    by (rw[EXTENSION] >> metis_tac[]) >> simp[]  >>
   ‘ {tfv (mk_bmap (REVERSE l0) ' i) |
            i |
            i < LENGTH l0 ∧ i ∈ fbounds (σ ' (s,l))} ⊆
     {tfv t0 | MEM t0 l0}
    ’
    by (rw[SUBSET_DEF] >>
       ‘i < LENGTH (REVERSE l0)’ by simp[] >> 
       drule_then assume_tac FAPPLY_mk_bmap >> simp[] >>
       irule_at Any EQ_REFL >> simp[MEM_EL] >>
       qexists ‘PRE (LENGTH l0 - i)’ >> simp[] >>
       irule EL_REVERSE  >> simp[]) >>
    drule_then assume_tac SUBSET_BIGUNION >>
    gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
gs[] >>
‘ BIGUNION
          {ffv (σ ' (P,sl)) | (P,sl) | (P = s ∧ sl = l) ∧ (P,sl) ∈ FDOM σ} = {}’
 by simp[EXTENSION] >> simp[]
QED
             
Definition cont_def:
cont (Γ:string # sort -> bool,A:form -> bool,f:form) = Γ
End

     
Definition assum_def:
assum (Γ:string # sort -> bool,A:form -> bool,f:form) = A
End

Definition assum_def:
assum (Γ:string # sort -> bool,A:form -> bool,f:form) = A
End        


Definition fsfv_def:
fsfv fs = BIGUNION {ffv f | f ∈ fs}
End

Definition fsfreefVars_def:
fsfreefVars fs = BIGUNION {freefVars f | f ∈ fs}
End

EXTRA_ffv_fVar_prpl


fsfv {σ1 ' (P,sl) | (P,sl) | (P,sl) ∈ fsfreefVars (A ∪ {f}) ∩ FDOM σ1} ∪
fsfv {σ2 ' (P,sl) | (P,sl) | (P,sl) ∈ fsfreefVars (IMAGE (fVar_prpl σ1) (A ∪ {f})) ∩ FDOM σ2} ⊆
fsfv (A ∪ {f}) ∪  fsfv {(o_fVmap σ2 σ1) ' (P,sl) |(P,sl) | (P,sl) ∈ fsfreefVars (A ∪ {f}) ∩ (FDOM σ1 ∪ FDOM σ2)}

Theorem fsfv_UNION:
fsfv A ∪ fsfv B = fsfv (A ∪ B)
Proof
rw[EXTENSION,fsfv_def] >> metis_tac[]
QED

ffVar_fVar_prpl
        
Theorem freefVars_fVar_prpl:
∀f σ. 
(∀P sl.
          (P,sl) ∈ FDOM σ ∩ freefVars f ⇒
          ∀P1 sl1. (P1,sl1) ∈ freefVars (σ ' (P,sl)) ⇒ ok_abs sl1) ⇒
freefVars (fVar_prpl σ f) = (freefVars f DIFF (FDOM σ)) ∪ fsfreefVars {σ ' (P,sl) | (P,sl) | (P,sl) ∈ freefVars f ∩ FDOM σ}
Proof
Induct_on ‘f’ >> gs[freefVars_def,fVar_prpl_def,fsfreefVars_def] (* 3 *) 
>- (rw[] >>
   ‘freefVars (fVar_prpl σ f) =
            freefVars f DIFF FDOM σ ∪
            BIGUNION
              {freefVars f'' |
               (∃P sl.
                  f'' = σ ' (P,sl) ∧ (P,sl) ∈ freefVars f ∧ (P,sl) ∈ FDOM σ)} ∧
    freefVars (fVar_prpl σ f') =
            freefVars f' DIFF FDOM σ ∪
            BIGUNION
              {freefVars f'' |
               (∃P sl.
                  f'' = σ ' (P,sl) ∧ (P,sl) ∈ freefVars f' ∧ (P,sl) ∈ FDOM σ)}’
    by metis_tac[] >>
   simp[] >> rw[EXTENSION] >> metis_tac[])
>- (rw[] >> metis_tac[]) >>
rw[] (* 3 *) >> gs[freefVars_def] >>
freefVars_fprpl 
            
Theorem foo:
wffVmap Σ σ1 ∧ wffVmap Σ σ2 ⇒
fsfv {(o_fVmap σ2 σ1) ' (P,sl) |(P,sl) | (P,sl) ∈ fsfreefVars (A ∪ {f}) ∩ (FDOM σ1 ∪ FDOM σ2)} ⊆
fsfv (A ∪ {f}) ∪
fsfv {σ1 ' (P,sl) | (P,sl) | (P,sl) ∈ fsfreefVars (A ∪ {f}) ∩ FDOM σ1} ∪
fsfv {σ2 ' (P,sl) | (P,sl) | (P,sl) ∈ fsfreefVars (IMAGE (fVar_prpl σ1) (A ∪ {f})) ∩ FDOM σ2} 
Proof
rw[fsfv_UNION] >> rw[SUBSET_DEF] >>
gs[fsfv_def,fsfreefVars_def,PULL_EXISTS] (* 4 *)
>- (rename [‘(P,sl) ∈ freefVars a’] >>
   drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
   (* ffv_fVar_prpl *)
   ‘ ffv (fVar_prpl σ2 (σ1 ' (P,sl))) ⊆
       ffv (σ1 ' (P,sl)) ∪
       BIGUNION {ffv (σ2 ' (P2,sl2)) | (P2,sl2) | (P2,sl2) ∈ FDOM σ2 ∩ freefVars (σ1 ' (P,sl))}’
     by cheat >>
   pop_assum mp_tac >> rw[SUBSET_DEF,PULL_EXISTS] >>
   first_x_assum $ drule_then assume_tac >> gs[] (* 2 *)
   >- (first_x_assum $ irule_at Any >> disj1_tac >> disj2_tac >> irule_at Any EQ_REFL >>
      metis_tac[])
   >- (first_assum $ irule_at Any >> disj2_tac >> irule_at Any EQ_REFL >>
      simp[PULL_EXISTS] >>
      qexists ‘fVar_prpl σ1 a’ >>simp[] >> rw[]  >- cheat >> metis_tac[](*lemma on what is in ffVar fVar_prpl*)))
>- (rename [‘(P,sl) ∈ freefVars a’] >>
   Cases_on ‘(P,sl) ∈ FDOM σ1’ >- cheat >>
   drule_all_then assume_tac FAPPLY_o_fVmap2 >>
   gs[] >> first_assum $ irule_at Any >>
   disj2_tac >> irule_at Any EQ_REFL >>
   simp[] >> qexists ‘fVar_prpl σ1 a’ >> rw[]
   >- cheat (*(P,sl) is not hit, so survives the subst*) >>
   metis_tac[])
>- (drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
   (* ffv_fVar_prpl *)
   ‘ ffv (fVar_prpl σ2 (σ1 ' (P,sl))) ⊆
       ffv (σ1 ' (P,sl)) ∪
       BIGUNION {ffv (σ2 ' (P2,sl2)) | (P2,sl2) | (P2,sl2) ∈ FDOM σ2 ∩ freefVars (σ1 ' (P,sl))}’
     by cheat >>
   pop_assum mp_tac >> rw[SUBSET_DEF,PULL_EXISTS] >>
   first_x_assum $ drule_then assume_tac >> gs[] (* 2 *)
   >- (first_x_assum $ irule_at Any >> disj1_tac >> disj2_tac >> irule_at Any EQ_REFL >>
      metis_tac[])
   >- (first_assum $ irule_at Any >> disj2_tac >> irule_at Any EQ_REFL >>
      simp[PULL_EXISTS] >>
      qexists ‘fVar_prpl σ1 f’ >>simp[] >> rw[] >> cheat (*lemma on what is in ffVar fVar_prpl*))) >>
Cases_on ‘(P,sl) ∈ FDOM σ1’ >- cheat >>
drule_all_then assume_tac FAPPLY_o_fVmap2 >>
gs[] >> first_assum $ irule_at Any >>
disj2_tac >> irule_at Any EQ_REFL >>
simp[] >> qexists ‘fVar_prpl σ1 f’ >> rw[] >> cheat
QED




drule_then assume_tac FAPPLY_o_fVmap1 >> gs[] >>
   ‘ffv (fVar_prpl σ2 (σ1 ' (P,sl))) ⊆
       ffv (σ1 ' (P,sl)) ∪
       BIGUNION {ffv (σ2 ' (P2,sl2)) | (P2,sl2) | (P2,sl2) ∈ FDOM σ2 ∩ freefVars (σ1 ' (P,sl))}’
     by cheat >>
   pop_assum mp_tac >> rw[SUBSET_DEF,PULL_EXISTS] >>
   first_x_assum $ drule_then assume_tac >> gs[] (* 2 *)
   >- 

first_assum $ irule_at Any >> disj2_tac >>
   first_assum $ irule_at Any >> first_assum $ irule_at Any >>
   simp[] >> drule_then assume_tac FAPPLY_o_fVmap1 >> 
         
      
     
   gs[] (* 2 *)
   >- freefVars
first_x_assum $ irule_at Any >>
Cases_on 
‘fsfv
          (A ∪ {f} ∪
           {o_fVmap σ2 σ1 ' (P,sl) |
            (P,sl) |
            (P,sl) ∈ fsfreefVars (A ∪ {f}) ∧
            ((P,sl) ∈ FDOM σ1 ∨ (P,sl) ∈ FDOM σ2)}) =
BIGUNION {ffv f0 ∪ } ’
>- 
rw[SUBSET_DEF] >> gs[fsfv_def,PULL_EXISTS,fsfreefVars_def] (* 4 *)
>- rename [‘(P,sl) ∈ freefVars a’] >>
   drule_then assume_tac FAPPLY_o_fVmap1 >>
   Cases_on ‘’
   disj2_tac >> first_x_assum $ irule_at Any >> simp[] >>
   simp[] >>
   

        
Theorem foo:
wffVmap (Σf,Σp) σ1 ∧ wffVmap (Σf,Σp) σ2 ⇒
cont (fVar_thprpl (o_fVmap σ2 σ1) (Γ,A,f)) ⊆ cont (fVar_thprpl σ2 (fVar_thprpl σ1 (Γ,A,f)))
Proof
rw[fVar_thprpl_def,cont_def] (* 2 *)
>- rw[SUBSET_DEF] >>
‘BIGUNION
          {ffv (o_fVmap σ2 σ1 ' fv) |
           (fv,f0) |
           (f0 ∈ A ∨ f0 = f) ∧ fv ∈ freefVars f0 ∧ fv ∈ FDOM (o_fVmap σ2 σ1)} ⊆
        Γ ∪
        BIGUNION
          {ffv (σ1 ' fv) |
           (fv,f0) |
           (f0 ∈ A ∨ f0 = f) ∧ fv ∈ freefVars f0 ∧ fv ∈ FDOM σ1} ∪
        BIGUNION
          {ffv (σ2 ' fv) |
           (fv,f0) |
           ((∃x. f0 = fVar_prpl σ1 x ∧ x ∈ A) ∨ f0 = fVar_prpl σ1 f) ∧
           fv ∈ freefVars f0 ∧ fv ∈ FDOM σ2}’ 

        
Theorem thinstance_fVar_prpl:
(∀fsym.
    isfsym Σf fsym ⇒
    sfv (fsymout Σf fsym) ⊆
    BIGUNION {{(n,s)} ∪ sfv s | MEM (n,s) (fsymin Σf fsym)}) ∧
wffVmap (Σf,Σp) σ1 ∧ wffVmap (Σf,Σp) σ1 ⇒
cont (fVar_thprpl σ2 (fVar_thprpl σ1 (Γ,A,f))) =



thinsts_of (Σf,Σp) (fVar_thprpl (Σf,Σp) σ (Γ,A,f)) ⊆
thinsts_of (Σf,Σp) (Γ,A,f)
Proof
rw[] >>
rw[Once SUBSET_DEF,thinsts_of_def] >>
qexists ‘o_fVmap ε σ’ >>
‘wffVmap (Σf,Σp) (o_fVmap ε σ)’ by (irule wffVmap_o_fVmap >> simp[])>>
simp[] >> rw[SPEC_ALL fVar_thprpl_def] (* 3 *)
>- ‘Γ ∪ BIGUNION {ffv f0 | f0 ∈ A ∨ f0 = f} ∪ 
        BIGUNION
          {ffv (σ ' fv) |
           (fv,f0) |
           (f0 ∈ A ∨ f0 = f) ∧ fv ∈ freefVars f0 ∧ fv ∈ FDOM σ} ∪
        BIGUNION
          {ffv (ε ' fv) |
           (fv,f0) |
           ((∃x. f0 = fVar_prpl σ x ∧ x ∈ A) ∨ f0 = fVar_prpl σ f) ∧
           fv ∈ freefVars f0 ∧ fv ∈ FDOM ε} =
        Γ ∪ BIGUNION {ffv f0 | f0 ∈ A ∨ f0 = f} ∪
        BIGUNION
          {ffv (o_fVmap ε σ ' fv) |
           (fv,f0) |
           (f0 ∈ A ∨ f0 = f) ∧ fv ∈ freefVars f0 ∧ fv ∈ FDOM (o_fVmap ε σ)}’
  suffices_by cheat >>
  ‘BIGUNION {ffv f0 | f0 ∈ A ∨ f0 = f} ∪
        BIGUNION
          {ffv (o_fVmap ε σ ' fv) |
           (fv,f0) |
           (f0 ∈ A ∨ f0 = f) ∧ fv ∈ freefVars f0 ∧ fv ∈ FDOM (o_fVmap ε σ)} =
   BIGUNION {ffv f0 ∪ BIGUNION {ffv ((o_fVmap ε σ)' (P,sl)) | (P,sl) | (P,sl) ∈ freefVars f0 ∩ FDOM (o_fVmap ε σ)} | f0 ∈ A ∨ f0 = f}’
  by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 8 *)
     >- metis_tac[] >- metis_tac[]
     >- (Cases_on ‘fv’ >> metis_tac[]) >- (Cases_on ‘fv’ >> metis_tac[])
     >- metis_tac[] >- metis_tac[]
     >> metis_tac[]) >>
  rw[GSYM UNION_ASSOC] >>
  
       
>- irule fVar_prpl_o_fVmap >> cheat  >>
‘  BIGUNION
          {ffv (σ ' fv) |
           (fv,f0) |
           (f0 ∈ A ∨ f0 = f) ∧ fv ∈ freefVars f0 ∧ fv ∈ FDOM σ} ∪
        BIGUNION
          {ffv (ε ' fv) |
           (fv,f0) |
           ((∃x. f0 = fVar_prpl σ x ∧ x ∈ A) ∨ f0 = fVar_prpl σ f) ∧
           fv ∈ freefVars f0 ∧ fv ∈ FDOM ε} =
 BIGUNION
          {ffv (o_fVmap ε σ ' fv) |
           (fv,f0) |
           (f0 ∈ A ∨ f0 = f) ∧ fv ∈ freefVars f0 ∧ fv ∈ FDOM (o_fVmap ε σ)}’
  by
   rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 6 *)
   >- Cases_on ‘fv’ >> drule_then assume_tac FAPPLY_o_fVmap1 >>
      first_x_assum $ irule_at Any >> simp[FDOM_o_fVmap] >>
      ffv_fVar_prpl
   >- (first_x_assum $ irule_at Any >> qexists ‘f0’ >> simp[])
   >- (first_x_assum $ irule_at Any >> qexists ‘f’ >> simp[])
   >- (first_x_assum $ irule_at Any >> qexists ‘x'’ >> simp[]) >>
   first_x_assum $ irule_at Any >> qexists ‘f’ 

simp[FDOM_o_fVmap] >> 
rw[fVar_thprpl_def] >>
rw[]
                

Theorem main:
∀pf.
  Pf Σ axs pf ⇒
  ∀th th1. MEM th pf ∧ th1 ∈ thinstance Σ th ⇒
   ∃pf0. Pf0 Σ (BIGUNION (IMAGE (instance Σ) axs)) pf0 ∧
         LAST pf0 = th1
Proof
Induct_on ‘Pf’ >> reverse (rw[]) (* 23 *)   
>- cheat
>- 

          
>- (gs[thinstance_def] >> cheat
    irule_at Any Pf0_AX >>
    cheat)
>- metis_tac[] (*Pf0_FalseE1 *)
>- (first_x_assum $ drule_then assume_tac >>
   Cases_on ‘th1’ >> Cases_on ‘r’ >>
   rename [‘LAST _ = (ct,ant,c)’] >>
   ‘(ct,ant ∪ {NEG c},False) ∈ thinstance Σ (Γ,A ∪ {NEG f},False)’ by cheat >>
   first_x_assum $ drule_then assume_tac >>
   pop_assum strip_assume_tac >> 
   irule_at Any Pf0_FalseE1 >>
   first_assum $ irule_at Any >> simp[] >>
   qexistsl [‘ct’,‘c’,‘ant’] >> simp[] >>
   cheat(
>-    


Theorem Pf_no_fVar_Pf0:
∀n pf. LENGTH pf = n ⇒
    ∀Σ axs Γ  A f.
    Pf Σ axs pf ∧ LAST pf = (Γ,A,f) ∧ fsfVar ({f} ∪ A) = {} ⇒
    ∃pf0. Pf0 Σ axs' pf0 ∧ LAST pf0 = (Γ,A,f)
Proof
 ho_match_mp_tac arithmeticTheory.COMPLETE_INDUCTION >> rw[] >>
 drule $ iffLR Pf_cases >> reverse (rpt strip_tac) (* 12 *)
 >- qpat_x_assum ‘pf = _ ’ (assume_tac o GSYM) >>
    rename [‘MEM (Γ0,A0,f0) pf0’] >>
    cheat  >>
              


val _ = export_theory();

