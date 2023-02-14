open HolKernel Parse boolLib bossLib;

val _ = new_theory "fVar_subst";




    
Definition ffVar_def:
ffVar (Pred _ _) = {} ∧
(ffVar (IMP f1 f2) = ffVar f1 ∪ ffVar f2)  ∧
ffVar False = {} ∧
ffVar (FALL s b) = ffVar b ∧
ffVar (fVar p vl _) = {(p,vl)}
End


Definition thfVar_def:
thfVar (ct,asm,f) = BIGUNION {ffVar f0 | f0 ∈ asm ∨ f0 = f }
End            

Definition wffvmap_def:
  wffvmap Σ ε ⇔ ∀P sl. (P,sl) ∈ FDOM ε ⇒ wff Σ (FALLL sl (ε ' (P,sl))) ∧ ffVar (ε ' (P,sl)) = {} 
End

        

Definition fVars_subst_def:
  fVars_subst ε f = ITFMAP (λfv ϕ fm. fVar_subst (FST fv,SND fv,ϕ) f) ε f
End


Definition instance_def:
instance Σ f = {fVars_subst ε f| ε | ffVar f ⊆ FDOM ε ∧ wffvmap Σ ε }
End



Definition fVars_thsubst_def:
  fVars_thsubst ε (ct,asm,f) =
  (ct ∪ (BIGUNION {ffv (ε ' fv) | ∃f0. f0 ∈ asm ∨ f0 = f ∧ fv ∈ ffVar f0}) ,
  IMAGE (fVars_subst ε) asm,fVars_subst ε f)
End        


Definition thfVar_def:
thfVar (ct,asm,f) = BIGUNION {ffVar f0 | f0 ∈ asm ∨ f0 = f }
End



Definition thinstance_def:
  thinstance Σ th = {fVars_thsubst ε th | ε | thfVar th ⊆ FDOM ε ∧ wffvmap Σ ε }
End


(* fVars_subst ε (fprpl (mk_bmap (REVERSE l0)) ϕ) =
        fprpl (mk_bmap (REVERSE l0)) (fVars_subst ε ϕ) *)        


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


Theorem fVar_prpl_fVar_subst:
(P,sl) ∈ FDOM ε ⇒
fVar_prpl ε (fVar P sl tl) =
fVar_subst (P,sl,ε ' (P,sl)) (fVar P sl tl)
Proof
rw[fVar_prpl_def,fVar_subst_def]
QED


Theorem fVar_prpl_fVar_subst1:
fVar_prpl ε (fVar P sl tl) =
if (P,sl) ∈ FDOM ε then 
fVar_subst (P,sl,ε ' (P,sl)) (fVar P sl tl)
else  (fVar P sl tl)
Proof
rw[fVar_prpl_def,fVar_subst_def] >> gs[]
QED        

Theorem fVars_subst_alt:
fVars_subst_alt
Proof      


Definition o_fVmap_def:
o_fVmap ε2 ε1 =
FUN_FMAP (λ(P,sl). if (P,sl) ∈ FDOM ε1 then fVar_prpl ε2 (ε1 ' (P,sl)) else if (P,sl) ∈ FDOM ε2 then (ε2 ' (P,sl)) else ARB) (FDOM ε1 ∪ FDOM ε2)
End


Theorem FDOM_o_fVmap:
FDOM (o_fVmap ε2 ε1) = FDOM ε1 ∪ FDOM ε2
Proof
cheat
QED

Theorem FAPPLY_o_fVmap1:
(P,sl) ∈ FDOM ε1 ⇒ (o_fVmap ε2 ε1) ' (P,sl) =
 fVar_prpl ε2 (ε1 ' (P,sl))
Proof
cheat
QED


(*in the case that the fvar is free the

∀f:A->B. P[A->B](0)

into ϕ[0]

*)


Theorem foo2:
(∀t bmap bmap1.
 tbounds t ⊆ FDOM bmap1 ⇒
tprpl (FMAP_MAP (tprpl bmap) bmap1) t =
tprpl bmap (tprpl bmap1 t)) ∧
(∀s bmap bmap1.
 sbounds s ⊆ FDOM bmap1 ⇒
sprpl (FMAP_MAP (tprpl bmap) bmap1) s =
sprpl bmap (sprpl bmap1 s))
Proof
ho_match_mp_tac better_tm_induction >>
simp[tbounds_thm,tprpl_def,SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
rw[] (* 4 *)
>- (first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (drule_then assume_tac (INST_TYPE [gamma |-> “:term”] FAPPLY_FMAP_MAP) >> simp[])
>- gs[FDOM_FMAP_MAP] >>
first_x_assum irule >> simp[] >> gs[SUBSET_DEF] >>
metis_tac[]
QED

                
Theorem foo1:
∀f bmap1 bmap.
fbounds f ⊆ FDOM bmap1 ⇒ 
fprpl (FMAP_MAP (tprpl bmap) bmap1) f =
        fprpl bmap (fprpl bmap1 f)
Proof
Induct_on ‘f’ >>
simp[fprpl_def,MAP_MAP_o,MAP_EQ_f,fbounds_thm]
>- (rw[] >> gs[SUBSET_DEF] >>
   irule $ cj 1 foo2 >> gs[SUBSET_DEF] >>
   metis_tac[])
>- simp[fprpl_def,MAP_MAP_o,MAP_EQ_f] >> rw[] (* 2 *)
   >- (irule $ cj 2 foo2 >> simp[]) >>
   shift_bmap_FEMPTY cheat >>
rw[]


Theorem ok_abs_slprpl:
∀l bmap. ok_abs l ⇒ slprpl bmap l = l
Proof
rw[] >> irule LIST_EQ >> simp[LENGTH_slprpl] >>
rw[] >> drule_then assume_tac slprpl_EL >>
simp[] >>
irule $ cj 2 tprpl_id >>
simp[FDOM_shift_bmap] >>
gs[ok_abs_def] >>
first_x_assum $ drule_then assume_tac >>
rw[Once EXTENSION] >>
CCONTR_TAC >> gs[] >>
gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >> gs[]
QED

Theorem foo: 
∀f bmap.
(∀P sl ϕ. (P,sl) ∈ FDOM ε2 ⇒ wff Σ (FALLL sl ϕ)) ⇒
fVar_prpl ε2 (fprpl bmap f) =
        fprpl bmap (fVar_prpl ε2 f)
Proof
Induct_on ‘f’
>> simp[fVar_prpl_def,fprpl_def] >> rw[] (* 7 *)
>- metis_tac[]
>- metis_tac[]
>- metis_tac[]
>- (‘slprpl bmap l = l’ by metis_tac[ok_abs_slprpl] >>
   simp[] >> cheat)
>- Cases_on ‘ok_abs l’ >> gs[] (* 2 *)
   >- metis_tac[ok_abs_slprpl] >>
   first_x_assum $ drule_then assume_tac >>
   (*wff Σ (FALLL (slprpl bmap l) ϕ) impossible since *)   
   

cheat

>- ‘slprpl bmap l = l’ by cheat >> simp[] >>
   


>- simp[fVar_prpl_def] >> rw[]

simp[fVar_prpl_def,fprpl_def] >>
reverse (rw[]) (* 4 *)
>- rw[fprpl_def]
>- cheat
>- cheat >>
simp[fprpl_def] 
        
        
Theorem fVar_prpl_o:
∀f.
(∀P sl ϕ. (P,sl) ∈ FDOM ε1 ⇒ wff Σ (FALLL sl ϕ)) ∧
(∀P sl ϕ. (P,sl) ∈ FDOM ε2 ⇒ wff Σ (FALLL sl ϕ)) ⇒
fVar_prpl ε2 (fVar_prpl ε1 f) = fVar_prpl (o_fVmap ε2 ε1) f
Proof
Induct_on ‘f’ >> simp[fVar_prpl_def] >>
rw[] (* 4 *)
>- metis_tac[]
>- metis_tac[]
>- metis_tac[] 
>- drule_then assume_tac FAPPLY_o_fVmap1 >> simp[] >>
   simp[fprpl_def]
   


Definition fVarl_subst_def:
fVarl_subst [] f = f ∧
fVarl_subst (h :: t) f = fVar_subst h (fVarl_subst t f)
End            

           
Theorem fVars_subst_fVar_prpl:
∀f ε. 
 ∃l. 
 fVar_prpl ε f = fVarl_subst l f
Proof
 Induct_on ‘f’ >> simp[fVar_prpl_def,fVar_subst_def]
 
 >- (qexists ‘FEMPTY’ >> cheat) >>

Theorem fVars_subst_fVar_prpl:
∀s. FINITE s ⇒
∀ε. s = FDOM ε ⇒
∀f. 
 ∃l. 
 fVar_prpl ε f = fVarl_subst l f

 
Proof
 Induct_on ‘FINITE’ >> rw[] (* 2 *)
 >- (qexists ‘[]’ >> rw[fVarl_subst_def] >>
    cheat) >>
 first_x_assum (qspecl_then [‘DRESTRICT ε s’] assume_tac) >>
 gs[DRESTRICT_DEF] >>
 ‘s = FDOM ε ∩ s’ by cheat >> gs[] >>
 first_x_assum (qspecl_then [‘f’] assume_tac) >> gs[] >>
 ‘fVar_prpl ε f =
  fVar_subst (nn,SND e,ε ' e)
             (fVar_prpl (DRESTRICT ε s) (fVar_rename e nn f))’
  by cheat  >>
 qexists ‘((nn,SND e), ε ' e) :: l ++ [((FST e,SND e),fVar nn (SND e)] ’          
 
  (qexists ‘FEMPTY’ >> cheat) >>
 
 

Theorem fVar_case:
∀f ϕ P sl. 
    fVars_subst ε (fVar_subst (P,sl,ϕ) f) =
    fVars_subst
    (FUN_FMAP (λ(P0,sl0).
    if (P0,sl0) = (P,sl) then fVars_subst ε ϕ else ε ' (P0,sl0)) ({(P,sl)} ∪ FDOM ε)) f 
Proof
reverse (Induct_on ‘f’) (* 5 *)
>- rw[] >>
   rw[fVar_subst_def]>>
   ‘fVars_subst
          (FUN_FMAP
             (λ(P0,sl0).
                  if P0 = P ∧ sl0 = l then fVars_subst ε ϕ else ε ' (P0,sl0))
             ({(P,l)} ∪ FDOM ε)) (fVar P l l0) =
   fVar_subst (P,l,fVars_subst ε ϕ) (fVar P l l0)’
   by cheat >>
   simp[] >> rw[fVar_subst_def]
   >- cheat >>
   ‘(FUN_FMAP
             (λ(P0,sl0).
                  if P0 = P ∧ sl0 = sl then fVars_subst ε ϕ else ε ' (P0,sl0))
             ({(P,sl)} ∪ FDOM ε)) =
   ε |+ ((P,sl),fVars_subst ε ϕ)’ by cheat >>
   simp[] >> rw[fVars_subst_def,ITFMAP_thm] >> 
   fVars_subst_def


                 

val _ = export_theory();

