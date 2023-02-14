
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



Definition o_fVmap_def:
o_fVmap σ2 σ1 =
FUN_FMAP
(λ(P,sl).
 if (P,sl) ∈ FDOM σ1 then fVar_prpl σ2 (σ1 ' (P,sl)) else
 σ2 ' (P,sl)) (FDOM σ1 ∪ FDOM σ2)
End 



                    
Definition subfm_def:
subfm False = {False} ∧
subfm (IMP f1 f2) = {IMP f1 f2} ∪ subfm f1 ∪ subfm f2 ∧
subfm (Pred p tl) = {Pred p tl} ∧
subfm (fVar P sl tl) = {fVar P sl tl} ∧
subfm (FALL s b) = {FALL s b} ∪ subfm b
End

Theorem slprpl_id:
∀l.slbounds l = {} ⇒ ∀bmap. slprpl bmap l = l
Proof
rw[] >> irule LIST_EQ >> gs[LENGTH_slprpl] >>
rw[] >> drule_then assume_tac slprpl_EL >> simp[] >>
irule $ cj 2 tprpl_id >>
rw[FDOM_shift_bmap] >> rw[Once EXTENSION] >>
Cases_on ‘x' ∈ sbounds (EL x l)’ >> gs[] >>
gs[Once EXTENSION] >>
gs[IN_slbounds] >> rw[] >> metis_tac[] 
QED



Theorem ok_abs_slprpl_fix:
ok_abs l ⇒ slbounds l = {}
Proof
rw[Once EXTENSION] >> rw[IN_slbounds] >>
Cases_on ‘m < LENGTH l’ >> gs[] >>
gs[ok_abs_def] >>
first_x_assum $ drule_then assume_tac >>
gs[SUBSET_DEF] >>
CCONTR_TAC >>
gs[] >>
first_x_assum $ drule_then assume_tac >>
gs[]
QED        




Theorem fVar_prpl_o_fVmap:
∀f σ1 σ2.
(∀P sl. (P,sl) ∈ FDOM σ1 ⇒
       ∀P1 sl1 tl1.
         fVar P1 sl1 tl1 ∈ subfm (σ1 ' (P,sl)) ⇒
         ok_abs sl1) ⇒
fVar_prpl σ2 (fVar_prpl σ1 f) = fVar_prpl (o_fVmap σ2 σ1) f
Proof
Induct_on ‘f’ >> gs[fVar_prpl_def] (* 3 *)
>- (rw[] (* 2 *) >> metis_tac[])
>- gs[] >> rw[] (* 4 *)
>- (‘(o_fVmap σ2 σ1 ' (s,l)) = fVar_prpl σ2 (σ1 ' (s,l))’
   by (irule FAPPLY_o_fVmap1 >> simp[]) >> simp[] >>
   irule fVar_prpl_fprpl >> cheat)
>- gs[FDOM_o_fVmap] (*¬((s,l) ∈ FDOM (o_fVmap σ2 σ1) ∧ ok_abs l),
   2.  (s,l) ∈ FDOM σ1
    3.  ok_abs l contra *)
>- (rw[fVar_prpl_def] (* 2 *)
   >- (gs[FDOM_o_fVmap] >>
      drule_all_then assume_tac FAPPLY_o_fVmap2 >>
      simp[]) >> gs[FDOM_o_fVmap]) >>
‘ok_abs l’ by cheat >>
gs[FDOM_o_fVmap] >>
rw[fVar_prpl_def] 
QED
*)
        
   
 
(*
Definition modifV_def:
modifV σ bmap False = False ∧
modifV σ bmap (IMP f1 f2) =
IMP (modifV σ bmap f1) (modifV σ bmap f2)  ∧
modifV σ bmap (Pred p tl) = Pred p tl ∧
modifV σ bmap (FALL s b) = FALL s (modifV σ (shift_bmap 1 bmap) b)∧
modifV σ bmap (fVar P sl tl) =
if (P,slprpl bmap sl) ∈ FDOM σ then 
fprpl (mk_bmap (REVERSE tl)) (σ ' (P,slprpl bmap sl))
else fVar P sl tl
End
*)

Theorem tprpl_FMAP_MAP_tprpl:
(∀tm bmap0 bmap.
tbounds tm ⊆ FDOM bmap0 ⇒
tprpl (FMAP_MAP (tprpl bmap) bmap0) tm =
tprpl bmap (tprpl bmap0 tm)) ∧
(∀st bmap0 bmap.
sbounds st ⊆ FDOM bmap0 ⇒
sprpl (FMAP_MAP (tprpl bmap) bmap0) st =
sprpl bmap (sprpl bmap0 st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,tprpl_def,MAP_MAP_o,MAP_EQ_f] >>
rw[] (* 4 *)
>- (first_x_assum irule >> gs[SUBSET_DEF] >>
   metis_tac[])
>- (irule FAPPLY_FMAP_MAP >> simp[])
>- gs[FDOM_FMAP_MAP] >>
first_x_assum irule >> gs[SUBSET_DEF] >>
metis_tac[]
QED

        
(*
 
Definition Rtprpl_def:
Rtprpl bmap bs (Var n s) = Var n s ∧
Rtprpl bmap bs (Fn f s tl) =
Fn f (Rsprpl bmap bs s) (MAP (Rtprpl bmap bs) tl) ∧
(Rtprpl bmap bs (Bound i) =
if i ∈ FDOM bmap ∩ bs then bmap ' i else Bound i) ∧
Rsprpl bmap bs (St n tl) =
St n (MAP (Rtprpl bmap bs) tl)
Termination
WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,_,t) => term_size t
         | INR (_,_,st) => sort_size st)’   
End


Definition Rslprpl_def:
Rslprpl bmap bs [] = [] ∧
Rslprpl bmap bs (h::t) =
Rsprpl bmap bs h :: Rslprpl (shift_bmap 1 bmap) bs t
End
 
Definition Rfprpl_def:
Rfprpl bmap bs False = False ∧
Rfprpl bmap bs (IMP f1 f2) =
IMP (Rfprpl bmap bs f1) (Rfprpl bmap bs f2) ∧
Rfprpl bmap bs (Pred p tl) =
Pred p (MAP (Rtprpl bmap bs) tl) ∧
Rfprpl bmap bs (fVar p sl tl) =
fVar p (Rslprpl bmap bs sl)
     (MAP (Rtprpl bmap bs) tl) ∧
Rfprpl bmap bs (FALL s b) =
       FALL (Rsprpl bmap bs s) (Rfprpl (shift_bmap 1 bmap) bs b)
End     
                  

Theorem fprpl_FMAP_MAP:
∀f bs bmap bmap0.
(fbounds f) DIFF bs ∩ BIGUNION {tbounds ()} = {} ⇒

Rfprpl (FMAP_MAP (Rtprpl bmap bs) bmap0) bs f =
Rfprpl bmap (Rfprpl bmap0 bs f)
Proof
Induct_on ‘f’ >>
gs[fprpl_def,fbounds_thm,MAP_MAP_o,MAP_EQ_f] (* 3 *)
>- (rw[] >> irule $ cj 1 tprpl_FMAP_MAP_tprpl >>
   gs[SUBSET_DEF] >> metis_tac[])
>- rw[] (* 2 *)
   >- (irule $ cj 2 tprpl_FMAP_MAP_tprpl >>
       simp[]) >>
   ‘(shift_bmap 1 (FMAP_MAP (tprpl bmap) bmap0)) =
    FMAP_MAP (tprpl (shift_bmap 1 bmap)) (shift_bmap 1 bmap0)’ suffices_by
    rw[] >> first_x_assum irule >>
    rw[FDOM_shift_bmap] >> gs[SUBSET_DEF] >>
    rw[] >> first_x_assum irule
rw[] cheat
cheat
QED
*)

Definition shift_bmap'_def:
  shift_bmap' i bmap =
  FUN_FMAP (λn. if i ≤ n then tshift i (bmap ' (n − i)) else Bound n) (count i ∪ (IMAGE ($+ i) (FDOM bmap)))
End  



(*     
Theorem fprpl_shift_bmap_lemma:
fprpl (shift_bmap n (FMAP_MAP (tprpl bmap) bmap0)) f =
        fprpl (shift_bmap n bmap) (fprpl (shift_bmap n bmap0) f)
Proof
*)                


Theorem FDOM_shift_bmap':
FDOM (shift_bmap' i bmap) = count i ∪ (IMAGE ($+i) (FDOM bmap))
Proof
rw[shift_bmap'_def]
QED



Theorem FAPPLY_shift_bmap':
 ∀x.(x ∈ FDOM bmap ⇒
 (shift_bmap' i bmap) ' (i + x) = tshift i (bmap ' x)) ∧
 ∀x. x < i ⇒ (shift_bmap' i bmap) ' x = Bound x
Proof
rw[shift_bmap'_def,FUN_FMAP_DEF]
QED
                  
Theorem tprpl_shift_bmap_shift_bmap':
(∀tm i bmap. tprpl (shift_bmap i bmap) tm =
tprpl (shift_bmap' i bmap) tm) ∧
(∀st i bmap. sprpl (shift_bmap i bmap) st =
sprpl (shift_bmap' i bmap) st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tprpl_def,MAP_EQ_f,FDOM_shift_bmap',FAPPLY_shift_bmap',FDOM_shift_bmap,FAPPLY_shift_bmap] >> rw[]  (* 5 *)
>- (drule_then assume_tac FAPPLY_shift_bmap >>
    gs[] >>
    drule_then assume_tac
               $ cj 1 FAPPLY_shift_bmap' >>
    gs[])
>- gs[] >>
gs[] >> drule_then assume_tac $ cj 2 FAPPLY_shift_bmap' >> gs[]
QED

(*        

Definition slprpl'_def:
slprpl' bmap [] = [] ∧
slprpl' bmap (h::t) = sprpl bmap h::slprpl (shift_bmap' 1 bmap) t
End 
       
Definition fprpl'_def:
  fprpl' bmap False = False ∧
  fprpl' bmap (IMP f1 f2) =
   IMP (fprpl' bmap f1) (fprpl' bmap f2) ∧
  fprpl' bmap (Pred p tl) =
  Pred p (MAP (tprpl bmap) tl) ∧
  fprpl' bmap (fVar p sl tl) =
   fVar p (slprpl' bmap sl)
        (MAP (tprpl bmap) tl) ∧
  fprpl' bmap (FALL s b) =
  FALL (sprpl bmap s) (fprpl' (shift_bmap' 1 bmap) b)
End
*)

       
(*Theorem shift_bmap_shift_bmap':
∀f i bmap.
fprpl (shift_bmap i bmap) f =
fprpl (shift_bmap' i bmap) f ∧
∀f0. f0 ∈ subfm f ⇒ fprpl 
Proof
Induct_on ‘f’ >> gs[fprpl_def,MAP_EQ_f,tprpl_shift_bmap_shift_bmap']  
ho_match_mp_tac better_tm_induction >>
gs[tprpl_def,MAP_EQ_f,FDOM_shift_bmap',FAPPLY_shift_bmap',FDOM_shift_bmap,FAPPLY_shift_bmap] >> rw[]  (* 5 *)
>- (drule_then assume_tac FAPPLY_shift_bmap >>
    gs[] >>
    drule_then assume_tac
               $ cj 1 FAPPLY_shift_bmap' >>
    gs[])
>- gs[] >>
gs[] >> drule_then assume_tac $ cj 2 FAPPLY_shift_bmap' >> gs[]
QED    
*)
                       
(*Theorem tprpl_shift_bmap'_tshift:
(∀tm n bmap.
tbounds tm ⊆ FDOM bmap ⇒
tprpl (shift_bmap' n bmap) (tshift n tm) =
tshift n (tprpl bmap tm)) ∧
(∀st n bmap.
sbounds st ⊆ FDOM bmap ⇒
sprpl (shift_bmap' n bmap) (sshift n st) =
sshift n (sprpl bmap st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,tprpl_def,tshift_def,MAP_MAP_o,MAP_EQ_f,FDOM_shift_bmap'] >> rw[] (* 4 *)
>- (first_x_assum irule >> gs[SUBSET_DEF] >>
   metis_tac[])
>- (rev_drule_then assume_tac $ cj 1 FAPPLY_shift_bmap' >>
   first_x_assum (qspecl_then [‘n'’] assume_tac) >>
   gs[])
>- gs[] >>
first_x_assum irule >> gs[SUBSET_DEF]  >>
metis_tac[]
QED   
*)


Theorem tprpl_shift_bmap'_tshift:
(∀tm n bmap.
tprpl (shift_bmap' n bmap) (tshift n tm) =
tshift n (tprpl bmap tm)) ∧
(∀st n bmap.
sprpl (shift_bmap' n bmap) (sshift n st) =
sshift n (sprpl bmap st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,tprpl_def,tshift_def,MAP_MAP_o,MAP_EQ_f,FDOM_shift_bmap'] >> rw[] (* 4 *) >> gs[] >>
gs[tshift_def]
>- (drule_then assume_tac $ cj 1 FAPPLY_shift_bmap' >>
   simp[] >>
   ‘n = x’ by simp[] >> gs[]) >>
‘n = x’ by simp[] >> gs[] 
QED

                     
Theorem shift_bmap'_FMAP_MAP:
∀n bmap bmap0.
(FMAP_MAP (tprpl (shift_bmap' n bmap)) (shift_bmap' n bmap0)) =
(shift_bmap' n (FMAP_MAP (tprpl bmap) bmap0))
Proof
rw[fmap_EXT,FDOM_FMAP_MAP,FDOM_shift_bmap'] (* 2 *)
>- (drule_then assume_tac $ cj 2 FAPPLY_shift_bmap'>>
   simp[] >>
   ‘x ∈ FDOM (shift_bmap' n bmap)’
     by rw[FDOM_shift_bmap'] >>
  drule_then assume_tac FAPPLY_FMAP_MAP >>
  ‘FMAP_MAP (tprpl (shift_bmap' n bmap)) (shift_bmap' n bmap0) ' x =
  (tprpl (shift_bmap' n bmap))
  ((shift_bmap' n bmap0) ' x)’
   by (irule FAPPLY_FMAP_MAP >>
      simp[FDOM_shift_bmap']) >>
  simp[] >> rw[tprpl_def,FAPPLY_shift_bmap']) >>
rename [‘x ∈ FDOM bmap0’] >>
‘x ∈ FDOM (FMAP_MAP (tprpl bmap) bmap0)’
 by rw[FDOM_FMAP_MAP] >>
drule_then assume_tac $ cj 1 FAPPLY_shift_bmap' >>
simp[] >>
‘FMAP_MAP (tprpl (shift_bmap' n bmap)) (shift_bmap' n bmap0) ' (n + x) =
 (tprpl (shift_bmap' n bmap))
 ((shift_bmap' n bmap0) ' (n + x))’
 by (irule FAPPLY_FMAP_MAP >>
    simp[FDOM_shift_bmap'])>>
simp[] >>
rev_drule_then assume_tac $ cj 1 FAPPLY_shift_bmap'>>
simp[] >>
‘(FMAP_MAP (tprpl bmap) bmap0 ' x) =
 tprpl bmap (bmap0 ' x)’
 by (irule FAPPLY_FMAP_MAP >> simp[]) >>
simp[] >> 
rw[tprpl_shift_bmap'_tshift]
QED    

Definition bmap_eff_def:
bmap_eff bmap i = if i ∈ FDOM bmap then bmap ' i else Bound i
End

Theorem shift_bmap_shift_bmap'_bmap_eff:
∀n i bmap. bmap_eff (shift_bmap n bmap) i =
bmap_eff (shift_bmap' n bmap) i
Proof
rw[bmap_eff_def,
   FAPPLY_shift_bmap',FAPPLY_shift_bmap,
   FDOM_shift_bmap',FDOM_shift_bmap](* 3 *)
>> gs[] (* 2 *)
>- (drule_then assume_tac FAPPLY_shift_bmap >>
   drule_then assume_tac $ cj 1 FAPPLY_shift_bmap' >>
   simp[]) >>
drule_then assume_tac $ cj 2 FAPPLY_shift_bmap'>>
gs[]
QED


        
Definition bmap_equiv_def:
bmap_equiv bmap1 bmap2 ⇔
(∀i. bmap_eff bmap1 i = bmap_eff bmap2 i)
End
        
Theorem bmap_eff_tprpl:
(∀tm bmap1 bmap2.
  bmap_equiv bmap1 bmap2 ⇒
  tprpl bmap1 tm = tprpl bmap2 tm) ∧
(∀st bmap1 bmap2.
  bmap_equiv bmap1 bmap2 ⇒
  sprpl bmap1 st = sprpl bmap2 st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[bmap_equiv_def,tprpl_def,MAP_EQ_f,bmap_eff_def] >>
rw[]
QED


Theorem bmap_eff_shift_bmap:
bmap_eff (shift_bmap n bmap) i =
if ∃a. i = n + a ∧ a ∈ FDOM bmap then tshift n (bmap ' (i-n)) else Bound i
Proof
rw[bmap_eff_def] (* 3 *)
>- (drule_then assume_tac FAPPLY_shift_bmap >>
   simp[] >>
   ‘a + n = n + a’ by simp[] >>
   pop_assum SUBST_ALL_TAC >>
   gs[])
>- gs[FDOM_shift_bmap] >>
gs[FDOM_shift_bmap]
QED



                         
Theorem shift_bmap_equiv:
bmap_equiv bmap1 bmap2 ⇒
∀n. bmap_equiv (shift_bmap n bmap1) (shift_bmap n bmap2)
Proof
rw[shift_bmap_def,bmap_equiv_def,bmap_eff_shift_bmap] >>
Cases_on ‘∃a. i = a + n’ (* 2 *)
>- (gs[] >>
   Cases_on ‘a ∈ FDOM bmap1’ >> gs[] >>
   Cases_on ‘a ∈ FDOM bmap2’ >> gs[] (* 3 *)
   >- (gs[bmap_eff_def] >>
      first_x_assum (qspecl_then [‘a’] assume_tac)>>
      gs[])
   >- (gs[bmap_eff_def] >>
      first_x_assum (qspecl_then [‘a’] assume_tac) >>
      gs[] >>
      rw[tshift_def])
   >- (gs[bmap_eff_def] >>
      first_x_assum (qspecl_then [‘a’] assume_tac) >>
      gs[] >>
      rw[tshift_def] >>
      pop_assum (assume_tac o GSYM) >>
      gs[tshift_def])) >>
gs[]
QED      

         
        
Theorem bmap_eff_slprpl:
∀sl bmap1 bmap2.
  bmap_equiv bmap1 bmap2 ⇒
  slprpl bmap1 sl = slprpl bmap2 sl
Proof
rw[] >> irule LIST_EQ >>
simp[LENGTH_slprpl] >> rw[] >>
drule_then assume_tac slprpl_EL >>
simp[] >> irule $ cj 2 bmap_eff_tprpl >>
irule shift_bmap_equiv >> simp[]
QED


Theorem bmap_eff_fprpl:
∀f bmap1 bmap2.
  bmap_equiv bmap1 bmap2 ⇒
  fprpl bmap1 f = fprpl bmap2 f
Proof 
Induct_on ‘f’ >> gs[fprpl_def,MAP_EQ_f] >>
rw[] (* 5 *)
>- metis_tac[bmap_eff_tprpl]
>- metis_tac[bmap_eff_tprpl]
>- (first_x_assum irule >>
   irule shift_bmap_equiv >> simp[])
>- metis_tac[bmap_eff_slprpl] >>
metis_tac[bmap_eff_tprpl]
QED   


(*                   
       
Theorem shift_bmap'_shift_bmap:
∀m n. (shift_bmap' m (shift_bmap n bmap)) =
shift_bmap' (m + n) bmap
Proof
rw[fmap_EXT,FDOM_shift_bmap',FDOM_shift_bmap] (* 3*)
>- rw[Once EXTENSION,PULL_EXISTS] >> rw[EQ_IMP_THM]
   (* 4 *)
   >- gs[]  
       
Theorem fprpl'_shift_bmap_shift_bmap':
∀f n bmap.
fprpl' (shift_bmap n bmap) f = fprpl' (shift_bmap' n bmap) f
Proof
Induct_on ‘f’ >>
simp[fprpl'_def,MAP_MAP_o,MAP_EQ_f,tprpl_shift_bmap_shift_bmap'] >> rw[] (* 5 *)
>- tprpl_shift_bmap'_tshift 
Theorem fprpl_fprpl':
∀f bmap. fprpl bmap f = fprpl' bmap f
Proof
Induct_on ‘f’ >> gs[fprpl_def,fprpl'_def] >> 


tprpl_shift_bmap'_tshift
         
*)

       
Theorem shift_bmap_shift_bmap'_equiv:
bmap_equiv (shift_bmap' n bmap) (shift_bmap n bmap)
Proof
rw[bmap_equiv_def,shift_bmap_shift_bmap'_bmap_eff]
QED 

Theorem fprpl_FMAP_MAP:
∀f bmap bmap0.
fbounds f ⊆ FDOM bmap0 ⇒ 
fprpl (FMAP_MAP (tprpl bmap) bmap0) f =
fprpl bmap (fprpl bmap0 f)
Proof
Induct_on ‘f’ >>
gs[fprpl_def,fbounds_thm,MAP_MAP_o,MAP_EQ_f] (* 3 *)
>- (rw[] >> irule $ cj 1 tprpl_FMAP_MAP_tprpl >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (rw[] (* 2 *)
   >- (irule $ cj 2 tprpl_FMAP_MAP_tprpl >>
       simp[]) >>
   ‘fbounds f ⊆ {0} ∪ IMAGE SUC (FDOM bmap0)’
    by (rw[SUBSET_DEF] >> gs[SUBSET_DEF,PULL_EXISTS]>>
       Cases_on ‘x = 0’ >> gs[] >>
       qspecl_then [‘x’] assume_tac arithmeticTheory.num_CASES >> gs[] >>
       first_x_assum $ drule_then assume_tac >>
       gs[]) >>
   first_assum (qspecl_then [‘shift_bmap' 1 bmap’,‘shift_bmap' 1 bmap0’] assume_tac) >>
   ‘fbounds f ⊆ FDOM (shift_bmap' 1 bmap0)’
    by (simp[FDOM_shift_bmap'] >>
        ‘{0} ∪ IMAGE SUC (FDOM bmap0) =
        count 1 ∪ IMAGE ($+ 1) (FDOM bmap0)’
         suffices_by (rw[] >> gs[]) >>
        rw[count_def,Once EXTENSION,arithmeticTheory.ADD1] >> ‘x = 0 ⇔ x < 1’ suffices_by metis_tac[] >>
        simp[]) >> 
   first_x_assum $ drule_then assume_tac >>
   ‘fprpl (shift_bmap' 1 (FMAP_MAP (tprpl bmap) bmap0)) f =
        fprpl (shift_bmap' 1 bmap) (fprpl (shift_bmap' 1 bmap0) f)’
   suffices_by
    (rw[] >>
     ‘fprpl (shift_bmap' 1 (FMAP_MAP (tprpl bmap) bmap0)) f = fprpl (shift_bmap 1 (FMAP_MAP (tprpl bmap) bmap0)) f’
      by (irule bmap_eff_fprpl >>
         rw[shift_bmap_shift_bmap'_equiv]) >>
     ‘fprpl (shift_bmap' 1 bmap0) f =
      fprpl (shift_bmap 1 bmap0) f’
      by (irule bmap_eff_fprpl >>
         rw[shift_bmap_shift_bmap'_equiv]) >>
     gs[] >> irule bmap_eff_fprpl >>
     rw[shift_bmap_shift_bmap'_equiv]) >>
   pop_assum (assume_tac o GSYM) >>
   pop_assum SUBST_ALL_TAC >>
   first_x_assum (qspecl_then [‘shift_bmap' 1 bmap’,‘shift_bmap' 1 bmap0’] assume_tac) >>
   gs[shift_bmap'_FMAP_MAP]) >>
reverse (rw[]) (* 2 *)
>- (irule $ cj 1 tprpl_FMAP_MAP_tprpl >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
irule LIST_EQ >> simp[LENGTH_slprpl] >>
rw[] >>
drule_then assume_tac slprpl_EL >>
simp[] >>
‘x < LENGTH (slprpl bmap0 l)’
  by simp[LENGTH_slprpl] >>
drule_then assume_tac slprpl_EL >>
simp[] >>
‘sprpl (shift_bmap' x (FMAP_MAP (tprpl bmap) bmap0)) (EL x l) =
        sprpl (shift_bmap' x bmap) (sprpl (shift_bmap' x bmap0) (EL x l))’
 suffices_by
  (rw[] >>
  ‘sprpl (shift_bmap' x (FMAP_MAP (tprpl bmap) bmap0)) (EL x l) =
  sprpl (shift_bmap x (FMAP_MAP (tprpl bmap) bmap0)) (EL x l)’
   by (irule $ cj 2 bmap_eff_tprpl >>
      rw[shift_bmap_shift_bmap'_equiv]) >>
  ‘(sprpl (shift_bmap' x bmap0) (EL x l)) =
   (sprpl (shift_bmap x bmap0) (EL x l))’
   by (irule $ cj 2 bmap_eff_tprpl >>
      rw[shift_bmap_shift_bmap'_equiv]) >>
  gs[] >>
  irule $ cj 2 bmap_eff_tprpl >>
  rw[shift_bmap_shift_bmap'_equiv]) >>
rw[GSYM shift_bmap'_FMAP_MAP] >>
irule $ cj 2 tprpl_FMAP_MAP_tprpl >>
simp[FDOM_shift_bmap'] >>
rw[SUBSET_DEF] >> Cases_on ‘x' < x’ >> gs[] >>
qexists ‘x' - x’ >> simp[] >>
‘x ≤ x'’ by simp[] >>
gs[SUBSET_DEF] >> last_x_assum irule >>
simp[IN_slbounds] >>
qexists ‘x’ >> simp[] 
QED




Theorem fVar_prpl_fprpl:
  ∀ϕ σ bmap.
    (∀P sl. (P,sl) ∈ FDOM σ ⇒ ok_abs sl ∧
                              fbounds (σ ' (P,sl)) ⊆ count (LENGTH sl)) ∧
    (∀P sl tl. fVar P sl tl ∈ subfm ϕ ⇒ ok_abs sl ∧ LENGTH sl = LENGTH tl) ⇒
    fVar_prpl σ (fprpl bmap ϕ) =
    fprpl bmap (fVar_prpl σ ϕ)
Proof
  reverse (Induct_on ‘ϕ’)>> gs[subfm_def] >>
  rw[fprpl_def] (* 5 *)
  >- (‘(slprpl bmap l) = l’
       by (irule slprpl_id >>  irule ok_abs_slprpl_fix >>
       gs[]) >> simp[] >>
      rw[fVar_prpl_def] (* 2 *)
      >- (rw[GSYM rich_listTheory.MAP_REVERSE,mk_bmap_MAP] >>
          first_x_assum $ drule_then assume_tac >>
          gs[] >>
          ‘fbounds (σ ' (s,l)) ⊆ FDOM (mk_bmap (REVERSE l0))’
            by gs[FDOM_mk_bmap] >>
          drule_then assume_tac fprpl_FMAP_MAP >>
          simp[]) >>
      rw[fprpl_def])
  >- (gs[fprpl_def,fVar_prpl_def] >>
      first_x_assum irule >> metis_tac[])
  >- (gs[fprpl_def,fVar_prpl_def] >> metis_tac[])
  >- gs[fprpl_def,fVar_prpl_def] >>
  gs[fprpl_def,fVar_prpl_def]
QED

                    
Theorem FDOM_o_fVmap:
FDOM (o_fVmap σ2 σ1) = FDOM σ1  ∪ FDOM σ2
Proof
rw[o_fVmap_def,FUN_FMAP_DEF]
QED

             

Theorem FAPPLY_o_fVmap:
(P,sl) ∈ FDOM σ1 ∪ FDOM σ2 ⇒
(o_fVmap σ2 σ1) ' (P,sl) = if (P,sl) ∈ FDOM σ1 then
fVar_prpl σ2 (σ1 ' (P,sl)) else σ2 ' (P,sl)
Proof
rw[o_fVmap_def,FUN_FMAP_DEF]
QED 



Theorem FAPPLY_o_fVmap1:
(P,sl) ∈ FDOM σ1 ⇒
(o_fVmap σ2 σ1) ' (P,sl) = fVar_prpl σ2 (σ1 ' (P,sl)) 
Proof
rw[o_fVmap_def,FUN_FMAP_DEF]
QED



Theorem FAPPLY_o_fVmap2:
(P,sl) ∉ FDOM σ1 ∧ (P,sl) ∈ FDOM σ2 ⇒
(o_fVmap σ2 σ1) ' (P,sl) = σ2 ' (P,sl)
Proof
rw[o_fVmap_def,FUN_FMAP_DEF]
QED        

Theorem fVar_prpl_o_fVmap:
∀f σ1 σ2.
(∀P sl tl. fVar P sl tl ∈ subfm f ⇒ ok_abs sl) ∧
(∀P sl. (P,sl) ∈ FDOM σ1 ⇒
       ∀P1 sl1 tl1.
         fVar P1 sl1 tl1 ∈ subfm (σ1 ' (P,sl)) ⇒
         ok_abs sl1 ∧ LENGTH sl1 = LENGTH tl1) ∧
(∀P sl.
          (P,sl) ∈ FDOM σ2 ⇒
          ok_abs sl ∧ fbounds (σ2 ' (P,sl)) ⊆ count (LENGTH sl))         ⇒
fVar_prpl σ2 (fVar_prpl σ1 f) = fVar_prpl (o_fVmap σ2 σ1) f
Proof
Induct_on ‘f’ >> gs[fVar_prpl_def,subfm_def] (* 3 *)
>- (rw[] (* 2 *) >> metis_tac[])
>- gs[] >> rw[] (* 4 *)
>- (‘(o_fVmap σ2 σ1 ' (s,l)) = fVar_prpl σ2 (σ1 ' (s,l))’
   by (irule FAPPLY_o_fVmap1 >> simp[]) >> simp[] >>
   irule fVar_prpl_fprpl >> rw[] (* 4 *)
   >- metis_tac[] >- metis_tac[] >> metis_tac[])
>- gs[FDOM_o_fVmap] 
>- (rw[fVar_prpl_def] (* 2 *)
   >- (gs[FDOM_o_fVmap] >>
      drule_all_then assume_tac FAPPLY_o_fVmap2 >>
      simp[]) >> gs[FDOM_o_fVmap]) >>
gs[FDOM_o_fVmap] >>
rw[fVar_prpl_def] 
QED        



Theorem subfm_refl:
∀f. f ∈ subfm f
Proof
Induct_on ‘f’ >> gs[subfm_def]
QED

           
(*        
Theorem modifV_lemma:
∀f σ bmap.
(∀P sl tl. fVar P sl tl ∈ subfm f ⇒ LENGTH tl = LENGTH sl) ∧
(∀P sl. (P,sl) ∈ FDOM σ ⇒ ok_abs sl ∧
 fbounds (σ ' (P,sl)) ⊆ count (LENGTH sl)) ⇒
fVar_prpl σ (fprpl bmap f) = fprpl bmap (modifV σ bmap f)
Proof
Induct_on ‘f’ >> gs[fprpl_def,fVar_prpl_def,modifV_def,fbounds_thm,subfm_def] >> rw[] (* 6 *)
>- metis_tac[]
>- metis_tac[]
>- metis_tac[]
>- (simp[GSYM rich_listTheory.MAP_REVERSE] >>
   simp[mk_bmap_MAP] >>
   irule fprpl_FMAP_MAP >> simp[FDOM_mk_bmap] >>
   first_x_assum $ drule_then assume_tac >>
   gs[LENGTH_slprpl])
>- (gs[] >> metis_tac[]) >>
gs[] >> rw[fprpl_def]
QED
                              


Definition fVar_eff_on_def:
fVar_eff σ (P,sl) = if (P,sl) ∈ FDOM σ then σ ' (P,sl) else fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
End



        
                 
Theorem fVar_prpl_eq:
∀f σ1 σ2.
 (∀P sl tl. fVar P sl tl ∈ subfm f ⇒ LENGTH sl = LENGTH tl) ∧
 (∀P sl. (P,sl) ∈ freefVars f ⇒ fVar_eff σ1 (P,sl) = fVar_eff σ2 (P,sl)) ⇒
 fVar_prpl σ1 f = fVar_prpl σ2 f
Proof
 Induct_on ‘f’ >>
 simp[fVar_prpl_def] >>
 gs[freefVars_def,subfm_def] >> rw[]
 >- metis_tac[]
 >- metis_tac[]
 >- metis_tac[](* 3 *)
 >- gs[fVar_eff_def]
 >- gs[fVar_eff_def,fprpl_def,MAP_MAP_o] >>
    rw[] (* 2 *)
    >- 

cheat >>
 gs[]
    


    

Theorem foo:
∀f θ1 θ2.
  (∀s l P sl tl. (s,l) ∈ FDOM θ1 ∧
   fVar P sl tl ∈ subfm (θ1 ' (s,l)) ⇒ LENGTH tl = LENGTH sl) ∧
   (∀P sl.
          (P,sl) ∈ FDOM θ2 ⇒
          ok_abs sl ∧ fbounds (θ2 ' (P,sl)) ⊆ count (LENGTH sl)) ⇒
  ∃θ3. ∀P sl. (P,sl) ∈ freefVars f ⇒
            fVar_prpl θ2 (θ1 ' (P,sl)) = θ3 ' (P,sl)
Proof
reverse (Induct_on ‘f’) >> simp[fVar_prpl_def,subfm_def]
>- (rw[] (* 2 *)
   >- (‘∃θ3. (s,l) ∈ FDOM θ3 ∧ fVar_prpl θ2 (fprpl (mk_bmap (REVERSE l0)) (θ1 ' (s,l))) = fprpl (mk_bmap (REVERSE l0)) (θ3 ' (s,l))’
   suffices_by (rw[] >> qexists ‘θ3’ >> simp[]) >> 
   ‘∃ff.fVar_prpl θ2 (fprpl (mk_bmap (REVERSE l0)) (θ1 ' (s,l))) = fprpl (mk_bmap (REVERSE l0)) ff’
     suffices_by
      (rw[] >> qexists ‘TO_FMAP [((s,l),ff)]’ >>
      rw[FDOM_TO_FMAP,TO_FMAP_SING]) >>
   qexists ‘modifV θ2 (mk_bmap (REVERSE l0))
   (θ1 ' (s,l))’ >>
   irule modifV_lemma >> simp[] >> metis_tac[]) >>
   rw[fVar_prpl_def] (* 2 *)
   >- (gs[] >> qexists ‘θ2’ >> simp[]) >>
   qexists ‘TO_FMAP []’ >>
   gs[FDOM_TO_FMAP]) 
>- (rw[] >>
   first_x_assum
    (qspecl_then [‘θ1’,‘θ2’] assume_tac) >>
  first_x_assum $ drule_then assume_tac >>
  ‘(∀P sl. (P,sl) ∈ FDOM θ2 ⇒ ok_abs sl)’
   by metis_tac[] >>
  first_x_assum $ drule_then assume_tac >>
  gs[] >>
 qexists ‘θ3’ >> rw[fVar_prpl_def] (* 2 *)
 >- (rw[fVar_prpl_def] >>
    first_x_assum irule >> rw[subfm_refl]) >>
 first_x_assum irule >> simp[]) >>
rw[] >>
first_x_assum $ drule_all_then assume_tac >>
last_x_assum $ drule_all_then assume_tac >>
gs[] >>
qexists ‘FUNION θ3 θ3'’ >> rw[] (* 3 *)
>- rw[fVar_prpl_def] (* 2 *)
   >- first_x_assum $ qspecl_then [‘f’] assume_tac>>
      gs[subfm_refl] >>
      ‘∀P sl tl. fVar P sl tl ∈ subfm f ⇒
       fVar_prpl θ3 (fVar P sl tl) =
       fVar_prpl θ3' (fVar P sl tl)’
       by rw[] >> 


    
Theorem foo:
∀f θ1 θ2.
  (∀s l P sl tl. (s,l) ∈ FDOM θ1 ∧
   fVar P sl tl ∈ subfm (θ1 ' (s,l)) ⇒ LENGTH tl = LENGTH sl) ∧
   (∀P sl.
          (P,sl) ∈ FDOM θ2 ⇒
          ok_abs sl ∧ fbounds (θ2 ' (P,sl)) ⊆ count (LENGTH sl)) ⇒
  ∃θ3. ∀f0. f0 ∈ subfm f ⇒
            fVar_prpl θ2 (fVar_prpl θ1 f0) = fVar_prpl θ3 f0
Proof
reverse (Induct_on ‘f’) >> simp[fVar_prpl_def,subfm_def]
>- (rw[] (* 2 *)
   >- (‘∃θ3. (s,l) ∈ FDOM θ3 ∧ fVar_prpl θ2 (fprpl (mk_bmap (REVERSE l0)) (θ1 ' (s,l))) = fprpl (mk_bmap (REVERSE l0)) (θ3 ' (s,l))’
   suffices_by (rw[] >> qexists ‘θ3’ >> simp[]) >> 
   ‘∃ff.fVar_prpl θ2 (fprpl (mk_bmap (REVERSE l0)) (θ1 ' (s,l))) = fprpl (mk_bmap (REVERSE l0)) ff’
     suffices_by
      (rw[] >> qexists ‘TO_FMAP [((s,l),ff)]’ >>
      rw[FDOM_TO_FMAP,TO_FMAP_SING]) >>
   qexists ‘modifV θ2 (mk_bmap (REVERSE l0))
   (θ1 ' (s,l))’ >>
   irule modifV_lemma >> simp[] >> metis_tac[]) >>
   rw[fVar_prpl_def] (* 2 *)
   >- (gs[] >> qexists ‘θ2’ >> simp[]) >>
   qexists ‘TO_FMAP []’ >>
   gs[FDOM_TO_FMAP]) 
>- (rw[] >>
   first_x_assum
    (qspecl_then [‘θ1’,‘θ2’] assume_tac) >>
  first_x_assum $ drule_then assume_tac >>
  ‘(∀P sl. (P,sl) ∈ FDOM θ2 ⇒ ok_abs sl)’
   by metis_tac[] >>
  first_x_assum $ drule_then assume_tac >>
  gs[] >>
 qexists ‘θ3’ >> rw[fVar_prpl_def] (* 2 *)
 >- (rw[fVar_prpl_def] >>
    first_x_assum irule >> rw[subfm_refl]) >>
 first_x_assum irule >> simp[]) >>
rw[] >>
first_x_assum $ drule_all_then assume_tac >>
last_x_assum $ drule_all_then assume_tac >>
gs[] >>
qexists ‘FUNION θ3 θ3'’ >> rw[] (* 3 *)
>- rw[fVar_prpl_def] (* 2 *)
   >- first_x_assum $ qspecl_then [‘f’] assume_tac>>
      gs[subfm_refl] >>
      ‘∀P sl tl. fVar P sl tl ∈ subfm f ⇒
       fVar_prpl θ3 (fVar P sl tl) =
       fVar_prpl θ3' (fVar P sl tl)’
       by rw[] >> 
      
 
‘∀P sl. (P,sl) ∈ FDOM θ3 ∩ FDOM θ3' ∩
        freefVars ⇒
 θ3 ' (P,sl) = θ3' ' (P,sl) ’
 
 
          
Theorem foo:
∀f θ1 θ2.
  ∃θ3. ∀f0. f0 ∈ subfm f ⇒
            fVar_prpl θ2 (fVar_prpl θ1 f0) = fVar_prpl θ3 f0
Proof
Induct_on ‘f’ >> simp[fVar_prpl_def,subfm_def]
(* 2 *)
>- cheat >>
rw[] >> 
first_x_assum (qspecl_then [‘θ1’,‘θ2’] assume_tac)>>
pop_assum strip_assume_tac >>
qexists ‘θ3’ >> rw[] >>

        
rw[fVar_prpl_def] >> first_x_assum irule
  rw[] >> gs[] (* 3 *)

  
>- ‘∃θ3. (s,l) ∈ FDOM θ3 ∧ fVar_prpl θ2 (fprpl (mk_bmap (REVERSE l0)) (θ1 ' (s,l))) = fprpl (mk_bmap (REVERSE l0)) (θ3 ' (s,l))’
   suffices_by (rw[] >> qexists ‘θ3’ >> simp[]) >> 
   ‘∃ff.fVar_prpl θ2 (fprpl (mk_bmap (REVERSE l0)) (θ1 ' (s,l))) = fprpl (mk_bmap (REVERSE l0)) ff’
     suffices_by
      (rw[] >> qexists ‘TO_FMAP [((s,l),ff)]’ >>
      rw[FDOM_TO_FMAP,TO_FMAP_SING]) >>
   qexists ‘modifV θ2 (mk_bmap (REVERSE l0))
   (θ1 ' (s,l))’ >>
   irule modifV_lemma >> 


cheat >>
   qabbrev_tac ‘f0 = θ1 ' (s,l)’ >>


*)

        
Definition fVmap_rename_def:
fVmap_rename (n,s) nn σ =
FUN_FMAP (λ(P,sl). frename (n,s) nn (σ ' (P,sl)))
(FDOM σ)
End

        
        
Theorem fVar_prpl_id:
∀f ε. FDOM ε ∩ freefVars f = {} ⇒
 fVar_prpl ε f = f
Proof
Induct_on ‘f’ >> gs[fVar_prpl_def,freefVars_def] (* 2 *)
>- (rw[] (* 2 *) >>
    (first_x_assum irule >> gs[EXTENSION] >> metis_tac[]))>>
rw[] >> gs[EXTENSION]    
QED
        



Theorem FDOM_fVmap_rename:
FDOM (fVmap_rename (n,s) nn σ) = FDOM σ
Proof
rw[fVmap_rename_def]
QED 

Theorem FAPPLY_fVmap_rename:
(P,sl) ∈ FDOM σ ⇒
(fVmap_rename (n,s) nn σ) ' (P,sl) =
frename (n,s) nn (σ ' (P,sl))
Proof
rw[fVmap_rename_def,FUN_FMAP_DEF]  
QED

Theorem fVar_prpl_fabs:
∀f i.
 (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧
 (∀P sl.
    (P,sl) ∈ freefVars f ∩ FDOM σ ⇒
    (nn,s) ∉ ffv (σ ' (P,sl)) ∧
    (∀st. MEM st sl ⇒ (n,s) ∉ sfv st ∧ (nn,s) ∉ sfv st)) ∧
 (nn,s) ∉ ffv f ∧
 nn ≠ n ⇒
(fVar_prpl σ (fabs (n,s) i f)) =
       frename (nn,s) n
       (fabs (n,s) i (fVar_prpl (fVmap_rename (n,s) nn σ)
                   f))
Proof
Induct_on ‘f’ >>
simp[fVar_prpl_def,fabs_def,frename_alt,PULL_EXISTS](* 4 *)
>- (rw[MAP_EQ_f,MAP_MAP_o] >>
    rw[Once EQ_SYM_EQ] >>
    irule $ cj 1 trename_fix >>
    ‘tfv (tabs (n,s) i e) ⊆ tfv e DELETE (n,s)’
     by (irule $ cj 1 tfv_tabs_SUBSET >> metis_tac[]) >>
    CCONTR_TAC >> gs[] >>
    ‘(nn,s) ∈ tfv e DELETE (n,s)’ by metis_tac[SUBSET_DEF]>>
    gs[] >> metis_tac[])
>- (rw[freefVars_def] (* 2 *) >>
   (first_x_assum irule >> simp[] >> rw[] (* 3 *)
   >- metis_tac[]
   >- metis_tac[]
   >- metis_tac[])) 
>- (rw[] (* 2 *)
   >- (rw[Once EQ_SYM_EQ] >>
      irule $ cj 2 trename_fix >>
      ‘(nn,s) ∉ sfv s' DELETE (n,s)’
        suffices_by metis_tac[tfv_tabs_SUBSET,SUBSET_DEF] >>
      gs[]) >>
   ‘fVar_prpl σ (fabs (n,s) (i +1) f) =
            frename (nn,s) n
              (fabs (n,s) (i+1) (fVar_prpl (fVmap_rename (n,s) nn σ) f))’
    by (first_x_assum irule >> gs[freefVars_def] >>
       metis_tac[])) >>
rw[] (* 4 *)
>- (rw[GSYM rich_listTheory.MAP_REVERSE,mk_bmap_MAP] >>
    ‘(fVmap_rename (n,s) nn σ ' (s',l)) =
     frename (n,s) nn (σ ' (s',l))’
     by (irule FAPPLY_fVmap_rename >> gs[FDOM_fVmap_rename])
     >> gs[] >>
    ‘abssl (n,s) i l = l’
    by (irule abssl_id >>
       drule_at_then Any assume_tac $ iffLR abssl_ok_abs >>
    metis_tac[]) >> gs[] >> 
   irule fprpl_FMAP_MAP_fabs_IN >> simp[FDOM_mk_bmap] >>
   rw[] (* 3 *)
   >- (‘b < LENGTH (REVERSE l0)’ by simp[] >>
      drule_then assume_tac FAPPLY_mk_bmap >>
      gs[] >> ‘MEM (EL b (REVERSE l0)) l0’
      suffices_by metis_tac[] >>
      drule_then assume_tac EL_REVERSE >> simp[] >>
      simp[MEM_EL] >>
      irule_at Any EQ_REFL >> simp[]) 
   >- (‘b < LENGTH (REVERSE l0)’ by simp[] >>
drule_then assume_tac FAPPLY_mk_bmap >>
      gs[] >> ‘MEM (EL b (REVERSE l0)) l0’
      suffices_by metis_tac[] >>
      drule_then assume_tac EL_REVERSE >> simp[] >>
      simp[MEM_EL] >>
      irule_at Any EQ_REFL >> simp[])
   >- gs[freefVars_def])
>-(gs[FDOM_fVmap_rename] (* 2 *)
>- (‘abssl (n,s) i l = l’ suffices_by metis_tac[] >>
   ‘ok_abs l’ by metis_tac[ok_abs_abssl] >> gs[] >>
    irule abssl_id >>
    drule_at_then Any assume_tac $ iffLR abssl_ok_abs >>
    metis_tac[]) >> (*maybe lemma ok_abs abs and itself ⇒abs are equal*)
metis_tac[ok_abs_abssl])
>- (gs[FDOM_fVmap_rename] (* 2 *)
   >> (‘abssl (n,s) i l = l’ suffices_by metis_tac[] >>
   gs[freefVars_def] >> irule abssl_id >> metis_tac[])) >>
rw[fabs_def,frename_alt] (* 2 *)
>- (rw[Once EQ_SYM_EQ,MAP_fix] >>
   rw[Once EQ_SYM_EQ] >> irule $ cj 2 trename_fix >>
   pop_assum mp_tac >> simp[MEM_EL] >> rw[LENGTH_abssl] >>
   drule_then assume_tac abssl_EL >> simp[] >>
   ‘(nn,s) ∉ sfv (EL n' l)’ by metis_tac[MEM_EL] >>
   ‘sfv (sabs (n,s) (i+n') (EL n' l)) ⊆
     sfv (EL n' l) DELETE (n,s)’
     by (irule $ cj 2 tfv_tabs_SUBSET >>
         metis_tac[MEM_EL]) >>
  pop_assum mp_tac >> rw[SUBSET_DEF] >> metis_tac[]) >>
rw[Once EQ_SYM_EQ,MAP_fix] >>
pop_assum mp_tac >> simp[MEM_MAP] >>
rw[] >> rw[Once EQ_SYM_EQ] >> irule $ cj 1 trename_fix >>
‘(nn,s) ∉ tfv y’ by metis_tac[] >>
‘tfv (tabs (n,s) i y) ⊆ tfv y DELETE (n,s)’
 by (irule $ cj 1 tfv_tabs_SUBSET >>
    metis_tac[]) >>
pop_assum mp_tac >> rw[SUBSET_DEF] >> metis_tac[]    
QED


Definition fVmap_eff_def:
fVmap_eff σ (P,sl) = if (P,sl) ∈ FDOM σ then σ ' (P,sl) else
 fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
End



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


Theorem fVar_prpl_eq_lemma:
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
                   
Theorem fVar_prpl_eq:
∀f σ1 σ2.
 (∀P sl tl. fVar P sl tl ∈ subfm f ⇒ LENGTH sl = LENGTH tl) ∧
 (∀P sl. (P,sl) ∈ freefVars f ⇒ fVmap_eff σ1 (P,sl) = fVmap_eff σ2 (P,sl)) ⇒
 fVar_prpl σ1 f = fVar_prpl σ2 f
Proof
 Induct_on ‘f’ >>
 simp[fVar_prpl_def] >>
 gs[freefVars_def,subfm_def] >> rw[]
 >- metis_tac[]
 >- metis_tac[]
 >- metis_tac[](* 3 *)
 >- gs[fVmap_eff_def]
 >- (gs[fVmap_eff_def,fprpl_def,MAP_MAP_o] >>
    rw[] (* 2 *)
    >- (irule ok_abs_slprpl >> simp[]) >>
    simp[fVar_prpl_eq_lemma]) >>
 gs[] >>
 gs[fVmap_eff_def] >>
 qpat_x_assum ‘_ = σ2 ' _’ (assume_tac o GSYM) >>
 simp[] >> rw[fprpl_def]
 >- (rw[Once EQ_SYM_EQ] >> irule ok_abs_slprpl >> simp[]) >>
 rw[Once EQ_SYM_EQ] >>
 gs[fVmap_eff_def,fprpl_def,MAP_MAP_o] >>
 rw[fVar_prpl_eq_lemma]
QED


Theorem freefVars_fprpl_eq:
∀f σ1 σ2.
FDOM σ1 ∩ freefVars f = FDOM σ2 ∩ freefVars f ∧
(∀P sl. (P,sl) ∈ FDOM σ1 ∩ FDOM σ2 ⇒ σ1 ' (P,sl) = σ2 ' (P,sl)) ⇒
fVar_prpl σ1 f = fVar_prpl σ2 f
Proof
Induct_on ‘f’ >> gs[fVar_prpl_def,freefVars_def,UNION_OVER_INTER] (* 2 *)
>- (rw[] (* 2 *)
    >> (first_x_assum irule >>
        gs[EXTENSION] >> metis_tac[])) >>
rw[] (* 2 *)
>> (gs[EXTENSION] >> metis_tac[])
QED

    

Theorem DRESTRICT_freefVars_fprpl_eq:
fVar_prpl (DRESTRICT σ (freefVars f)) f = fVar_prpl σ f
Proof
rw[] >> irule freefVars_fprpl_eq >>
rw[DRESTRICT_DEF] >> gs[EXTENSION] >> metis_tac[]
QED


Theorem freefVars_fabs:
∀f i.
    (∀n1 s1.(n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
    freefVars (fabs (n,s) i f) =
    freefVars f DIFF {(P,sl) | (P,sl) ∈ freefVars f ∧
    ∃st. MEM st sl ∧ (n,s) ∈ sfv st}
Proof
metis_tac[fabs_abs,freefVars_abs]
QED                    

Theorem NOTIN_freefVars_fabs:
(∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒ 
∀P sl. (P,sl) ∈ freefVars (fabs (n,s) i f) ⇒
(∀st. MEM st sl ⇒ (n,s) ∉ sfv st)
Proof
rw[] >> drule_then assume_tac freefVars_fabs >>
gs[] >> metis_tac[]
QED

Theorem fVar_prpl_fabs1:
∀f i σ.
       (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ∧ 
       (∀P sl st. (P,sl) ∈ FDOM σ ∩ freefVars f ∧ MEM st sl ⇒ (n,s) ∉ sfv st) ∧
       (∀P sl. (P,sl) ∈ FDOM σ ∩ freefVars f⇒
        (n,s) ∉ ffv (σ ' (P,sl))) ⇒
       fVar_prpl σ (fabs (n,s) i f) =
       fabs (n,s) i (fVar_prpl σ f)
Proof
Induct_on ‘f’ >> rw[] (* 5 *)
>- rw[fabs_def,fVar_prpl_def]
>- gs[fabs_def,fVar_prpl_def,freefVars_def]
>- (gs[fabs_def,fVar_prpl_def,freefVars_def] (* 2 *) >>
   rw[] (* 2 *)
   >>first_x_assum irule >> metis_tac[])
>- (gs[fabs_def,fVar_prpl_def,freefVars_def] >>
   metis_tac[]) >>
gs[fabs_def,fVar_prpl_def,freefVars_def] >> rw[] (* 4 *)
>- (rw[mk_bmap_MAP,GSYM rich_listTheory.MAP_REVERSE] >>
     ‘abssl (n,s) i l = l’
    by (irule abssl_id >> gs[]) >>
   gs[] >>
    metis_tac[fprpl_mk_bmap_abs])
>- (drule_at_then Any assume_tac ok_abs_abssl >> gs[] >>
    ‘ok_abs l’ by metis_tac[] >> gs[] >>
    ‘abssl (n,s) i l = l’ suffices_by metis_tac[] >>
    irule abssl_id >>
    drule_at_then Any assume_tac $ iffLR abssl_ok_abs >>
    metis_tac[])
>- (gs[] (* 2 *)
   >> (‘abssl (n,s) i l = l’ suffices_by metis_tac[] >>
    irule abssl_id >> metis_tac[])) >>
rw[fabs_def]
QED


(*
Theorem ffv_fVar_subst':
∀f P sl ϕ.
(∀n s. (n,s) ∈ ffv ϕ ⇒ sbounds s = ∅) ⇒
ffv (fVar_subst (P,sl,ϕ) f) ⊆
ffv f ∪ ffv ϕ
Proof
Induct_on ‘f’ >>
gs[freefVars_def,fVar_subst_def,ffv_thm] (* 3 *) >> rw[](*7*)
>- (first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >> metis_tac[])
>-  (first_x_assum $ drule_then assume_tac >>
      gs[SUBSET_DEF] >> metis_tac[]) 
>-(first_x_assum $ drule_then assume_tac >>
      gs[SUBSET_DEF] >> metis_tac[])
>- (first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >> metis_tac[])
>- drule_then assume_tac ffv_fprpl >>
   rw[] >> simp[FDOM_mk_bmap] >>
   cheat 
>- rw[SUBSET_DEF] >>
rw[SUBSET_DEF]
QED
*)        

Theorem ffv_fVar_prpl:
∀f σ.
  (∀P sl n s.(P,sl) ∈ FDOM σ ∩ freefVars f ⇒
             (n,s) ∈ ffv (σ ' (P,sl)) ⇒ sbounds s = ∅)  ⇒
  ffv (fVar_prpl σ f) ⊆
  ffv f ∪ BIGUNION {ffv (σ ' (P,sl)) | (P,sl) | (P,sl) ∈ FDOM σ ∩ freefVars f}
Proof
Induct_on ‘f’ >>
gs[freefVars_def,fVar_prpl_def,ffv_thm] (* 3 *) >> rw[] (* 7*)
>- (‘ffv (fVar_prpl σ f) ⊆
            ffv f ∪
            BIGUNION
              {ffv (σ ' (P,sl)) |
               (P,sl) |
               (P,sl) ∈ FDOM σ ∧ (P,sl) ∈ freefVars f}’
   suffices_by (rw[SUBSET_DEF] >> metis_tac[]) >>
   first_x_assum irule >>
   metis_tac[])
>-  (‘ffv (fVar_prpl σ f') ⊆
            ffv f' ∪
            BIGUNION
              {ffv (σ ' (P,sl)) |
               (P,sl) |
               (P,sl) ∈ FDOM σ ∧ (P,sl) ∈ freefVars f'}’
   suffices_by (rw[SUBSET_DEF] >> metis_tac[]) >>
   first_x_assum irule >>
   metis_tac[])
>- rw[SUBSET_DEF]
>- (first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >> metis_tac[])
>- (drule_then assume_tac ffv_fprpl >>
   simp[] >>
   rw[] (* 2 *)
   >- (rw[SUBSET_DEF] >>
   ‘{tfv (mk_bmap (REVERSE l0) ' i) |
           i |
           i ∈ FDOM (mk_bmap (REVERSE l0)) ∧ i ∈ fbounds (σ ' (s,l))} ⊆ {tfv t | MEM t l0}’
    suffices_by
    (rw[] >>
    ‘BIGUNION {tfv (mk_bmap (REVERSE l0) ' i) |
         i |
         i ∈ FDOM (mk_bmap (REVERSE l0)) ∧ i ∈ fbounds (σ ' (s,l))} ⊆
        BIGUNION {tfv t | MEM t l0}’ by
    metis_tac[SUBSET_BIGUNION] >>
    gs[SUBSET_DEF] >> metis_tac[]) >>
    rw[SUBSET_DEF] >>
    qexists ‘(mk_bmap (REVERSE l0) ' i)’ >>
    simp[] >> simp[MEM_EL] >>
    gs[FDOM_mk_bmap]>>
    ‘i < LENGTH (REVERSE l0)’ by simp[] >>
    drule_then assume_tac FAPPLY_mk_bmap >> simp[] >>
    rev_drule_then assume_tac EL_REVERSE >>
    simp[] >>
    irule_at Any EQ_REFL >>
    simp[]) >>
    ‘{tfv (mk_bmap (REVERSE l0) ' i) |
           i |
           i ∈ FDOM (mk_bmap (REVERSE l0)) ∧ i ∈ fbounds (σ ' (s,l))} ⊆ {tfv t | MEM t l0}’
    suffices_by
    (rw[] >>
    ‘BIGUNION {tfv (mk_bmap (REVERSE l0) ' i) |
         i |
         i ∈ FDOM (mk_bmap (REVERSE l0)) ∧ i ∈ fbounds (σ ' (s,l))} ⊆
        BIGUNION {tfv t | MEM t l0}’ by
    metis_tac[SUBSET_BIGUNION] >>
    gs[SUBSET_DEF] >> metis_tac[]) >>
    rw[SUBSET_DEF] >>
    qexists ‘(mk_bmap (REVERSE l0) ' i)’ >>
    simp[] >> simp[MEM_EL] >>
    gs[FDOM_mk_bmap]>>
    ‘i < LENGTH (REVERSE l0)’ by simp[] >>
    drule_then assume_tac FAPPLY_mk_bmap >> simp[] >>
    rev_drule_then assume_tac EL_REVERSE >>
    simp[] >>
    irule_at Any EQ_REFL >>
    simp[])
>- rw[SUBSET_DEF] >>
rw[SUBSET_DEF]    
QED        
       
        


Theorem sbounds_frename_EMPTY:
(∀n s. (n,s) ∈ ffv f ⇒ sbounds s = {}) ⇒
(∀n s. (n,s) ∈ ffv (frename (n0,s0) nn f) ⇒ sbounds s = {})
Proof
  rw[] >> CCONTR_TAC >>
  ‘∃i. i ∈ sbounds s’
    by metis_tac[MEMBER_NOT_EMPTY] >>
  ‘i ∈ BIGUNION (IMAGE (sbounds o SND)
                 (ffv (frename (n0,s0) nn f)))’
              by (rw[IMAGE_DEF,PULL_EXISTS] >>
                  qexists ‘(n,s)’ >> simp[]) >>
   ‘BIGUNION (IMAGE (sbounds ∘ SND) (ffv (frename (n0,s0) nn f))) = BIGUNION (IMAGE (sbounds ∘ SND) (ffv f))’
            by metis_tac[BIGUNION_IMAGE_sbounds_ffv] >>         ‘BIGUNION (IMAGE (sbounds ∘ SND) (ffv f)) = {}’
            suffices_by (strip_tac >> gs[] >> gs[EXTENSION]>>
             metis_tac[])  >>
  rw[Once EXTENSION] >>
  Cases_on ‘ (∀x. x ∉ ffv f)’ >> simp[] >>
  simp[Once EXTENSION,IMAGE_DEF] >> 
  rw[] >>
  rw[EQ_IMP_THM] (* 2 *)
  >- (Cases_on ‘x'’ >> simp[] >> metis_tac[]) >>
  gs[] >> qexists ‘x'’ >> simp[] >>
  Cases_on ‘x'’ >> simp[] >> metis_tac[]          
QED 

            
Theorem fVars_fabs:
 ∀f v. v ∉ fVslfv f ⇒ ∀i. fVars (fabs v i f) = fVars f
Proof 
 Induct_on ‘f’ >> gs[fVslfv_def,fabs_def,fVars_def] >>
 cheat
QED
 
Theorem wff_fVar_prpl:
(∀fsym.
        isfsym (Σf:string |-> sort # (string # sort) list)
         fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
∀f. wff (Σf,Σp) f ⇒
    ∀ε. (∀P:string sl. (P,sl) ∈ FDOM ε ⇒  wff (Σf,Σp) (FALLL sl (ε ' (P, sl)))) ⇒
    wff (Σf,Σp) (fVar_prpl ε f)
Proof
Induct_on ‘wff’ >> rw[fVar_prpl_def,wff_rules] (* 2 *)       
>- (Cases_on ‘(P,sl) ∈ FDOM ε’ >> simp[] (* 2 *)
   >- (drule_then assume_tac wfabsap_ok_abs >> simp[] >>
      gvs[] >>
      assume_tac (GEN_ALL $ SRULE [] wff_fVar_subst_lemma) >>
      first_x_assum $ drule_then assume_tac >>
      metis_tac[]) >>
   simp[wff_rules]) >>
rw[mk_FALL_def,fVar_prpl_def] >>
first_x_assum $ drule_then assume_tac >>

qabbrev_tac ‘σ1 = DRESTRICT ε (freefVars f)’ >>
‘FDOM σ1 = FDOM ε ∩ freefVars f’ by simp[DRESTRICT_DEF,Abbr‘σ1’] >>
qabbrev_tac ‘σ = DRESTRICT ε (freefVars (abst (n,s) f))’ >>
‘wff (Σf,Σp) (FALL s (fVar_prpl σ (abst (n,s) f)))’
 suffices_by
  (‘(fVar_prpl σ (abst (n,s) f)) = (fVar_prpl ε (abst (n,s) f))’ suffices_by metis_tac[] >>
  rw[Abbr‘σ’] >> irule DRESTRICT_freefVars_fprpl_eq) >>
‘FDOM σ = FDOM ε ∩ freefVars (abst (n,s) f)’
 by simp[DRESTRICT_DEF,Abbr‘σ’] >> 
‘∀P sl st. (P,sl) ∈ FDOM σ ∧ MEM st sl ⇒ (n,s) ∉ sfv st’
 by (rw[] >>
    irule NOTIN_freefVars_fabs >>
    first_x_assum $ irule_at Any >>
    gs[abst_def] >>
    first_x_assum $ irule_at Any >>
    metis_tac[]) >>
‘FDOM σ ⊆ FDOM σ1’
 by (simp[] >>
    drule_then assume_tac freefVars_fabs_SUBSET >>
    gs[abst_def,SUBSET_DEF] >> metis_tac[]) >>    
‘∀P sl. (P,sl) ∈ FDOM σ ⇒ σ ' (P,sl) = σ1 ' (P,sl)’
 by (simp[Abbr‘σ’,Abbr‘σ1’,DRESTRICT_DEF] >>
    rw[] >> gs[DRESTRICT_DEF] >> gs[SUBSET_DEF]) >>
‘∀P sl. (P,sl) ∈ FDOM σ1 ⇒ wff (Σf,Σp) (FALLL sl (σ1 ' (P,sl)))’
 by rw[Abbr‘σ1’,DRESTRICT_DEF] >> 
Cases_on ‘∀P sl. (P,sl) ∈ FDOM σ1 ⇒ (n,s) ∉ ffv (σ1 ' (P,sl))’ 
>- (‘fVar_prpl σ (abst (n,s) f) =
     abst (n,s) (fVar_prpl σ f)’ by
     (rw[abst_def] >> irule fVar_prpl_fabs1 >>
     rw[] (* 3 *)
     >- (gs[EXTENSION] >> metis_tac[])
     >- metis_tac[]) >> 
     (*fVar_subst_fabs1*)
    simp[] >> rw[GSYM mk_FALL_def] >>
    irule $ cj 5 wff_rules >> simp[] >>
    rw[] (* 2 *)
    >- (‘ffv (fVar_prpl σ f) ⊆
       ffv f ∪ BIGUNION {ffv (σ ' (P,sl)) | (P,sl)| (P,sl) ∈ FDOM σ ∩ freefVars f}’
        by (irule ffv_fVar_prpl >> rw[] >>
           ‘wff (Σf,Σp) (FALLL sl (σ1 ' (P,sl)))’
            by (first_x_assum irule >> simp[]) >>
            irule wff_FALLL_no_vbound >> metis_tac[]) >>
    gs[SUBSET_DEF,PULL_EXISTS] >>
    first_x_assum $ drule_then assume_tac >>
    gs[] (* 2 *)
    >- (metis_tac[] >>
       ‘(n,s) ∉ ffv (σ1 ' (P,sl))’
         suffices_by
         (strip_tac >> CCONTR_TAC >>
         metis_tac[SUBSET_DEF,sfv_ffv]) >>
        simp[]) >>
    ‘(n,s) ∉ ffv (σ1 ' (P,sl))’
         suffices_by
         (strip_tac >> CCONTR_TAC >>
         metis_tac[SUBSET_DEF,sfv_ffv]) >>
    ‘(P,sl) ∈ freefVars f’ suffices_by metis_tac[] >>
    drule_then assume_tac freefVars_fabs_SUBSET >>
    gs[abst_def])
    >- cheat >>
    first_x_assum irule >>
    metis_tac[SUBSET_DEF]) >>




        
‘∃nn.  (nn,s) ∉ ffv f ∪ BIGUNION {ffv (σ1 ' (P,sl)) | (P,sl) | (P,sl) ∈ FDOM σ1} ∪ BIGUNION {sfv st | (P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM σ1} ∪
     sfv s ∪ {(n,s)}’
  by (‘FINITE (ffv f ∪ BIGUNION {ffv (σ1 ' (P,sl)) | (P,sl) | (P,sl) ∈ FDOM σ1} ∪
          BIGUNION {sfv st | (P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM σ1} ∪
          sfv s ∪ {(n,s)})’
       suffices_by metis_tac[fresh_name_ex] >>
     simp[] >> rw[PULL_EXISTS] (* 2 *)
     >- (‘{ffv (σ1 ' (P,sl)) | (P,sl) ∈ FDOM ε ∧ (P,sl) ∈ freefVars f} = IMAGE (λ(P,sl). ffv (σ1 ' (P,sl)))
       {(P,sl) | (P,sl) ∈ FDOM ε ∧ (P,sl) ∈ freefVars f}’
       by (rw[Once EXTENSION] >> rw[EQ_IMP_THM] (* 2 *)
          >- (simp[PULL_EXISTS] >> metis_tac[]) >>
          qexistsl [‘P’,‘sl’] >> simp[]) >>
      simp[] >> irule IMAGE_FINITE >>
      ‘FINITE (FDOM ε)’ by simp[] >>
      irule SUBSET_FINITE  >>
      first_x_assum $ irule_at Any >>
      rw[SUBSET_DEF] >> simp[]) >>
    ‘{sfv st |
           (P,sl,st) |
           MEM st sl ∧ (P,sl) ∈ FDOM ε ∧ (P,sl) ∈ freefVars f} = IMAGE (sfv o SND o SND)
            {(P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM ε ∧ (P,sl) ∈ freefVars f}’
      by (simp[Once EXTENSION] >> rw[] >>
         rw[EQ_IMP_THM] (* 2 *)
         >> (rw[PULL_EXISTS] >> metis_tac[])) >>
     simp[] >> irule IMAGE_FINITE >>
     ‘{(P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM ε ∧ (P,sl) ∈ freefVars f} ⊆ {P | ∃sl. (P,sl) ∈ freefVars f ∩ FDOM ε} × {sl | ∃P. (P,sl) ∈ freefVars f ∩ FDOM ε} × {st | ∃P sl. (P,sl) ∈ FDOM ε ∩ freefVars f ∧ MEM st sl}’
      by (rw[SUBSET_DEF] >> simp[] >> metis_tac[]) >>
      irule SUBSET_FINITE >>
      first_x_assum $ irule_at Any >>
      irule FINITE_CROSS >> rw[] (* 2 *)
      >- (‘{P | (∃sl. (P,sl) ∈ freefVars f ∧ (P,sl) ∈ FDOM ε)} = IMAGE FST (freefVars f ∩ FDOM ε)’
          by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM]
             >- (qexists ‘(x,sl)’ >> simp[]) >>
             qexists ‘SND x'’ >> simp[]) >>
         simp[] >> irule IMAGE_FINITE >>
         irule SUBSET_FINITE >> qexists ‘FDOM ε’ >>
         simp[]) >>
     disj2_tac >> disj2_tac >> rw[] (* 2 *)
     >- (‘{sl | (∃P. (P,sl) ∈ freefVars f ∧ (P,sl) ∈ FDOM ε)} = IMAGE SND (freefVars f ∩ FDOM ε)’
          by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM]
             >- (qexists ‘(P,x)’ >> simp[]) >>
             qexists ‘FST x'’ >> simp[]) >>
         simp[] >> irule IMAGE_FINITE >>
         irule SUBSET_FINITE >> qexists ‘FDOM ε’ >>
         simp[]) >>
     ‘{st | (∃P sl. ((P,sl) ∈ FDOM ε ∧ (P,sl) ∈ freefVars f) ∧ MEM st sl)} =
     BIGUNION {set sl | ∃P. (P,sl) ∈ FDOM ε ∩ freefVars f}’
     by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] >>
        metis_tac[]) >>
     simp[PULL_EXISTS] >>
     ‘{set sl | (∃P. (P,sl) ∈ FDOM ε ∧ (P,sl) ∈ freefVars f)} = IMAGE (set o SND) (FDOM ε ∩ freefVars f)’
       by (rw[Once EXTENSION,PULL_EXISTS,EQ_IMP_THM] (* 2 *)
          >- (qexists ‘(P,sl)’ >> simp[]) >>
          qexistsl [‘SND x'’,‘FST x'’] >> simp[]) >>
     simp[]) >>


     
‘nn ≠ n’ by (CCONTR_TAC >> gs[]) >> 
‘(fVar_prpl σ (abst (n,s) f)) =
 frename (nn,s) n
       (fabs (n,s) 0 (fVar_prpl (fVmap_rename (n,s) nn σ)
                   f))’
by (rw[abst_def] >> irule fVar_prpl_fabs >>
   rw[] (* 5 *)
   >- (‘(nn,s) ∉
        BIGUNION {ffv (σ1 ' (P,sl)) | (P,sl) | (P,sl) ∈ FDOM σ1}’
        by gs[] >>
       gs[] >> metis_tac[])
   >- (first_x_assum irule >> simp[] >>
      metis_tac[])
   >- (‘(nn,s) ∉
        BIGUNION {sfv st | (P,sl,st) | MEM st sl ∧ (P,sl) ∈ FDOM σ1}’  by gs[] >>
      gs[] >> metis_tac[])
   >- metis_tac[SUBSET_DEF,sfv_ffv]
   >- gs[]) >>
   
simp[] >> rw[GSYM abst_def] >> 
‘(FALL s
             (frename (nn,s) n
                (abst (n,s) (fVar_prpl (fVmap_rename (n,s) nn σ) f)))) =
    (FALL (srename (nn,s) n s)
             (frename (nn,s) n
                (abst (n,s) (fVar_prpl (fVmap_rename (n,s) nn σ) f))))’
     by (rw[] >> rw[Once EQ_SYM_EQ] >>
         irule  $ cj 2 trename_fix >> gs[]) >>
simp[] >> rw[GSYM frename_alt] >>
irule wff_frename >> simp[] >>
rw[GSYM mk_FALL_def] >> irule $ cj 5 wff_rules >>
simp[] >> rw[]
>- (‘ffv (fVar_prpl (fVmap_rename (n,s) nn σ) f) ⊆
       ffv f ∪
       BIGUNION {ffv ((fVmap_rename (n,s) nn σ) ' (P,sl)) | (P,sl) | (P,sl) ∈ FDOM (fVmap_rename (n,s) nn σ) ∩ freefVars f}’ by (irule ffv_fVar_prpl >>
      rw[] >> gs[FDOM_fVmap_rename] >>
      ‘(fVmap_rename (n,s) nn σ ' (P,sl))=
      frename (n,s) nn (σ ' (P,sl))’
       by (irule FAPPLY_fVmap_rename >> simp[]) >>
      gs[] >> irule sbounds_frename_EMPTY  >>
      first_x_assum $ irule_at Any >>
      rw[] >> irule wff_FALLL_no_vbound >>
      first_x_assum $ irule_at Any >>
      metis_tac[]) >>
  pop_assum mp_tac >> simp[SUBSET_DEF] >> rw[] >>
  first_x_assum $ drule_then assume_tac >>
  gs[] (* 2 *)
  >- metis_tac[] >>
  rename [‘ (P,sl) ∈ freefVars f’] >>
  gs[FDOM_fVmap_rename] >> 
   ‘(fVmap_rename (n,s) nn σ ' (P,sl))=
      frename (n,s) nn (σ ' (P,sl))’
       by (irule FAPPLY_fVmap_rename >> simp[]) >>
  gs[] >> drule_then assume_tac NOTIN_frename >>
  metis_tac[SUBSET_DEF,sfv_ffv])
>- cheat
   (*‘fVslfv (fVar_prpl (fVmap_rename (n,s) nn σ) f) =
    ofFMAP fVslfv (fVmap_rename (n,s) nn σ)
           ()’
   >> *) >>
first_x_assum irule >>
simp[FDOM_fVmap_rename] >>
rw[] >>
‘(fVmap_rename (n,s) nn σ ' (P,sl))=
      frename (n,s) nn (σ ' (P,sl))’
       by (irule FAPPLY_fVmap_rename >> simp[]) >>
simp[]>> 
‘frename (n,s) nn (FALLL sl (σ1 ' (P,sl))) =
 (FALLL (MAP (srename (n,s) nn) sl) (frename (n,s) nn (σ1 ' (P,sl))))’
 by simp[frename_FALLL] >>
‘(MAP (srename (n,s) nn) sl) = sl’
  by  (rw[MAP_fix] >> irule $ cj 2 trename_fix >>
      drule_then assume_tac NOTIN_freefVars_fabs>>
      gs[abst_def] >> metis_tac[]) >>
gs[] >>
qpat_x_assum ‘_ = FALLL _ _’ (assume_tac o GSYM) >> simp[] >>
irule wff_frename >> simp[] >>
first_x_assum irule >> simp[] >>
drule_then assume_tac freefVars_fabs_SUBSET >>
metis_tac[SUBSET_DEF,abst_def]
QED   


        
