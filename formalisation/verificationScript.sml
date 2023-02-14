open HolKernel Parse boolLib bossLib;
open stringTheory pred_setTheory listTheory;
open finite_mapTheory;
val _ = new_theory "verification";


Datatype: term = Var string sort | Fn string (term list);
          sort = St string (term list)
End


Datatype:
  form = False
       | Pred string (term list)
       | IMP form form
       | FALL string sort form
       | fVar string ((string # sort) list) (term list)
End

(* one key fact that we can remove the sort parameter of Fn is that this slot, though can have other terms, cannot have extra variables. 
*)

Definition tfv_def:
  tfv (Var n s) = {(n,s)} ∪ sfv s ∧
  tfv (Fn n tl) = BIGUNION (set (MAP tfv tl)) ∧
  sfv (St n tl) = BIGUNION (set (MAP tfv tl))
Termination
WF_REL_TAC ‘measure (λs. case s of INL t => term_size t
                                | INR s => sort_size s)’                        
End

Definition ffv_def[simp]:
  ffv False = {} ∧
  ffv (Pred p tl) = BIGUNION (set (MAP tfv tl)) ∧
  ffv (fVar p _ tl) = BIGUNION (set (MAP tfv tl)) ∧
  ffv (FALL n s f) = ffv f DELETE (n,s) ∧
  ffv (IMP f1 f2) = ffv f1 ∪ ffv f2
End

val original_tm_induction =
TypeBase.induction_of ``:term``
  
Theorem better_tm_induction =
TypeBase.induction_of ``:term``
|> Q.SPECL [‘Pt’,‘Ps’,‘λtl. ∀t. MEM t tl ⇒ Pt t’]
|> SRULE [DISJ_IMP_THM,FORALL_AND_THM]
|> UNDISCH_ALL
|> (fn th => CONJ (cj 1 th) (cj 2 th))
|> DISCH_ALL
|> Q.GENL [‘Pt’,‘Ps’] 
 
Theorem tfv_thm[simp]:
  tfv (Var n s) = {(n,s)} ∪ sfv s ∧
  tfv (Fn n tl) = BIGUNION {tfv t | MEM t tl} ∧
  sfv (St n tl) = BIGUNION  {tfv t | MEM t tl}
Proof
  simp[tfv_def,PULL_EXISTS] >> simp[Once EXTENSION,PULL_EXISTS,MEM_MAP]  
QED




Definition tinst_def[simp]:
  (tinst (σ:string # sort |-> term) (Var n s) =
   if (n,s) ∉ FDOM σ then Var n (sinst σ s)
   else σ ' (n,s)) ∧
  (tinst σ (Fn f tl) =  Fn f (MAP (tinst σ) tl)) ∧
  sinst σ (St n tl) = St n (MAP (tinst σ) tl)
Termination
  WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,t) => term_size t
         | INR (_,s) => sort_size s)’ 
End            

Definition finput_def:
  finput Σf f = SND  (Σf ' f)
End


Definition foutput_def:
  foutput Σf f = FST (Σf ' f)
End

(*                                       
Definition fsig_size_def:
  fsig_size Σf =
End  
*)



(*

Definition tmatch_def:
  (tmatch Σf (lcs:string # sort -> bool) (Var n s) ct (f:string # sort |-> term) =
   if  (n,s) ∈ lcs then
     if Var n s = ct then SOME f else NONE
   else 
     if (n,s) ∈ FDOM f then
       if ct = f ' (n, s) then SOME f else NONE
     else
       let cs =
           (case ct of
             (Var name sort) => sort
           | Fn fname arg =>
               sinst (THE (tlmatch Σf {} (MAP (UNCURRY Var) (finput Σf fname)) arg FEMPTY)) (foutput Σf fname))
       in
       case smatch Σf lcs s cs f of
         SOME f0 => SOME (f0 |+ ((n, s),ct))
       | _ => NONE) ∧
  (tmatch Σf lcs (Fn f1 tl1) (Fn f2 tl2) f =
   if f1 = f2 then tlmatch Σf lcs tl1 tl2 f else NONE) ∧
  (tmatch Σf lcs (Fn _ _ ) (Var _ _)  f = NONE) ∧
  (smatch Σf (lcs:string # sort -> bool) (St n1 tl1) (St n2 tl2) f =
   if n1 = n2 then tlmatch Σf lcs tl1 tl2 f else NONE) ∧
  tlmatch Σf lcs [] [] f = SOME f ∧
  tlmatch Σf lcs [] (h :: t) f = NONE ∧
  tlmatch Σf lcs (h :: t) [] f = NONE ∧
  (tlmatch Σf lcs (h1 :: t1) (h2 :: t2) f =
   case tmatch Σf lcs h1 h2 f of
     SOME f1 => tlmatch Σf lcs t1 t2 f1
   | _ => NONE)
Termination
 WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,_,t1,t2,_) => term_size t1 
         | INR (INL (_,_,s1,s2,_)) => sort_size s1
         | INR (INR (_,_,tl1,tl2,_)) => term1_size tl2)’ >>
 
  ‘λx y.
   case (x,y) of
   (INR (INL (_,_,s,cs,_)), INL (_,_,pt,ct,_)) =>
    sort_size s < term_size pt
   | (INR (INR (_,_,ptl,_,_)), INL (_,_,pt,ct2,_)) =>
     term1_size ptl < term_size pt
   | (INR (INR (_,_,ptl,_,_)), INR (INL (_,_,s,cs,_))) =>
     term1_size ptl < sort_size s
   | (INL (_,_,pt,ct,_), INR (INR (_,_,ptl,ctl,_))) =>
     term_size pt < term1_size ptl ∧ term_size ct < term1_size ctl
   | (INR (INR (_,_,ptl1,_,_)),INR (INR (_,_,ptl2,_,_))) =>
     term1_size ptl1 < term1_size ptl2
   | _ => F’ >> simp[]
End

*)

Definition tmatch_def:
  (tmatch Σf (lcs:string # sort -> bool) (Var n s) ct (f:string # sort |-> term) =
   if  (n,s) ∈ lcs then
     if Var n s = ct then SOME f else NONE
   else 
     if (n,s) ∈ FDOM f then
       if ct = f ' (n, s) then SOME f else NONE
     else
       case smatch Σf lcs s (sort_of Σf ct) f of
         SOME f0 => SOME (f0 |+ ((n, s),ct))
       | _ => NONE) ∧
  (tmatch Σf lcs (Fn f1 tl1) (Fn f2 tl2) f =
   if f1 = f2 then tlmatch Σf lcs tl1 tl2 f else NONE) ∧
  (tmatch Σf lcs (Fn _ _ ) (Var _ _)  f = NONE) ∧
  (smatch Σf (lcs:string # sort -> bool) (St n1 tl1) (St n2 tl2) f =
   if n1 = n2 then tlmatch Σf lcs tl1 tl2 f else NONE) ∧
  tlmatch Σf lcs [] [] f = SOME f ∧
  tlmatch Σf lcs [] (h :: t) f = NONE ∧
  tlmatch Σf lcs (h :: t) [] f = NONE ∧
  (tlmatch Σf lcs (h1 :: t1) (h2 :: t2) f =
   case tmatch Σf lcs h1 h2 f of
     SOME f1 => tlmatch Σf lcs t1 t2 f1
   | _ => NONE) ∧
  (sort_of Σf (Var n s) = s) ∧
  (sort_of Σf (Fn fn tl) =
  sinst (THE (tlmatch Σf {} (MAP (UNCURRY Var) (finput Σf fn)) tl FEMPTY)) (foutput Σf fn))
Termination
 WF_REL_TAC
  ‘λx y.
   case (x,y) of
   (INR (INL (_,_,s,cs,_)), INL (_,_,pt,ct,_)) =>
    sort_size s < term_size pt
   | (INR (INR (INL (_,_,ptl,_,_))), INL (_,_,pt,ct2,_)) =>
     term1_size ptl < term_size pt
   | (INR (INR (INL (_,_,ptl,_,_))), INR (INL (_,_,s,cs,_))) =>
     term1_size ptl < sort_size s
   | (INL (_,_,pt,ct,_), INR (INR (INL (_,_,ptl,ctl,_)))) =>
     term_size pt < term1_size ptl ∧ term_size ct < term1_size ctl
   | (INR (INR (INL (_,_,ptl1,_,_))),INR (INR (INL (_,_,ptl2,_,_)))) =>
     term1_size ptl1 < term1_size ptl2
   | (INR (INR (INR (_,ct1))), INL (_,_,pt,ct2,_)) => ct1 = ct2
   | (INR (INR (INL (_,_,ptl,ctl,_))),INR (INR (INR (_,ct)))) =>
     term1_size ctl < term_size ct
   | _ => F’ >> cheat
End
(*
  WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,_,t1,t2,_) => term_size t1 + term_size t2
         | INR (INL (_,_,s1,s2,_)) => sort_size s1 + sort_size s2
         | INR (INR (INL (_,_,tl1,tl2,_))) => term1_size tl1 + term1_size tl2
         | INR (INR (INR (_,t))) => term_size t)’ >>
 simp[]
+ (the whole dictionary,))’ 
previously the following works
      
   WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,t1,t2,_) => term_size t1 + term_size t2 
         | INR (INL (_,s1,s2,_)) => sort_size s1 + sort_size s2
         | INR (INR (_,tl1,tl2,_)) => term1_size tl1 + term1_size tl2)’   >>
   rw[] >> Cases_on ‘ct’ >> rw[]
*)
        
Definition stms_def[simp]:
  stms (St n tl) = tl
End

Theorem tm_induction2 =
        better_tm_induction
          |> Q.SPECL [‘P’,‘λs. ∀t. MEM t (stms s) ⇒ P t’]
          |> SRULE []
          |> cj 1
          |> Q.GEN ‘P’ 

val _ = update_induction tm_induction2;
          
Theorem tfv_FINITE[simp]:
 (∀t. FINITE (tfv t)) ∧ (∀s. FINITE (sfv s))
Proof
 ho_match_mp_tac better_tm_induction >> simp[PULL_EXISTS] >>
 ‘∀l. {tfv t | MEM t l} = IMAGE tfv (set l)’  suffices_by simp[] >>
 simp[EXTENSION]
QED     
        
Theorem ffv_FINITE[simp]:
 ∀f. FINITE (ffv f)
Proof
 Induct_on ‘f’ >> simp[MEM_MAP,PULL_EXISTS]
QED


(*prove under current definition Var n s cannot match any bound variable?
 input is a finite map, not be an option, since we know that it will terminate and will not continue when NONE is hit. 
*)        

Definition ffVar_def[simp]:
  ffVar False = {} ∧
  ffVar (IMP f1 f2) = ffVar f1 ∪ ffVar f2 ∧
  ffVar (FALL n s ϕ) = ffVar ϕ ∧
  ffVar (Pred _ _) = {} ∧
  ffVar (fVar p vl tl) = {(p,vl)}
End   


Theorem ffVar_FINITE[simp]:
 ∀f. FINITE (ffVar f)
Proof
 Induct_on ‘f’ >> simp[MEM_MAP,PULL_EXISTS]
QED

                    
val term_size_def = DB.fetch "-" "term_size_def"
val _ = export_rewrites ["term_size_def"]


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
  EX n s b = NEG (FALL n s (NEG b))
End  


Definition EXL_def:
  EXL [] f = f ∧
  EXL ((n,s) :: t) f = EX n s (EXL t f)
End  


Definition FALLL_def:
  FALLL [] f = f ∧
  FALLL ((n,s) :: t) f = FALL n s (FALLL t f)
End  
     
  
Definition new_psym_def:
  new_psym (fsig,psig) P vl = (fsig,psig |+ (P,vl))
End


Definition new_fsym_def:
  new_fsym (fsig,psig) f s vl = (fsig |+ (f,(s,vl)),psig)
End


Definition isfsym_def:
  isfsym fsig f ⇔ f ∈ FDOM fsig 
End


Definition ispsym_def:
  ispsym psig p ⇔ p ∈ FDOM psig
End        


Definition wft_def:
  (wft Σf (Var n s) ⇔ wfs Σf s) ∧
  (wft Σf (Fn f tl) ⇔
     (∀t. MEM t tl ⇒ wft Σf t) ∧
     isfsym Σf f ∧
     IS_SOME
     (tlmatch Σf {} (MAP (UNCURRY Var) (SND (Σf ' f))) tl FEMPTY)) ∧
  (wfs Σf (St n tl) ⇔ EVERY (wft Σf) tl)
Termination
 WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,t) => term_size t
         | INR (_,st) => sort_size st)’ 
End
           
(*all
the variables of sort 𝑠 must also be in Γ \ {𝑥 } automatically satisfied?
 not true ,because x might be completely fresh

∀x:s1. P(x:s2) just means the quantifier is not on x:s2.

allI x does not occur in the assumption list automatically true?       
*)

  
Definition wffVar_def:
  wffVar Σf (fVar P vl tl) ⇔
    EVERY (wft Σf) (MAP (UNCURRY Var) vl) ∧
    EVERY (wft Σf) tl ∧
    IS_SOME (tlmatch Σf {} (MAP (UNCURRY Var) vl) tl FEMPTY)
End
  
Definition tsubst_def[simp]:
  (tsubst n s t (Var n0 s0) =
  if n = n0 ∧ s = s0 then t else Var n0 (ssubst n s t s0)) ∧
  tsubst n s t (Fn f tl) =
  Fn f (MAP (tsubst n s t) tl) ∧
  ssubst n s t (St sn tl) = St sn (MAP (tsubst n s t) tl)
Termination
  WF_REL_TAC
  ‘measure
    (λs. case s of
           INL (_,_,_,a) => term_size a
         | INR (_,_,_,s) => sort_size s)’ 
End  
  
  
  
Definition fsubst_def[simp]:
  fsubst n (s:sort) (t:term) False = False ∧
  fsubst n s t (IMP f1 f2) = IMP (fsubst n s t f1) (fsubst n s t f2) ∧
  (fsubst n s t (FALL n0 s0 b) =
  if n = n0 ∧ s = s0 then (FALL n0 s0 b)
  else FALL n0 s0 (fsubst n s t b)) ∧
  fsubst n s t (Pred p tl) = Pred p (MAP (tsubst n s t) tl) ∧
  fsubst n s t (fVar p vl tl) = fVar p vl (MAP (tsubst n s t) tl)
End
 



(*this assumes no sort depends on itself, so if (n,s) ∈ FDOM σ, then (n,s) does not occur in s, each s depends only on other s*)

Definition finst_def[simp]:
  finst σ False = False ∧
  finst σ (Pred p tl) = Pred p (MAP (tinst σ) tl) ∧
  finst σ (IMP f1 f2) = IMP (finst σ f1) (finst σ f2) ∧
  finst σ (fVar p vl tl) = fVar p vl (MAP (tinst σ) tl) ∧
  finst σ (FALL n s f) =
  if (n,s) ∈ FDOM σ then
    FALL n (sinst (σ \\ (n,s)) s) (finst (σ \\ (n,s)) f)
  else FALL n (sinst σ s) (finst σ f)
End

Definition fVar_subst_def:
 fVar_subst Σf (P,vl,ϕ:form) False = False ∧
 fVar_subst Σf (P,vl,ϕ) (Pred p tl) = Pred p tl ∧
 fVar_subst Σf (P,vl,ϕ) (IMP f1 f2) = IMP (fVar_subst Σf (P,vl,ϕ) f1)
                                       (fVar_subst Σf (P,vl,ϕ) f2) ∧
 fVar_subst Σf (P,vl,ϕ) (FALL n s f) = FALL n s 
                                       (fVar_subst Σf (P,vl,ϕ) f) ∧
 fVar_subst Σf (P,vl,ϕ) (fVar Pname Pvl tl) =
 if P = Pname ∧ vl = Pvl then 
  finst (THE (tlmatch Σf {} (MAP (λ(n,s). Var n s) vl) tl (FEMPTY:string # sort |-> term))) ϕ   
 else fVar Pname Pvl tl
End

Definition wff_def[simp]:
  (wff (Σf,Σp) False ⇔ T) ∧
  (wff (Σf,Σp) (Pred p tl) ⇔
     ispsym Σp p ∧
     IS_SOME (tlmatch Σf {} (MAP (UNCURRY Var) (Σp ' p)) tl FEMPTY)) ∧
  (wff (Σf,Σp) (IMP f1 f2) ⇔ wff (Σf,Σp) f1 ∧ wff (Σf,Σp) f2) ∧
  (wff (Σf,Σp) (FALL n s b) ⇔ wfs Σf s ∧ wff (Σf,Σp) b) ∧
  (wff (Σf,Σp) (fVar P vl tl) ⇔
     EVERY (wft Σf) (MAP (UNCURRY Var) vl) ∧
     EVERY (wft Σf) tl ∧
     IS_SOME (tlmatch Σf {} (MAP (UNCURRY Var) vl) tl FEMPTY))
End
 
(*well-formed variable map*)        
Definition wfvmap_def:
  wfvmap Σf σ ⇔
  (∀n s. (n,s) ∈ FDOM σ ⇒ wfs Σf s ∧ wft Σf (σ ' (n,s)) ∧
   sort_of Σf (σ ' (n,s)) = sinst σ s)
End

(*slash u plus ⊎*)

Theorem FUNION_IDEM:
 σ ⊌ σ = σ
Proof
  cheat
QED   

Theorem tmatch_FUNION_lemma:
  (case a of
     NONE => NONE
   | SOME a0 => f a0) = SOME c <=>
  (∃a0. a = SOME a0 ∧ f a0 = SOME c)
Proof
  Cases_on ‘a’ >> simp[]
QED


(*        
              
Theorem tmatch_FUNION:
  ∀t1 t2 t3 σ σ1 σ2.
  (tlmatch Σf lcs t1 t2 σ) = SOME σ1 ∧ (tlmatch Σf lcs t2 t3 σ) = SOME σ2 ⇒
  tlmatch Σf lcs t1 t3 σ = SOME (σ2 o_f σ1)
Proof
  Induct_on ‘t1’ >> Induct_on ‘t2’ >> Induct_on ‘t3’ >>
  gs[tmatch_def,FUNION_IDEM] >> rpt strip_tac >>
  gs[tmatch_FUNION_lemma,PULL_EXISTS] >>
  rename [‘tmatch Σf lcs h2 h1 σ = SOME f1’]
  ‘∀h' h σ σ1 σ2.
          tlmatch Σf lcs t1 t2 () ∧
          SOME σ1 ∧ tlmatch Σf lcs (h'::t2) t3 σ = SOME σ2 ⇒
          tlmatch Σf lcs (h::t1) t3 σ = SOME (σ1 ⊌ σ2)’
  Cases_on ‘Σf lcs h'' h' σ’ >> 
  Cases_on ‘Σf lcs h' h σ’ >> Cases_on ‘Σf lcs h'' h σ’
  >- rw[FUNION_IDEM] >>
*)
  
(*DRESTRICT_SUBSET*)  
Theorem fmap_tfv_tinst_eq:
  DRESTRICT σ1 (tfv t) = DRESTRICT σ2 (tfv t) ⇒ tinst σ1 t = tinst σ2 t
Proof
  Induct_on ‘t’ >> simp[]
  >- (Cases_on ‘s’ >> gs[stms_def] >>
     rw[] >> rename [‘St sn l’] (* 4 *)
     >- (simp[MAP_EQ_f] >> rw[] >> first_x_assum $ irule_at Any >>
        simp[] >> irule DRESTRICT_SUBSET >>
        first_x_assum $ irule_at Any >> rw[SUBSET_DEF] >> metis_tac[]) >>
     gs[DRESTRICT_EQ_DRESTRICT_SAME,PULL_EXISTS,EXTENSION] >> 
     metis_tac[]) >>
  rw[MAP_EQ_f] >> first_x_assum irule >> irule_at Any DRESTRICT_SUBSET >>
  last_x_assum (irule_at Any) >> simp[SUBSET_DEF] >> metis_tac[]
QED  
     

Theorem fmap_sfv_sinst_eq:
  DRESTRICT σ1 (sfv s) = DRESTRICT σ2 (sfv s) ⇒ sinst σ1 s = sinst σ2 s
Proof
  cheat
QED  

Definition o_vmap_def:
  o_vmap Σf σ2 σ1 =
  fmap_ABS
    (λ(n,s).
       if (n,s) ∈ FDOM σ1 then INL (tinst σ2 (σ1 ' (n,s))) else
         if (n,s) ∈ FDOM σ2 then INL (σ2 ' (n,s)) else INR ())
End

Theorem tinst_vmap_id:
  ∀t σ. (∀n s. (n,s) ∈ FDOM σ ∩ tfv t ⇒ σ ' (n,s) = Var n s) ⇒ tinst σ t = t
Proof
  Induct_on ‘t’ >> rw[tinst_def] (* 2 *)
  >- (Cases_on ‘s’ >>
      ‘MAP (λa. tinst σ a) l = MAP I l’ suffices_by simp[] >>
      rw[MAP_EQ_f] >> gvs[PULL_EXISTS] >>
      first_x_assum irule >> rw[] >> first_x_assum irule >> metis_tac[]) >>
  ‘MAP (λa. tinst σ a) l = MAP I l’ suffices_by simp[] >>
  rw[MAP_EQ_f] >> gvs[PULL_EXISTS] >>
  first_x_assum irule >> rw[] >> first_x_assum irule >> metis_tac[]
QED  

(*t and its instance can match iff σ and f do not send local constants to somewhere else *)

Definition vmap_fix_def:
  vmap_fix σ vs ⇔ (∀n s. (n,s) ∈ FDOM σ ∩ vs ⇒ σ ' (n,s) = Var n s)
End

Theorem vmap_fix_FEMPTY[simp]: 
  vmap_fix FEMPTY vs
Proof
  simp[vmap_fix_def]
QED

(*if matchable then fix local constants
  for each step the f obtained resp to lcs.
  matchable iff exists a σ such that it is a inst.
  what if there is no local constants in the term?
  if equal on intersection than can glue to a new subst map
  
*)

Definition complete_def:
  complete σ ⇔ ∀n s. (n,s) ∈ FDOM σ ⇒ ∀v. v ∈ sfv s ⇒ v ∈ FDOM σ
End  
        
Theorem DRESTRICT_UNION_SING:
  x ∈ FDOM σ ⇒ DRESTRICT σ (s ∪ {x}) = DRESTRICT σ s |+ (x, σ ' x)
Proof
  rw[fmap_EXT,DRESTRICT_DEF]
  >- (rw[EQ_IMP_THM,EXTENSION] >> metis_tac[])
  >- (Cases_on ‘x' = x’ >> rw[FAPPLY_FUPDATE,DRESTRICT_DEF,NOT_EQ_FAPPLY]) >>
  rw[FAPPLY_FUPDATE]
QED



Theorem vsort_tfv_closed:
  (∀h n s v. (n,s) ∈ tfv h ∧ v ∈ sfv s ⇒ v ∈ tfv h) ∧
  (∀st n s v. (n,s) ∈ sfv st ∧ v ∈ sfv s ⇒ v ∈ sfv st)
Proof
  ho_match_mp_tac better_tm_induction >> rw[] (* 4 *)
  >- simp[] >- (disj2_tac >> first_x_assum irule >> metis_tac[])
  >- (simp[PULL_EXISTS] >> first_assum $ irule_at Any >>
     first_assum irule >> metis_tac[]) >>
  last_assum $ irule_at Any >> metis_tac[]
QED

(* in the case that start with an f a:1->A and have not assigned a to anywhere else, A is not stores*)
Theorem IS_SOME_tmatch:
   (∀t f.
     complete f ∧ wfvmap Σ σ ∧
     (tfv t ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ tfv t ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     tmatch Σ {} t (tinst σ t) f = SOME (FUNION f (DRESTRICT σ (tfv t)))) ∧
   (∀st f.
     complete f ∧ wfvmap Σ σ ∧
     (sfv st ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ sfv st ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     smatch Σ {} st (sinst σ st) f = SOME (FUNION f (DRESTRICT σ (sfv st))))
Proof       
  ho_match_mp_tac better_tm_induction >> rw[PULL_EXISTS] (* 3 *)
  >- (gs[tmatch_def,AllCaseEqs()] >>
     Cases_on ‘(s0,st) ∈ FDOM f’ >> gs[] (* 2 *)
     >- (Cases_on ‘st’ >> gs[tmatch_def,PULL_EXISTS] >>
        rw[fmap_EXT,Once EQ_SYM_EQ,Once UNION_COMM,GSYM SUBSET_UNION_ABSORPTION] (* 2 *)
        >- (gs[SUBSET_DEF,complete_def,DRESTRICT_DEF] >> rw[] (* 2 *)
            >- first_x_assum irule >>
            first_x_assum irule >>
            first_x_assum $ irule_at Any >> gs[tfv_def,MEM_MAP] >>
            metis_tac[]) >>
        rw[FUNION_DEF])
     >- (gs[wfvmap_def,Once UNION_COMM] >> drule_then strip_assume_tac DRESTRICT_UNION_SING >>
        simp[FUNION_FUPDATE_2]))
  >> (gs[tmatch_def] >>
     rpt (pop_assum mp_tac) >>
     Q.ID_SPEC_TAC `f` >> Q.ID_SPEC_TAC `l`  >> Induct_on ‘l’
     >- rw[tmatch_def,DRESTRICT_IS_FEMPTY] >>
     rw[tmatch_def] >>
     ‘tmatch Σ ∅ h (tinst σ h) f = SOME (f ⊌ DRESTRICT σ (tfv h))’
      by (first_x_assum irule >> rw[] >> irule_at Any SUBSET_TRANS >>
          first_x_assum $ irule_at Any >> rw[SUBSET_DEF] >> metis_tac[]) >>
     rw[] >>
     ‘tlmatch Σ ∅ l (MAP (λa. tinst σ a) l) (f ⊌ DRESTRICT σ (tfv h)) =
      SOME ((f ⊌ DRESTRICT σ (tfv h)) ⊌ DRESTRICT σ (BIGUNION {tfv t | MEM t l}))’
        by (first_x_assum irule >>
        simp[DRESTRICT_DEF] >> (irule_at Any) SUBSET_TRANS >>
        qexists_tac ‘BIGUNION {tfv t | t = h ∨ MEM t l}’ >> simp[] >> rw[SUBSET_DEF] (* 4 *)
        >- metis_tac[]
        >- (rw[FUNION_DEF] >> first_x_assum irule >> metis_tac[])
        >- rw[FUNION_DEF,DRESTRICT_DEF] >>
        gs[complete_def,DRESTRICT_DEF] >> rw[] (* 2 *)
        >- (disj1_tac >> first_x_assum irule >> metis_tac[]) >>
        disj2_tac >> gs[SUBSET_DEF,PULL_EXISTS] >> first_assum $ irule_at Any >>
        qexists_tac ‘h’ >> simp[] >> metis_tac[vsort_tfv_closed]) >>
     rw[DRESTRICT_FUNION,GSYM FUNION_ASSOC] >>
     rpt AP_TERM_TAC >> rw[EXTENSION] >> metis_tac[])
QED



(*
Theorem tmatch_FDOM:
  (∀t1 t2 f f1.
     complete f ∧ wfvmap Σ σ ∧
     (tfv t ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ tfv t ⇒ f ' (n,s) = σ ' (n,s)) ∧
     tmatch Σ {} t2 t2 f = SOME f1 ==) ∧
   (∀st f.
     complete f ∧ wfvmap Σ σ ∧
     (sfv st ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ sfv st ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     smatch Σ {} st (sinst σ st) f = SOME (FUNION f (DRESTRICT σ (sfv st))))
Proof
*)

(*todo:tmatch gives a map records each variable once start with a complete map *)

Theorem tlmatch_LENGTH:
  ∀tl1 tl2 f σ.
  tlmatch Σ lcs tl1 tl2 f = SOME σ ⇒
  LENGTH tl1 = LENGTH tl2
Proof
  Induct_on ‘tl1’ >> Induct_on ‘tl2’ >>
  gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >>
  metis_tac[]
QED


(*                  
Theorem original_tm_induction':
  ∀P0 P1 P2.
       (∀s. P1 s ⇒ ∀s0. P0 (Var s0 s)) ∧ (∀l. P2 l ⇒ ∀s. P0 (Fn s l)) ∧
       (∀l. P2 l ⇒ ∀s. P1 (St s l)) ∧ P2 [] ∧ (∀t l. P0 t ∧ P2 l ⇒ P2 (SNOC t l)) ⇒
       (∀t. P0 t) ∧ (∀s. P1 s) ∧ ∀l. P2 l
Proof
  rpt gen_tac >> disch_tac>>
  ho_match_mp_tac original_tm_induction >>
  gs[] >>
  qspec_then ‘λl. ∀t. ’
  ‘’
  
  ‘∀l t. P0 t ∧ P2 l ⇒ P2 (t::l)’
    suffices_by metis_tac[] >>
  Induct_on ‘l’ >- cheat >>
  
  
  ho_match_mp_tac SNOC_INDUCT >> gs[] >> conj_tac
  >- (rw[] >>
     first_x_assum (qspecl_then [‘t’,‘[]’] assume_tac)>>
     gs[SNOC]) >>
  rw[] >>  
  first_x_assum (qspecl_then [‘x’,‘t:: l’] assume_tac) >>
  
  list_INDUCT
*)





Definition is_cont_def:
  is_cont ct ⇔ ∀n s. (n,s) ∈ ct ⇒ sfv s ⊆ ct
End

Theorem tfv_is_cont:
 (∀t. is_cont (tfv t)) ∧
 (∀s. is_cont (sfv s))
Proof
 ho_match_mp_tac better_tm_induction >>
 gs[tfv_def,is_cont_def,SUBSET_DEF,PULL_EXISTS] >>
 rw[] (* 3 *)
 >- simp[]
 >- (disj2_tac >> first_x_assum irule >> metis_tac[]) >>
 qexists_tac ‘s’ >> gs[MEM_MAP] >>
 metis_tac[]
QED

Theorem fmap_sfv_sinst_eq:
  DRESTRICT σ1 (sfv s) = DRESTRICT σ2 (sfv s) ⇒
  sinst σ1 s = sinst σ2 s
Proof
  Cases_on ‘s’ >> gs[tinst_def,MAP_EQ_f] >>
  rw[] >> irule fmap_tfv_tinst_eq >>
  irule DRESTRICT_SUBSET >>
  first_x_assum $ irule_at Any >>
  rw[SUBSET_DEF] >> metis_tac[]
QED  
            

Theorem wfvmap_cont_DRESTRICT:
  wfvmap Σ σ ∧ complete σ ∧ is_cont s ⇒ wfvmap Σ (DRESTRICT σ s)
Proof
  rw[wfvmap_def,is_cont_def,DRESTRICT_DEF] (* 2 *)
  >- metis_tac[] >>
  irule fmap_sfv_sinst_eq >>
  rw[Once EQ_SYM_EQ] >> AP_TERM_TAC >>
  rw[Once INTER_COMM,GSYM SUBSET_INTER_ABSORPTION] >>
  first_x_assum irule>> metis_tac[]
QED 

(*matchable to a map implies matchable to a submap*)    
(*Theorem tmatch_SUBMAP:
  tlmatch Σ {} t1 t2 f = SOME σ ⇒
  ∀n. n < LENGTH tl1 ⇒
  ∃σ1. tmatch Σ {} (EL n tl1) (EL n tl2) f = SOME σ1
Proof*)  




(*****)
Theorem tmatch_complete:
  (∀t1 t2 f σ.
     complete f ∧
     tmatch Σ {} t1 t2 f = SOME σ ⇒
     tfv t1 ⊆ FDOM σ ∧ FDOM f ⊆ FDOM σ ∧ complete σ) ∧
  (∀s1 s2 f σ.
     complete f ∧
     smatch Σ {} s1 s2 f = SOME σ ⇒
     sfv s1 ⊆ FDOM σ ∧ FDOM f ⊆ FDOM σ ∧ complete σ) ∧
  (∀tl1 tl2 f σ.
     complete f ∧
     tlmatch Σ {} tl1 tl2 f = SOME σ ⇒
     (∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧
     FDOM f ⊆ FDOM σ ∧ complete σ)
Proof
  ho_match_mp_tac original_tm_induction >> rw[] (* 16 *)
  >- (gs[tmatch_def,AllCaseEqs()] >>
     pop_assum (assume_tac o GSYM) >> rw[])
  >- (gs[tmatch_def,AllCaseEqs()] (* 2 *)
     >- metis_tac[complete_def,SUBSET_DEF] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF])
  >- (gs[tmatch_def,AllCaseEqs()] >>
     first_x_assum drule_all >>
     rw[] >> gs[complete_def,SUBSET_DEF] >>
     metis_tac[])
  >- (gs[tmatch_def,AllCaseEqs()] >>
     first_x_assum drule_all >>
     rw[] >> gs[complete_def,SUBSET_DEF] >>
     metis_tac[])
  >- (Cases_on ‘t2’ >> gs[tmatch_def] >>
     rw[SUBSET_DEF] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF] >> metis_tac[])
  >- (Cases_on ‘t2’ >> gs[tmatch_def] >>
     first_x_assum drule_all >> rw[])
  >- (Cases_on ‘t2’ >> gs[tmatch_def] >>
     first_x_assum drule_all >> rw[]) (*9 remains*)
  >- (Cases_on ‘s2’ >> gs[tmatch_def] >>
     rw[SUBSET_DEF] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF] >> metis_tac[])
  >- (Cases_on ‘s2’ >> gs[tmatch_def] >>
     first_x_assum drule_all >> rw[])
  >- (Cases_on ‘s2’ >> gs[tmatch_def] >>
     first_x_assum drule_all >> rw[]) (* 6 *)
  >- (drule tlmatch_LENGTH >> rw[] >> gs[tmatch_def])
  >- (drule tlmatch_LENGTH >> rw[] >> gs[tmatch_def]) (* 4 *)
  >- (Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tlmatch Σ ∅ tl1 tl2 f1 = SOME σ’] >>
     rename [‘tmatch Σ ∅ t1 t2 f = SOME f1’] >> 
     rpt (pop_assum mp_tac)>>
     Q.ID_SPEC_TAC ‘f’ >> Q.ID_SPEC_TAC ‘f1’ >>
     Q.ID_SPEC_TAC ‘σ’ >>
     Q.ID_SPEC_TAC ‘t2’ >> Q.ID_SPEC_TAC ‘t1’ >>
     Q.ID_SPEC_TAC ‘tl2’ >> Q.ID_SPEC_TAC ‘tl1’ >>
     Induct_on ‘tl1’ >> gs[tmatch_def] >> rw[] (* 2 *)
     >- (drule tlmatch_LENGTH >> rw[] >> gs[tmatch_def] >>
        last_x_assum drule_all >> rw[]) >>
     rename [‘h1::tl1’] >>
     Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tmatch Σ ∅ h1 h2 f1 = SOME f2’] >>
     rename [‘tlmatch Σ ∅ tl1 tl2 f2 = SOME σ’] >>
     last_x_assum
     (qspecl_then [‘tl2’,‘h1’,‘h2’,‘σ’,‘f2’,‘f1’]
      assume_tac) >>
     gs[]>>
     ‘tfv t1 ⊆ FDOM f1 ∧ FDOM f ⊆ FDOM f1 ∧ complete f1’
       by (first_x_assum irule >> simp[] >>
          qexists_tac ‘t2’ >> simp[]) >>
      ‘(∀t. t = h1 ∨ MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧
       FDOM f1 ⊆ FDOM σ ∧
       complete σ’
       by (first_x_assum irule >> simp[] >>
          qexists_tac ‘h2 :: tl2’ >> gs[tmatch_def]) >>
     ‘tfv h1 ⊆ FDOM σ’
     suffices_by
     (rw[] >>
      irule SUBSET_TRANS >> qexists_tac ‘FDOM f1’ >>
      simp[]) >>
     first_x_assum irule >> simp[])
  >- (Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tlmatch Σ ∅ tl1 tl2 f1 = SOME σ’] >>
     ‘tfv t1 ⊆ FDOM f1 ∧ FDOM f ⊆ FDOM f1 ∧ complete f1’
      by (first_x_assum irule >> simp[] >>
         qexists_tac ‘h’ >> gs[]) >>
     ‘(∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧ FDOM f1 ⊆ FDOM σ ∧ complete σ’
      by (first_x_assum irule >> simp[] >>
          metis_tac[]) >>
     metis_tac[])
  >- (Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tlmatch Σ ∅ tl1 tl2 f1 = SOME σ’] >>
     rename [‘tmatch Σ ∅ t1 t2 f = SOME f1’] >> 
     ‘tfv t1 ⊆ FDOM f1 ∧ FDOM f ⊆ FDOM f1 ∧ complete f1’
      by (first_x_assum irule >> simp[] >>
         qexists_tac ‘t2’ >> gs[]) >>
     ‘(∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧ FDOM f1 ⊆ FDOM σ ∧ complete σ’
      by (first_x_assum irule >> simp[] >>
          metis_tac[]) >>
     metis_tac[SUBSET_TRANS]) >>
  Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tlmatch Σ ∅ tl1 tl2 f1 = SOME σ’] >>
     rename [‘tmatch Σ ∅ t1 t2 f = SOME f1’] >> 
     ‘tfv t1 ⊆ FDOM f1 ∧ FDOM f ⊆ FDOM f1 ∧ complete f1’
      by (first_x_assum irule >> simp[] >>
         qexists_tac ‘t2’ >> gs[]) >>
     ‘(∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧ FDOM f1 ⊆ FDOM σ ∧ complete σ’
      by (first_x_assum irule >> simp[] >>
          metis_tac[])
QED          


Theorem tm_tree_WF:
  (∀t:term s n l. (n,St s l) ∈ tfv t ⇒ ¬MEM t l) ∧
  (∀s n.(n,s) ∉ sfv s)
Proof
(* ho_match_mp_tac better_tm_induction >>
 simp[tfv_def] >> rw[] >>
 gs[tfv_def,MEM_MAP,GSYM IMP_DISJ_THM,PULL_FORALL]
 >- (first_x_assum irule >> simp[tfv_def] >> metis_tac[])
 >- (strip_tac >>
    ‘(s0,s) ∈  sfv s’ suffices_by  metis_tac[] >>
    cheat)
 >- (gvs[] >>
     strip_tac >> first_x_assum $ drule_then assume_tac >>
     ‘’ )




(gvs[] >> rename [‘St s1 l1’] >>
     first_x_assum irule >>
     simp[tfv_def,MEM_MAP,PULL_EXISTS] >> )
 rename [‘_ ∉ s0’] >> rw[GSYM IMP_DISJ_THM] >>
 
  rw[]>> Cases_on ‘s’>>
  rename [‘St s l’] >>
  Induct_on ‘l’ >> gs[tfv_def]  >>*) 
  cheat
QED  
             

Theorem tmatch_SUBMAP:
  (∀t1 t2 f σ.
     complete f ∧
     (∀n s. (n,s) ∈ tfv t1 ⇒ (n,s) ∉ sfv s) ∧
     tmatch Σ {} t1 t2 f = SOME σ ⇒
     f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ tfv t1) ∧
  (∀s1 s2 f σ.
     complete f ∧
     (∀n s. (n,s) ∈ sfv s1 ⇒ (n,s) ∉ sfv s) ∧ 
     smatch Σ {} s1 s2 f = SOME σ ⇒
     f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ sfv s1) ∧
  (∀tl1 tl2 f σ.
     complete f ∧ 
     (∀t n s. MEM t tl1 ∧ (n,s) ∈ tfv t ⇒ (n,s) ∉ sfv s) ∧
     tlmatch Σ {} tl1 tl2 f = SOME σ ⇒
     f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ BIGUNION {tfv t | MEM t tl1}) 
Proof
  ho_match_mp_tac original_tm_induction >> rw[] (* 10 *)
  >- (gs[tmatch_def,AllCaseEqs()] >>
     first_x_assum drule_all >> rw[] >>
     irule SUBMAP_TRANS >> 
     qexists_tac ‘f0’ >>  
     rw[SUBMAP_FUPDATE_EQN] >> disj1_tac >>
     gs[SUBSET_DEF] >> metis_tac[])
  >- (gs[tmatch_def,AllCaseEqs()] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF] >> metis_tac[]) 
  >- (Cases_on ‘t2’ >>
     gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >> metis_tac[])
  >- (Cases_on ‘t2’ >>
     gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >> metis_tac[])
  >- (Cases_on ‘s2’ >> 
     gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >> metis_tac[])
  >- (Cases_on ‘s2’ >> 
     gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >> metis_tac[])
  >- (drule tlmatch_LENGTH >> rw[] >>
     gs[tmatch_def])
  >- (drule tlmatch_LENGTH >> rw[] >>
     gs[tmatch_def])
  >- (Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tmatch Σ ∅ t1 t2 f’,‘tlmatch Σ ∅ tl1 tl2 f1’]>>
     last_x_assum (drule_all_then strip_assume_tac) >>
     ‘complete f1’ by metis_tac[tmatch_complete] >>
     ‘f1 ⊑ σ ∧
      FDOM σ ⊆ FDOM f1 ∪ BIGUNION {tfv t | MEM t tl1}’
      by metis_tac[] >>
     metis_tac[SUBMAP_TRANS]) >>
  Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
  rename [‘tmatch Σ ∅ t1 t2 f’,‘tlmatch Σ ∅ tl1 tl2 f1’]>>
  last_x_assum (drule_all_then strip_assume_tac) >>
  ‘complete f1’ by metis_tac[tmatch_complete] >>
  ‘f1 ⊑ σ ∧
   FDOM σ ⊆ FDOM f1 ∪ BIGUNION {tfv t | MEM t tl1}’
    by metis_tac[] >>
  gs[SUBSET_DEF] >> metis_tac[]
QED


Theorem tmatch_FDOM_SUBMAP:
  (∀t1 t2 f σ.
        complete f ∧ (∀n s. (n,s) ∈ tfv t1 ⇒ (n,s) ∉ sfv s) ∧
        tmatch Σ ∅ t1 t2 f = SOME σ ⇒
        complete σ ∧
        f ⊑ σ ∧ FDOM σ = FDOM f ∪ tfv t1) ∧
     (∀s1 s2 f σ.
        complete f ∧ (∀n s. (n,s) ∈ sfv s1 ⇒ (n,s) ∉ sfv s) ∧
        smatch Σ ∅ s1 s2 f = SOME σ ⇒
        complete σ ∧
        f ⊑ σ ∧ FDOM σ = FDOM f ∪ sfv s1) ∧
     ∀tl1 tl2 f σ.
       complete f ∧ (∀t n s. MEM t tl1 ∧ (n,s) ∈ tfv t ⇒ (n,s) ∉ sfv s) ∧
       tlmatch Σ ∅ tl1 tl2 f = SOME σ ⇒
       complete σ ∧
       f ⊑ σ ∧ FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1}
Proof
 rw[]
 >- metis_tac[tmatch_complete]
 >- metis_tac[tmatch_SUBMAP]
 >- (rw[GSYM SUBSET_ANTISYM_EQ] (* 3 *)
    >> metis_tac[tmatch_SUBMAP,tmatch_complete])
 >- metis_tac[tmatch_complete]
 >- metis_tac[tmatch_SUBMAP]
 >- (rw[GSYM SUBSET_ANTISYM_EQ] (* 3 *)
    >> metis_tac[tmatch_SUBMAP,tmatch_complete])
 >- metis_tac[tmatch_complete]
 >- metis_tac[tmatch_SUBMAP] >>
 rw[GSYM SUBSET_ANTISYM_EQ] (* 3 *)
 >- metis_tac[tmatch_SUBMAP]
 >- metis_tac[tmatch_complete] >>
 rw[SUBSET_DEF] >> metis_tac[tmatch_complete,SUBSET_DEF]
QED 



(*
Theorem tmatch_wfvmap:
  (∀t1 t2 f σ.
     complete f ∧ wfvmap Σ f ∧ 
     tmatch Σ {} t1 t2 f = SOME σ ⇒
     wfvmap Σ σ) ∧
  (∀s1 s2 f σ.
     complete f ∧
     (∀n s. (n,s) ∈ sfv s1 ⇒ (n,s) ∉ sfv s) ∧ 
     smatch Σ {} s1 s2 f = SOME σ ⇒
     f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ sfv s1) ∧
  (∀tl1 tl2 f σ.
     complete f ∧ 
     (∀t n s. MEM t tl1 ∧ (n,s) ∈ tfv t ⇒ (n,s) ∉ sfv s) ∧
     tlmatch Σ {} tl1 tl2 f = SOME σ ⇒
     f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ BIGUNION {tfv t | MEM t tl1})
Proof
*)

val tmatch_property = cj 1 tmatch_FDOM_SUBMAP
val smatch_property = cj 2 tmatch_FDOM_SUBMAP
val tlmatch_property = cj 3 tmatch_FDOM_SUBMAP



(*    
Theorem tmatch_SOME_tinst:
 (∀t1 t2 f σ.
     complete f ∧
     (∀n s. (n,s) ∈ tfv t1 ⇒ (n,s) ∉ sfv s) ∧ 
     tmatch Σ {} t1 t2 f = SOME σ ⇒
     tinst σ t1 = t2 ∧ wfvmap Σ σ) ∧
 (∀st1 st2 f σ.
    complete f ∧
    (∀n s. (n,s) ∈ sfv st1 ⇒ (n,s) ∉ sfv st1) ∧
    smatch Σ {} st1 st2 f = SOME σ  ⇒
    sinst σ st1 = st2 ∧ wfvmap Σ σ) ∧
 (∀tl1 tl2 f σ.
    complete f ∧
    (∀t n s. MEM t tl1 ∧ (n,s) ∈ tfv t ⇒ (n,s) ∉ sfv s) ∧
    tlmatch Σ {} tl1 tl2 f = SOME σ ⇒
    (∀n. n < LENGTH tl1 ⇒ tinst σ (EL n tl1) = EL n tl2) ∧
    wfvmap Σ σ)
Proof
 ho_match_mp_tac original_tm_induction >> rw[] (* 9 *)
 >- (‘(s0,st1) ∈ FDOM σ’
      by (drule tmatch_property >> rw[] >>
         first_x_assum
         (qspecl_then [‘Σ’,‘Var s0 st1’,‘t2’,‘σ’]
          assume_tac) >>
         gs[] >>
         first_x_assum (drule_then strip_assume_tac)>>
         gs[EXTENSION]) >>
     gs[tmatch_def,AllCaseEqs(),fmap_EXT,SUBMAP_DEF] >>
     first_x_assum (qspecl_then [‘(s0,st1)’]assume_tac) >>
     gs[FAPPLY_FUPDATE])
 >- simp[wfvmap_def]
         

Cases_on ‘(s0,st1) ∈ FDOM σ’ (* 2 *)
     gs[tmatch_def,AllCaseEqs(),fmap_EXT,SUBMAP_DEF] >>

  gs[]
    Cases_on ‘(s0,st1) ∈ FDOM f’ >>
    
    gs[DISJ_IMP_THM])
 >- (Cases_on ‘t2’ >> gs[tmatch_def] >>
    rename [‘tlmatch Σ ∅ l1 l2 f’] >>
    drule tlmatch_LENGTH >> rw[] >> 
    ‘MAP (λa. tinst σ a) l1 = MAP I l2’
      suffices_by simp[] >>
    rw[MAP_EQ_EVERY2,LIST_REL_EL_EQN] >>
    first_x_assum irule>> simp[] >>
    qexists_tac ‘f’>> gs[PULL_EXISTS])
 >- (Cases_on ‘st2’ >> gs[tmatch_def] >>
    rename [‘tlmatch Σ ∅ l1 l2 f’] >>
    drule tlmatch_LENGTH >> rw[] >> 
    ‘MAP (λa. tinst σ a) l1 = MAP I l2’
      suffices_by simp[] >>
    rw[MAP_EQ_EVERY2,LIST_REL_EL_EQN] >>
    first_x_assum irule>> simp[] >>
    qexists_tac ‘f’>> gs[PULL_EXISTS]) >>
 gs[PULL_EXISTS] >>
 Cases_on ‘tl2’ >> fs[tmatch_def,AllCaseEqs()] >>
 rename [‘tmatch Σ ∅ t1 t2 f = SOME f1’,
         ‘tlmatch Σ ∅ tl1 tl2 f1 = SOME σ’] >>
 Cases_on ‘n = 0’ >> gs[] (* 2 *)
 >-
    ‘tinst f1 t1 = t2’ suffices_by cheat >>
    first_x_assum irule >> gs[PULL_EXISTS] >>
    qexists_tac ‘f’>> gs[] >> tmatch_complete
*)            



Theorem SUBMAP_DRESTRICT_IFF:
  f ⊑ g ⇔ f = DRESTRICT g (FDOM f)
Proof
  rw[SUBMAP_DEF,DRESTRICT_DEF,fmap_EXT,EQ_IMP_THM] (* 3 *)
  >- (rw[EXTENSION,INTER_DEF] >> metis_tac[])
  >- (gs[EXTENSION,INTER_DEF] >> metis_tac[]) >>
  gs[EXTENSION,INTER_DEF] >>
  first_assum (drule o iffLR) >> rw[]
QED

Theorem complete_FDOM_is_cont:
 complete f ⇔ is_cont (FDOM f)
Proof         
 rw[complete_def,is_cont_def,SUBSET_DEF]
QED



Theorem UNION_is_cont:
  is_cont s1 ∧ is_cont s2 ⇒ is_cont (s1 ∪ s2)
Proof         
 rw[is_cont_def,SUBSET_DEF,UNION_DEF] (* 2 *)
 >> metis_tac[]
QED         
              
Theorem tmatch_SOME_tinst:
 (∀t1 t2 f σ.
     complete f ∧ wfvmap Σ σ ∧
     (∀n s. (n,s) ∈ tfv t1 ⇒ (n,s) ∉ sfv s) ∧
     tmatch Σ {} t1 t2 f = SOME σ ⇒
     tinst σ t1 = t2) ∧
 (∀st1 st2 f σ.
    complete f ∧ wfvmap Σ σ ∧
    (∀n s. (n,s) ∈ sfv st1 ⇒ (n,s) ∉ sfv st1) ∧
    smatch Σ {} st1 st2 f = SOME σ  ⇒
    sinst σ st1 = st2) ∧
 (∀tl1 tl2 f σ.
    complete f ∧ wfvmap Σ σ ∧
    (∀t n s. MEM t tl1 ∧ (n,s) ∈ tfv t ⇒ (n,s) ∉ sfv s) ∧
    tlmatch Σ {} tl1 tl2 f = SOME σ ⇒
    ∀n. n < LENGTH tl1 ⇒ tinst σ (EL n tl1) = EL n tl2)
Proof
 ho_match_mp_tac original_tm_induction >> rw[] (* 4 *)
 >- (‘(s0,st1) ∈ FDOM σ’
      by (drule tmatch_property >> rw[] >>
         first_x_assum
         (qspecl_then [‘Σ’,‘Var s0 st1’,‘t2’,‘σ’]
          assume_tac) >>
         gs[] >>
         first_x_assum (drule_then strip_assume_tac)>>
         gs[EXTENSION]) >>
     gs[tmatch_def,AllCaseEqs(),fmap_EXT,SUBMAP_DEF] >>
     first_x_assum (qspecl_then [‘(s0,st1)’]assume_tac) >>
     gs[FAPPLY_FUPDATE])
 >- (Cases_on ‘t2’ >> gs[tmatch_def] >>
    rename [‘tlmatch Σ ∅ l1 l2 f’] >>
    drule tlmatch_LENGTH >> rw[] >> 
    ‘MAP (λa. tinst σ a) l1 = MAP I l2’
      suffices_by simp[] >>
    rw[MAP_EQ_EVERY2,LIST_REL_EL_EQN] >>
    first_x_assum irule>> simp[PULL_EXISTS] >>
    qexists_tac ‘f’>> gs[PULL_EXISTS] >> metis_tac[])
 >- (Cases_on ‘st2’ >> gs[tmatch_def] >>
    rename [‘tlmatch Σ ∅ l1 l2 f’] >>
    drule tlmatch_LENGTH >> rw[] >> 
    ‘MAP (λa. tinst σ a) l1 = MAP I l2’
      suffices_by simp[] >>
    rw[MAP_EQ_EVERY2,LIST_REL_EL_EQN] >>
    first_x_assum irule>> simp[PULL_EXISTS] >>
    qexists_tac ‘f’>> gs[PULL_EXISTS] >> metis_tac[]) >>
 gs[PULL_EXISTS] >>
 Cases_on ‘tl2’ >> fs[tmatch_def,AllCaseEqs()] >>
 rename [‘tmatch Σ ∅ t1 t2 f = SOME f1’,
         ‘tlmatch Σ ∅ tl1 tl2 f1 = SOME σ’] >>
 Cases_on ‘n = 0’ >> gs[] (* 2 *)
 >- (drule_then assume_tac tmatch_property >>
    ‘complete f1 ∧ f ⊑ f1 ∧ FDOM f1 = FDOM f ∪ tfv t1’
     by metis_tac[] >>
    drule_then assume_tac tlmatch_property >>
    ‘complete σ ∧ f1 ⊑ σ ∧
     FDOM σ = FDOM f1 ∪ BIGUNION {tfv t | MEM t tl1}’
     by metis_tac[] >>
    ‘tinst f1 t1 = t2’
     suffices_by
       (rw[] >> irule fmap_tfv_tinst_eq >>
       gs[DRESTRICT_EQ_DRESTRICT_SAME,SUBMAP_DEF] >>
       rw[EXTENSION] >> metis_tac[]) >>
    first_x_assum irule >> gs[PULL_EXISTS] >>
    qexists_tac ‘f’ >> gs[] >>
    ‘f1 = DRESTRICT σ (FDOM f1)’
     by metis_tac[SUBMAP_DRESTRICT_IFF] >>
    gs[] >>
    irule_at Any wfvmap_cont_DRESTRICT >>
    simp[] >> irule UNION_is_cont >>
    rw[tfv_is_cont,GSYM complete_FDOM_is_cont])
 >> (‘∃m. n = SUC m’
      by metis_tac[arithmeticTheory.num_CASES] >>
    gs[] >> first_x_assum irule >> gs[PULL_EXISTS] >>
    qexists_tac ‘f1’  >> gs[] >>
    ‘complete f1’ by metis_tac[tmatch_property] >>
    metis_tac[])
QED

val tmatch_tinst = cj 1 tmatch_SOME_tinst
val smatch_sinst = cj 2 tmatch_SOME_tinst
val tlmatch_EL_tinst = cj 3 tmatch_SOME_tinst



Theorem wfvmap_SUBMAP:
  wfvmap Σ f ∧ f ⊑ σ ∧ complete f ∧
  (∀n s. (n,s) ∈ FDOM σ ∧ (n,s) ∉ FDOM f ⇒
  wfs Σ s ∧
  wft Σ (σ ' (n,s)) ∧ sort_of Σ (σ ' (n,s)) = sinst σ s) ⇒
  wfvmap Σ σ
Proof
 rw[wfvmap_def] (* 3 *)
 >- (Cases_on ‘(n,s) ∈ FDOM f’ >> gs[]
    >> metis_tac[])
 >- (Cases_on ‘(n,s) ∈ FDOM f’ >> gs[SUBMAP_DEF]) >>
 drule $ iffLR SUBMAP_DRESTRICT_IFF >>
 rw[] >>
 Cases_on ‘(n,s) ∈ FDOM f’ (* 2 *)
 >- (last_x_assum (drule_then strip_assume_tac) >>
    gs[SUBMAP_DEF] >> irule fmap_sfv_sinst_eq >>
    rw[DRESTRICT_DEF,fmap_EXT,EXTENSION] >>
    gs[complete_def] >> metis_tac[]) >>
 first_x_assum (drule_all_then strip_assume_tac)   
QED



Theorem wft_tfv:
  (∀t. wft Σ t ⇒ ∀n s. (n,s) ∈ tfv t ⇒ wfs Σ s) ∧
  (∀s. wfs Σ s ⇒ ∀n st. (n,st) ∈ sfv s ⇒ wfs Σ st) (* ∧
  ∀l. (∀t. MEM t l ⇒ wft Σ t) ⇒ ∀n s t. MEM t l ∧ (n,s) ∈ tfv t ⇒ wfs Σ st*)
Proof  
  ho_match_mp_tac better_tm_induction >> 
  gs[wft_def,EVERY_MEM] >> rw[] (* 4 *)
  >- simp[]
  >> metis_tac[]
QED  

Theorem tmatch_TRANS:
 tmatch Σ {} t1 t2 f = σ1 ∧ 
 tmatch Σ {} t2 t3 f = σ2 

Theorem wft_wfs:
  ∀t. wft Σ t ⇒ wfs Σ (sort_of Σ t)
Proof
  Cases_on ‘t’ >> rw[wft_def]
  >- rw[tmatch_def] >> Cases_on ‘’

gs[optionTheory.IS_SOME_DEF]
  
QED
         
Theorem tmatch_SOME_wfvmap:
 (∀t1 t2 f σ.
     complete f ∧ wfvmap Σ f ∧
     (∀n s. (n,s) ∈ tfv t1 ⇒ (n,s) ∉ sfv s) ∧
     wft Σ t1 ∧ wft Σ t2 ∧
     tmatch Σ {} t1 t2 f = SOME σ ⇒
     wfvmap Σ σ ∧ tinst σ t1 = t2) ∧
 (∀st1 st2 f σ.
    complete f ∧ wfvmap Σ f ∧
    (∀n s. (n,s) ∈ sfv st1 ⇒ (n,s) ∉ sfv s) ∧
    wfs Σ st1 ∧ wfs Σ st2 ∧ 
    smatch Σ {} st1 st2 f = SOME σ ⇒
    wfvmap Σ σ ∧ sinst σ st1 = st2) ∧
 ∀tl1 tl2 f σ.
    complete f ∧ wfvmap Σ f ∧
    (∀t n s. MEM t tl1 ∧ (n,s) ∈ tfv t ⇒ (n,s) ∉ sfv s) ∧
    (∀t. MEM t tl1 ⇒ wft Σ t) ∧
    (∀t. MEM t tl2 ⇒ wft Σ t) ∧
    tlmatch Σ {} tl1 tl2 f = SOME σ ⇒
    wfvmap Σ σ ∧
    (∀n. n < LENGTH tl1 ⇒ tinst σ (EL n tl1) = EL n tl2)
Proof
  ho_match_mp_tac original_tm_induction>> rw[]
  >- ‘complete σ ∧ f ⊑ σ ∧
      FDOM σ = FDOM f ∪ tfv (Var s0 st1)’
      by (irule tmatch_property >>
         gs[tfv_def,PULL_EXISTS] >>
         qexistsl [‘t2’,‘Σ’] >> metis_tac[]) >>
     drule_then assume_tac wfvmap_SUBMAP >>
     first_x_assum irule >> simp[] >>
     rpt gen_tac >> disch_tac >>
     gs[wft_def,tmatch_def,AllCaseEqs()] (* 2 *)
     >- (gs[complete_def] >> metis_tac[])
     >- ‘σ ' (s0,st1) = t2’
        by (gs[fmap_EXT] >>
        first_x_assum (qspecl_then [‘(s0,st1)’] assume_tac)
        >> gs[FAPPLY_FUPDATE]) >> gs[] >>
        ‘sort_of Σ t2 = sinst f0 st1’ suffices_by cheat >>
        ‘wfvmap Σ f0 ∧ sinst f0 st1 = sort_of Σ t2’
         suffices_by metis_tac[] >>
        first_x_assum irule >>
        
     drule tmatch_tinst >> 
     simp[wfvmap_def]

        drule_then assume_tac tmatch_property >>
    
        
Theorem tinst_wft:
 wft Σf t ⇒ ∀σ. wfvmap Σf σ ⇒ wft Σf (tinst σ t)
Proof
 Induct_on ‘t’ >> rw[tinst_def,wft_def] (* 2 *) 
 >- (Cases_on ‘s’ >> rw[] >> gs[wft_def,EVERY_MEM] (* 2 *) >>
    rename [‘St s l’]
    >- (rw[MEM_MAP] >> last_x_assum irule >> simp[]) >>
    gs[wfvmap_def]) >>
    
    
 
QED
     

Theorem matchs_trans:
  IS_SOME (tlmatch Σf lcs t1 t2 σ) ∧
  IS_SOME (tlmatch Σf lcs t2 t3 σ) ⇒ 
  IS_SOME (tlmatch Σf lcs t1 t3 σ)
Proof 
  Cases_on ‘t1’ >> Cases_on ‘t2’ >> Cases_on ‘t3’ >>
  Cases_on ‘tmatch Σf lcs h h' σ’ >> 
  Cases_on ‘tmatch Σf lcs h' h'' σ’ >> gs[tmatch_def] >>
  rw[] >> 
  
Theorem finst_subst_wff:
 wff (Σf,Σp) ϕ ⇒ ∀σ. wfvmap Σf σ ⇒ wff (Σf,Σp) (finst σ ϕ)
Proof
 Induct_on ‘ϕ’ >> rw[finst_def] (* 2 *) >> gs[] >>
 cheat
QED

        
Theorem fVar_subst_wff:
 wff (Σf,Σp) ϕ ∧ wff (Σf,Σp) f ∧ wfarg Σf vl ⇒
 wff (Σf,Σp) (fVar_subst Σf (P,vl,ϕ:form) f)
Proof
 Induct_on ‘f’ >> rw[fVar_subst_def] (* 2 *) >> gs[] >>
 cheat
QED 

(*∀A a:mem(A). P(a).
 inst to \B b:mem(B). Q(a:mem(A))
 then need to rename A a into A' a':mem(A). *)


Definition fVar_substs_def:
  fVar_substs Σf [] f = f ∧
  fVar_substs Σf (h :: t) f = fVar_substs Σf t (fVar_subst Σf h f)
End 
 

Definition fVar_insts_def:
  fVar_insts Σ f = {fVar_substs (FST Σ) l f | EVERY (wff Σ) (MAP (SND o SND) l)}
End

(*fVar concrete instances*)
         
Definition fVar_concr_insts_def:
  fVar_concr_insts Σ f = fVar_insts Σ f ∩ {ϕ | ffVar ϕ = {}}
End  

Definition is_concr_def:
  is_concr f ⇔ (ffVar f = {})
End  
                
(*                     

Definition pvariantt_def:
  pvariantt vs (Var n s) =
  if (n,s) ∈ vs then pvariantt vs (Var (n ^ "'") s)
  else 
*)
  
(*
Definition is_eqv_def:
  is_eqv 
End
*)

Overload TO_FMAP = “FUPDATE_LIST FEMPTY”        




(*say, if we start with a:mem(A),b:mem(B), we do not want to make it a':mem(A') b':mem(B'), but only a':mem(A),b':mem(B),
 therefore we do not just add prim to every variable we spot, bu try to do it uniformly by tinst *)          

Definition refl_of:
 refl_of (vl1,vl2) ϕ = finst (TO_FMAP (ZIP (vl1 ++ vl2,MAP (UNCURRY Var) (vl1 ++ vl1)))) ϕ
End 


Definition sym_of:
 sym_of (vl1,vl2) ϕ =
 IMP ϕ (finst (TO_FMAP (ZIP (vl1 ++ vl2,MAP (UNCURRY Var) (vl2 ++ vl1)))) ϕ)
End 

(*assume the list are all distinct*)
(*
Definition mk_prim_fmap:
  mk_prim_fmap σ [] = (σ,[]) ∧
  mk_prim_fmap σ ((n,s) :: t) = mk_prim_fmap (σ |+ ((n,s),Var(n',s))) (MAP )
*)

(*abs of A,B a in A, b in B
         C D c in C, d in D are equal.
 no way for a:A b:B, and c:C,d:D to be equal, since A B C D are free.
 abs of a:mem(A),a':mem(A) are equal.*)

(* 
Definition mk_abs_vl:
  mk_abs_vl σ [] = (σ,[]) ∧
  mk_abs_vl σ ((n,s) :: t) =
  let σ1 = (σ |+ ((n,s),Var(toString 0,s)))
  in
  mk_abs_vl σ1 (MAP (λ(n,s). (n,sinst σ1 s)) t)
End
*)

(*require all the names are different, UNZIP to two list, both of the list satisfies ALL_DISTINCT
  if do so then do not require keeping information in an accumulator.
  only former variables can affect later variables but not vice versa.
*)

        

Definition abs_list_eqv_def:
  (abs_list_eqv ([]:(string # sort) list) ([]:(string # sort) list) ⇔ T) ∧
  (abs_list_eqv ((n1,s1) :: vl1) ((n2,s2) :: vl2) ⇔
   s1 = s2 ∧ (let σ = FEMPTY |+ ((n2,s1),Var n1 s1) in abs_list_eqv vl1 (MAP (λ(n,s). (n,sinst σ s)) vl2))) ∧
  (abs_list_eqv [] (h :: t) = F) ∧
  (abs_list_eqv (h :: t) [] = F)
End

Definition tlfv_def:
   tlfv tl = BIGUNION (IMAGE tfv (set tl))
End
   
Definition sdepend_def:
  sdepend (St n tl) v ⇔ v ∈ tlfv tl
End

Definition wfv_def:
  wfv Σf (n,s) ⇔ EVERY (wft Σf) (stms s)
End  

(*so f:A->B A is ill-formed*)       
Definition wfarg_def:
  wfarg Σf vl ⇔
  ALL_DISTINCT vl ∧
  EVERY (wfv Σf) vl ∧
  ∀n1 n2. n1 < n2 ∧ n2 ≤ LENGTH vl ⇒ ¬(sdepend (SND (EL n1 vl)) (EL n2 vl))
End



Definition vlcanmch_def:
  vlcanmch Σf vl1 vl2 ⇔
  IS_SOME
  (tlmatch Σf {} (MAP (UNCURRY Var) vl1) (MAP (UNCURRY Var) vl2) FEMPTY)
End


Definition tlcanmch_def:
  tlcanmch Σf tl1 tl2 ⇔
  IS_SOME (tlmatch Σf {} tl1 tl2 FEMPTY)
End

Definition arg_eqv_def:
  arg_eqv Σf vl1 vl2 ⇔ (vlcanmch Σf vl1 vl2 ∧ vlcanmch Σf vl2 vl1)
End  

(*     
Theorem tlcanmch_refl:
  tlmatch Σf {} tl tl FEMPTY =
  let vl = SET_TO_LIST 
  SOME (TO_FMAP (ZIP (tl, MAP (UNCURRY Var) tl)))
Proof
*)
        
(*
Theorem vlmatchable_sym:
 vlmatchable Σf vl1 vl2 ⇔ vlmatchable Σf vl2 vl1
Proof
 metis_tac[vlmatchable_def]
QED              



Theorem vlmatchable_refl:
 vlmatchable Σf vl vl
Proof
 
QED                 
*)

          
(*Theorem abs_list_sym:
  ∀l1 l2.
  ALL_DISTINCT (MAP FST (l1 ++ l2)) ⇒
  (abs_list_eqv l1 l2 ⇔ abs_list_eqv l2 l1)
Proof
  Induct_on ‘l1’ >> Induct_on ‘l2’ >> simp[abs_list_eqv_def] >>
  Cases_on ‘h’ >> Cases_on ‘h'’ >>
  rename [‘FST (n1,s1) ≠ FST (n2,s2)’] >> simp[abs_list_eqv_def] >>
  rw[] >> Cases_on ‘s1 = s2’ >> simp[] >> rw[EQ_IMP_THM] (* 2 *) >> cheat
QED  *)
  
(*        
Definition abs_list_eqv:
  (abs_list_eqv ([]:(string # sort) list) ([]:(string # sort) list) ⇔ T) ∧
  (abs_list_eqv ((n1,s1) :: vl1) ((n2,s2) :: vl2) ⇔
   s1 = s2 ∧ (let σ = FEMPTY |+ ((n2,s1),Var (n1,s1)) in abs_list_eqv (MAP ((sinst σ) o SND) vl1) (MAP ((sinst σ) o SND) vl2)))
End   
*)

(*            
Definition trans_of:
 trans_of (vl1,vl2,vl3) ϕ =
 let vl3 = MAP (tinst (TO_FMAP (MAP (λ(n,s) => Var (n^"'"))))) vl2
 in
 IMP (CONJ ϕ (finst (TO_FMAP (ZIP (vl1 ++ vl2,MAP (UNCURRY Var) (vl2 ++ vl1)))) ϕ)
End 
*)
                        
((∀ax. ax ∈ axs ⇒ wff Σ ax) ⇒
        (∀axs. ax ∈ axs ⇒ Thm Σ axs (ffv ax) {} ax)) ∧


Definition wffs_def:
 wffs Σ fs ⇔ (∀f. f ∈ fs ⇒ wff Σ f)
End 
                  
Inductive Thm:
[~AX:] (∀axs ax. wffs Σ axs ∧ ax ∈ axs ⇒ Thm Σ axs (ffv ax) {} ax) ∧
[~FalseE1:]
  (∀Γ A f. Thm Σ axs Γ (A ∪ {NEG f}) False ⇒ Thm Σ axs Γ A f) ∧
[~FalseE2:]
  (∀Γ A f. Thm Σ axs (Γ ∪ ffv f) A False ⇒ Thm Σ axs Γ A f) ∧
[~assume:]
  (∀c:form. wff Σ c ⇒ Thm Σ axs (ffv c) {c} c) ∧
[~mp:]
  (∀Γ1 Γ2 A1 A2 f1 f2.
     Thm Σ axs Γ1 A1 (IMP f1 f2) ∧ Thm Σ axs Γ2 A2 f1 ⇒
     Thm Σ axs (Γ1 ∪ Γ2) (A1 ∪ A2) f2) ∧
[~disch:]
  (∀Γ A f a.
     Thm Σ axs Γ A f ∧ wff Σ a ∧ ffv a ⊆ Γ ⇒ 
     Thm Σ axs Γ (A DELETE a) (IMP a f)) ∧
[~refl:]
  (∀t. wft (FST Σ) t ⇒ 
     Thm Σ axs (tfv t) {} (EQ t t)) ∧
[~sym:]
  (∀Γ A t1 t2.
     Thm Σ axs Γ A (EQ t1 t2) ⇒
     Thm Σ axs Γ A (EQ t2 t1)) ∧
[~trans:]
  (∀Γ1 Γ2 A1 A2 t1 t2 t3.
     Thm Σ axs Γ1 A1 (EQ t1 t2) ∧ Thm Σ axs Γ2 A2 (EQ t2 t3) ⇒
     Thm Σ axs (Γ1 ∪ Γ2) (A1 ∪ A2) (EQ t1 t3)) ∧
[~ALLI:]
  (∀Γ A f x s.
     Thm Σ axs Γ A f ∧ wfs (FST Σ) s ∧
     (sfv s) ⊆ Γ ∧
     (∀n0 s0. (n0,s0) ∈ Γ ⇒ (x,s) ∉ sfv v) ∧
     (∀a. a ∈ A ⇒ (x,s) ∉ ffv a) ⇒
     Thm Σ axs (Γ DELETE (x,s)) A (FALL x s f)) ∧
[~ALLE:]
  (∀Γ A n s f t.
    Thm Σ axs Γ A (FALL n s f) ∧ wft (FST Σ) t ∧ sort_of (FST Σ) t = s ⇒
    Thm Σ axs (Γ ∪ tfv t) A (fsubst n s t f)) ∧
[~fvar_inst:]
  (∀Γ A f P:string vl:(string # sort) list ϕ:form.
     Thm Σ axs Γ A f ⇒ Thm Σ axs (Γ ∪ (ffv ϕ)) (IMAGE (fVar_subst (FST Σ) (P,vl,ϕ)) A)
                     (fVar_subst (FST Σ) (P,vl,ϕ) f)) ∧
[~pred_spec:]
  ∀pname argl ϕ.
  wff Σ ϕ ∧ wfarg (FST Σ) argl ∧
  ffv ϕ ⊆ set argl ⇒
  (Thm (new_psym Σ pname argl) axs (ffv ϕ) {}
   (IFF (Pred pname (MAP (UNCURRY Var) argl)) ϕ))
End


        

(*
(*   
[~fun_spec:]
  
  Thm Σ axs Γ {} (EXL vl1 True) ∧
  ALL_DISTINCT (vl1 ++ vl2 ++ vl3) ∧
  arg_eqv (FST Σ) vl1 vl2 ∧ arg_eqv (FST Σ) vl2 vl3 ∧
  Thm Σ axs Γ0 A0
  (mk_eqv ϕ vl1 vl2 vl3) 

  
  (*same pattern*)
  IS_SOME (tlmatch (FST Σ) {} (MAP (UNCURRY Var) vl1)
                              (MAP (UNCURRY Var) vl2) FEMPTY) ∧
  IS_SOME (tlmatch (FST Σ) {} (MAP (UNCURRY Var) vl2)
                              (MAP (UNCURRY Var) vl3) FEMPTY) ∧
  Thm Σ axs Γ0 A0
  (FALL vl1 (finst (THE (tlmatch (FST Σ) ∅ (MAP (UNCURRY Var) (vl1++vl2))
                (MAP (UNCURRY Var) (vl1++vl1))  FEMPTY)) ϕ)) ∧
  Thm Σ axs Γ0 A0
  FALL (vl1 ++ vl2)
  (IMP ϕ
      (finst (THE (tlmatch (FST Σ) ∅ (MAP (UNCURRY Var) (vl1++vl2))
                   (MAP (UNCURRY Var) (vl2++vl1))  FEMPTY)) ϕ)) ∧
  FALL (vl1 ++ vl2 ++ vl3)              
  (IMP
      (CONJ
       (finst (THE (tlmatch (FST Σ) ∅ (MAP (UNCURRY Var) (vl1++vl2))
                    (MAP (UNCURRY Var) (vl2++vl1))  FEMPTY)) ϕ)
       (finst (THE (tlmatch (FST Σ) ∅ (MAP (UNCURRY Var) (vl1++vl2))
                    (MAP (UNCURRY Var) (vl2++vl3))  FEMPTY)) ϕ))
      (finst (THE (tlmatch (FST Σ) ∅ (MAP (UNCURRY Var) (vl1++vl2))
                   (MAP (UNCURRY Var) (vl1++vl3))  FEMPTY)) ϕ)) ∧

         
  ⇒ Thm (new_fsym Γ f s vl) axs A (fVar_subst (FST Σ) )  *) 
*)        

(*To prove:
-- every free variable is included by Γ
-- fvar stuff
-- tranalation
-- sig extend, ax extend
-- thm inst can be derived from allI and allE
-- sufficient to prove results for theorems without assumptions
-- sometimes do need to strip quantifiers first before inst.
   ∀A B f:A->B. ...
   ∀A B a:mem(A) b:mem(B).

*)

        (*
Theorem Thm_no_assum_equiv:
  Thm Σ axs Γ A f ⇔ Thm Σ axs {} {} (GENL Γ)
Proof
cheat
QED
*)

                        
(*sig extend*)

(*      
Theorem Sig_extend:
  Σ1 ⊆ Σ2 ⇒ Thm Σ1 axs Γ A f ⇒ Thm Σ2 axs Γ A f
Proof
cheat
QED
*)

              
(*⊥ implies everything and ~phi |- ⊥ *)

(*formalise *)    
Inductive Thm1:
[~AX:] (∀ax. ax ∈ axs ⇒ Thm1 Σ axs (ffv ax) {} ax) ∧
[~FalseE1:]
  (∀Γ A f. Thm1 Σ axs Γ (A ∪ {NEG f}) False ⇒ Thm1 Σ axs Γ A f) ∧
[~FalseE2:]
  (∀Γ A f. Thm1 Σ axs (Γ ∪ ffv f) A False ⇒ Thm1 Σ axs Γ A f) ∧
[~assume:]
  (∀c:form. Thm1 Σ axs (ffv c) {c} c) ∧
[~TrueI:]
  (∀Γ A. Thm1 Σ axs Γ A True) ∧
[~mp:]
  (∀Γ1 Γ2 A1 A2 f1 f2.
     Thm1 Σ axs Γ1 A1 (IMP f1 f2) ∧ Thm1 Σ axs Γ2 A2 f1 ⇒
     Thm1 Σ axs (Γ1 ∪ Γ2) (A1 ∪ A2) f2) ∧
[~disch:]
  (∀Γ A f.
     Thm1 Σ axs Γ A f ⇒
     Thm1 Σ axs Γ (A DELETE a) (IMP a f)) ∧
[~refl:]
  (∀t.
     Thm1 Σ axs (tfv t) {} (EQ t t)) ∧
[~sym:]
  (∀Γ A t1 t2.
     Thm1 Σ axs Γ A (EQ t1 t2) ⇒
     Thm1 Σ axs Γ A (EQ t2 t1)) ∧
[~trans:]
  (∀Γ1 Γ2 A1 A2 t1 t2 t3.
     Thm1 Σ axs Γ1 A1 (EQ t1 t2) ∧ Thm1 Σ axs Γ2 A2 (EQ t2 t3) ⇒
     Thm1 Σ axs (Γ1 ∪ Γ2) (A1 ∪ A2) (EQ t1 t3)) ∧
[~ALLI:]
  (∀Γ A f x s.
     Thm1 Σ axs Γ A f ∧
     (sfv s) ⊆ Γ ∧
     (∀n0 s0. (n0,s0) ∈ Γ ⇒ (x,s) ∉ sfv v) ∧
     (∀a. a ∈ A ⇒ (x,s) ∉ ffv a) ⇒
     Thm1 Σ axs (Γ DELETE (x,s)) A (FALL x s f)) ∧
[~ALLE:]
  (∀Γ A n s f t.
    Thm1 Σ axs Γ A (FALL n s f) ∧ sort_of t = s ⇒
    Thm1 Σ axs (Γ ∪ tfv t) A (fsubst n s t f)) ∧
[~pred_spec:]
  ∀pname argl ϕ.
  ffv ϕ ⊆ set argl ⇒
  (Thm1 (Σ ∪ {(pname,argl)}) axs (ffv ϕ) {}
   (IFF (Pred pname (MAP (UNCURRY Var) argl)) ϕ)) ∧
[~fun_spec:]
  
End

(*start with the LHS, subst one by one. So if P |-> Q, Q |->R, the result would be P |-> R. In particular, can subst a subst*)


(*subst with all well formed formula yields a wf formula.*)        

Definition isfsym_def:
  isfsym fsig f = IS_SOME (fsig ' f)
End


Definition ispsym_def:
  ispsym psig p = IS_SOME (psig ' p)
End
                   


         


() not correc because might by multiple occurrence of fvar in the same axiom.

Theorem remove_fVar_is_fine:
  ∀ϕ. ffVar ϕ = {} ⇒
  Thm Σ axs Γ {} ϕ ⇔ Thm Σ ((BIGUNION (IMAGE (fVarinsts Σ) axs)) ∩ {f | ffVar f = {}}) Γ {} ϕ
Proof    
  

        

Datatype: thm = thm ((string # sort) set) (form set) form
End

Definition tmatchable_def:
  tmatchable lcs t1 t2 f ⇔ ∃σ. tmatch lcs t1 t2 f = SOME σ
End  


Definition tlmatchable_def:
  tlmatchable lcs tl1 tl2 f ⇔ ∃σ. tlmatch lcs tl1 tl2 f = SOME σ
End     

(*well-formed abstraction arguments, free variables in previous arguments does not appear as bound variable later*)        
Definition wfaa_def:
  wfaa vl = ∀n1 n2. n1 < n2 ⇒ EL n1 vl ∉ sfv (SND (EL n2 vl)) ∪ {EL n2 vl}
End  
        
Definition ffVar_def:
  ffVar s False = s
  ffVar s (Pred _ _) = s
  ffVar s (IMP f1 f2) = s ∪ ffVar f1 ∪ ffVar f2
  ffVar s (FALL n st b) = s ∪ ffVar b
  ffVar s (fVar P tl) =
  if ∃P0 tl0. (P0,tl0) ∈ s ∧ tlmatchable 
End  

Theorem remove_fVar_is_fine:
  ∀axs:thm set.
    (∀ax. ax ∈ axs ⇒
          ∀P vl. (P,vl) ∈ thmfVar ax ⇒ ()) ⇒
    ∀Γ A f. thmfV Thm Γ A f ⇒ Thm1 Γ A f
Proof    
  

        
val _ = export_theory();

