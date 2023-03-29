open HolKernel Parse boolLib bossLib;
open stringTheory finite_setTheory pred_setTheory listTheory;
open finite_mapTheory;
val _ = new_theory "tm";


Datatype: term = Var string sort | Fn string sort (term list)
               | Bound num;
          sort = St string (term list)
End

        
Definition tfv_def:
  tfv (Var n s) = {(n,s)} ∪ sfv s ∧
  tfv (Fn n s tl) = BIGUNION (set (MAP tfv tl)) ∪ sfv s ∧
  tfv (Bound _) = {} ∧
  sfv (St n tl) = BIGUNION (set (MAP tfv tl))
Termination
WF_REL_TAC ‘measure (λs. case s of INL t => term_size t
                                | INR s => sort_size s)’                        
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
  tfv (Fn n s tl) = BIGUNION {tfv t | MEM t tl} ∪ sfv s ∧
  tfv (Bound _ ) = {} ∧
  sfv (St n tl) = BIGUNION {tfv t | MEM t tl}
Proof
  simp[tfv_def,PULL_EXISTS] >> simp[Once EXTENSION,PULL_EXISTS,MEM_MAP,LIST_TO_SET_MAP,IMAGE_DEF,EXTENSION]  
QED


Definition tinst_def[simp]:
  (tinst (σ:string # sort |-> term) (Var n s) =
   if (n,s) ∉ FDOM σ then Var n (sinst σ s)
   else σ ' (n,s)) ∧
  (tinst σ (Fn f s tl) =  Fn f (sinst σ s) (MAP (tinst σ) tl)) ∧
  tinst σ (Bound i) = Bound i ∧
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

Definition sort_of_def:
  sort_of (Var n s) = s ∧
  sort_of (Fn f s l) = s
End  



val term_size_def = DB.fetch "-" "term_size_def"
val term_size_eq = DB.fetch "-" "term_size_eq"
val _ = export_rewrites ["term_size_def"]

Theorem MEM_list_size_leq:
  ∀l x.MEM x l ⇒ size x ≤ list_size size l
Proof
  Induct_on ‘l’ >> gs[list_size_def] >> rw[] (* 2 *)
  >- simp[] >> first_x_assum drule >> rw[]
QED  

 
Theorem tm_tree_size_less:
  (∀t n st. (n,st) ∈ tfv t ⇒
            sort_size st < term_size t) ∧
  (∀s n st.(n,st) ∈ sfv s ⇒
           sort_size st < sort_size s)
Proof
  ho_match_mp_tac better_tm_induction >>
  rw[term_size_def] (* 4 *)
  >- simp[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule_all >> rw[] >>
     ‘term_size t ≤ term1_size l’
       suffices_by rw[] >>
     rw[term_size_eq] >>
     drule MEM_list_size_leq >> metis_tac[]) >>
  first_x_assum drule_all >> rw[] >>
  ‘term_size t ≤ term1_size l’
       suffices_by rw[] >>
     rw[term_size_eq] >>
     drule MEM_list_size_leq >> metis_tac[]
QED     

Theorem tm_tree_WF:
  ∀s n.(n,s) ∉ sfv s  
Proof
  rpt strip_tac >>
  ‘sort_size s < sort_size s’ by metis_tac[tm_tree_size_less] >> gs[]
QED  


Definition is_bound_def:
is_bound (Var _ _) = F ∧
is_bound (Fn _ _ _) = F ∧
is_bound (Bound _) = T
End


Definition tbounds_def:
  tbounds (Bound i) = {i} ∧
  tbounds (Var n s) = sbounds s ∧
  tbounds (Fn n s l) = BIGUNION (set (MAP tbounds l)) ∪ sbounds s ∧
  sbounds (St n tl) = BIGUNION (set (MAP tbounds tl))
Termination
WF_REL_TAC ‘measure (λs. case s of INL t => term_size t
                                | INR s => sort_size s)’                        
End


Theorem tbounds_thm:
  tbounds (Bound i) = {i} ∧
  tbounds (Var n s) = sbounds s ∧
  tbounds (Fn n s l) = BIGUNION {tbounds t | MEM t l} ∪ sbounds s ∧
  sbounds (St n tl) = BIGUNION {tbounds t | MEM t tl}
Proof
rw[tbounds_def,EXTENSION,MEM_MAP]
QED

        
Definition no_bound_def:
  no_bound σ ⇔ ∀x. x ∈ FDOM σ ⇒ tbounds  (σ ' x) = {}
End         


Theorem is_bound_alt:
is_bound t ⇔ ∃i. t = Bound i
Proof
Cases_on ‘t’ >> rw[is_bound_def]
QED
            
Theorem no_bound_not_bound:
  no_bound σ ∧ x ∈ FDOM σ ⇒ ¬(is_bound (σ ' x))
Proof
  rw[no_bound_def,is_bound_alt] >> strip_tac >>
  first_x_assum drule  >> gs[tbounds_def]
QED  

          
Definition tmatch_def:
  (tmatch (lcs:string # sort -> bool) (Var n s) ct (f:string # sort |-> term) =
   if tbounds ct ≠ {} then NONE else
   if  (n,s) ∈ lcs then
     if Var n s = ct then SOME f else NONE
   else 
     if (n,s) ∈ FDOM f then
       if ct = f ' (n, s) then SOME f else NONE
     else
       case smatch lcs s (sort_of ct) f of
         SOME f0 => SOME (f0 |+ ((n, s),ct))
       | _ => NONE) ∧
  (tmatch lcs (Fn f1 s1 tl1) (Fn f2 s2 tl2) f =
   if f1 = f2 then
     (case tlmatch lcs tl1 tl2 f of
       SOME σ0 => smatch lcs s1 s2 σ0
      | _ => NONE)
   else NONE) ∧
  (tmatch lcs (Fn _ _ _ ) (Var _ _)  f = NONE) ∧
  (tmatch lcs (Fn _ _ _ ) (Bound _)  f = NONE) ∧
  (tmatch lcs (Bound i) (Bound j) f = if i = j then SOME f else NONE) ∧
  (tmatch lcs (Bound i) (Var _ _) f = NONE) ∧
  (tmatch lcs (Bound i) (Fn _ _ _) f = NONE) ∧
  (smatch (lcs:string # sort -> bool) (St n1 tl1) (St n2 tl2) f =
   if n1 = n2 then tlmatch lcs tl1 tl2 f else NONE) ∧
  tlmatch lcs [] [] f = SOME f ∧
  tlmatch lcs [] (h :: t) f = NONE ∧
  tlmatch lcs (h :: t) [] f = NONE ∧
  (tlmatch lcs (h1 :: t1) (h2 :: t2) f =
   case tmatch lcs h1 h2 f of
     SOME f1 => tlmatch lcs t1 t2 f1
   | _ => NONE)
Termination
  WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,t1,t2,_) => term_size t1 + term_size t2 
         | INR (INL (_,s1,s2,_)) => sort_size s1 + sort_size s2
         | INR (INR (_,tl1,tl2,_)) => term1_size tl1 + term1_size tl2)’   >>
   rw[] >> Cases_on ‘ct’ >> gs[sort_of_def,tbounds_def]
End   
                
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
          

        

           
(*all
the variables of sort 𝑠 must also be in Γ \ {𝑥 } automatically satisfied?
 not true ,because x might be completely fresh

∀x:s1. P(x:s2) just means the quantifier is not on x:s2.

allI x does not occur in the assumption list automatically true?       
*)

        
(*consistant variable map*)        
Definition cstt_def:
  cstt σ ⇔
  (∀n s. (n,s) ∈ FDOM σ ⇒ sort_of (σ ' (n,s)) = sinst σ s)
End

(*slash u plus ⊎*)
Theorem fmap_fv_inst_eq:
  (∀t σ1 σ2.
  DRESTRICT σ1 (tfv t) = DRESTRICT σ2 (tfv t) ⇒
  tinst σ1 t = tinst σ2 t) ∧
  (∀s σ1 σ2.
   DRESTRICT σ1 (sfv s) = DRESTRICT σ2 (sfv s) ⇒ sinst σ1 s = sinst σ2 s) 
Proof
  ho_match_mp_tac better_tm_induction >>
  rw[] (* 4 *)
  >- (‘(s0,s) ∈ FDOM σ1 <=> (s0,s) ∈ FDOM σ2’
      by (gs[DRESTRICT_DEF,fmap_EXT,EXTENSION] >>
         metis_tac[]) >>
     Cases_on ‘(s0,s) ∈ FDOM σ1’ >> gs[] (* 2 *)
     >- (gs[DRESTRICT_DEF,fmap_EXT,EXTENSION] >>
        metis_tac[]) >>
     first_x_assum irule >> 
     irule DRESTRICT_SUBSET >>
     first_x_assum $ irule_at Any >>
     rw[SUBSET_DEF])
  >- (first_x_assum irule >>
     irule DRESTRICT_SUBSET >>
     first_x_assum $ irule_at Any >>
     rw[SUBSET_DEF]) >>
  gs[MAP_EQ_f,EVERY_MEM] >> rw[] >>
  first_x_assum irule >>
  rw[] >> irule DRESTRICT_SUBSET >> 
  first_x_assum $ irule_at Any >> 
  rw[SUBSET_DEF] >> metis_tac[]
QED  

val fmap_tfv_tinst_eq = cj 1 fmap_fv_inst_eq
val fmap_sfv_sinst_eq = cj 2 fmap_fv_inst_eq



Theorem tinst_vmap_id:
  (∀t σ.
  (∀n s. (n,s) ∈ FDOM σ ∩ tfv t ⇒ σ ' (n,s) = Var n s) ⇒
  tinst σ t = t) ∧
  (∀st σ.
  (∀n s. (n,s) ∈ FDOM σ ∩ sfv st ⇒ σ ' (n,s) = Var n s) ⇒
  sinst σ st = st)
Proof
  ho_match_mp_tac better_tm_induction >> rw[tinst_def]
  >> (‘MAP (λa. tinst σ a) l = MAP I l’ suffices_by simp[] >>
  rw[MAP_EQ_f] >> gvs[PULL_EXISTS] >>
  first_x_assum irule >> rw[] >> first_x_assum irule >> metis_tac[])
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
  ho_match_mp_tac better_tm_induction >> rw[] (* 5 *)
  >- simp[] >- (disj2_tac >> first_x_assum irule >> metis_tac[])
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> metis_tac[]) >>
  metis_tac[]
QED

(* in the case that start with an f a:1->A and have not assigned a to anywhere else, A is not stores*)


Theorem tlmatch_LENGTH:
  ∀tl1 tl2 f σ.
  tlmatch lcs tl1 tl2 f = SOME σ ⇒
  LENGTH tl1 = LENGTH tl2
Proof
  Induct_on ‘tl1’ >> Induct_on ‘tl2’ >>
  gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >>
  metis_tac[]
QED


Definition is_cont_def:
  is_cont ct ⇔ ∀n s. (n,s) ∈ ct ⇒ sfv s ⊆ ct
End

Theorem tfv_is_cont:
 (∀t. is_cont (tfv t)) ∧
 (∀s. is_cont (sfv s))
Proof
 ho_match_mp_tac better_tm_induction >>
 gs[tfv_def,is_cont_def,SUBSET_DEF,PULL_EXISTS] >>
 rw[] (* 5 *)
 >- simp[]
 >- (disj2_tac >> first_x_assum irule >> metis_tac[])
 >- (disj1_tac >> gs[MEM_MAP] >> metis_tac[])
 >- (disj2_tac >> first_x_assum irule >> metis_tac[]) >>
 qexists_tac ‘s’ >> gs[MEM_MAP] >>
 metis_tac[]
QED
        
Theorem wfvmap_cont_DRESTRICT:
  cstt σ ∧ complete σ ∧ is_cont s ⇒
  cstt (DRESTRICT σ s)
Proof
  rw[cstt_def,is_cont_def,DRESTRICT_DEF] >>
  irule fmap_sfv_sinst_eq >>
  rw[Once EQ_SYM_EQ] >> AP_TERM_TAC >> 
  rw[Once INTER_COMM,GSYM SUBSET_INTER_ABSORPTION] >>
  first_x_assum irule>> metis_tac[]
QED 

(*****)
Theorem match_complete:
  (∀t1 t2 f σ.
     complete f ∧
     tmatch {} t1 t2 f = SOME σ ⇒
     tfv t1 ⊆ FDOM σ ∧ FDOM f ⊆ FDOM σ ∧ complete σ) ∧
  (∀s1 s2 f σ.
     complete f ∧
     smatch {} s1 s2 f = SOME σ ⇒
     sfv s1 ⊆ FDOM σ ∧ FDOM f ⊆ FDOM σ ∧ complete σ) ∧
  (∀tl1 tl2 f σ.
     complete f ∧
     tlmatch {} tl1 tl2 f = SOME σ ⇒
     (∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧
     FDOM f ⊆ FDOM σ ∧ complete σ)
Proof
  ho_match_mp_tac original_tm_induction >> rw[] (* 19 *)
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
  >- (Cases_on ‘t2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rw[SUBSET_DEF] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF] >> metis_tac[])
  >- (Cases_on ‘t2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rw[SUBSET_DEF] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF] >> metis_tac[])
  >- (Cases_on ‘t2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rw[SUBSET_DEF] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF] >> metis_tac[])
  >- (Cases_on ‘t2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rw[SUBSET_DEF] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF] >> metis_tac[]) (*11 remains*)
  >- (Cases_on ‘t2’ >> gs[tmatch_def])
  >- (Cases_on ‘t2’ >> gs[tmatch_def]) (*9 remains*)
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
     rename [‘tlmatch ∅ tl1 tl2 f1 = SOME σ’] >>
     rename [‘tmatch ∅ t1 t2 f = SOME f1’] >> 
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
     rename [‘tmatch ∅ h1 h2 f1 = SOME f2’] >>
     rename [‘tlmatch ∅ tl1 tl2 f2 = SOME σ’] >>
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
     rename [‘tlmatch ∅ tl1 tl2 f1 = SOME σ’] >>
     ‘tfv t1 ⊆ FDOM f1 ∧ FDOM f ⊆ FDOM f1 ∧ complete f1’
      by (first_x_assum irule >> simp[] >>
         qexists_tac ‘h’ >> gs[]) >>
     ‘(∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧ FDOM f1 ⊆ FDOM σ ∧ complete σ’
      by (first_x_assum irule >> simp[] >>
          metis_tac[]) >>
     metis_tac[])
  >- (Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tlmatch ∅ tl1 tl2 f1 = SOME σ’] >>
     rename [‘tmatch ∅ t1 t2 f = SOME f1’] >> 
     ‘tfv t1 ⊆ FDOM f1 ∧ FDOM f ⊆ FDOM f1 ∧ complete f1’
      by (first_x_assum irule >> simp[] >>
         qexists_tac ‘t2’ >> gs[]) >>
     ‘(∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧ FDOM f1 ⊆ FDOM σ ∧ complete σ’
      by (first_x_assum irule >> simp[] >>
          metis_tac[]) >>
     metis_tac[SUBSET_TRANS]) >>
  Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tlmatch ∅ tl1 tl2 f1 = SOME σ’] >>
     rename [‘tmatch ∅ t1 t2 f = SOME f1’] >> 
     ‘tfv t1 ⊆ FDOM f1 ∧ FDOM f ⊆ FDOM f1 ∧ complete f1’
      by (first_x_assum irule >> simp[] >>
         qexists_tac ‘t2’ >> gs[]) >>
     ‘(∀t. MEM t tl1 ⇒ tfv t ⊆ FDOM σ) ∧ FDOM f1 ⊆ FDOM σ ∧ complete σ’
      by (first_x_assum irule >> simp[] >>
          metis_tac[])
QED          

val tmatch_complete = cj 1 match_complete
val smatch_complete = cj 2 match_complete
val tlmatch_complete = cj 3 match_complete


        
Theorem MEM_list_size_leq:
  ∀l x.MEM x l ⇒ size x ≤ list_size size l
Proof
  Induct_on ‘l’ >> gs[list_size_def] >> rw[] (* 2 *)
  >- simp[] >> first_x_assum drule >> rw[]
QED  

 
Theorem tm_tree_size_less:
  (∀t n st. (n,st) ∈ tfv t ⇒
            sort_size st < term_size t) ∧
  (∀s n st.(n,st) ∈ sfv s ⇒
           sort_size st < sort_size s)
Proof
  ho_match_mp_tac better_tm_induction >>
  rw[term_size_def] (* 4 *)
  >- simp[]
  >- (first_x_assum drule >> rw[])
  >- (first_x_assum drule_all >> rw[] >>
     ‘term_size t ≤ term1_size l’
       suffices_by rw[] >>
     rw[term_size_eq] >>
     drule MEM_list_size_leq >> metis_tac[]) >>
  first_x_assum drule_all >> rw[] >>
  ‘term_size t ≤ term1_size l’
       suffices_by rw[] >>
     rw[term_size_eq] >>
     drule MEM_list_size_leq >> metis_tac[]
QED     
            
             
Theorem tm_tree_WF:
  ∀s n.(n,s) ∉ sfv s  
Proof
  rpt strip_tac >>
  ‘sort_size s < sort_size s’ by metis_tac[tm_tree_size_less] >> gs[]
QED  
             
    

Theorem match_SUBMAP:
  (∀t1 t2 f σ.
     complete f ∧
     tmatch {} t1 t2 f = SOME σ ⇒
     f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ tfv t1) ∧
  (∀s1 s2 f σ.
     complete f ∧
     smatch {} s1 s2 f = SOME σ ⇒
     f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ sfv s1) ∧
  (∀tl1 tl2 f σ.
     complete f ∧
     tlmatch {} tl1 tl2 f = SOME σ ⇒
     f ⊑ σ ∧ FDOM σ ⊆ FDOM f ∪ BIGUNION {tfv t | MEM t tl1}) 
Proof
  ho_match_mp_tac original_tm_induction >> rw[] (* 12 *)
  >- (gs[tmatch_def,AllCaseEqs()] >>
     first_x_assum drule_all >> rw[] >>
     irule SUBMAP_TRANS >> 
     qexists_tac ‘f0’ >>  
     rw[SUBMAP_FUPDATE_EQN] >> disj1_tac >>
     gs[SUBSET_DEF] >> metis_tac[tm_tree_WF])
  >- (gs[tmatch_def,AllCaseEqs()] >>
     first_x_assum drule_all >> rw[] >>
     gs[SUBSET_DEF] >> metis_tac[tm_tree_WF]) 
  >- (Cases_on ‘t2’ >>
      gvs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >>
      first_x_assum $ drule_all_then strip_assume_tac >>
      ‘complete σ0’ by metis_tac[tlmatch_complete] >>
      first_x_assum $ drule_all_then strip_assume_tac >>
      metis_tac[SUBMAP_TRANS])
  >- (Cases_on ‘t2’ >>
      gvs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >>
      first_x_assum $ drule_all_then strip_assume_tac >>
      ‘complete σ0’ by metis_tac[tlmatch_complete] >>
      first_x_assum $ drule_all_then strip_assume_tac >>
      gs[SUBSET_DEF] >> metis_tac[])
  >- (Cases_on ‘t2’ >> gs[tmatch_def])
  >- (Cases_on ‘t2’ >> gs[tmatch_def]) 
  >- (Cases_on ‘s2’ >> 
     gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >> metis_tac[])
  >- (Cases_on ‘s2’ >> 
     gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >> metis_tac[])
  >- (drule tlmatch_LENGTH >> rw[] >>
     gs[tmatch_def])
  >- (drule tlmatch_LENGTH >> rw[] >>
     gs[tmatch_def])
  >- (Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tmatch ∅ t1 t2 f’,‘tlmatch ∅ tl1 tl2 f1’]>>
     last_x_assum (drule_all_then strip_assume_tac) >>
     ‘complete f1’ by metis_tac[tmatch_complete] >>
     ‘f1 ⊑ σ ∧
      FDOM σ ⊆ FDOM f1 ∪ BIGUNION {tfv t | MEM t tl1}’
      by metis_tac[] >>
     metis_tac[SUBMAP_TRANS]) >>
  Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
  rename [‘tmatch ∅ t1 t2 f’,‘tlmatch ∅ tl1 tl2 f1’]>>
  last_x_assum (drule_all_then strip_assume_tac) >>
  ‘complete f1’ by metis_tac[tmatch_complete] >>
  ‘f1 ⊑ σ ∧
   FDOM σ ⊆ FDOM f1 ∪ BIGUNION {tfv t | MEM t tl1}’
    by metis_tac[] >>
  gs[SUBSET_DEF] >> metis_tac[]
QED

val tmatch_SUBMAP = cj 1 match_SUBMAP
val smatch_SUBMAP = cj 2 match_SUBMAP
val tlmatch_SUBMAP = cj 3 match_SUBMAP
        


Theorem tmatch_FDOM_SUBMAP:
  (∀t1 t2 f σ.
        complete f ∧ 
        tmatch ∅ t1 t2 f = SOME σ ⇒
        complete σ ∧
        f ⊑ σ ∧ FDOM σ = FDOM f ∪ tfv t1) ∧
     (∀s1 s2 f σ.
        complete f ∧ 
        smatch ∅ s1 s2 f = SOME σ ⇒
        complete σ ∧
        f ⊑ σ ∧ FDOM σ = FDOM f ∪ sfv s1) ∧
     ∀tl1 tl2 f σ.
       complete f ∧ 
       tlmatch ∅ tl1 tl2 f = SOME σ ⇒
       complete σ ∧
       f ⊑ σ ∧ FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1}
Proof
 rw[] (* 9 *)
 >- metis_tac[match_complete]
 >- metis_tac[match_SUBMAP]
 >- (rw[GSYM SUBSET_ANTISYM_EQ] (* 3 *)
    >> metis_tac[tmatch_SUBMAP,match_complete])
 >- metis_tac[match_complete]
 >- metis_tac[match_SUBMAP]
 >- (rw[GSYM SUBSET_ANTISYM_EQ] (* 3 *)
    >> metis_tac[match_SUBMAP,match_complete])
 >- metis_tac[match_complete]
 >- metis_tac[match_SUBMAP] >>
 rw[GSYM SUBSET_ANTISYM_EQ] (* 3 *)
 >- metis_tac[match_SUBMAP]
 >- metis_tac[match_complete] >>
 rw[SUBSET_DEF] >> metis_tac[match_complete,SUBSET_DEF]
QED 

Theorem DRESTRICT_SUBMAP_SUBSET:
  f ⊑ g ⇒ ∀s. s ⊆ FDOM f ⇒ DRESTRICT f s = DRESTRICT g s
Proof
  rw[fmap_EXT,SUBMAP_DEF,DRESTRICT_DEF,EXTENSION,SUBSET_DEF] >> metis_tac[]
QED  





val tmatch_property = cj 1 tmatch_FDOM_SUBMAP
val smatch_property = cj 2 tmatch_FDOM_SUBMAP
val tlmatch_property = cj 3 tmatch_FDOM_SUBMAP



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
     complete f ∧ 
     tmatch {} t1 t2 f = SOME σ ⇒
     tinst σ t1 = t2) ∧
 (∀st1 st2 f σ.
    complete f ∧
    smatch {} st1 st2 f = SOME σ  ⇒
    sinst σ st1 = st2) ∧
 (∀tl1 tl2 f σ.
    complete f ∧ 
    tlmatch {} tl1 tl2 f = SOME σ ⇒
    ∀n. n < LENGTH tl1 ⇒ tinst σ (EL n tl1) = EL n tl2)
Proof
 ho_match_mp_tac original_tm_induction >> rw[] (* 5 *)
 >- (‘(s0,st1) ∈ FDOM σ’
      by (drule tmatch_property >> rw[] >>
         first_x_assum
         (qspecl_then [‘Var s0 st1’,‘t2’,‘σ’]
          assume_tac) >>
         gs[] >>
         first_x_assum (drule_then strip_assume_tac)>>
         gs[EXTENSION]) >>
     gs[tmatch_def,AllCaseEqs(),fmap_EXT,SUBMAP_DEF] >>
     first_x_assum (qspecl_then [‘(s0,st1)’]assume_tac) >>
     gs[FAPPLY_FUPDATE])
 >- (Cases_on ‘t2’ >> gs[tmatch_def,AllCaseEqs()] >>
    rename [‘tlmatch ∅ l1 l2 f’] >>
    drule_then assume_tac tlmatch_LENGTH >>
    ‘sinst σ st1 = s’
     by (first_x_assum irule >> simp[] >>
        qexists_tac ‘σ0’ >> simp[] >>
        metis_tac[tlmatch_complete]) >> simp[] >>
    ‘MAP (λa. tinst σ a) l1 = MAP I l2’
      suffices_by simp[] >>
    rw[MAP_EQ_EVERY2,LIST_REL_EL_EQN] >>
    ‘tinst σ (EL n l1) = tinst σ0 (EL n l1)’
     by (irule fmap_tfv_tinst_eq >>
        drule_all_then strip_assume_tac
        tlmatch_property >>
        drule_all_then strip_assume_tac
        smatch_property >>
        rw[Once EQ_SYM_EQ] >>
        irule DRESTRICT_SUBMAP_SUBSET >>
        rw[SUBSET_DEF] >> metis_tac[MEM_EL]) >>
    rw[] >>
    first_x_assum irule>> simp[PULL_EXISTS] >>
    qexists_tac ‘f’>> gs[PULL_EXISTS])
 >- (Cases_on ‘t2’ >> gs[tmatch_def]) (*Q:how does HOL know it?*)
 >- (Cases_on ‘st2’ >> gs[tmatch_def] >>
    rename [‘tlmatch ∅ l1 l2 f’] >>
    drule tlmatch_LENGTH >> rw[] >> 
    ‘MAP (λa. tinst σ a) l1 = MAP I l2’
      suffices_by simp[] >>
    rw[MAP_EQ_EVERY2,LIST_REL_EL_EQN] >>
    first_x_assum irule>> simp[PULL_EXISTS] >>
    qexists_tac ‘f’>> gs[PULL_EXISTS]) >>
 gs[PULL_EXISTS] >>
 Cases_on ‘tl2’ >> fs[tmatch_def,AllCaseEqs()] >>
 rename [‘tmatch ∅ t1 t2 f = SOME f1’,
         ‘tlmatch ∅ tl1 tl2 f1 = SOME σ’] >>
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



Theorem SUBMAP_DRESTRICT_IFF:
  f ⊑ g ⇔ f = DRESTRICT g (FDOM f)
Proof
  rw[SUBMAP_DEF,DRESTRICT_DEF,fmap_EXT,EQ_IMP_THM] (* 3 *)
  >- (rw[EXTENSION,INTER_DEF] >> metis_tac[])
  >- (gs[EXTENSION,INTER_DEF] >> metis_tac[]) >>
  gs[EXTENSION,INTER_DEF] >>
  first_assum (drule o iffLR) >> rw[]
QED

Theorem cstt_SUBMAP:
  cstt f ∧ f ⊑ σ ∧ complete f ∧
  (∀n s. (n,s) ∈ FDOM σ ∧ (n,s) ∉ FDOM f ⇒
         sort_of (σ ' (n,s)) = sinst σ s) ⇒
  cstt σ
Proof 
 rw[cstt_def] >>
 Cases_on ‘(n,s) ∈ FDOM f’ >> gs[] >>
 gs[SUBMAP_DEF]>>
 irule fmap_sfv_sinst_eq >>
 irule DRESTRICT_SUBMAP_SUBSET>>
 gs[complete_def,SUBSET_DEF,SUBMAP_DEF] >>
 metis_tac[]
QED

    
Theorem match_SOME_cstt:
  (∀t1 t2 f σ.
     complete f ∧ cstt f ∧
     tmatch {} t1 t2 f = SOME σ ⇒
     cstt σ) ∧
  (∀st1 st2 f σ.
     complete f ∧ cstt f ∧
     smatch {} st1 st2 f = SOME σ  ⇒
     cstt σ) ∧
  (∀tl1 tl2 f σ.
     complete f ∧ cstt f ∧
     tlmatch {} tl1 tl2 f = SOME σ ⇒
     cstt σ)
Proof    
  ho_match_mp_tac original_tm_induction >> rw[] (* 6 *)
  >- (drule_all_then assume_tac tmatch_tinst >>
     drule_all_then strip_assume_tac tmatch_property >>
     ‘(s0,st1) ∈ FDOM σ’
       by gs[EXTENSION,tfv_def] >> 
     gs[tinst_def,tmatch_def,AllCaseEqs()] >>
     first_x_assum $ drule_all_then assume_tac >>
     irule cstt_SUBMAP >>
     drule_all_then strip_assume_tac smatch_property >>
     qexists_tac ‘f0’ >> gs[] >>
     ‘f0 ⊑ σ’
      by (‘(s0,st1) ∉ FDOM f0’
          suffices_by metis_tac[SUBMAP_FUPDATE_EQN] >>
          gs[EXTENSION] >>
          metis_tac[tm_tree_WF]) >>
     simp[] >> rw[] >>
  drule_all_then assume_tac smatch_sinst >>
  ‘sinst f0 s = sinst σ s’
    suffices_by metis_tac[] >>
  irule fmap_sfv_sinst_eq >>
  irule DRESTRICT_SUBMAP_SUBSET >>
  gs[SUBSET_DEF,EXTENSION])
  >- (Cases_on ‘t2’ >> gs[tmatch_def,AllCaseEqs()] >>
     rename [‘tlmatch ∅ tl1 tl2 f’,
             ‘smatch ∅ st1 st2 σ0’] >>
     drule_all_then strip_assume_tac tlmatch_property >>
     drule_all_then strip_assume_tac smatch_property >>
     metis_tac[])
  >- (Cases_on ‘t2’ >> gs[tmatch_def])
  >- (Cases_on ‘st2’ >> gvs[tmatch_def,AllCaseEqs()] >>
     metis_tac[]) 
  >- (drule tlmatch_LENGTH >> rw[] >> gs[tmatch_def]) >>
  Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
  first_x_assum irule >>
  qexistsl [‘f1’,‘t’] >> gs[] >>
  metis_tac[tmatch_property]
QED  
  

Theorem IS_SOME_match:
   (∀t f σ.
     complete f ∧ cstt σ ∧ no_bound σ ∧
     (tfv t ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ tfv t ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     tmatch {} t (tinst σ t) f = SOME (FUNION f (DRESTRICT σ (tfv t)))) ∧
   (∀st f σ.
     complete f ∧ cstt σ ∧ no_bound σ ∧
     (sfv st ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ sfv st ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     smatch {} st (sinst σ st) f =
     SOME (FUNION f (DRESTRICT σ (sfv st)))) ∧
   (∀l f σ.
     complete f ∧ cstt σ ∧ no_bound σ ∧
     (BIGUNION {tfv t | MEM t l} ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩
            BIGUNION {tfv t | MEM t l} ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     tlmatch {} l (MAP (tinst σ) l) f =
     SOME (FUNION f (DRESTRICT σ
     (BIGUNION {tfv t | MEM t l}))))     
Proof
  ho_match_mp_tac original_tm_induction>> rw[] (* 6 *)
  >- (gs[tmatch_def,AllCaseEqs()] >>
     drule_then assume_tac $ iffLR no_bound_def >>
     first_x_assum (drule_then assume_tac) >> gs[] >> 
     Cases_on ‘(s0,st) ∈ FDOM f’ >> gs[] (* 2 *)
     >- (Cases_on ‘st’ >> gs[tmatch_def,PULL_EXISTS] >>
        rw[fmap_EXT,Once EQ_SYM_EQ,Once UNION_COMM,GSYM SUBSET_UNION_ABSORPTION] (* 2 *)
        >- (gs[SUBSET_DEF,complete_def,DRESTRICT_DEF] >> rw[] (* 2 *)
            >- first_x_assum irule >>
            first_x_assum irule >>
            first_x_assum $ irule_at Any >> gs[tfv_def,MEM_MAP] >>
            metis_tac[]) >>
        rw[FUNION_DEF])
     >- (gs[cstt_def,Once UNION_COMM] >> drule_then strip_assume_tac DRESTRICT_UNION_SING >>
        simp[FUNION_FUPDATE_2]))
  >- (rw[GSYM DRESTRICT_FUNION,FUNION_ASSOC,
        tmatch_def,AllCaseEqs()] >>
     ‘tlmatch ∅ l (MAP (tinst σ) l) f =
      SOME
      (f ⊌ DRESTRICT σ (BIGUNION {tfv t | MEM t l}))’
      by (first_x_assum irule >> metis_tac[]) >>
     qabbrev_tac ‘σ0 = f ⊌ DRESTRICT σ (BIGUNION {tfv t | MEM t l})’ >>
     qexists ‘σ0’ >>
     ‘(λa. tinst σ a) = tinst σ’ by metis_tac[ETA_AX] >>
     gs[] >> first_x_assum irule >>
     gs[] >>
     drule_all_then strip_assume_tac tlmatch_property>>
     gs[PULL_EXISTS] >> rw[] (* 2 *)
     >- (last_x_assum (K all_tac) >>
         rw[Abbr‘σ0’,FUNION_DEF]) >>
     last_x_assum (K all_tac) >>
     rw[Abbr‘σ0’,FUNION_DEF,DRESTRICT_DEF] >>
     metis_tac[])
  >- (gs[tmatch_def,DRESTRICT_IS_FEMPTY])
  >- (gs[PULL_EXISTS,tmatch_def] >> metis_tac[])
  >- rw[DRESTRICT_IS_FEMPTY,tmatch_def] >>
  ‘BIGUNION {tfv t' | t' = t ∨ MEM t' l} =
   tfv t ∪ BIGUNION {tfv t' | MEM t' l}’
   by (rw[EXTENSION] >> metis_tac[]) >>
  rw[GSYM DRESTRICT_FUNION,FUNION_ASSOC] >>
  gs[tmatch_def] >>
  first_x_assum irule >> gs[] >>
  ‘complete (f ⊌ DRESTRICT σ (tfv t))’
   by (rw[complete_FDOM_is_cont] >>
      irule UNION_is_cont >>
      gs[complete_FDOM_is_cont,DRESTRICT_DEF] >>
      ‘FDOM σ ∩ tfv t = tfv t’
        by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
      gs[tfv_is_cont]) >> gs[] >>
  rw[] (* 2 *)
  >- (rw[FUNION_DEF] >> metis_tac[]) >>
  rw[FUNION_DEF] (* 2 *) >- metis_tac[] >>
  gs[DRESTRICT_DEF]
QED


Theorem FEMPTY_complete:
  complete FEMPTY
Proof
 rw[complete_def]
QED 


Theorem FEMPTY_cstt:
  cstt FEMPTY
Proof
 rw[cstt_def]
QED



Theorem update_inst_lemma:
  v ∉ sfv s ∧ v ∉ FDOM σ ⇒
  sinst σ s = sinst (σ |+ (v,t)) s
Proof
 rw[] >> irule fmap_sfv_sinst_eq >>
 rw[fmap_EXT,DRESTRICT_DEF] (* 2 *)
 >- (gs[EXTENSION] >> metis_tac[]) >>
 rw[Once EQ_SYM_EQ] >>
 irule NOT_EQ_FAPPLY >> metis_tac[]
QED 




Theorem tmatch_FEMPTY_property:
  tmatch ∅ t1 t2 FEMPTY = SOME σ  ⇒
  complete σ ∧ FDOM σ = tfv t1
Proof
  strip_tac >>
  assume_tac (INST_TYPE [alpha |-> “:term” ]
 FEMPTY_complete) >>
  drule_then assume_tac tmatch_property >>
  first_x_assum $ drule_all_then strip_assume_tac >>
  gs[]
QED


Theorem no_bound_FUPDATE:
  no_bound f ∧ tbounds t = {} ⇒ no_bound (f |+ (x,t))
Proof
 rw[no_bound_def] (* 2 *)
 >- rw[FAPPLY_FUPDATE] >>
 Cases_on ‘x' = x’ >> rw[FAPPLY_FUPDATE] >>
 rw[FAPPLY_FUPDATE_THM]
QED 
      
Theorem tmatch_no_bound:
  (∀t1 t2 f σ. no_bound f ∧ tmatch ∅ t1 t2 f  = SOME σ ⇒ no_bound σ) ∧
  (∀s1 s2 f σ. no_bound f ∧ smatch ∅ s1 s2 f  = SOME σ ⇒ no_bound σ) ∧
  (∀tl1 tl2 f σ. no_bound f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒ no_bound σ)
Proof
  ho_match_mp_tac original_tm_induction >> rw[] (* 6 *)
  >-  (gs[tmatch_def,AllCaseEqs()] >>
       first_x_assum $ drule_all_then assume_tac >>
       qpat_x_assum ‘_ = σ’ (assume_tac o GSYM) >> rw[] >>
       irule no_bound_FUPDATE >> simp[])
  >- (Cases_on ‘t2’ >>  gvs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >>
     rpt (first_x_assum $ drule_all_then assume_tac) >> rw[])
  >- (Cases_on ‘t2’ >> gvs[tmatch_def,AllCaseEqs(),PULL_EXISTS])
  >- (Cases_on ‘s2’ >> 
     gs[tmatch_def,AllCaseEqs(),PULL_EXISTS] >> metis_tac[]) 
  >- (drule tlmatch_LENGTH >> rw[] >> gs[tmatch_def]) >>
  Cases_on ‘tl2’ >> gs[tmatch_def,AllCaseEqs()] >>
  rename [‘tmatch ∅ t1 t2 f’,‘tlmatch ∅ tl1 tl2 f1’]>>
  rpt (last_x_assum (drule_all_then strip_assume_tac))
QED

Theorem FEMPTY_no_bound:
no_bound FEMPTY
Proof
rw[no_bound_def]
QED

val tmatch_no_bound_FEMPTY = tmatch_no_bound |> cj 1
                                             |> Q.SPECL [‘t1’,‘t2’,‘FEMPTY’]
                                             |> SRULE [FEMPTY_no_bound]
                                             |> GEN_ALL

val smatch_no_bound_FEMPTY = tmatch_no_bound |> cj 2
                                             |> Q.SPECL [‘s1’,‘s2’,‘FEMPTY’]
                                             |> SRULE [FEMPTY_no_bound]
                                             |> GEN_ALL


val tlmatch_no_bound_FEMPTY = tmatch_no_bound |> cj 3
                                             |> Q.SPECL [‘tl1’,‘tl2’,‘FEMPTY’]
                                             |> SRULE [FEMPTY_no_bound]
                                             |> GEN_ALL
                                             
                                             
Theorem match_SOME_iff_inst:
  (∀t1 t2. IS_SOME (tmatch {} t1 t2 FEMPTY) ⇔
           ∃σ. cstt σ ∧ no_bound σ ∧ tfv t1 ⊆ FDOM σ ∧ t2 = tinst σ t1)
Proof
 rw[EQ_IMP_THM] (* 2 *)
 >- (Cases_on ‘tmatch ∅ t1 t2 FEMPTY’ >> gs[] >>
    qexists ‘x’ >>
    ‘cstt x’ by metis_tac[match_SOME_cstt,FEMPTY_complete,FEMPTY_cstt] >> simp[Once EQ_SYM_EQ] >>
    ‘tfv t1 ⊆ FDOM x’
    by
    metis_tac[tmatch_FEMPTY_property,SUBSET_ANTISYM_EQ]>>
    ‘no_bound x’ by metis_tac[tmatch_no_bound_FEMPTY] >>
    rw[] >> 
    irule $ cj 1 tmatch_SOME_tinst >>
    metis_tac[FEMPTY_complete]) >> 
 assume_tac (INST_TYPE [alpha |-> “:term” ]
 FEMPTY_complete) >>
 drule_then assume_tac $ cj 1 IS_SOME_match >>
 gs[]
QED


Definition o_vmap_def:
  o_vmap σ2 σ1 =
  FMAP_MAP2 (λ((n,s),t). tinst σ2 t) σ1
End        


Theorem FAPPLY_o_vmap:
  (n:string,s:sort) ∈ FDOM σ1 ⇒
  (o_vmap σ2 σ1) ' (n,s) = tinst σ2 (σ1 ' (n,s))
Proof
  rw[o_vmap_def] >>
  drule $ cj 2
  (INST_TYPE [beta |-> “:term”] FMAP_MAP2_THM) >>
  rw[]
QED

Theorem FDOM_o_vmap:
  FDOM (o_vmap σ2 σ1) = FDOM σ1
Proof
  rw[o_vmap_def,FMAP_MAP2_THM]
QED



Theorem inst_o_vmap:
  (∀t σ1 σ2. tfv t ⊆ FDOM σ1 ∧
             tfv (tinst σ1 t) ⊆ FDOM σ2 ⇒
     tinst σ2 (tinst σ1 t) =
     tinst (o_vmap σ2 σ1) t) ∧
  (∀s σ1 σ2. sfv s ⊆ FDOM σ1 ∧
             sfv (sinst σ1 s) ⊆ FDOM σ2 ⇒
     sinst σ2
     (sinst σ1 s) =
     sinst (o_vmap σ2 σ1) s)
Proof
  ho_match_mp_tac better_tm_induction >> rpt strip_tac (* 3 *)
  >- gs[tfv_def,tinst_def,FDOM_o_vmap,FAPPLY_o_vmap]
  >- (gs[tfv_def,tinst_def,MAP_MAP_o,MAP_EQ_f] >>
     rw[] >>
     first_x_assum irule >> rw[] (* 2 *)
     >> gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]) >>
  rw[tinst_def,tfv_def,MAP_MAP_o,MAP_EQ_f] >>
  first_x_assum irule >> rw[] (* 2 *)
  >> (gs[tfv_def,SUBSET_DEF,MEM_MAP] >>
     metis_tac[])
QED

val tinst_o_vmap = cj 1 inst_o_vmap
val sinst_o_vmap = cj 2 inst_o_vmap        


Theorem match_SOME_iff_inst':
  (∀t1 t2. IS_SOME (tmatch {} t1 t2 FEMPTY) ⇔
           ∃σ. cstt σ ∧ no_bound σ ∧ tfv t1 = FDOM σ ∧ t2 = tinst σ t1)
Proof
 rw[EQ_IMP_THM] (* 2 *)
 >- (Cases_on ‘tmatch ∅ t1 t2 FEMPTY’ >> gs[] >>
    qexists ‘x’ >>
    ‘cstt x’ by metis_tac[match_SOME_cstt,FEMPTY_complete,FEMPTY_cstt] >> simp[Once EQ_SYM_EQ] >>
    ‘tfv t1 = FDOM x’
    by
    metis_tac[tmatch_FEMPTY_property]>>
    ‘no_bound x’ by metis_tac[tmatch_no_bound_FEMPTY] >>
    rw[] >> simp[Once EQ_SYM_EQ] >>
    irule $ cj 1 tmatch_SOME_tinst >>
    metis_tac[FEMPTY_complete]) >> 
 assume_tac (INST_TYPE [alpha |-> “:term” ]
 FEMPTY_complete) >>
 drule_then assume_tac $ cj 1 IS_SOME_match >>
 gs[]
QED
    




Theorem cstt_sort_of_tinst':
 cstt σ ∧ no_bound σ ∧ ¬(is_bound t) ⇒
 sort_of (tinst σ t) = sinst σ (sort_of t)
Proof
 Induct_on ‘t’ >> gs[sort_of_def] >> rw[] >>
 gs[cstt_def,sort_of_def,tbounds_def,is_bound_alt]
QED 

Theorem cstt_sort_of_tinst:
 cstt σ ∧ no_bound σ ∧ tbounds t = {} ⇒
 sort_of (tinst σ t) = sinst σ (sort_of t)
Proof
 Induct_on ‘t’ >> gs[sort_of_def] >> rw[] >>
 gs[cstt_def,sort_of_def,tbounds_def]
QED 

Definition tsubtm_def:
  tsubtm (Var n s) = (Var n s) INSERT (ssubtm s) ∧
  tsubtm (Fn f s l) = (Fn f s l) INSERT (ssubtm s) ∪
                      BIGUNION (set (MAP tsubtm l)) ∧
  tsubtm (Bound i) = {Bound i} ∧                      
  ssubtm (St n l) =  BIGUNION (set (MAP tsubtm l))
Termination
WF_REL_TAC ‘measure (λs. case s of INL t => term_size t
                                | INR s => sort_size s)’
End                                

Theorem tsubtm_REFL:
∀t. t ∈ tsubtm t
Proof
rw[] >> Cases_on ‘t’ >> simp[tsubtm_def]
QED

                                   
Theorem fv_subtm:
 (∀t n st. (n,st) ∈ tfv t ⇔ ∃t0. t0 ∈ tsubtm t ∧
                                 (n,st) ∈ tfv t0) ∧
 (∀s n st. (n,st) ∈ sfv s ⇔ ∃t0. t0 ∈ ssubtm s ∧
                                 (n,st) ∈ tfv t0)
Proof
 ho_match_mp_tac better_tm_induction >> rw[] (* 3 *)
 >- (pop_assum (assume_tac o GSYM) >> rw[] >>
    eq_tac (* 2 *)
    >- (rw[] (* 2 *)
       >- (qexists ‘Var n s’ >> rw[tsubtm_def])
       >- (rw[tsubtm_def] >> qexists ‘Var s0 s’ >>
          rw[tfv_def])) >>
    rw[] >> Cases_on ‘n = s0 ∧ st = s’ (* 2 *)
    >- rw[] >>
    gs[tsubtm_def] >> disj2_tac >> metis_tac[])
 >- (eq_tac (* 2 *)
    >- (strip_tac (* 2 *)
       >- (qexists ‘t’ >> rw[tsubtm_def,MEM_MAP] >>
          disj2_tac >> disj2_tac >>
          simp[PULL_EXISTS] >>
          qexists ‘t’ >> metis_tac[tsubtm_REFL]) >>
       qexists ‘t0’ >> gs[tsubtm_def]) >>
    rw[] >>
    gvs[tsubtm_def] (* 4 *)
    >- (disj1_tac >> metis_tac[])
    >- metis_tac[]
    >- metis_tac[] >>
    gvs[MEM_MAP] >> metis_tac[]) >>
 rw[tsubtm_def,MEM_MAP] >> metis_tac[]
QED

Theorem ssubtm_tsubtm:
∀t0 t. tbounds t = {} ∧ t0 ∈ ssubtm (sort_of t) ⇒ t0 ∈ tsubtm t
Proof
rw[] >> Cases_on ‘t’ >> gs[tsubtm_def,sort_of_def,tbounds_def]
QED

Theorem tbounds_Fn:
  tbounds (Fn s0 s l) = ∅ ⇔ sbounds s = {} ∧
  ∀t. MEM t l ⇒ tbounds t = {}
Proof
rw[tbounds_def,LIST_TO_SET_MAP,IMAGE_DEF,EXTENSION] >>
metis_tac[]
QED



Theorem sbounds_St:
  sbounds (St n l) = ∅ ⇔ 
  ∀t. MEM t l ⇒ tbounds t = {}
Proof
rw[tbounds_def,LIST_TO_SET_MAP,IMAGE_DEF,EXTENSION] >>
metis_tac[]
QED



Theorem sfv_tfv:
∀t n s. ¬(is_bound t) ∧ (n,s) ∈ sfv (sort_of t) ⇒ (n,s) ∈ tfv t
Proof
Cases_on ‘t’ >> gs[sort_of_def,tfv_def,is_bound_def]
QED
        

Theorem ssubtm_tsubtm:
∀t0 t. ¬(is_bound t) ∧ t0 ∈ ssubtm (sort_of t) ⇒ t0 ∈ tsubtm t
Proof
rw[] >> Cases_on ‘t’ >> gs[tsubtm_def,sort_of_def,is_bound_def]
QED

Theorem no_bound_not_is_bound:
  no_bound σ ∧ x ∈ FDOM σ ⇒ ¬(is_bound (σ ' x))
Proof
  rpt strip_tac >> gs[no_bound_def,is_bound_alt]   >>
  first_x_assum drule >> rw[tbounds_def]
QED          

Theorem tinst_subtm:
(∀t σ n st. (n,st) ∈ FDOM σ ∩ tfv t ∧ cstt σ ∧ no_bound σ ⇒
           σ ' (n,st) ∈ tsubtm (tinst σ t)) ∧
(∀s σ n st. (n,st) ∈ FDOM σ ∩ sfv s ∧ cstt σ ∧ no_bound σ ⇒
           σ ' (n,st) ∈ ssubtm (sinst σ s))
Proof                 
ho_match_mp_tac better_tm_induction >> rw[] >> gvs[]
(* 5 *)
>- metis_tac[tsubtm_REFL]
>- (rename [‘(n1,st1) ∉ FDOM σ’] >> 
   Cases_on ‘(n1,st1) ∈ FDOM σ’ (* 2 *)
   >- (gs[] >>  irule ssubtm_tsubtm >>
       drule_then assume_tac no_bound_not_is_bound >>
       first_x_assum drule >> rw[] >>
       gs[cstt_def]) >>
   gs[tsubtm_def])
>- (gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
   rpt disj2_tac >> qexists ‘t’ >>
   metis_tac[])
>- gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
metis_tac[]
QED
        
 





Theorem tinst_subtm1:
(∀t σ n st. (n,st) ∈ FDOM σ ∩ tfv t ∧ cstt σ ∧
 (∀v. v ∈ FDOM σ ⇒ ¬(is_bound (σ ' v))) ⇒
           σ ' (n,st) ∈ tsubtm (tinst σ t)) ∧
(∀s σ n st. (n,st) ∈ FDOM σ ∩ sfv s ∧ cstt σ ∧
(∀v. v ∈ FDOM σ ⇒ ¬(is_bound (σ ' v))) ⇒
           σ ' (n,st) ∈ ssubtm (sinst σ s))
Proof                 
ho_match_mp_tac better_tm_induction >> rw[] >> gvs[]
(* 5 *)
>- metis_tac[tsubtm_REFL]
>- (rename [‘(n1,st1) ∉ FDOM σ’] >> 
   Cases_on ‘(n1,st1) ∈ FDOM σ’ (* 2 *)
   >- (gs[] >>  irule ssubtm_tsubtm >> simp[] >>
       last_x_assum rev_drule >> rw[] >>
       gs[cstt_def]) >>
   gs[tsubtm_def])
>- (gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
   rpt disj2_tac >> qexists ‘t’ >>
   metis_tac[])
>- gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
metis_tac[]
QED
 
Theorem tfv_tinst:
(∀t σ. cstt σ ∧ tfv t ⊆ FDOM σ ∧
 (∀v. v ∈ FDOM σ ⇒ ¬(is_bound (σ ' v))) ⇒
 (∀n st. (n,st) ∈ tfv (tinst σ t) ⇔
       ∃n0 st0. (n0,st0) ∈ tfv t ∧ (n,st) ∈ tfv (σ ' (n0,st0)))) ∧
(∀s σ. cstt σ ∧ sfv s ⊆ FDOM σ ∧
   (∀v. v ∈ FDOM σ ⇒ ¬(is_bound (σ ' v))) ⇒
 (∀n st. (n,st) ∈ sfv (sinst σ s) ⇔
       ∃n0 st0. (n0,st0) ∈ sfv s ∧ (n,st) ∈ tfv (σ ' (n0,st0))))
Proof                 
ho_match_mp_tac better_tm_induction >> rw[] >> gvs[]
(* 3 *)
>- (eq_tac (* 2 *)
   >- metis_tac[] >>
   rw[] (* 2 *)
   >- simp[] >>
   first_x_assum $ drule_all_then assume_tac >>
   ‘(n,st) ∈ sfv (sinst σ s)’ by metis_tac[] >> 
   pop_assum mp_tac >> pop_assum (K all_tac) >>
   gs[cstt_def] >> first_x_assum (drule o GSYM) >> rw[] >>
   irule sfv_tfv >> simp[])
>- (eq_tac(* 2 *)
   >- (simp[PULL_EXISTS,MEM_MAP] >> rw[] (* 2 *)
      >- (‘tfv a ⊆ FDOM σ’ by (gs[SUBSET_DEF]  >> metis_tac[]) >>
         first_x_assum $ drule_all_then assume_tac >> gs[] >>
         metis_tac[]) >>
      ‘(n,st) ∈ sfv (sinst σ s)’
        by (simp_tac std_ss [Once fv_subtm] >>
           qexistsl [‘σ ' (n0,st0)’] >> simp[] >>
           irule $ cj 2 tinst_subtm1 >> gs[SUBSET_DEF]) >>
      gs[] >> metis_tac[]) >>
   simp[PULL_EXISTS,MEM_MAP] >>
   rw[] (* 2 *)
   >- (disj1_tac >> qexists ‘t’ >> simp[] >>
      first_x_assum (irule o iffRL) >> simp[] >> gs[SUBSET_DEF] >>
      metis_tac[]) >>
   disj2_tac >> metis_tac[]) >>
simp[PULL_EXISTS,MEM_MAP] >> eq_tac (* 2 *)
>- (rw[] >> ‘tfv a ⊆ FDOM σ’ by (gs[SUBSET_DEF] >> metis_tac[]) >>
   metis_tac[]) >>
rw[] >> qexists ‘t’ >> simp[] >>
first_x_assum $ irule o iffRL  >> simp[] >> gs[SUBSET_DEF] >>
metis_tac[]
QED
                

 
Theorem tfv_sinst:
(∀t σ. cstt σ ∧ tfv t ⊆ FDOM σ ∧ no_bound σ ⇒
 (∀n st. (n,st) ∈ tfv (tinst σ t) ⇔
       ∃n0 st0. (n0,st0) ∈ tfv t ∧ (n,st) ∈ tfv (σ ' (n0,st0)))) ∧
(∀s σ. cstt σ ∧ sfv s ⊆ FDOM σ ∧ no_bound σ ⇒
 (∀n st. (n,st) ∈ sfv (sinst σ s) ⇔
       ∃n0 st0. (n0,st0) ∈ sfv s ∧ (n,st) ∈ tfv (σ ' (n0,st0))))
Proof                 
ho_match_mp_tac better_tm_induction >> rw[] >> gvs[]
(* 3 *)
>- (eq_tac (* 2 *)
   >- metis_tac[] >>
   rw[] (* 2 *)
   >- simp[] >>
   first_x_assum $ drule_all_then assume_tac >>
   ‘(n,st) ∈ sfv (sinst σ s)’ by metis_tac[] >> 
   pop_assum mp_tac >> pop_assum (K all_tac) >>
   gs[cstt_def] >> first_x_assum (drule o GSYM) >> rw[] >>
   irule sfv_tfv >> simp[] >>
   gs[no_bound_def,is_bound_alt,tbounds_def] >>
   first_x_assum drule >> rw[] >>
   CCONTR_TAC >> gs[tbounds_def])
>- (eq_tac(* 2 *)
   >- (simp[PULL_EXISTS,MEM_MAP] >> rw[] (* 2 *)
      >- (‘tfv a ⊆ FDOM σ’ by (gs[SUBSET_DEF]  >> metis_tac[]) >>
         first_x_assum $ drule_all_then assume_tac >> gs[] >>
         metis_tac[]) >>
      first_x_assum $ drule_all_then assume_tac >>
      ‘(n,st) ∈ sfv (sinst σ s)’
        by (simp_tac std_ss [Once fv_subtm] >>
           qexistsl [‘σ ' (n0,st0)’] >> simp[] >>
           irule $ cj 2 tinst_subtm >> gs[SUBSET_DEF]) >>
      gs[] >> metis_tac[]) >>
   simp[PULL_EXISTS,MEM_MAP] >>
   rw[] (* 2 *)
   >- (disj1_tac >> qexists ‘t’ >> simp[] >>
      first_x_assum (irule o iffRL) >> simp[] >> gs[SUBSET_DEF] >>
      metis_tac[]) >>
   disj2_tac >> metis_tac[]) >>
simp[PULL_EXISTS,MEM_MAP] >> eq_tac (* 2 *)
>- (rw[] >> ‘tfv a ⊆ FDOM σ’ by (gs[SUBSET_DEF] >> metis_tac[]) >>
   metis_tac[]) >>
rw[] >> qexists ‘t’ >> simp[] >>
first_x_assum $ irule o iffRL  >> simp[] >> gs[SUBSET_DEF] >>
metis_tac[]
QED
                

                         
(*fv_subtm tinst_subtm cstt_sort_of_tinst tfv_def*)

Theorem tmatch_TRANS_lemma:
  cstt σ ∧ sfv s ⊆ tfv t ∧ tfv t ⊆ FDOM σ ∧ no_bound σ ⇒
  sfv (sinst σ s) ⊆ tfv (tinst σ t)
Proof
  rw[] >> drule_all_then assume_tac $ cj 1 tfv_sinst >>
  drule_all_then assume_tac SUBSET_TRANS >>
  drule_all_then assume_tac $ cj 2 tfv_sinst >>
  rw[SUBSET_DEF] >> Cases_on ‘x’ >> gs[] >>
  gs[SUBSET_DEF] >> metis_tac[]
QED  

     
Theorem sbounds_tbounds:
(∀t n st. (n,st) ∈ tfv t ⇒ sbounds st ⊆ tbounds t) ∧
(∀s n st. (n,st) ∈ sfv s ⇒ sbounds st ⊆ sbounds s)
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 5 *)
>- gs[tbounds_def]
>- (gs[tbounds_def] >> metis_tac[])
>- (gs[tbounds_def] >>
   first_x_assum $ drule_all_then assume_tac >>
   irule SUBSET_TRANS >> first_x_assum $ irule_at Any >>
   rw[SUBSET_DEF,MEM_MAP] >> metis_tac[])
>- (first_x_assum $ drule_then assume_tac >>
   irule SUBSET_TRANS >> first_x_assum $ irule_at Any >>
   rw[SUBSET_DEF,MEM_MAP,tbounds_def]) >>
first_x_assum $ drule_all_then assume_tac >>
irule SUBSET_TRANS >> first_x_assum $ irule_at Any >>
rw[SUBSET_DEF,MEM_MAP,tbounds_def] >> metis_tac[]
QED


Theorem tbounds_EMPTY_tinst_no_bound:
  tbounds t = {} ∧ no_bound σ ⇒ tbounds (tinst σ t) = {}
Proof
 Induct_on ‘t’ (* 3 *)
 >- (rw[tinst_def,tbounds_def] (* 2 *)
    >- (Cases_on ‘s’ >> gs[tinst_def,sbounds_St,MEM_MAP,PULL_EXISTS]) >>
    gs[no_bound_def])
 >- (rw[tinst_def,tbounds_def] (* 3 *)
    >- (Cases_on ‘s’ >> gs[tinst_def,sbounds_St,MEM_MAP,PULL_EXISTS])
    >- (gs[MAP_MAP_o,EXTENSION,MEM_MAP] >> metis_tac[]) >>
    Cases_on ‘s’ >> gs[tinst_def,sbounds_St,MEM_MAP,PULL_EXISTS]) >>
 rw[tbounds_def]
QED 
    
          
Theorem o_vmap_no_bound:
no_bound (σ1:string # sort |-> term) ∧ no_bound σ2 ⇒ no_bound (o_vmap σ2 σ1)
Proof
rw[no_bound_def,FDOM_o_vmap] >> Cases_on ‘x’ >>
drule FAPPLY_o_vmap >> rw[] >> 
gs[FDOM_o_vmap,FAPPLY_o_vmap] >>
irule tbounds_EMPTY_tinst_no_bound >> gs[no_bound_def]
QED




Theorem tmatch_TRANS:
 ∀t1 t2 t3.
 IS_SOME (tmatch ∅ t1 t2 FEMPTY) ∧
 IS_SOME (tmatch ∅ t2 t3 FEMPTY) ⇒
 IS_SOME (tmatch ∅ t1 t3 FEMPTY)
Proof
 rw[match_SOME_iff_inst'] >>
 qexists_tac ‘o_vmap σ' σ’ >>
 irule_at Any tinst_o_vmap >> rw[FDOM_o_vmap] >>
 rw[cstt_def] >>
 gs[FDOM_o_vmap,FAPPLY_o_vmap] >>
 drule cstt_sort_of_tinst >> rw[] (* 2 *)>-
 (‘sort_of (σ ' (n,s)) = sort_of (tinst σ (Var n s))’
  by simp[tinst_def,sort_of_def] >>
 pop_assum SUBST_ALL_TAC >>
 rev_drule cstt_sort_of_tinst >> rw[] >>
 rw[sort_of_def] >>
 last_x_assum (qspecl_then [‘σ ' (n,s)’] assume_tac) >>
 gs[no_bound_def,cstt_def] >> 
 irule sinst_o_vmap >>
 ‘sfv s ⊆ FDOM σ’
   by (irule $ iffLR is_cont_def >>
      metis_tac[tfv_is_cont]) >>
 simp[] >>
 qpat_x_assum ‘tfv (tinst σ t1) = _’
 (assume_tac o GSYM) >> gs[] >>
 qpat_x_assum ‘ tfv t1 = FDOM σ’
 (assume_tac o GSYM) >> gs[] >>
 irule tmatch_TRANS_lemma >> gs[cstt_def,no_bound_def] >>
 CCONTR_TAC >> gs[GSYM MEMBER_NOT_EMPTY] >>
 drule $ cj 1 sbounds_tbounds >> rw[SUBSET_DEF] >>
 metis_tac[]) >>
 irule o_vmap_no_bound >> simp[]
QED    
        

Theorem DRESTRICT_no_bound:
  no_bound σ ⇒ no_bound (DRESTRICT σ s)
Proof
rw[no_bound_def,DRESTRICT_DEF]
QED
   


Theorem tmatch_FEMPTY:
  ∀f. complete f ∧ cstt f ∧ no_bound f ⇒
 (tmatch {} t1 t2 f = SOME σ ⇔
  ∃σ0.   no_bound σ0 ∧
         (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ0 ⇒ f ' (n,s) = σ0 ' (n,s)) ∧
         tmatch {} t1 t2 FEMPTY = SOME σ0 ∧ σ = FUNION f σ0)
Proof 
 rw[] >> eq_tac (* 2 *)
 >- (rw[] >> drule_all_then assume_tac $ cj 1 tmatch_SOME_tinst >>
    pop_assum (assume_tac o GSYM) >> rw[] >>
    qexists ‘DRESTRICT σ (tfv t1)’ >> rw[] (* 3 *)
    >- (drule_all_then assume_tac $ cj 1 tmatch_no_bound >>
       metis_tac[DRESTRICT_no_bound])
    >- (drule_all_then strip_assume_tac tmatch_property >> gs[SUBMAP_DEF,DRESTRICT_DEF])
    >- (‘tmatch ∅ t1 (tinst σ t1) FEMPTY = SOME (FUNION FEMPTY (DRESTRICT σ (tfv t1)))’
        suffices_by simp[] >> 
       irule $ cj 1 IS_SOME_match >> simp[FEMPTY_complete] >>
       ‘ no_bound σ ’ by metis_tac[tmatch_no_bound] >> simp[] >>
       drule_all_then strip_assume_tac tmatch_property >>
       rw[SUBSET_UNION] >>
       irule $ cj 1 match_SOME_cstt >> metis_tac[]) >>
    ‘tmatch ∅ t1 (tinst σ t1) f = SOME (f ⊌ DRESTRICT σ (tfv t1))’
       suffices_by (rw[] >> gs[]) >>
    irule $ cj 1 IS_SOME_match >> simp[] >>
     ‘ no_bound σ ’ by metis_tac[tmatch_no_bound] >> simp[] >>
    drule_all_then strip_assume_tac $ cj 1 match_SOME_cstt >>
    drule_all_then strip_assume_tac tmatch_property >> simp[SUBSET_UNION] >>
    rw[] >> gs[SUBMAP_DEF]) >>
 rw[] >>
 ‘tinst σ0 t1 = t2’
  by (irule $ cj 1 tmatch_SOME_tinst >> metis_tac[FEMPTY_complete]) >>
 pop_assum (assume_tac o GSYM) >> gs[] >>
 ‘complete (FEMPTY:string#sort |-> term)’ by metis_tac[FEMPTY_complete] >>
 drule_all_then strip_assume_tac tmatch_property >> gs[] >>
 ‘DRESTRICT σ0 (tfv t1) = σ0’ by metis_tac[DRESTRICT_FDOM] >> 
 ‘tmatch ∅ t1 (tinst σ0 t1) f = SOME (f ⊌ (DRESTRICT σ0 (tfv t1)))’
  suffices_by metis_tac[] >>
 irule $ cj 1 IS_SOME_match >> simp[] >> 
 ‘cstt (FEMPTY:string#sort |-> term)’ by metis_tac[FEMPTY_cstt] >>
 drule_all_then strip_assume_tac $ cj 1 match_SOME_cstt >> gs[]
QED 
 

Theorem tlmatch_each_lemma:
complete f ∧ cstt f ∧ no_bound f ∧ tmatch ∅ t1 t2 f = SOME σ ∧
f ⊑ f1 ∧ complete f1 ∧ cstt f1 ∧ no_bound f1 ∧
(∀x. x ∈ FDOM f1 ∧ x ∈ FDOM σ ⇒ f1 ' x = σ ' x) ⇒
tmatch ∅ t1 t2 f1 = SOME (FUNION f1 σ)
Proof
rw[] >>
rev_drule_all_then strip_assume_tac tmatch_FEMPTY >>
first_x_assum (drule o iffLR) >>rw[] >>
irule $ iffRL tmatch_FEMPTY >>
simp[FUNION_ASSOC] >>
‘f1 ⊌ f = f1’
 by (gs[fmap_EXT,FUNION_DEF,SUBMAP_DEF,EXTENSION] >> rw[] >> metis_tac[]) >>
simp[] >>
‘cstt (FEMPTY:string#sort |-> term)’ by metis_tac[FEMPTY_cstt] >>
‘complete (FEMPTY:string#sort |-> term)’ by metis_tac[FEMPTY_complete] >>
drule_all_then strip_assume_tac tmatch_property >>
gs[] >>
rw[] >>
first_x_assum (qspecl_then [‘(n,s)’] assume_tac) >>
gs[] >>
Cases_on ‘(n,s) ∈ FDOM f’ >> gs[FUNION_DEF]
QED



               

(*TODO:set equal implies matching equal, order of list does not matter*)
       
Theorem FUNION_COMM1:
∀f g.
((∀x. x ∈ FDOM f ∧ x ∈ FDOM g ⇒ f ' x = g ' x) ⇒
 FUNION f g = FUNION g f)
Proof
rw[fmap_EXT] (*  3*)
>- metis_tac[UNION_COMM] 
>- (gs[FUNION_DEF]>> Cases_on ‘x ∈ FDOM g’ >> gs[]) >>
(gs[FUNION_DEF]>> Cases_on ‘x ∈ FDOM f’ >> gs[])
QED


Theorem tlmatch_each:
∀tl1 tl2 f.
 complete f ∧ cstt f ∧ no_bound f ∧
 tl1 ≠ [] ∧ tl2 ≠ [] ∧ LENGTH tl1 = LENGTH tl2 ⇒
 ∀σ. (tlmatch {} tl1 tl2 f = SOME σ ⇔
  FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧ 
  (∀n. n < LENGTH tl1 ⇒
   tmatch {} (EL n tl1) (EL n tl2) f =
   SOME (DRESTRICT σ (FDOM f ∪ tfv (EL n tl1)))))
Proof
 Induct_on ‘tl1’ >> rw[tmatch_def] >> Cases_on ‘tl2’ (* 2 *) >> gs[] >>
 rename [‘tlmatch ∅ (t1::tl1) (t2::tl2) f’] >>
 rw[tmatch_def,AllCaseEqs()] >>
 rw[] >> Cases_on ‘tl1 = []’ >> Cases_on ‘tl2 = []’ >> gs[tmatch_def] (* 2 *)
 >- (eq_tac >> rw[] (* 3 *)
    >- (drule_all_then assume_tac tmatch_property >> gs[EXTENSION] >> metis_tac[])
    >- (‘n = 0’ by simp[] >> drule_all_then assume_tac tmatch_property >>
        gs[] >> pop_assum (assume_tac o GSYM) >> gs[DRESTRICT_FDOM]) >>
    first_x_assum (qspecl_then [‘0’] assume_tac) >> gs[] >>
    ‘FDOM f ∪ BIGUNION {tfv t | t = t1} = FDOM f ∪ tfv t1’
     by (gs[EXTENSION] >> metis_tac[]) >>
    metis_tac[DRESTRICT_FDOM]) >>
eq_tac (* 2 *)
>- (strip_tac >>
   drule_all_then strip_assume_tac tmatch_property >>
   drule_all_then strip_assume_tac tlmatch_property >>
   ‘FDOM σ = FDOM f ∪ BIGUNION {tfv t | t = t1 ∨ MEM t tl1}’
     by (gs[EXTENSION] >> metis_tac[]) >> gs[] >>
   first_x_assum (qspecl_then [‘tl2’,‘f1’] assume_tac) >> gs[] >>
   rw[] >>
   Cases_on ‘n = 0’ (* 2 *) >> gs[]
   >- gs[SUBMAP_DRESTRICT_IFF] >>
   ‘∃n0. n = SUC n0’ by metis_tac[arithmeticTheory.num_CASES] >>
   gs[] >>
   ‘cstt f1’ by metis_tac[match_SOME_cstt] >> gs[] >>
  ‘no_bound f1’ by metis_tac[tmatch_no_bound] >> gs[] >>
  first_x_assum (qspecl_then [‘σ’] assume_tac) >> gs[] >>
  first_x_assum $ drule_all_then assume_tac >>
  drule_all_then assume_tac tmatch_FEMPTY >>
  first_x_assum (drule o iffLR) >> rw[] >>
  rev_drule tmatch_FEMPTY >> strip_tac >>
  first_x_assum $ drule_then assume_tac >>
  first_x_assum $ irule o iffRL >> simp[] >>
  (*qexists ‘σ0’ >> simp[] >> *)
  ‘∀n s. (n,s) ∈ FDOM f ∧ (n,s) ∈ FDOM σ0 ⇒ f ' (n,s) = σ0 ' (n,s)’
    by (gs[SUBMAP_DEF] >> metis_tac[]) >>
  simp[] >>
  ‘DRESTRICT σ (FDOM f ∪ tfv (EL n0 tl1)) =
   DRESTRICT (DRESTRICT σ (FDOM f ∪ tfv t1 ∪ tfv (EL n0 tl1))) (FDOM f ∪ tfv (EL n0 tl1))’
   by
    (rw[DRESTRICT_DRESTRICT] >> AP_TERM_TAC >> gs[EXTENSION] >> metis_tac[]) >>
  qpat_x_assum ‘ DRESTRICT σ (FDOM f ∪ tfv t1 ∪ tfv (EL n0 tl1)) = f1 ⊌ σ0’
  SUBST_ALL_TAC >> gs[] >>
  gs[fmap_EXT,DRESTRICT_DEF,FUNION_DEF] >>
  ‘FDOM σ0 = tfv (EL n0 tl1)’
    by (drule_at (Pos (el 2)) tmatch_property >> simp[FEMPTY_complete] >>
  simp[]) >> rw[] (* 5 *)
  >- (simp[EXTENSION] >> metis_tac[]) 
  >- (gs[Once SUBMAP_DEF] >> metis_tac[])
  >- gs[Once SUBMAP_DEF,EXTENSION]
  >- (Cases_on ‘x’ >> gs[Once SUBMAP_DEF,EXTENSION]) >>
  metis_tac[]) >>
rw[] >>
‘tmatch ∅ t1 t2 f = SOME (DRESTRICT σ (FDOM f ∪ tfv t1))’
 by (first_x_assum (qspecl_then [‘0’] assume_tac) >> gs[]) >>
qexists ‘(DRESTRICT σ (FDOM f ∪ tfv t1))’ >> simp[] >>
qabbrev_tac ‘f1 = (DRESTRICT σ (FDOM f ∪ tfv t1))’ >>
first_x_assum (irule o iffRL) >>
drule_all_then strip_assume_tac tmatch_property >>
drule_all_then strip_assume_tac $ cj 1 match_SOME_cstt >> simp[] >>
‘FDOM f ∪ BIGUNION {tfv t | t = t1 ∨ MEM t tl1} =
        FDOM f ∪ tfv t1 ∪ BIGUNION {tfv t | MEM t tl1}’
 by (rw[EXTENSION] >> metis_tac[]) >> simp[] >>
pop_assum (K all_tac) >>
‘no_bound f1’ by metis_tac[tmatch_no_bound]>>
rw[] >> ‘SUC n < SUC (LENGTH tl2)’ by simp[] >>
first_x_assum $ drule_then assume_tac >> gs[] >>
‘DRESTRICT σ (FDOM f ∪ tfv t1 ∪ tfv (EL n tl1)) =
 FUNION (DRESTRICT σ (FDOM f ∪ tfv (EL n tl1))) f1’
 by (gs[Abbr‘f1’,DRESTRICT_FUNION] >> AP_TERM_TAC >>
     simp[EXTENSION] >> metis_tac[]) >>
simp[] >> pop_assum (K all_tac) >>
qabbrev_tac ‘σ1 = DRESTRICT σ (FDOM f ∪ tfv (EL n tl1))’ >>
rev_drule tlmatch_each_lemma >>
rw[] >> first_x_assum drule >> rw[] >>
first_x_assum drule >>
simp[] >> rw[] >>
‘∀x. (x ∈ FDOM f ∨ x ∈ tfv t1) ∧ x ∈ FDOM σ1 ⇒ f1 ' x = σ1 ' x’
 suffices_by
 (rw[] >>
 first_x_assum drule >> rw[] >>
 irule FUNION_COMM1 >>
 fs[EXTENSION] >> metis_tac[]) >>
‘∀x. (x ∈ FDOM f ∨ x ∈ tfv t1) ∧ x ∈ FDOM σ1 ⇒
f1 ' x = σ ' x ∧ σ1 ' x = σ ' x’
 suffices_by  metis_tac[] >>
 rw[] (* 4 *)
 >- gs[EXTENSION,Abbr‘f1’,DRESTRICT_DEF]
 >- gs[EXTENSION,Abbr‘σ1’,DRESTRICT_DEF]
 >- (gs[Abbr‘f1’,DRESTRICT_DEF,PULL_EXISTS] >>
    simp[] >>
    ‘x ∈ FDOM f ∨ ∃t. x ∈ tfv t ∧ (t = t1 ∨ MEM t tl1)’
    suffices_by rw[] >>
    metis_tac[] (* strange HOL behaviour *)) >>
 gs[EXTENSION,Abbr‘σ1’,DRESTRICT_DEF] (* 2 *)
 >- (‘x ∈ FDOM f ∨
           ∃s. x ∈ s ∧ ∃t. (∀x. x ∈ s ⇔ x ∈ tfv t) ∧ (t = t1 ∨ MEM t tl1)’
  suffices_by rw[] >>
  metis_tac[EXTENSION]) >>
 ‘x ∈ FDOM f ∨
           ∃s. x ∈ s ∧ ∃t. (∀x. x ∈ s ⇔ x ∈ tfv t) ∧ (t = t1 ∨ MEM t tl1)’ suffices_by  rw[] >>
  metis_tac[EXTENSION]
QED


Theorem tlmatch_FEMPTY_each:
∀tl1 tl2.
 tl1 ≠ [] ∧ tl2 ≠ [] ∧ LENGTH tl1 = LENGTH tl2 ⇒
 ∀σ. (tlmatch {} tl1 tl2 FEMPTY = SOME σ ⇔
  FDOM σ = BIGUNION {tfv t | MEM t tl1} ∧ 
  (∀n. n < LENGTH tl1 ⇒
   tmatch {} (EL n tl1) (EL n tl2) FEMPTY =
   SOME (DRESTRICT σ (tfv (EL n tl1)))))
Proof
 rw[] >>
 drule_at Any tlmatch_each >> rw[] >> 
 first_x_assum (qspecl_then [‘FEMPTY’,‘σ’] assume_tac) >>
 gs[FEMPTY_complete,FEMPTY_cstt,FEMPTY_no_bound]
QED
        
        

Theorem IS_SOME_match_FEMPTY:
 (∀t σ.
    cstt σ ∧ tfv t ⊆ FDOM σ ∧ no_bound σ ⇒
    tmatch ∅ t (tinst σ t) FEMPTY = SOME (DRESTRICT σ (tfv t))) ∧
 (∀st σ.
    cstt σ ∧ sfv st ⊆ FDOM σ ∧ no_bound σ ⇒
    smatch ∅ st (sinst σ st) FEMPTY = SOME (DRESTRICT σ (sfv st))) ∧
 ∀l σ.
   cstt σ ∧ BIGUNION {tfv t | MEM t l} ⊆ FDOM σ ∧ no_bound σ ⇒
       tlmatch ∅ l (MAP (tinst σ) l) FEMPTY =
       SOME (DRESTRICT σ (BIGUNION {tfv t | MEM t l}))
Proof
  rw[] (* 3 *)
 >- (drule_at (Pos (el 2)) $ cj 1 IS_SOME_match >>
 rw[] >>
 first_x_assum (qspecl_then [‘t’,‘FEMPTY’] assume_tac) >>
 gs[FEMPTY_complete])
 >- (drule_at (Pos (el 2)) $ cj 2 IS_SOME_match >>
 rw[] >>
 first_x_assum (qspecl_then [‘st’,‘FEMPTY’] assume_tac) >>
 gs[FEMPTY_complete]) >>
 (drule_at (Pos (el 2)) $ cj 3 IS_SOME_match >>
 rw[] >>
 first_x_assum (qspecl_then [‘l’,‘FEMPTY’] assume_tac) >>
 gs[FEMPTY_complete])
QED 

(*
Theorem tmatch_TRANS:
 ∀t1 t2 t3.
 IS_SOME (tmatch ∅ t1 t2 FEMPTY) ∧
 IS_SOME (tmatch ∅ t2 t3 FEMPTY) ⇒
 IS_SOME (tmatch ∅ t1 t3 FEMPTY)
Proof
 rw[match_SOME_iff_inst'] >>
 qexists_tac ‘o_vmap σ' σ’ >>
 irule_at Any tinst_o_vmap >> rw[FDOM_o_vmap] >>
 rw[cstt_def] >>
 gs[FDOM_o_vmap,FAPPLY_o_vmap] >>
 drule cstt_sort_of_tinst >> rw[] >>
 ‘sort_of (σ ' (n,s)) = sort_of (tinst σ (Var n s))’
  by simp[tinst_def,sort_of_def] >>
 pop_assum SUBST_ALL_TAC >>
 rev_drule cstt_sort_of_tinst >> rw[] >>
 rw[sort_of_def] >>
 irule sinst_o_vmap >>
 ‘sfv s ⊆ FDOM σ’
   by (irule $ iffLR is_cont_def >>
      metis_tac[tfv_is_cont]) >>
 simp[] >>
 qpat_x_assum ‘tfv (tinst σ t1) = _’
 (assume_tac o GSYM) >> gs[] >>
 qpat_x_assum ‘ tfv t1 = FDOM σ’
 (assume_tac o GSYM) >> gs[] >>
 metis_tac[SUBSET_ANTISYM_EQ,tmatch_TRANS_lemma]
QED
*)
      
    
val tmatch_FEMPTY_tinst = 
tmatch_SOME_tinst |> cj 1 |> Q.SPECL [‘t1’,‘t2’,‘FEMPTY’]
                          |> GEN_ALL
                          |> SRULE [FEMPTY_complete]

    
val tmatch_FEMPTY_property =
tmatch_property |>Q.SPECL [‘t1’,‘t2’,‘FEMPTY’]
                          |> GEN_ALL
                          |> SRULE [FEMPTY_complete]

                          


Theorem o_vmap_cstt:
cstt σ1 ∧ cstt σ2 ∧ no_bound σ1 ∧ no_bound σ2 ∧
complete σ1 ∧
(∀x. x ∈ FDOM σ1 ⇒ tfv (σ1 ' x) ⊆ FDOM σ2) ⇒ cstt (o_vmap σ2 σ1)
Proof
strip_tac >> rw[cstt_def] >> gs[FDOM_o_vmap,FAPPLY_o_vmap]  >>
first_x_assum $ drule_then assume_tac >>
drule cstt_sort_of_tinst >> rw[] >>
first_x_assum (qspecl_then [‘σ1 ' (n,s)’] assume_tac) >>
gs[no_bound_def] >> 
‘sinst σ2 (sinst σ1 s) = sinst (o_vmap σ2 σ1) s’
 suffices_by
  (rw[] >> pop_assum (assume_tac o GSYM) >>
  gs[cstt_def]) >> 
irule $ cj 2 inst_o_vmap  >> gs[complete_def] >>
gs[SUBSET_DEF] >> rw[] (* 2 *)
>- metis_tac[] >>
first_x_assum irule >> gs[cstt_def] >>
last_x_assum $ drule_then (assume_tac o GSYM) >>
gs[] >> Cases_on ‘x’ >> irule sfv_tfv >> simp[] >>
irule no_bound_not_is_bound >> gs[no_bound_def]
QED




        
    


Theorem tlmatch_SOME_MAP:
∀tl1 tl2 f σ.
          complete f ∧ tlmatch ∅ tl1 tl2 f = SOME σ ⇒
          tl2 = MAP (tinst σ) tl1
Proof
rw[] >> irule LIST_EQ  >> drule tlmatch_LENGTH >> gs[] >>
drule $ cj 3 tmatch_SOME_tinst >> rw[] >>
‘x < LENGTH tl1’ by metis_tac[] >>
first_x_assum drule_all >>
drule (INST_TYPE [beta |-> “:term”] EL_MAP) >> rw[]
QED


val tlmatch_FEMPTY_SOME_MAP = tlmatch_SOME_MAP |>Q.SPECL [‘tl1’,‘tl2’,‘FEMPTY’]
                          |> GEN_ALL
                          |> SRULE [FEMPTY_complete]
                          
val tlmatch_FEMPTY_property = tlmatch_property |>Q.SPECL [‘tl1’,‘tl2’,‘FEMPTY’]
                          |> GEN_ALL
                          |> SRULE [FEMPTY_complete]                          


val tlmatch_FEMPTY_cstt = match_SOME_cstt |> cj 3
                                          |> Q.SPECL [‘tl1’,‘tl2’,‘FEMPTY’]
                                          |> SRULE [FEMPTY_complete,FEMPTY_cstt]
(*IS_SOME_match tmatch_SOME_tinst*)
val tlmatch_each_FEMPTY = tlmatch_each |> Q.SPECL [‘tl1’,‘tl2’,‘FEMPTY’]
                                          |> SRULE [FEMPTY_complete,FEMPTY_cstt]

(*match_SOME_iff_inst *)



Theorem tlmatch_tinst_imp_SOME:
  ∀tl1 tl2 f.
       complete f ∧ cstt f ∧ no_bound f ∧
       tl1 ≠ [] ∧ tl2 ≠ [] ∧ LENGTH tl1 = LENGTH tl2 ⇒
       ∀σ. f ⊑ σ ∧ cstt σ ∧ no_bound σ ∧
           FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
           (∀n. n < LENGTH tl1 ⇒
               EL n tl2 = tinst σ (EL n tl1)) ⇒ 
               tlmatch ∅ tl1 tl2 f = SOME σ 
Proof               
 rw[] >> drule_all_then assume_tac tlmatch_each >> gs[] >>
 pop_assum (K all_tac) >> rw[] >>
 first_x_assum drule >> rw[] >>
 ‘f ⊌ DRESTRICT σ (tfv (EL n tl1)) =  DRESTRICT σ (FDOM f ∪ tfv (EL n tl1))’
  by (rw[GSYM DRESTRICT_FUNION] >> gs[SUBMAP_DRESTRICT_IFF] >> metis_tac[]) >>
 pop_assum (assume_tac o GSYM) >> gs[] >>
 irule $ cj 1 IS_SOME_match >>
 simp[] >> rw[] (* 3 *)              
 >- gs[SUBMAP_DEF] >- gs[SUBMAP_DEF] >>
 rw[SUBSET_DEF] >> metis_tac[rich_listTheory.EL_MEM]
QED 





Theorem tlmatch_tinst_imp_SOME':
  ∀tl1 tl2 f.
       complete f ∧ cstt f ∧ LENGTH tl1 = LENGTH tl2 ∧ no_bound f ⇒
       ∀σ. f ⊑ σ ∧ cstt σ ∧  no_bound σ ∧
           FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
           (∀n. n < LENGTH tl1 ⇒
               EL n tl2 = tinst σ (EL n tl1)) ⇒ 
               tlmatch ∅ tl1 tl2 f = SOME σ 
Proof               
 rw[] >> Cases_on ‘tl1 = []’ >> gs[] (* 2*)
 >- (simp[tmatch_def] >> gs[SUBMAP_DEF,fmap_EXT]) >>
 ‘tl2 ≠ []’ by (CCONTR_TAC >> gs[]) >>
 metis_tac[tlmatch_tinst_imp_SOME]
QED 


 

Theorem tlmatch_each_imp_tinst:
  ∀tl1 tl2 f.
       complete f ∧ cstt f ∧  no_bound f ∧
       tl1 ≠ [] ∧ tl2 ≠ [] ∧ LENGTH tl1 = LENGTH tl2 ⇒
       ∀σ. tlmatch ∅ tl1 tl2 f = SOME σ ⇒
           FDOM σ = FDOM f ∪ BIGUNION {tfv t | MEM t tl1} ∧
           ∀n. n < LENGTH tl1 ⇒
               EL n tl2 = tinst σ (EL n tl1)
Proof               
 rw[] >> drule_all_then assume_tac tlmatch_each >> gs[] >>
 pop_assum (K all_tac) >> 
 first_x_assum drule >> rw[] >>
 ‘tinst σ (EL n tl1) = tinst (DRESTRICT σ (FDOM f ∪ tfv (EL n tl1))) (EL n tl1)’
   by (irule $ cj 1 fmap_fv_inst_eq >>
       rw[DRESTRICT_DRESTRICT] >>
       AP_TERM_TAC >> rw[EXTENSION] >> metis_tac[]) >>
 gs[] >> rw[Once EQ_SYM_EQ] >>
 irule $ cj 1 tmatch_SOME_tinst >> metis_tac[]
QED

val tlmatch_tinst_imp_SOME_FEMPTY = tlmatch_tinst_imp_SOME'
                                      |> Q.SPECL [‘tl1’,‘tl2’,‘FEMPTY’]
                                          |> SRULE [FEMPTY_complete,FEMPTY_cstt]     



Definition fsymin_def:
  fsymin Σf f = SND  (Σf ' f)
End


Definition fsymout_def:
  fsymout Σf f = FST (Σf ' f)
End


Definition isfsym_def:
  isfsym Σf f ⇔ f ∈ FDOM Σf
End

Overload Var' = “UNCURRY Var”        
        
Definition wft_def:
  (wft Σf (Var n s) ⇔ wfs Σf s) ∧
  (wft Σf (Fn f s tl) ⇔
     wfs Σf s ∧ 
     (∀t. MEM t tl ⇒ wft Σf t) ∧
     isfsym Σf f ∧
     IS_SOME (tlmatch {} (MAP (UNCURRY Var) (fsymin Σf f)) tl FEMPTY) ∧
     sinst (THE (tlmatch {} (MAP (UNCURRY Var) (fsymin Σf f)) tl FEMPTY)) (fsymout Σf f) = s) ∧
  (wft Σf (Bound i) = F) ∧
  (wfs Σf (St n tl) ⇔ EVERY (wft Σf) tl)
Termination
 WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,t) => term_size t
         | INR (_,st) => sort_size st)’ 
End

Definition wfcod_def:
  wfcod Σf σ ⇔ ∀n s. (n,s) ∈ FDOM σ ⇒ wft Σf (σ ' (n,s))
End

(*Q:Once EXTENSION |> DISCH_ALL *)

     
Theorem wft_no_bound:
 (∀t. wft Σf t ⇒ tbounds t = {}) ∧
 (∀s. wfs Σf s ⇒ sbounds s = {})
Proof
 ho_match_mp_tac better_tm_induction >>
 rw[wft_def,tbounds_def] (* 2 *)
 >- (gs[Once EXTENSION,MEM_MAP] >>
    simp[LIST_TO_SET_MAP,Once EXTENSION,IMAGE_DEF] >>
    Cases_on ‘l’ >> gs[] >> metis_tac[]) >>
 gs[Once EXTENSION,MEM_MAP] >>
 simp[LIST_TO_SET_MAP,Once EXTENSION,IMAGE_DEF] >>
 Cases_on ‘l’ >> gs[EVERY_MEM,EXTENSION] >> rw[] >>
 metis_tac[]
QED 
        
(*function symbol output cannot have extra variables than its argument, since we want to restrict to talk about inst where
each var has a value. *)

Theorem wfcod_no_bound0:
  wfcod Σf σ ⇒ ∀x. x ∈  FDOM σ ⇒ tbounds (σ ' x) = {}
Proof
  rw[wfcod_def] >> Cases_on ‘x’ >>
  first_x_assum drule >> metis_tac[wft_no_bound]
QED  


Theorem wfcod_no_bound:
  wfcod Σf σ ⇒ no_bound σ
Proof
  rw[no_bound_def] >>  irule wfcod_no_bound0 >>
  metis_tac[]
QED


Theorem IS_SOME_tlmatch_inst:
cstt σ ∧  wfcod Σf σ ∧ BIGUNION {tfv t | MEM t l} ⊆ FDOM σ ∧
IS_SOME (tlmatch ∅ l0 l FEMPTY) ⇒
IS_SOME (tlmatch ∅ l0 (MAP (tinst σ) l) FEMPTY)
Proof
rw[optionTheory.IS_SOME_EXISTS] >>
‘l = MAP (tinst x) l0’
  by metis_tac[tlmatch_FEMPTY_SOME_MAP] >>
simp[] >> rw[MAP_MAP_o] >> 
‘tlmatch ∅ l0 (MAP (tinst σ ∘ tinst x) l0) FEMPTY = SOME
 (o_vmap σ x)’
 suffices_by metis_tac[] >>
irule tlmatch_tinst_imp_SOME_FEMPTY >>
simp[FDOM_o_vmap,FEMPTY_no_bound] >>
‘no_bound x’
  by metis_tac[FEMPTY_no_bound,tmatch_no_bound]>>
‘no_bound (o_vmap σ x)’
  by (irule o_vmap_no_bound >> metis_tac[wfcod_no_bound])>>
simp[] >>
‘cstt (o_vmap σ x)’
  by (irule o_vmap_cstt >> simp[PULL_EXISTS] >>
     ‘no_bound σ’ by  metis_tac[wfcod_no_bound] >>
     simp[] >>
     ‘complete x’
      by metis_tac[FEMPTY_complete,tlmatch_complete] >>
     simp[] >>
     ‘cstt x’
      by metis_tac[FEMPTY_cstt,FEMPTY_complete,tlmatch_property,match_SOME_cstt] >> 
     drule_all_then assume_tac tlmatch_FEMPTY_property >>
     gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> rw[] >>
     last_x_assum irule >> qexists ‘t’ >> simp[] >>
     Cases_on ‘x'’ >> Cases_on ‘x''’ >>
     irule $ iffRL $ cj 1 tfv_sinst >>
     simp[SUBSET_DEF] >> (*tactic stupid*)
     metis_tac[]) >> simp[] >>
drule_all_then assume_tac tlmatch_FEMPTY_property >> gs[]>>
 rw[] >>
 drule (INST_TYPE [beta |-> “:term”] EL_MAP) >> rw[] >>
 irule $ cj 1 inst_o_vmap >>
 simp[SUBSET_DEF] >> rw[] (* 2 *)
 >-  metis_tac[MEM_EL] >>
 gs[MEM_MAP,SUBSET_DEF] >> metis_tac[MEM_EL]
QED      

(*assum (∀fsym. isfsym Σf fsym ⇒ sfv (fsymout Σf fsym) ⊆ BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) is used for
 sinst (THE (tlmatch ∅ farg (MAP (tinst σ ∘ tinst x) farg) FEMPTY)) st =
        sinst σ (sinst x st)

Maybe can be removed.        

*) 
Theorem wft_tinst:
  (∀fsym. isfsym Σf fsym ⇒ sfv (fsymout Σf fsym) ⊆ BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
  (∀t. wft Σf t ⇒ ∀σ. cstt σ ∧ wfcod Σf σ ∧ tfv t ⊆ FDOM σ ⇒
  wft Σf (tinst σ t)) ∧
  (∀s. wfs Σf s ⇒ ∀σ. cstt σ ∧ wfcod Σf σ ∧ sfv s ⊆ FDOM σ ⇒
  wfs Σf (sinst σ s))
Proof
 disch_tac >>
 ho_match_mp_tac better_tm_induction >> rw[] (* 3 *)
 >- gs[wfcod_def]
 >- (gs[wft_def,MEM_MAP,PULL_EXISTS] >>
 qabbrev_tac ‘farg = (MAP (UNCURRY Var) (fsymin Σf s0))’ >>
 ‘∀a. MEM a l ⇒ wft Σf (tinst σ a)’
   by (rw[] >> last_x_assum irule >> simp[] >> gs[SUBSET_DEF] >>
      metis_tac[]) >> simp[] >>
 qabbrev_tac ‘st = fsymout Σf s0’ >>
 gs[optionTheory.IS_SOME_EXISTS] >>
 ‘l = MAP (tinst x) farg’ by metis_tac[tlmatch_FEMPTY_SOME_MAP] >>
 gs[SF ETA_ss,MAP_MAP_o] >>
 qpat_x_assum ‘sinst x st = s’ (assume_tac o GSYM) >> gs[]>>
 drule_all_then strip_assume_tac tlmatch_FEMPTY_property >>
 drule_all_then strip_assume_tac tlmatch_FEMPTY_cstt >>
 ‘tlmatch ∅ farg (MAP (tinst σ ∘ tinst x) farg) FEMPTY = SOME
 (o_vmap σ x)’
 suffices_by
 (rw[] >> simp[Once EQ_SYM_EQ] >>
 irule $ cj 2 inst_o_vmap >> simp[] >>
 last_x_assum drule >>
 simp[Abbr‘st’,Abbr‘farg’,MEM_MAP] >> rw[] >>
 ‘{{(n,s')} ∪ sfv s' | MEM (n,s') (fsymin Σf s0)} =
 {tfv t | (∃y. t = UNCURRY Var y ∧ MEM y (fsymin Σf s0))}’
  by  (simp[EXTENSION,PULL_EXISTS] >>
 rw[EQ_IMP_THM] >- (qexists ‘(n,s')’  >> simp[pairTheory.UNCURRY_DEF] >>
                   metis_tac[]) >>
 Cases_on ‘y’ >> qexistsl [‘q’,‘r’] >> gs[pairTheory.UNCURRY_DEF] >>
 metis_tac[]) >> metis_tac[]) >>
 irule tlmatch_tinst_imp_SOME_FEMPTY >>
 simp[] >>
 ‘no_bound x’
  by metis_tac[FEMPTY_no_bound,tmatch_no_bound]>>
 simp[FEMPTY_no_bound] >>
 ‘no_bound (o_vmap σ x)’
  by (irule o_vmap_no_bound >> metis_tac[wfcod_no_bound]) >>
 ‘cstt (o_vmap σ x)’
  by (irule o_vmap_cstt >> simp[PULL_EXISTS] >>
     ‘no_bound σ’ by  metis_tac[wfcod_no_bound] >>
     gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> rw[] >>
     last_x_assum irule >> qexists ‘t’ >> simp[] >>
     Cases_on ‘x'’ >> Cases_on ‘x''’ >>
     irule $ iffRL $ cj 1 tfv_sinst >>
     simp[SUBSET_DEF] >> (*tactic stupid*)
     metis_tac[]) >>
 simp[FDOM_o_vmap] >> rw[] >>
 drule (INST_TYPE [beta |-> “:term”] EL_MAP) >> rw[] >>
 irule $ cj 1 inst_o_vmap >>
 simp[SUBSET_DEF] >> rw[] (* 2 *)
 >-  metis_tac[MEM_EL] >>
 gs[MEM_MAP,SUBSET_DEF] >> metis_tac[MEM_EL]) >>
gs[wft_def,EVERY_MEM,MEM_MAP,PULL_EXISTS] >> rw[] >>
last_x_assum irule >> simp[] >>
gs[SUBSET_DEF] >> metis_tac[]
QED


Definition variant_def:
  variant (ns:string fset) (n:string) =
  if fIN n ns then variant ns (n ++ "'")
  else n
Termination
   WF_REL_TAC
   ‘measure
   (λ(ns,n).
   fCARD ns + fITSET (λs m. LENGTH s + m) ns 0 - LENGTH n)’>>
   simp[] >>
   Induct_on ‘ns’ >> simp[] >> rw[] (* 2 *)
   >> simp[fITSET_INSERT] >>
   first_x_assum $ drule_then assume_tac >> simp[] 
End   
 
      

Theorem variant_NOT_fIN:
∀ns n. ¬fIN (variant ns n) ns
Proof
ho_match_mp_tac variant_ind >> rw[] >>
simp[Once variant_def] >>
rw[]            
QED


Theorem variant_NOTIN:
∀vs n. FINITE vs ⇒ (variant (fromSet vs) n) ∉ vs
Proof
rpt strip_tac >>
drule_all_then assume_tac $ iffRL IN_fromSet >>
gs[] >> metis_tac[variant_NOT_fIN]
QED
        
Theorem variant_var_NOTIN:
∀vs n s. FINITE vs ⇒ (variant (fromSet (IMAGE FST vs)) n,s) ∉ vs
Proof
rpt strip_tac >>
‘FST (variant (fromSet (IMAGE FST vs)) n,s) ∈ IMAGE FST vs’
 by simp[] >>
‘FINITE (IMAGE FST vs)’ by simp[] >>
drule_all_then assume_tac $ iffRL IN_fromSet >>
gs[] >> metis_tac[variant_NOT_fIN]
QED



Definition trpl_def:
(trpl i new (Bound j) =
   if i = j then new else Bound j) ∧
(trpl i new (Var n s) = Var n s) ∧
(trpl i new (Fn f s tl) = Fn f (srpl i new s)
(MAP (trpl i new) tl)) ∧
 srpl i new (St n tl) =
 St n (MAP (trpl i new) tl)
Termination
WF_REL_TAC
‘measure (λs. case s of INL (_,_,t) => term_size t
                     | INR (_,_,s) => sort_size s)’
End
     


Theorem MAP_fix:
MAP f l = l ⇔ ∀x. MEM x l ⇒ f x = x
Proof
rw[EQ_IMP_THM] (* 2 *)
>- (‘MAP f l = MAP I l’ by simp[] >>
   gs[MAP_EQ_f]) >>
‘MAP f l = MAP I l’ suffices_by simp[] >>
gs[MAP_EQ_f]
QED

Theorem trpl_id:
(∀t i new. i ∉ tbounds t ⇒ trpl i new t = t) ∧
∀st i new. i ∉ sbounds st ⇒ srpl i new st = st
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 4 *)
>- (gs[trpl_def,tbounds_def])
>- (gs[trpl_def,tbounds_def,MEM_MAP] >> rw[MAP_fix] >>
    metis_tac[])
>- gs[trpl_def,tbounds_def] >>
gs[trpl_def,tbounds_def,MEM_MAP] >> rw[MAP_fix] >>
metis_tac[]
QED

          
Definition specsl_def:
  specsl i t [] = [] ∧
  specsl i t (s :: sl)  =
  (srpl i t s) :: specsl (i + 1) t sl
End

Definition wfabsap_def:
  (wfabsap Σf [] [] ⇔ T) ∧
  (wfabsap Σf (s:: sl) (t :: tl) ⇔
  (∀n0 s0 st. MEM st sl ∧ (n0,s0) ∈ sfv st ⇒
              sbounds s0 = {}) ∧
  wft Σf t ∧ s = sort_of t ∧ wfs Σf s ∧ wfabsap Σf (specsl 0 t sl) tl) ∧
  (wfabsap Σf (s:: sl) [] ⇔ F) ∧
  (wfabsap Σf [] (t :: tl) ⇔ F)
End        


Definition ok_abs_def:
  ok_abs sl = ∀n. n < LENGTH sl ⇒ sbounds (EL n sl) ⊆ count n
End
             
           


Definition tshift_def:
  tshift i (Bound j) = Bound (j + i) ∧
  tshift i (Var n s) = Var n s ∧
  tshift i (Fn f s l) =
  Fn f (sshift i s) (MAP (tshift i) l) ∧
  sshift i (St n l) = St n (MAP (tshift i) l)
Termination
WF_REL_TAC ‘measure (λs. case s of INL (_, t) => term_size t
                                | INR (_,s) => sort_size s)’       
End

        

Theorem tshift_id:
(∀tm n.tbounds tm = {} ⇒ tshift n tm = tm) ∧
(∀st n.sbounds st = {} ⇒ sshift n st = st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,tshift_def,MAP_fix,EXTENSION] >> rw[](* 2 *)
>> metis_tac[]
QED


Definition shift_bmap_def:
  shift_bmap i bmap =
  FUN_FMAP (λn. tshift i (bmap ' (n - i))) (IMAGE ($+i) (FDOM bmap))
End                


Definition mk_bmap_def:
mk_bmap tl = FUN_FMAP (λn. EL n tl) (count (LENGTH tl))
End

Theorem Bound_tsubtm:
(∀t. Bound i ∈ tsubtm t ⇔ i ∈ tbounds t) ∧
(∀s. Bound i ∈ ssubtm s ⇔ i ∈ sbounds s)
Proof
ho_match_mp_tac better_tm_induction >>
rw[tsubtm_def,tbounds_thm,MEM_MAP] >> metis_tac[]
QED

Theorem trpl_eliminate0:
(∀tm i new.
 (∀n s.(n,s) ∈ tfv tm ⇒ sbounds s = {}) ∧
 (Bound i) ∉ tsubtm new ⇒
 (Bound i) ∉ tsubtm (trpl i new tm)) ∧
(∀st i new.
  (∀n s.(n,s) ∈ sfv st ⇒ sbounds s = {}) ∧
  (Bound i) ∉ tsubtm new ⇒
 (Bound i) ∉ ssubtm (srpl i new st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tsubtm_def,trpl_def,MEM_MAP,tbounds_thm,Bound_tsubtm] >> rw[] (* 4 *)
>- (Cases_on ‘i ∉ s'’ >> simp[] >> gs[] >> rw[] >>
   metis_tac[])
>- metis_tac[]
>- rw[tbounds_thm] >>
Cases_on ‘i ∉ s'’ >> simp[] >> gs[] >> rw[] >>
metis_tac[]
QED

        




Theorem trpl_eliminate:
(∀tm i new.
   (∀n s.(n,s) ∈ tfv tm ⇒ sbounds s = {}) ∧
   tbounds new = {} ⇒
  tbounds (trpl i new tm) = tbounds tm DELETE i) ∧
(∀st i new.
  (∀n s.(n,s) ∈ sfv st ⇒ sbounds s = {}) ∧
  tbounds new = {}  ⇒
  sbounds (srpl i new st) = sbounds st DELETE i)
Proof
ho_match_mp_tac better_tm_induction >>
simp[tbounds_thm,trpl_def,MEM_MAP] >> rw[tbounds_thm] (* 3 *)
>- (‘{tbounds t | (∃a. t = trpl i new a ∧ MEM a l)} =
    {tbounds t DELETE i | MEM t l}’
    by (rw[Once EXTENSION,PULL_EXISTS] >>
        metis_tac[]) >>
    simp[] >>
    ‘sbounds (srpl i new st) = sbounds st DELETE i’
    by metis_tac[] >> simp[] >> 
    rw[Once EXTENSION,PULL_EXISTS] >> metis_tac[])
>- rw[Once EXTENSION] >>
‘BIGUNION {tbounds t | (∃a. t = trpl i new a ∧ MEM a l)} =
   BIGUNION {tbounds t DELETE i | MEM t l}’
    by (rw[Once EXTENSION] >> metis_tac[]) >>
    simp[] >> rw[Once EXTENSION,PULL_EXISTS] >> metis_tac[]
QED    
        

Definition tsstt_def:
  (tsstt old new (Bound i) =
  if Bound i = old then new else Bound i) ∧
  (tsstt old new (Var n s) = (if Var n s = old then new else
  Var n (ssstt old new s))) ∧
  (tsstt old new (Fn f st tl) =
  if Fn f st tl = old then new else
  Fn f (ssstt old new st) (MAP (tsstt old new) tl)) ∧
  (ssstt old new (St n tl) = St n (MAP (tsstt old new) tl))
Termination
WF_REL_TAC ‘measure (λs.
 case s of INL (_,_,t) => term_size t
    | INR (_,_,s) => sort_size s)’   
End


Definition tsubst_def:
  (tsubst (m,s) t (Var n st) =
  if m = n ∧ s = st then t else Var n (ssubst (m,s) t st)) ∧
  (tsubst (m,s) t (Fn f st tl) =
  Fn f (ssubst (m,s) t st) (MAP (tsubst (m,s) t) tl)) ∧
  tsubst (m,s) t (Bound i) = Bound i ∧
  (ssubst (m,s) t (St n tl) =
   St n (MAP (tsubst (m,s) t) tl))
Termination
 WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,_,t) => term_size t
         | INR (_,_,st) => sort_size st)’
End



       
Overload TO_FMAP = “FUPDATE_LIST FEMPTY”

Theorem DRESTRICT_eq:
  (s ⊆ FDOM σ1 ∧ s ⊆ FDOM σ2 ∧
  ∀x. x ∈ s ⇒ σ1 ' x = σ2 ' x) ⇒
  DRESTRICT σ1 s = DRESTRICT σ2 s
Proof
  gs[fmap_EXT,DRESTRICT_DEF,SUBSET_DEF] >> rw[] >>
  simp[EXTENSION] >> metis_tac[]
QED  

Theorem fmap_fv_inst_eq_alt:
  (∀t σ1 σ2.
       tfv t ⊆ FDOM σ1 ∧ tfv t ⊆ FDOM σ2 ∧
       (∀x. x ∈ tfv t ⇒ σ1 ' x = σ2 ' x) ⇒
       tinst σ1 t = tinst σ2 t) ∧
  ∀s σ1 σ2.
       sfv s ⊆ FDOM σ1 ∧ sfv s ⊆ FDOM σ2 ∧
       (∀x. x ∈ sfv s ⇒ σ1 ' x = σ2 ' x) ⇒
       sinst σ1 s = sinst σ2 s
Proof
 rw[] (* 2 *)
 >- (irule $ cj 1 fmap_fv_inst_eq >>
    irule DRESTRICT_eq  >> rw[]) >>
 irule $ cj 2 fmap_fv_inst_eq >>
 irule DRESTRICT_eq  >> rw[]
QED 
        


Theorem tfv_tinst_SUBSET_lemma:
  cstt σ ∧  no_bound σ ∧
  (∀x. x ∈ FDOM σ ⇒ tfv (σ ' x) ⊆ s) ∧
  tfv t ⊆ FDOM σ ⇒
  tfv (tinst σ t) ⊆ s
Proof
  rw[] >>
  simp[SUBSET_DEF] >> drule $ cj 1 tfv_sinst >>
  rw[] >>
  first_x_assum drule >> rw[] >>
  Cases_on ‘x’ >> gs[SUBSET_DEF] >>
  metis_tac[]
QED  
  

Theorem tlmatch_EMPTY_TRANS_lemma:
  cstt σ1 ∧ cstt σ2 ∧ complete σ1 ∧
  no_bound σ1 ∧ no_bound σ2 ∧
  (∀x. x ∈ FDOM σ1 ⇒ tfv (σ1 ' x) ⊆ FDOM σ2) ∧
  FDOM σ1 = BIGUNION {tfv t | MEM t farg}
  ⇒
  tlmatch ∅ farg (MAP (tinst σ2 ∘ tinst σ1) farg) FEMPTY =
  SOME (o_vmap σ2 σ1)
Proof
  rw[] >>
  irule tlmatch_tinst_imp_SOME_FEMPTY >>
  simp[FDOM_o_vmap] >> 
  ‘cstt (o_vmap σ2 σ1)’
   by (irule o_vmap_cstt >> simp[]) >>
  rw[] >> simp[FEMPTY_no_bound] >>
  rev_drule_then assume_tac o_vmap_no_bound >>
  gs[] >> rw[] >>
  drule (INST_TYPE [beta |-> “:term”] EL_MAP) >> rw[] >>
  irule $ cj 1 inst_o_vmap >>
  drule rich_listTheory.EL_MEM >> rw[] (* 2 *)
  >- (rw[SUBSET_DEF] >> metis_tac[]) >>
  irule tfv_tinst_SUBSET_lemma >>
  simp[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
  first_x_assum $ irule_at Any >> simp[]
QED  
 

Theorem tlmatch_TRANS_o_vmap:
 tlmatch ∅ tl1 tl2 FEMPTY = SOME σ1 ∧
 tlmatch ∅ tl2 tl3 FEMPTY = SOME σ2 ⇒
 tlmatch {} tl1 tl3 FEMPTY = SOME (o_vmap σ2 σ1)
Proof
 rw[] >>
 drule tlmatch_FEMPTY_property >>
 rev_drule tlmatch_FEMPTY_property >>
 drule tlmatch_FEMPTY_cstt  >>
 rev_drule tlmatch_FEMPTY_cstt >>
 rw[] >> 
 drule_all tlmatch_FEMPTY_SOME_MAP  >>
 rev_drule_all tlmatch_FEMPTY_SOME_MAP >>
 rw[MAP_MAP_o] >>
 irule tlmatch_EMPTY_TRANS_lemma >>
 simp[PULL_EXISTS,SUBSET_DEF,MEM_MAP,PULL_EXISTS] >>
 drule_then assume_tac tlmatch_no_bound_FEMPTY >>
 rev_drule_then assume_tac tlmatch_no_bound_FEMPTY >>
 rw[] >> qexists ‘t’ >> simp[] >>
 rev_drule $ cj 1 tfv_sinst >> rw[] >>
 Cases_on ‘x'’ >>
 first_x_assum (qspecl_then [‘t’,‘q’,‘r’] assume_tac) >>
 gs[SUBSET_DEF] >> Cases_on ‘x’ >>
 metis_tac[]
QED 
 
Theorem FAPPLY_DOMSUB:
  x ∈ FDOM σ ⇒ 
  (σ \\ x0) ' x =
  if x = x0 then FEMPTY ' x else σ ' x
Proof
 rw[fmap_domsub,DRESTRICT_DEF] >>  fs[]
QED


  
Theorem FUPDATE_cstt:
  complete σ ∧ cstt σ ∧ sfv s0 ⊆ FDOM σ ∧
  (∀n s. (n,s) ∈ FDOM σ ⇒ (n0,s0) ∉ sfv s) ⇒
  ∀t. sort_of t = sinst σ s0 ⇒ cstt (σ |+ ((n0,s0), t))
Proof
  simp[cstt_def] >> rw[] (* 2 *)
  >- (rw[FAPPLY_FUPDATE_THM] >>
     irule $ cj 2 fmap_fv_inst_eq_alt >> gs[SUBSET_DEF] >>
     rw[] >>
     ‘x ≠ (n,s)’ by metis_tac[tm_tree_WF] >>
     gs[FAPPLY_FUPDATE_THM]) >>
  Cases_on ‘(n,s) = (n0,s0)’ >> gs[] (* 2 *)
  >- (irule $ cj 2 fmap_fv_inst_eq_alt >> gs[SUBSET_DEF] >>
     rw[] >>
     ‘x ≠ (n,s)’ by metis_tac[tm_tree_WF] >>
     gs[FAPPLY_FUPDATE_THM]) >>
  ‘(n,s) ≠ (n0,s0)’ by simp[] >>
  rw[FAPPLY_FUPDATE_THM] >>
  irule $ cj 2 fmap_fv_inst_eq_alt >>
  gs[complete_def] >> last_assum drule >> rw[SUBSET_DEF]>>
  ‘x ≠ (n0,s0)’
  suffices_by rw[FAPPLY_FUPDATE_THM] >> metis_tac[]
QED
        

Definition tlfv_def:
  tlfv l = BIGUNION {tfv t | MEM t l}
End


Theorem tsubst_tsstt:
(∀tm n s new. tsubst (n,s) new tm = tsstt (Var n s) new tm) ∧
(∀st n s new. ssubst (n,s) new st = ssstt (Var n s) new st)
Proof
ho_match_mp_tac better_tm_induction >> rw[tsubst_def,tsstt_def,MAP_EQ_f] >>
Cases_on ‘n = s0’ >> Cases_on ‘s = st’ >> gs[]
QED


Theorem tsstt_fix:
(∀t1 t2. tsstt t1 t2 t1 = t2)
Proof
Induct_on ‘t1’ >> simp[tsstt_def]
QED


Theorem subtm_size_less:
  (∀t t0. t0 ∈ tsubtm t ⇒
            term_size t0 ≤ term_size t) ∧
  (∀s t0. t0 ∈ ssubtm s ⇒
            term_size t0 < sort_size s)
Proof
  ho_match_mp_tac better_tm_induction >>
  rw[term_size_def,tsubtm_def] (* 6 *)
  >- rw[term_size_def]
  >- (first_x_assum drule >> rw[])
  >- rw[term_size_def]
  >- (first_x_assum drule_all >> rw[])
  >- (gs[MEM_MAP] >>
     first_x_assum $ drule_all_then assume_tac >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     first_x_assum $ irule_at Any >>
     simp[term_size_eq] >>
     drule MEM_list_size_leq >>
     rw[] >>
     first_x_assum (qspecl_then [‘term_size’] assume_tac) >>
     simp[]) >>
  gs[MEM_MAP] >>
     first_x_assum $ drule_all_then assume_tac >>
   ‘term_size t0 ≤ term1_size l’
       suffices_by rw[] >>
    rw[term_size_eq] >>
     drule MEM_list_size_leq >> rw[] >>
   first_x_assum (qspecl_then [‘term_size’] assume_tac) >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     metis_tac[]
QED                         




                 
Theorem tsstt_tsubtm:
(∀t t1 t2.
  t1 ∈ tsubtm t ⇒ t2 ∈ tsubtm (tsstt t1 t2 t)) ∧
(∀s t1 t2.
  t1 ∈ ssubtm s ⇒ t2 ∈ ssubtm (ssstt t1 t2 s))
Proof
ho_match_mp_tac better_tm_induction >>
rw[tsubtm_def,tsstt_def,tsubtm_REFL] (* 4 *)
>- (Cases_on ‘Var s0 s = t1’ >> rw[tsubtm_REFL] >>
   irule ssubtm_tsubtm >> simp[is_bound_def,sort_of_def])
>- (Cases_on ‘Fn s0 s l = t1’ >> rw[tsubtm_REFL] >>
   rw[tsubtm_def])
>- (Cases_on ‘Fn s0 s l = t1’ >> rw[tsubtm_REFL] >>
   gs[MEM_MAP,tsubtm_def] >> rpt disj2_tac >>
   gs[PULL_EXISTS] >> qexists ‘a’ >> simp[])>>
gs[MEM_MAP,PULL_EXISTS]  >> qexists ‘a’ >> simp[]
QED

Theorem tsstt_id:
(∀t t1 t2. t1 ∉ tsubtm t ⇒ tsstt t1 t2 t = t) ∧
(∀s t1 t2. t1 ∉ ssubtm s ⇒ ssstt t1 t2 s = s) 
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 4 *)
>- (gs[tsstt_def,tsubtm_def])
>- (gs[tsstt_def,tsubtm_def,MEM_MAP] >> rw[MAP_fix] >>
    metis_tac[])
>- gs[tsstt_def,tsubtm_def] >>
gs[tsstt_def,tsubtm_def,MEM_MAP] >> rw[MAP_fix] >>
metis_tac[]
QED   
        
Definition tpsubtm_def:
tpsubtm t = tsubtm t DELETE t
End

Theorem tpsubtm_size_LESS:
∀t t0. t0 ∈ tpsubtm t ⇒ term_size t0 < term_size t
Proof
Induct_on ‘t’ >> simp[tpsubtm_def,tsubtm_def] (* 2 *)
>- (rw[] >>
   ‘term_size t0 < sort_size s’ suffices_by simp[] >>
   irule $ cj 2 subtm_size_less >> simp[]) >>
rw[MEM_MAP] (* 2 *)
>- (‘term_size t0 < sort_size s’ suffices_by simp[] >>
   irule $ cj 2 subtm_size_less >> simp[]) >>
drule_then assume_tac $ cj 1 subtm_size_less >>
‘term_size t0 <
         (term1_size l + 1)’ suffices_by simp[] >>
‘term_size a ≤ term1_size l’
 by (rw[term_size_eq] >> irule MEM_list_size_leq >> simp[])>>
drule_all_then assume_tac arithmeticTheory.LESS_EQ_TRANS >>
simp[]
QED



Theorem Var_tsubtm_tfv:
(∀tm n s. Var n s ∈ tsubtm tm ⇔(n,s) ∈ tfv tm) ∧
(∀st n s. Var n s ∈ ssubtm st ⇔ (n,s) ∈ sfv st)
Proof
ho_match_mp_tac better_tm_induction>>
rw[tsubtm_def,tfv_def,EQ_IMP_THM,MEM_MAP,PULL_EXISTS] (*8 *)
>- metis_tac[]
>- metis_tac[]
>- gs[MEM_MAP,PULL_EXISTS]
>> (gs[MEM_MAP,PULL_EXISTS] >> metis_tac[])
QED        

Theorem Var_tpsubtm:
t0 ∈ ssubtm s ⇒ t0 ∈ tpsubtm (Var n s)
Proof
rw[tpsubtm_def,tsubtm_def] >>
CCONTR_TAC >> gs[] >>
drule $ iffLR $ cj 2 Var_tsubtm_tfv >> metis_tac[tm_tree_WF]
QED


Theorem Fn_tpsubtm:
(t0 ∈ ssubtm s ⇒ t0 ∈ tpsubtm (Fn f s tl)) ∧
(∀t. MEM t tl ∧ t0 ∈ tsubtm t ⇒
     t0 ∈ tpsubtm (Fn f s tl))
Proof
rw[tpsubtm_def,tsubtm_def] (* 3 *)
>- (CCONTR_TAC >> gs[] >>
   drule_then assume_tac $ cj 2 subtm_size_less >>
   gs[term_size_def])
>- (rpt disj2_tac >> gs[MEM_MAP,PULL_EXISTS] >>
   metis_tac[]) >>
CCONTR_TAC >> gs[] >>
drule_then assume_tac $ cj 1 subtm_size_less >>
gs[term_size_def] >>
‘term_size t < sort_size s + (term1_size tl + (list_size char_size f + 1))’ suffices_by simp[] >>
‘term_size t ≤ term1_size tl’ suffices_by simp[] >>
rw[term_size_eq] >>
irule MEM_list_size_leq >> simp[]
QED

Theorem Var_tpsubtm_neq:
t0 ∈ ssubtm s ⇒ t0 ≠ Var n s
Proof
rw[] >> drule Var_tpsubtm >> rw[tpsubtm_def]
QED

Theorem Fn_tpsubtm_neq:
(t0 ∈ ssubtm s ⇒ t0 ≠ Fn f s tl) ∧
(∀t. MEM t tl ∧ t0 ∈ tsubtm t ⇒ t0 ≠ Fn f s tl)
Proof
rw[] (* 2 *)
>- (drule $ cj 1 Fn_tpsubtm >> rw[tpsubtm_def]) >>
drule $ cj 2 Fn_tpsubtm >> rw[tpsubtm_def]
QED
              
Theorem tsstt_itself:
 (∀t t0. tsstt t0 t0 t = t) ∧
 (∀s t0. ssstt t0 t0 s = s)
Proof
 ho_match_mp_tac better_tm_induction >>
 rw[tsstt_def] (* 3 *)
 >- (Cases_on ‘Var s0 s = t0’ >> simp[])
 >- (Cases_on ‘Fn s0 s l = t0’ >> simp[] >>
    rw[MAP_fix]) >>
 rw[MAP_fix]
QED 



  
        
    
Theorem tsstt_tsstt:
(∀t t1 t2 t3.
  t1 ∈ tsubtm t ∧ t2 ∉ tsubtm t ⇒
  tsstt t2 t3 (tsstt t1 t2 t) = tsstt t1 t3 t) ∧
(∀s t1 t2 t3.
  t1 ∈ ssubtm s ∧ t2 ∉ ssubtm s ⇒
  ssstt t2 t3 (ssstt t1 t2 s) = ssstt t1 t3 s)
Proof
  ho_match_mp_tac better_tm_induction >> rw[tsstt_def,MAP_EQ_f] (* 5 *)
  >- (Cases_on ‘Var s0 s = t1’ >> rw[] (* 2 *)
     >- rw[tsstt_fix] >>
     gs[tsubtm_def,tsstt_def] >>
     ‘Var s0 (ssstt t1 t2 s) ≠ t2’ suffices_by simp[] >>
     rw[Once EQ_SYM_EQ] >> irule Var_tpsubtm_neq >>
     irule $ cj 2 tsstt_tsubtm >> simp[])
  >- (Cases_on ‘Fn s0 s l = t1’ >> simp[] (* 2 *)
     >- rw[tsstt_fix] >>
     ‘Fn s0 (ssstt t1 t2 s) (MAP (λa. tsstt t1 t2 a) l) ≠ t2’
      by
       (gs[tsubtm_def] (* 2 *)
       >- (rw[Once EQ_SYM_EQ] >>
          irule $ cj 1 Fn_tpsubtm_neq >>
          irule $ cj 2 tsstt_tsubtm >> simp[]) >>
       rw[Once EQ_SYM_EQ] >>
       gs[MEM_MAP,PULL_EXISTS] >>
       irule $ cj 2 Fn_tpsubtm_neq >>
       gs[MEM_MAP,PULL_EXISTS] >>
       qexists ‘a’ >> simp[] >>
       irule $ cj 1 tsstt_tsubtm >> simp[]) >>
     gs[tsubtm_def,MEM_MAP,SF ETA_ss,tsstt_def]  (* 2 *)
     >- (rw[MAP_MAP_o,MAP_EQ_f] >>
        ‘∀y. MEM y l ⇒ t2 ∉ tsubtm y’ by metis_tac[] >>
        Cases_on ‘t1 ∈ tsubtm e’ (* 2 *)
        >- (first_x_assum irule >> metis_tac[]) >>
        drule_then assume_tac $ cj 1 tsstt_id >>
        simp[] >>
        irule $ cj 1 tsstt_id >> metis_tac[]) >>
     rw[MAP_MAP_o,MAP_EQ_f] (* 2 *)
     >- (Cases_on ‘t1 ∈ ssubtm s’ (* 2 *)
        >- (first_x_assum irule >> metis_tac[]) >>
        drule_then assume_tac $ cj 2 tsstt_id >> simp[] >>
        irule $ cj 2  tsstt_id >> metis_tac[]) >>
     Cases_on ‘t1 ∈ tsubtm e’ (* 2 *)
     >- (first_x_assum irule >> metis_tac[]) >>
     drule_then assume_tac $ cj 1 tsstt_id >> simp[] >>
     irule $ cj 1 tsstt_id >> metis_tac[])
  >- rw[tsstt_fix]
  >- gs[tsubtm_def] >>
  rw[MAP_MAP_o,MAP_EQ_f] >> gs[tsubtm_def,MEM_MAP] >>
  Cases_on ‘t1 ∈ tsubtm a’ (*2  *)
  >- metis_tac[] >>
  drule_then assume_tac $ cj 1 tsstt_id >> simp[] >>
  irule $ cj 1 tsstt_id >> metis_tac[]
QED  


Theorem tsstt_tsstt1:
(∀t t1 t2 t3.
  t2 ∉ tsubtm t ⇒
  tsstt t2 t3 (tsstt t1 t2 t) = tsstt t1 t3 t) ∧
(∀s t1 t2 t3.
  t2 ∉ ssubtm s ⇒
  ssstt t2 t3 (ssstt t1 t2 s) = ssstt t1 t3 s)
Proof
rw[] (* 2 *)
>- (Cases_on ‘t1 ∈ tsubtm t’ >- metis_tac[tsstt_tsstt] >>
   drule_then assume_tac $ cj 1 tsstt_id >> simp[] >>
   metis_tac[tsstt_id]) >>
Cases_on ‘t1 ∈ ssubtm s’ >- metis_tac[tsstt_tsstt] >>
drule_then assume_tac $ cj 2 tsstt_id >> simp[] >>
metis_tac[tsstt_id]
QED
        



Theorem tsstt_back:
(∀t t1 t2.
  t1 ∈ tsubtm t ∧ t2 ∉ tsubtm t ⇒ tsstt t2 t1 (tsstt t1 t2 t) = t) ∧
(∀s t1 t2.
  t1 ∈ ssubtm s ∧ t2 ∉ ssubtm s ⇒ ssstt t2 t1 (ssstt t1 t2 s) = s)
Proof
rw[] (* 2 *)
>- (drule_all_then assume_tac $ cj 1 tsstt_tsstt >>
    simp[tsstt_itself]) >>
drule_all_then assume_tac $ cj 2 tsstt_tsstt >>
simp[tsstt_itself]
QED



Theorem tlfv_is_cont:
∀l. is_cont (tlfv l)
Proof
Induct_on ‘l’ >> rw[is_cont_def,tlfv_def] (* 2 *)
>> rw[SUBSET_DEF] >> metis_tac[vsort_tfv_closed]
QED        




Theorem TO_FMAP_MEM:
ALL_DISTINCT (MAP FST l) ⇒ MEM (a,b) l ⇒ (TO_FMAP l) ' a = b
Proof
rw[] >> irule FUPDATE_LIST_APPLY_MEM >>
drule $ iffLR MEM_EL >> rw[] >>
qexists ‘n’ >> gs[] >>
‘EL n (MAP FST l) = FST (EL n l)’
  by (irule EL_MAP >> rw[]) >>
‘EL n (MAP SND l) = SND (EL n l)’
  by (irule EL_MAP >> rw[]) >> simp[] >>
 qpat_x_assum ‘(a,b) = EL n l’ (assume_tac o GSYM) >>
simp[] >> rw[] >>
CCONTR_TAC >>
drule ALL_DISTINCT_EL_IMP >> rw[] >>
qexistsl [‘n’,‘m’] >> gs[]
QED
        




        
Theorem DRESTRICT_cstt:        
  cstt σ ∧ s ⊆ FDOM σ ∧
  is_cont s ⇒ cstt (DRESTRICT σ s)
Proof
  rw[cstt_def,DRESTRICT_DEF] >>
  rename [‘(n,s) ∈ ss’] >>
  irule $ cj 2 fmap_fv_inst_eq_alt >>
  simp[DRESTRICT_DEF] >> gs[is_cont_def] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  ‘sfv s ⊆ FDOM σ’ by metis_tac[SUBSET_TRANS] >>
  rw[] >> metis_tac[SUBSET_DEF]
QED  



Theorem tsubst_id:
(∀t. (n,s) ∉ tfv t ⇒ tsubst (n,s) t1 t = t) ∧
(∀st. (n,s) ∉ sfv st ⇒ ssubst (n,s) t1 st = st) 
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 4 *)
>- (gs[tsubst_def] >>
   ‘¬(n = s0 ∧ s = st)’ by metis_tac[] >> simp[])
>- (gs[tsubst_def] >> rw[MAP_fix] >> metis_tac[])
>- gs[tsubst_def] >>
gs[tsubst_def] >> rw[MAP_fix] >> metis_tac[]
QED


Theorem tfv_tsubst_SUBSET:
(∀tm n s t. 
      (∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (n,s) ∉ sfv s0) ⇒
tfv (tsubst (n,s) t tm) ⊆ (tfv tm DELETE (n,s)) ∪ tfv t) ∧
∀st n s t. 
     (∀n0 s0. (n0,s0) ∈ sfv st ⇒ (n,s) ∉ sfv s0)⇒
sfv (ssubst (n,s) t st) ⊆ (sfv st DELETE (n,s)) ∪ tfv t
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 4 *)
>- (gs[tsubst_def,tfv_def] >>
   Cases_on ‘n = s0 ∧ s = st’ >> simp[] >>
   ‘ssubst (n,s) t st = st’
    by (irule $ cj 2 tsubst_id >> metis_tac[]) >>
   simp[] >> rw[] >>
   gs[SUBSET_DEF])
>- (gs[tsubst_def,tfv_thm,MEM_MAP,PULL_EXISTS] >> 
   rw[SUBSET_DEF,PULL_EXISTS] (* 2 *)
   >- (first_x_assum $ drule_then assume_tac >>
      ‘tfv (tsubst (n,s) t a) ⊆ tfv a DELETE (n,s) ∪ tfv t’
        by (first_x_assum irule >> metis_tac[]) >>
      gs[SUBSET_DEF] >> metis_tac[]) >>
   ‘sfv (ssubst (n,s) t st) ⊆ sfv st DELETE (n,s) ∪ tfv t’
     by (first_x_assum irule >> metis_tac[]) >>
   gs[SUBSET_DEF] >> metis_tac[])
>- gs[tsubst_def,tfv_def] >>
gs[tsubst_def,tfv_thm,MEM_MAP,PULL_EXISTS] >> 
rw[SUBSET_DEF,PULL_EXISTS] >>
first_x_assum $ drule_then assume_tac >>
‘tfv (tsubst (n,s) t a) ⊆ tfv a DELETE (n,s) ∪ tfv t’
 by (first_x_assum irule >> metis_tac[]) >>
gs[SUBSET_DEF] >> metis_tac[]
QED





Definition tabs_def:
  (tabs (m,s) i (Var n st) =
  if m = n ∧ s = st then Bound i else (Var n st)) ∧
  (tabs (m,s) i (Fn f st tl) =
  Fn f (sabs (m,s) i st) (MAP (tabs (m,s) i) tl)) ∧
  tabs (m,s) t (Bound i) = Bound i ∧
  (sabs (m,s) i (St n tl) =
   St n (MAP (tabs (m,s) i) tl))
Termination
 WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,_,t) => term_size t
         | INR (_,_,st) => sort_size st)’
End

        
Theorem tabs_tsubst:
(∀tm n s i.
(∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ⇒
tabs (n,s) i tm = tsubst (n,s) (Bound i) tm) ∧
(∀st n s i.
(∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ⇒
sabs (n,s) i st = ssubst (n,s) (Bound i) st)
Proof
ho_match_mp_tac better_tm_induction >>
simp[tabs_def,tfv_thm,tsubst_def,MAP_EQ_f,SF ETA_ss,PULL_EXISTS] >>
rw[] (* 4 *)
>- (Cases_on ‘n = s0 ∧ s = st’ >> simp[] >>
   metis_tac[tsubst_id]) 
>- metis_tac[]
>- metis_tac[]>>
metis_tac[]
QED        


Theorem tfv_tabs_SUBSET:
  (∀tm n s t. 
     (∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (n,s) ∉ sfv s0) ⇒
     tfv (tabs (n,s) i tm) ⊆ tfv tm DELETE (n,s)) ∧
  ∀st n s t. 
    (∀n0 s0. (n0,s0) ∈ sfv st ⇒ (n,s) ∉ sfv s0) ⇒
    sfv (sabs (n,s) i st) ⊆ sfv st DELETE (n,s)
Proof
  rw[] (* 2 *)
  >- (drule_then assume_tac $ cj 1 tabs_tsubst >>
      simp[] >>
      drule_then assume_tac $ cj 1 tfv_tsubst_SUBSET >>
      first_x_assum (qspecl_then [‘Bound i’] assume_tac) >>
      gs[tfv_thm]) >>
  drule_then assume_tac $ cj 2 tabs_tsubst >>
  simp[] >>
  drule_then assume_tac $ cj 2 tfv_tsubst_SUBSET >>
  first_x_assum (qspecl_then [‘Bound i’] assume_tac) >>
  gs[tfv_thm]
QED   


Theorem tabs_id:
(∀t. (n,s) ∉ tfv t ⇒ tabs (n,s) i t = t) ∧
∀st. (n,s) ∉ sfv st ⇒ sabs (n,s) i st = st
Proof
ho_match_mp_tac better_tm_induction >>
simp[tfv_thm,tabs_def,MAP_fix,SF ETA_ss] >> rw[] (* 3 *) 
>- (‘¬(n = s0 ∧ s = st)’ by metis_tac[] >> simp[])
>> metis_tac[]
QED
              
Theorem tabs_tinst:
∀e an ast σ nn.
  (tfv e ∪ sfv ast) DELETE (an,ast) ⊆ FDOM σ ∧
  (an,ast) ∉ FDOM σ ∧
  (∀x s. x ∈ tfv e ∪ sfv ast ∧ x ≠ (an,ast) ⇒
         (nn,s) ∉ tfv (σ ' x)) ∧
  (∀n1 s1. (n1,s1) ∈ tfv e ⇒ (an,ast) ∉ sfv s1) ⇒
  tabs (nn,sinst σ ast) i
         (tinst (σ |+ ((an,ast),Var nn (sinst σ ast))) e) =
 tinst σ (tabs (an,ast) i e)
Proof
Induct_on ‘e’ (* 3 *)
>- (rw[] (* 2 *)
    >- gs[SUBSET_DEF] >>
    gs[] (* 2 *)
    >- simp[tinst_def,tabs_def] >>
   rename [‘(n,s) ∈ FDOM σ’] >>
   ‘(n,s) ≠ (an,ast)’ by metis_tac[] >>
   ‘(tabs (an,ast) i (Var n s)) = Var n s’
    by (irule $ cj 1 tabs_id >> gs[tfv_def] >>
        metis_tac[])>>
   simp[FAPPLY_FUPDATE_THM] >>
   ‘(nn,sinst σ ast) ∉ tfv (σ ' (n,s))’
     by (first_x_assum irule >> gs[EXTENSION]) >>
   irule $ cj 1 tabs_id >> gs[])
>- (rw[] >>
simp[tinst_def,tabs_def,SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
Cases_on ‘s’ >>
rename [‘(St sn tl)’] >>
simp[tinst_def,tabs_def,SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
gs[stms_def,PULL_EXISTS,DISJ_IMP_THM] >> rw[] (* 2 *)
>> qabbrev_tac ‘σ1 = DRESTRICT σ (tfv e ∪ sfv ast)’ >>
   ‘FDOM σ1 = (tfv e ∪ sfv ast) DELETE (an,ast)’
     by (rw[Abbr‘σ1’,DRESTRICT_DEF,EXTENSION] >>
        gs[SUBSET_DEF] >> metis_tac[]) >>
   ‘FDOM σ1 ⊆ FDOM σ’
     by (gs[SUBSET_DEF] >> metis_tac[]) >>
   ‘∀x. x ∈ FDOM σ1 ⇒ σ1 ' x = σ ' x’
     by (gs[Abbr‘σ1’,DRESTRICT_DEF,SUBSET_DEF] >>
         metis_tac[]) >>
   ‘tfv (tabs (an,ast) i e) ⊆
    tfv e DELETE (an,ast)’
     by (irule $ cj 1 tfv_tabs_SUBSET >>
        metis_tac[]) >>
   pop_assum mp_tac >> rw[tfv_def] >> rw[] >> 
   ‘tinst σ (tabs (an,ast) i e) =
    tinst σ1 (tabs (an,ast) i e)’
     by (irule $ cj 1 fmap_fv_inst_eq_alt >>
        ‘tfv (tabs (an,ast) i e) ⊆ FDOM σ’
          by  (irule SUBSET_TRANS >>
               first_x_assum $ irule_at Any >>
             gs[SUBSET_DEF] >> metis_tac[]) >>
        ‘tfv (tabs (an,ast) i e) ⊆ FDOM σ1’
          by (irule SUBSET_TRANS >>
             last_x_assum $ irule_at Any >>
             gs[SUBSET_DEF] >> metis_tac[]) >>
        simp[] >>
        rw[] >> simp[Once EQ_SYM_EQ] >>
        first_x_assum irule >> metis_tac[SUBSET_DEF]) >>
   simp[] >> 
   ‘sinst σ ast = sinst σ1 ast’
    by (irule $ cj 2 fmap_fv_inst_eq_alt >>
        gs[SUBSET_DEF] >> metis_tac[tm_tree_WF]) >>
   simp[] >>
   ‘(tinst (σ |+ ((an,ast),Var nn (sinst σ1 ast))) e) =
    (tinst (σ1 |+ ((an,ast),Var nn (sinst σ1 ast))) e)’
    by (irule $ cj 1 fmap_fv_inst_eq_alt >>
       simp[FDOM_FUPDATE] >>
       ‘tfv e ⊆ (an,ast) INSERT FDOM σ ∧
       tfv e ⊆ (an,ast) INSERT tfv e ∪ sfv ast
       DELETE (an,ast)’
         by (gs[SUBSET_DEF] >> metis_tac[tm_tree_WF]) >>
       simp[] >> rw[] >>
       Cases_on ‘x = (an,ast)’ >>
       simp[FAPPLY_FUPDATE_THM] >>
       gs[SUBSET_DEF] >> metis_tac[tm_tree_WF]) >>
   simp[] 
   >- (last_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
   first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
rw[tfv_def,tinst_def,tabs_def]   
QED         


Theorem tsubst_tinst:
∀e an ast σ nn.
  (tfv e ∪ sfv ast) DELETE (an,ast) ⊆ FDOM σ ∧
  (an,ast) ∉ FDOM σ ∧
  (∀x s. x ∈ tfv e ∪ sfv ast ∧ x ≠ (an,ast) ⇒
         (nn,s) ∉ tfv (σ ' x)) ∧
  (∀n1 s1. (n1,s1) ∈ tfv e ⇒ (an,ast) ∉ sfv s1) ⇒
  tsubst (nn,sinst σ ast) (Bound i)
         (tinst (σ |+ ((an,ast),Var nn (sinst σ ast))) e) =
 tinst σ (tsubst (an,ast) (Bound i) e)
Proof
Induct_on ‘e’ (* 3 *)
>- (rw[] (* 2 *)
    >- gs[SUBSET_DEF] >>
    gs[] (* 2 *)
    >- simp[tinst_def,tsubst_def] >>
   rename [‘(n,s) ∈ FDOM σ’] >>
   ‘(n,s) ≠ (an,ast)’ by metis_tac[] >>
   ‘(tsubst (an,ast) (Bound i) (Var n s)) = Var n s’
    by (irule $ cj 1 tsubst_id >> gs[tfv_def] >>
        metis_tac[])>>
   simp[FAPPLY_FUPDATE_THM] >>
   ‘(nn,sinst σ ast) ∉ tfv (σ ' (n,s))’
     by (first_x_assum irule >> gs[EXTENSION]) >>
   irule $ cj 1 tsubst_id >> gs[])
>- (rw[] >>
simp[tinst_def,tsubst_def,SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
Cases_on ‘s’ >>
rename [‘(St sn tl)’] >>
simp[tinst_def,tsubst_def,SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
gs[stms_def,PULL_EXISTS,DISJ_IMP_THM] >> rw[] (* 2 *)
>> qabbrev_tac ‘σ1 = DRESTRICT σ (tfv e ∪ sfv ast)’ >>
   ‘FDOM σ1 = (tfv e ∪ sfv ast) DELETE (an,ast)’
     by (rw[Abbr‘σ1’,DRESTRICT_DEF,EXTENSION] >>
        gs[SUBSET_DEF] >> metis_tac[]) >>
   ‘FDOM σ1 ⊆ FDOM σ’
     by (gs[SUBSET_DEF] >> metis_tac[]) >>
   ‘∀x. x ∈ FDOM σ1 ⇒ σ1 ' x = σ ' x’
     by (gs[Abbr‘σ1’,DRESTRICT_DEF,SUBSET_DEF] >>
         metis_tac[]) >>
   ‘tfv (tsubst (an,ast) (Bound i) e) ⊆
    tfv e DELETE (an,ast) ∪ tfv (Bound i)’
     by (irule $ cj 1 tfv_tsubst_SUBSET >>
        metis_tac[]) >>
   pop_assum mp_tac >> rw[tfv_def] >> rw[] >> 
   ‘tinst σ (tsubst (an,ast) (Bound i) e) =
    tinst σ1 (tsubst (an,ast) (Bound i) e)’
     by (irule $ cj 1 fmap_fv_inst_eq_alt >>
        ‘tfv (tsubst (an,ast) (Bound i) e) ⊆ FDOM σ’
          by (irule SUBSET_TRANS >>
             first_x_assum $ irule_at Any >>
             gs[SUBSET_DEF] >> metis_tac[]) >>
        ‘tfv (tsubst (an,ast) (Bound i) e) ⊆ FDOM σ1’
          by (irule SUBSET_TRANS >>
             last_x_assum $ irule_at Any >>
             gs[SUBSET_DEF] >> metis_tac[]) >>
        simp[] >>
        rw[] >> simp[Once EQ_SYM_EQ] >>
        first_x_assum irule >> metis_tac[SUBSET_DEF]) >>
   simp[] >> 
   ‘sinst σ ast = sinst σ1 ast’
    by (irule $ cj 2 fmap_fv_inst_eq_alt >>
        gs[SUBSET_DEF] >> metis_tac[tm_tree_WF]) >>
   simp[] >>
   ‘(tinst (σ |+ ((an,ast),Var nn (sinst σ1 ast))) e) =
    (tinst (σ1 |+ ((an,ast),Var nn (sinst σ1 ast))) e)’
    by (irule $ cj 1 fmap_fv_inst_eq_alt >>
       simp[FDOM_FUPDATE] >>
       ‘tfv e ⊆ (an,ast) INSERT FDOM σ ∧
       tfv e ⊆ (an,ast) INSERT tfv e ∪ sfv ast
       DELETE (an,ast)’
         by (gs[SUBSET_DEF] >> metis_tac[tm_tree_WF]) >>
       simp[] >> rw[] >>
       Cases_on ‘x = (an,ast)’ >>
       simp[FAPPLY_FUPDATE_THM] >>
       gs[SUBSET_DEF] >> metis_tac[tm_tree_WF]) >>
   simp[] 
   >- (last_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
   first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[]) >>
rw[tfv_def,tinst_def,tsubst_def]   
QED         

                          


Theorem sabs_sinst:
∀e an ast σ nn.
  sfv e ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧ (an,ast) ∉ FDOM σ ∧
  (∀x s. x ∈ sfv e ∪ sfv ast ∧ x ≠ (an,ast)⇒ (nn,s) ∉ tfv (σ ' x)) ∧
  (∀n1 s1. (n1,s1) ∈ sfv e ⇒ (an,ast) ∉ sfv s1) ⇒
  sabs (nn,sinst σ ast) i
         (sinst (σ |+ ((an,ast),Var nn (sinst σ ast))) e) =
 sinst σ (sabs (an,ast) i e)
Proof
rw[] >> Cases_on ‘e’ >>
rw[tabs_def,tinst_def,MAP_EQ_f,MAP_MAP_o] >>
irule tabs_tinst >> gs[SUBSET_DEF] >> metis_tac[]
QED

        
Theorem ssubst_sinst:
∀e an ast σ nn.
  sfv e ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧ (an,ast) ∉ FDOM σ ∧
  (∀x s. x ∈ sfv e ∪ sfv ast ∧ x ≠ (an,ast)⇒ (nn,s) ∉ tfv (σ ' x)) ∧
  (∀n1 s1. (n1,s1) ∈ sfv e ⇒ (an,ast) ∉ sfv s1) ⇒
  ssubst (nn,sinst σ ast) (Bound i)
         (sinst (σ |+ ((an,ast),Var nn (sinst σ ast))) e) =
 sinst σ (ssubst (an,ast) (Bound i) e)
Proof
rw[] >> Cases_on ‘e’ >>
rw[tsubst_def,tinst_def,MAP_EQ_f,MAP_MAP_o] >>
irule tsubst_tinst >> gs[SUBSET_DEF] >> metis_tac[]
QED
        

Theorem tsubst_id':
 (n,s) ≠ (n1,s1) ∧ (n,s) ∉ sfv s1 ⇒
 tsubst (n,s) (Bound i) (Var n1 s1) = Var n1 s1
Proof
 rw[tsubst_def] >>
 irule $ cj 2 tsubst_id >> rw[]
QED
 




Theorem tfv_tsubst:
(∀tm n s.
 (∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (n,s) ∉ sfv s0) ∧
 (n,s) ∈ tfv tm ⇒
 sfv s ∪ tfv (tsubst (n,s) (Bound i) tm) =
 tfv tm DELETE (n,s)) ∧
(∀st n s.
 (∀n0 s0. (n0,s0) ∈ sfv st ⇒ (n,s) ∉ sfv s0) ∧
 (n,s) ∈ sfv st ⇒
 sfv s ∪ sfv (ssubst (n,s) (Bound i) st) =
 sfv st DELETE (n,s))
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 5 *)
>- (rw[tsubst_def,tfv_def,EXTENSION] >> metis_tac[])
>- (‘(tsubst (n,s) (Bound i) (Var s0 st)) =
    (Var s0 st)’ by (irule tsubst_id' >> metis_tac[]) >>
   simp[] >>
   ‘sfv s ∪ sfv (ssubst (n,s) (Bound i) st) =
   sfv st DELETE (n,s)’
    by (first_x_assum irule >> metis_tac[]) >>
   ‘(ssubst (n,s) (Bound i) st) = st’
    by (irule $ cj 2 tsubst_id >> metis_tac[]) >>
   gs[] >> simp[SimpLHS, Once UNION_COMM] >>
   simp[GSYM UNION_ASSOC] >>
   ‘(sfv st ∪ sfv s) = (sfv s ∪ sfv st)’
    by simp[Once UNION_COMM] >>
   simp[] >> gs[EXTENSION] >>
   ‘(s0,st) ≠ (n,s)’ by simp[] >> 
   metis_tac[])
>- (gs[PULL_EXISTS] >>
    rw[tfv_thm,tsubst_def,MEM_MAP,SF ETA_ss] >>
    rw[UNION_ASSOC] >>
    ‘BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l)} =
    (BIGUNION {tfv t1 | (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∈ tfv y)}) ∪
    (BIGUNION {tfv t1 | (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∉ tfv y)})’
    by (rw[EXTENSION] >> metis_tac[]) >>
    qabbrev_tac ‘BU =  BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l)}’ >>
    qabbrev_tac ‘BU1 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∈ tfv y)}’ >>
    qabbrev_tac ‘BU2 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∉ tfv y)}’ >>
    simp[] >>
    ‘BU2 = BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y}’
     by
      (rw[Abbr‘BU2’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
      (* 2 *)
      >> (‘(tsubst (n,s) (Bound i) y) = y’
          suffices_by metis_tac[] >>
         irule $ cj 1 tsubst_id >> simp[])) >>
    simp[UNION_ASSOC] >>
    Cases_on ‘(n,s) ∈ sfv st’ (* 2 *) >-
    (‘sfv s ∪ BU1 ∪ BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} ∪
        sfv (ssubst (n,s) (Bound i) st) =
     sfv s ∪ BU1 ∪ BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} ∪
        sfv (ssubst (n,s) (Bound i) st) ∪ sfv s ’
      by (rw[Once EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
     pop_assum SUBST_ALL_TAC >>
    ‘sfv s ∪ BU1 =
     BIGUNION {sfv s0 ∪ tfv t1 |
     (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧ s0 = s}’
     by (rw[Abbr‘BU1’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv t1 |
           (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧
           s0 = s} =
      BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
            MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} =
      BIGUNION
          {tfv y DELETE (n0,s0) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by
        (‘∀y n0 s0. MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n ⇒
          sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) =
          tfv y DELETE (n0,s0)’
         suffices_by
          (strip_tac >> AP_TERM_TAC >> 
          rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
          metis_tac[]) >>
         rw[] >>
         first_x_assum irule >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {tfv y DELETE (n0,s0) | MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} ∪
        BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} =
     BIGUNION {tfv y | MEM y l} DELETE (n,s)’
      by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
         >>  metis_tac[]) >>
     simp[] >>
     rw[GSYM UNION_ASSOC] >>
     ‘BIGUNION {tfv y | MEM y l} DELETE (n,s) ∪
        (sfv s ∪ sfv (ssubst (n,s) (Bound i) st)) =
        BIGUNION {tfv t | MEM t l} ∪ sfv st DELETE (n,s)’
       suffices_by metis_tac[UNION_COMM] >>
     ‘sfv s ∪ sfv (ssubst (n,s) (Bound i) st) =
      sfv st DELETE (n,s)’
          by (first_x_assum irule >> metis_tac[]) >>
     simp[] >>
     rw[Once EXTENSION] >> metis_tac[]) >>
    (*second case start here*)
    ‘sfv s ∪ BU1 =
     BIGUNION {sfv s0 ∪ tfv t1 |
     (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧ s0 = s}’
     by (rw[Abbr‘BU1’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv t1 |
           (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧
           s0 = s} =
      BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
            MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} =
      BIGUNION
          {tfv y DELETE (n0,s0) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by
        (‘∀y n0 s0. MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n ⇒
          sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) =
          tfv y DELETE (n0,s0)’
         suffices_by
          (strip_tac >> AP_TERM_TAC >> 
          rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
          metis_tac[]) >>
         rw[] >>
         first_x_assum irule >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {tfv y DELETE (n0,s0) | MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} ∪
        BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} =
     BIGUNION {tfv y | MEM y l} DELETE (n,s)’
      by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
         >>  metis_tac[]) >>
     simp[] >>
     ‘(ssubst (n,s) (Bound i) st) = st’
      by (irule $ cj 2 tsubst_id >> metis_tac[]) >>
     simp[] >> rw[EXTENSION] >> metis_tac[])
>- (gs[PULL_EXISTS] >>
   rw[tfv_thm,tsubst_def,MEM_MAP,SF ETA_ss] >>      
   rw[UNION_ASSOC] >>
    ‘BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l)} =
    (BIGUNION {tfv t1 | (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∈ tfv y)}) ∪
    (BIGUNION {tfv t1 | (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∉ tfv y)})’
    by (rw[EXTENSION] >> metis_tac[]) >>
    qabbrev_tac ‘BU =  BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l)}’ >>
    qabbrev_tac ‘BU1 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∈ tfv y)}’ >>
    qabbrev_tac ‘BU2 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∉ tfv y)}’ >>
    simp[] >>
    ‘BU2 = BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y}’
     by
      (rw[Abbr‘BU2’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
      (* 2 *)
      >> (‘(tsubst (n,s) (Bound i) y) = y’
          suffices_by metis_tac[] >>
         irule $ cj 1 tsubst_id >> simp[])) >>
    simp[UNION_ASSOC] >>
    ‘sfv s ∪ sfv (ssubst (n,s) (Bound i) st) =
     sfv st DELETE (n,s)’ by metis_tac[] >>
    Cases_on ‘∃y. MEM y l ∧ (n,s) ∈ tfv y’ >> gs[] >-
    (‘ sfv s ∪ BU1 ∪ BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} ∪
        sfv (ssubst (n,s) (Bound i) st) =
      sfv s ∪ BU1 ∪ BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} ∪ sfv s ∪
        sfv (ssubst (n,s) (Bound i) st)’
      by (rw[EXTENSION] >> metis_tac[]) >> simp[] >>
     ‘sfv s ∪ BU1 ∪ BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} ∪ (sfv s ∪
        sfv (ssubst (n,s) (Bound i) st)) =
      BIGUNION {tfv t | MEM t l} ∪ sfv st DELETE (n,s)’
       suffices_by simp[UNION_ASSOC] >>
      simp[] >> 
‘sfv s ∪ BU1 =
     BIGUNION {sfv s0 ∪ tfv t1 |
     (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧ s0 = s}’
     by (rw[Abbr‘BU1’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv t1 |
           (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧
           s0 = s} =
      BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
            MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >> simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} =
      BIGUNION
          {tfv y DELETE (n0,s0) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by
        (‘∀y n0 s0. MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n ⇒
          sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) =
          tfv y DELETE (n0,s0)’
         suffices_by
          (strip_tac >> AP_TERM_TAC >> 
          rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
          metis_tac[]) >>
         rw[] >>
         first_x_assum irule >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {tfv y DELETE (n0,s0) | MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} ∪
        BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} =
     BIGUNION {tfv y | MEM y l} DELETE (n,s)’
      by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
         >>  metis_tac[]) >>
     simp[] >>
     rw[EXTENSION] >> metis_tac[]) >>
    ‘BU1 = {}’
     by (rw[Abbr‘BU1’] >> disj1_tac >>
        rw[EXTENSION]) >> simp[] >>
    ‘{tfv y | MEM y l ∧ (n,s) ∉ tfv y} =
     {tfv t | MEM t l}’ by (rw[EXTENSION] >> metis_tac[]) >>
    simp[] >>
    ‘BIGUNION {tfv t | MEM t l} ∪ (sfv s ∪ sfv (ssubst (n,s) (Bound i) st)) =
        BIGUNION {tfv t | MEM t l} ∪ sfv st DELETE (n,s)’
     suffices_by metis_tac[UNION_ASSOC,UNION_COMM] >>
    simp[] >> rw[EXTENSION] >> metis_tac[]) >>
gs[PULL_EXISTS] >>
rw[tfv_thm,tsubst_def,MEM_MAP,SF ETA_ss] >>          
 ‘BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l)} =
    (BIGUNION {tfv t1 | (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∈ tfv y)}) ∪
    (BIGUNION {tfv t1 | (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∉ tfv y)})’
    by (rw[EXTENSION] >> metis_tac[]) >>
    qabbrev_tac ‘BU =  BIGUNION {tfv t' | (∃y. t' = tsubst (n,s) (Bound i) y ∧ MEM y l)}’ >>
    qabbrev_tac ‘BU1 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∈ tfv y)}’ >>
    qabbrev_tac ‘BU2 = BIGUNION
          {tfv t1 |
           (∃y. t1 = tsubst (n,s) (Bound i) y ∧ MEM y l ∧ (n,s) ∉ tfv y)}’ >>
    simp[] >>
    ‘BU2 = BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y}’
     by
      (rw[Abbr‘BU2’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
      (* 2 *)
      >> (‘(tsubst (n,s) (Bound i) y) = y’
          suffices_by metis_tac[] >>
         irule $ cj 1 tsubst_id >> simp[])) >>
    simp[UNION_ASSOC] >>
‘sfv s ∪ BU1 =
     BIGUNION {sfv s0 ∪ tfv t1 |
     (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧ s0 = s}’
     by (rw[Abbr‘BU1’,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv t1 |
           (∃y. t1 = tsubst (n,s0) (Bound i) y ∧ MEM y l ∧ (n,s0) ∈ tfv y) ∧
           s0 = s} =
      BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
            MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS]
     (* 4 *)
     >> metis_tac[]) >> simp[] >>
     ‘BIGUNION
          {sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} =
      BIGUNION
          {tfv y DELETE (n0,s0) |
           MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n}’
       by
        (‘∀y n0 s0. MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n ⇒
          sfv s0 ∪ tfv (tsubst (n0,s0) (Bound i) y) =
          tfv y DELETE (n0,s0)’
         suffices_by
          (strip_tac >> AP_TERM_TAC >> 
          rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] >>
          metis_tac[]) >>
         rw[] >>
         first_x_assum irule >> metis_tac[]) >>
     simp[] >>
     ‘BIGUNION
          {tfv y DELETE (n0,s0) | MEM y l ∧ (n0,s0) ∈ tfv y ∧ s0 = s ∧ n0 = n} ∪
        BIGUNION {tfv y | MEM y l ∧ (n,s) ∉ tfv y} =
     BIGUNION {tfv y | MEM y l} DELETE (n,s)’
      by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 3 *)
         >>  metis_tac[]) >>
     simp[]
QED     




        
Theorem tfv_tabs:
(∀tm n s.
 (∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (n,s) ∉ sfv s0) ∧
 (n,s) ∈ tfv tm ⇒
 sfv s ∪ tfv (tabs (n,s) i tm) =
 tfv tm DELETE (n,s)) ∧
(∀st n s.
 (∀n0 s0. (n0,s0) ∈ sfv st ⇒ (n,s) ∉ sfv s0) ∧
 (n,s) ∈ sfv st ⇒
 sfv s ∪ sfv (sabs (n,s) i st) =
 sfv st DELETE (n,s))
Proof
metis_tac[tabs_tsubst,tfv_tsubst]
QED        




Theorem DRESTRICT_wfcod:
  wfcod Σf σ ⇒ ∀s.wfcod Σf (DRESTRICT σ s)
Proof
 rw[wfcod_def,DRESTRICT_DEF]
QED 


Theorem FUPDATE_wfcod:
  wfcod Σf σ ⇒ ∀x t. wft Σf t ⇒ wfcod Σf (σ |+ ((n,s),t))
Proof
 rw[wfcod_def,FAPPLY_FUPDATE_THM] >>
 Cases_on ‘n' = n ∧ s' = s ’ >> simp[]
QED 
               

Theorem tfv_FINITE[simp]:
 (∀t. FINITE (tfv t)) ∧ (∀s. FINITE (sfv s))
Proof
 ho_match_mp_tac better_tm_induction >> simp[PULL_EXISTS] >>
 ‘∀l. {tfv t | MEM t l} = IMAGE tfv (set l)’  suffices_by simp[] >>
 simp[EXTENSION]
QED


Theorem FDOM_TO_FMAP:
FDOM (TO_FMAP l) = set (MAP FST l)
Proof
simp[FDOM_FUPDATE_LIST]
QED


        
Theorem tsubst_eq_tinst:
(∀t n s new.
tsubst (n,s) new t = tinst (TO_FMAP [((n,s),new)]) t) ∧
(∀st n s new.
ssubst (n,s) new st = sinst (TO_FMAP [((n,s),new)]) st)
Proof  
ho_match_mp_tac better_tm_induction >>
rw[tsubst_def,tinst_def] (* 3 *)
>- (Cases_on ‘n = s0 ∧ s = st’ >- (simp[FDOM_TO_FMAP] >>
   rw[Once EQ_SYM_EQ] >> irule TO_FMAP_MEM >>
   simp[]) >>
   simp[FDOM_TO_FMAP] >>
   ‘s0 = n ⇒ st ≠ s’ by metis_tac[] >> simp[])
>> rw[MAP_EQ_f]
QED


 



Theorem wft_tbounds:
(∀t. wft Σf t ⇒ tbounds t = {}) ∧
(∀s. wfs Σf s ⇒ sbounds s = {})
Proof
ho_match_mp_tac better_tm_induction >>
simp[wft_def,tbounds_thm] >> rw[] (* 2 *) 
>- (Cases_on ‘l’ >> gs[] >> 
    disj2_tac >> rw[Once EXTENSION] >>
    metis_tac[]) >>
gs[EVERY_MEM] >>
Cases_on ‘l’ >> gs[] >> 
disj2_tac >> rw[Once EXTENSION] >>
metis_tac[]
QED


Theorem Bound_NOT_wft:
¬(wft Σf (Bound i))
Proof
rw[wft_def]
QED



Theorem tfv_tsubtm_closed:
(∀tm n s t0. (n,s) ∈ tfv tm ∧ t0 ∈ ssubtm s ⇒
             t0 ∈ tsubtm tm) ∧
(∀st n s t0. (n,s) ∈ sfv st ∧ t0 ∈ ssubtm s ⇒
             t0 ∈ ssubtm st)
Proof             
ho_match_mp_tac better_tm_induction >>
simp[tfv_thm,tsubtm_def,MEM_MAP] >> rw[] (* 5 *)
>- simp[]
>> metis_tac[]
QED

Theorem wfabsap_sfv_sbounds:
  wfabsap Σf sl tl ⇒
  (∀n0 s0 st. MEM st sl ∧ (n0,s0) ∈ sfv st ⇒
              sbounds s0 = {})
Proof
Cases_on ‘sl’ >> Cases_on ‘tl’ >> simp[wfabsap_def] >>
rw[] (* 2 *)
>- (CCONTR_TAC >> gs[GSYM MEMBER_NOT_EMPTY] >>
   drule_then assume_tac $ cj 2 wft_tbounds>>
   Cases_on ‘h'’ >> gs[wft_def,sort_of_def] (* 2 *)
   >> (gs[GSYM Bound_tsubtm]  >>
      drule_all_then assume_tac $ cj 2 tfv_tsubtm_closed >>
      gs[Bound_tsubtm]) )>>
metis_tac[]
QED      
     
        

Theorem LENGTH_specsl:
∀sl t i.  LENGTH (specsl i t sl) =  LENGTH sl
Proof
Induct_on ‘sl’ >> simp[specsl_def]
QED


        

Theorem specsl_sbounds:
 ∀sl n t i.
 (∀n s st. (n,s) ∈ sfv st ∧ MEM st sl ⇒
           sbounds s = {}) ∧
 tbounds t = {} ∧ n < LENGTH sl ⇒
 sbounds (EL n (specsl i t sl)) =
 sbounds (EL n sl) DELETE (n + i)
Proof
 Induct_on ‘sl’ >> rw[] >>
 Cases_on ‘n < LENGTH sl’ >> simp[specsl_def] (* 2 *)
 >- (Cases_on ‘n’ >> simp[] >- 
    metis_tac[trpl_eliminate] >>
    simp[arithmeticTheory.ADD1] >> gs[] >>
    ‘i + (n' + 1) = (i + 1) + n'’ by simp[] >>
    pop_assum SUBST_ALL_TAC >> first_x_assum irule >>
    ‘n' < LENGTH sl’ by simp[] >> metis_tac[]) >>
 ‘n = LENGTH sl’ by simp[] >>
 Cases_on ‘n’ >> gs[] >- metis_tac[trpl_eliminate] >>
 rename [‘SUC n = LENGTH sl’] >>
 gs[arithmeticTheory.ADD1] >>
 pop_assum (assume_tac o GSYM) >> simp[] >>
 ‘i + (n + 1) = (i + 1) + n’ by simp[] >>
 pop_assum SUBST_ALL_TAC >> first_x_assum irule >>
 ‘n < LENGTH sl’ by simp[] >> metis_tac[]
QED 
        


Theorem specsl_sbounds_SUBSET:
 ∀sl n t i.
 (∀n s st. (n,s) ∈ sfv st ∧ MEM st sl ⇒
           sbounds s = {}) ∧ tbounds t = {} ∧ n < LENGTH sl ⇒
 sbounds (EL n sl) ⊆
 sbounds (EL n (specsl i t sl)) ∪ {n + i}
Proof
 rw[] >> drule_all_then assume_tac specsl_sbounds >>
 gs[SUBSET_DEF,EXTENSION]
QED 



Theorem wfabsap_ok_abs:
 ∀tl sl. wfabsap Σf sl tl ⇒ ok_abs sl
Proof
 Induct_on ‘tl’ >> gs[wfabsap_def] (* 2 *)
 >- (Cases_on ‘sl’ >> simp[wfabsap_def,ok_abs_def]) >>
 ‘∀sl h. wfabsap Σf sl (h::tl) ⇒ ok_abs sl’
  suffices_by metis_tac[] >>
 Induct_on ‘sl’ >> simp[wfabsap_def] >> rw[] >>
 rename [‘wfabsap Σf (specsl 0 t sl) tl’] >>
 first_x_assum $ drule_then assume_tac >>
 ‘sbounds (sort_of t) = {}’ by metis_tac[wft_no_bound] >>
 rw[ok_abs_def] >>
 Cases_on ‘n’ >> gs[] >>
 rename [‘n < LENGTH sl’] >>
 irule SUBSET_TRANS >>
 irule_at Any specsl_sbounds_SUBSET >>
 simp[] >>
 qexistsl [‘t’,‘0’] >> simp[] >>
 ‘sbounds (EL n (specsl 0 t sl)) ⊆ count (SUC n)’
   by (gs[ok_abs_def,LENGTH_specsl] >>
      first_x_assum $ drule_then assume_tac >>
      irule SUBSET_TRANS >> first_x_assum $ irule_at Any >>
      rw[SUBSET_DEF]) >> simp[] >>
 metis_tac[wft_no_bound]
QED 
                

Theorem wfabsap_wft:
  ∀tl sl t. wfabsap Σf sl tl ∧ MEM t tl ⇒ wft Σf t
Proof
Induct_on ‘tl’ >> simp[wfabsap_def] >>
Cases_on ‘sl’ >> simp[wfabsap_def] >> metis_tac[]
QED




 
Theorem sinst_srpl1:
(∀tm i t σ.
(∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = {}) ∧
(∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = {}) ⇒
tinst σ (trpl i t tm) =
trpl i (tinst σ t) (tinst σ tm)) ∧
(∀st i t σ.
(∀n s. (n,s) ∈ sfv st ⇒ sbounds s = {}) ∧
(∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = {}) ⇒
sinst σ (srpl i t st) =
srpl i (tinst σ t) (sinst σ st))
Proof
ho_match_mp_tac better_tm_induction >>
rw[] (* 4 *)
>- (Cases_on ‘(s0,st) ∈ FDOM σ ’ >> simp[trpl_def] >>
    rw[Once EQ_SYM_EQ] >>
   irule $ cj 1 trpl_id >>
   first_x_assum $ drule_then assume_tac >> gs[])
>- (rw[trpl_def,tinst_def] (* 2 *)
   >- (first_x_assum irule >> simp[] >>
      gs[SUBSET_DEF] >> metis_tac[]) >>
   rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
   first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[])
>- rw[trpl_def,tinst_def] >>
rw[trpl_def,tinst_def] >>
rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
first_x_assum irule >> simp[] >>
gs[SUBSET_DEF] >> metis_tac[]
QED

        
Theorem sinst_srpl:
(∀tm i t σ.
(∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = {}) ∧
(∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = {}) ∧
tfv tm ⊆ FDOM σ ⇒
tinst σ (trpl i t tm) =
trpl i (tinst σ t) (tinst σ tm)) ∧
(∀st i t σ.
(∀n s. (n,s) ∈ sfv st ⇒ sbounds s = {}) ∧
(∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = {}) ∧
sfv st ⊆ FDOM σ ⇒
sinst σ (srpl i t st) =
srpl i (tinst σ t) (sinst σ st))
Proof
ho_match_mp_tac better_tm_induction >>
rw[] (* 4 *)
>- (‘(trpl i t (Var s0 st)) = (Var s0 st)’
    by (irule $ cj 1 trpl_id >> gs[tbounds_def]) >>
   simp[] >>
   rw[Once EQ_SYM_EQ] >>
   irule $ cj 1 trpl_id >>
   first_x_assum $ drule_then assume_tac >> gs[])
>- (rw[trpl_def,tinst_def] (* 2 *)
   >- (first_x_assum irule >> simp[] >>
      gs[SUBSET_DEF] >> metis_tac[]) >>
   rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
   first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[])
>- rw[trpl_def,tinst_def] >>
rw[trpl_def,tinst_def] >>
rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
first_x_assum irule >> simp[] >>
gs[SUBSET_DEF] >> metis_tac[]
QED
        

Theorem ok_abs_HD:
ok_abs (s:: sl) ⇒ sbounds s = {}
Proof
rw[ok_abs_def] >>
first_x_assum (qspecl_then [‘0’] assume_tac) >> gs[]
QED



Theorem MAP_sinst_specsl1:
∀sl i t σ.
(∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = ∅) ∧
(∀n s st. MEM st sl ∧ (n,s) ∈ sfv st ⇒ sbounds s = ∅) ⇒
MAP (sinst σ) (specsl i t sl) =
specsl i (tinst σ t) (MAP (sinst σ) sl)
Proof
Induct_on ‘sl’ >> simp[specsl_def] >>
rw[] (* 2 *)
>- (irule $ cj 2 sinst_srpl1 >>
   gs[no_bound_def] >> gs[SUBSET_DEF] >>
   metis_tac[]) >>
first_x_assum irule >> gs[SUBSET_DEF] >> metis_tac[]
QED

        
Theorem MAP_sinst_specsl:
∀sl i t σ.
(∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = ∅) ∧
(∀n s st. MEM st sl ∧ (n,s) ∈ sfv st ⇒ sbounds s = ∅) ∧
BIGUNION {sfv s | MEM s sl} ⊆ FDOM σ  ⇒
MAP (sinst σ) (specsl i t sl) =
specsl i (tinst σ t) (MAP (sinst σ) sl)
Proof
Induct_on ‘sl’ >> simp[specsl_def] >>
rw[] (* 2 *)
>- (irule $ cj 2 sinst_srpl >>
   gs[no_bound_def] >> gs[SUBSET_DEF] >>
   metis_tac[]) >>
first_x_assum irule >> gs[SUBSET_DEF] >> metis_tac[]
QED


   
Theorem specsl_EL:
∀sl t i n. n < LENGTH sl ⇒
 EL n (specsl i t sl) = srpl (i + n) t (EL n sl)
Proof
Induct_on ‘sl’ >> rw[specsl_def] >>
Cases_on ‘n’ >> gs[arithmeticTheory.ADD1] 
QED


 

Theorem tfv_trpl:
 (∀t i new. i ∈ tbounds t ∧
            (∀n0 s0. (n0,s0) ∈ tfv t ⇒ sbounds s0 = ∅) ⇒
           tfv (trpl i new t) = tfv new ∪ tfv t) ∧
 (∀s i new. i ∈ sbounds s ∧
            (∀n0 s0. (n0,s0) ∈ sfv s ⇒ sbounds s0 = ∅) ⇒
           sfv (srpl i new s) = tfv new ∪ sfv s)
Proof
 ho_match_mp_tac better_tm_induction >>
 simp[tbounds_def,trpl_def,tfv_thm,MEM_MAP] >>
 rw[] (* 4 *)
 >- (‘sbounds s = ∅’ by metis_tac[] >>
     gs[GSYM MEMBER_NOT_EMPTY])
 >- (gs[PULL_EXISTS] >>
    ‘BIGUNION {tfv t | (∃a. t = trpl i new a ∧ MEM a l)} =   tfv new ∪ BIGUNION {tfv t | MEM t l}’
     by (rw[Once EXTENSION,PULL_EXISTS] >>
        rw[EQ_IMP_THM] (* 3 *)
        >- (Cases_on ‘i ∈ tbounds a'’ (* 2 *)
           >- (‘tfv (trpl i new a') = tfv new ∪ tfv a'’
                by (first_x_assum irule >> metis_tac[]) >>
              gs[] >> metis_tac[]) >>
           ‘ (trpl i new a') = a'’ by metis_tac[trpl_id] >>
           metis_tac[])
        >- (qexists ‘a’ >> simp[] >>
           ‘tfv (trpl i new a) = tfv new ∪ tfv a ’
             by metis_tac[] >>
           gs[]) >>
        qexists ‘t’ >>
        simp[] >>
        Cases_on ‘i ∈ tbounds t’ (* 2 *)
        >- (‘tfv (trpl i new t) = tfv new ∪ tfv t’
            by metis_tac[] >>
           simp[]) >>
        ‘(trpl i new t) = t’ by metis_tac[trpl_id] >>
        simp[]) >> 
    Cases_on ‘i∈ sbounds s’ (* 2 *)
    >- (‘sfv (srpl i new s) = tfv new ∪ sfv s’
         by (first_x_assum irule >> metis_tac[]) >>
        simp[] >>
        rw[] >> simp[] >>
        rw[Once EXTENSION] >> metis_tac[]) >>
    ‘(srpl i new s) = s’ by metis_tac[trpl_id] >>
    simp[UNION_ASSOC])
>- (Cases_on ‘∃a. MEM a l ∧ i ∈ tbounds a’ (* 2 *)
   >- (‘BIGUNION {tfv t | (∃a. t = trpl i new a ∧ MEM a l)} =   tfv new ∪ BIGUNION {tfv t | MEM t l}’
     by (rw[Once EXTENSION,PULL_EXISTS] >>
        rw[EQ_IMP_THM] (* 3 *)
        >- (Cases_on ‘i ∈ tbounds a'’ (* 2 *)
           >- (‘tfv (trpl i new a') = tfv new ∪ tfv a'’
                by (first_x_assum irule >> metis_tac[]) >>
              gs[] >> metis_tac[]) >>
           ‘ (trpl i new a') = a'’ by metis_tac[trpl_id] >>
           metis_tac[])
        >- (qexists ‘a’ >> simp[] >>
           ‘tfv (trpl i new a) = tfv new ∪ tfv a ’
             by metis_tac[] >>
           gs[]) >>
        qexists ‘t’ >>
        simp[] >>
        Cases_on ‘i ∈ tbounds t’ (* 2 *)
        >- (‘tfv (trpl i new t) = tfv new ∪ tfv t’
            by metis_tac[] >>
           simp[]) >>
        ‘(trpl i new t) = t’ by metis_tac[trpl_id] >>
        simp[]) >>
        simp[] >> ‘sfv (srpl i new s) = tfv new ∪ sfv s’
         by (first_x_assum irule >> metis_tac[]) >>
        simp[] >> rw[EXTENSION] >> metis_tac[]) >>
    ‘∀a. MEM a l ⇒ i ∉ tbounds a’ by metis_tac[] >>
    ‘BIGUNION {tfv t | (∃a. t = trpl i new a ∧ MEM a l)} =
     BIGUNION {tfv t | MEM t l}’
    by (AP_TERM_TAC >> rw[Once EXTENSION] >>
       rw[EQ_IMP_THM] (* 2 *)
       >- (qexists ‘a’ >> metis_tac[trpl_id]) >>
       qexists ‘t’ >> simp[] >>
       qexists ‘t’ >> metis_tac[trpl_id]) >> simp[] >>
     ‘sfv (srpl i new s) = tfv new ∪ sfv s’
      by  metis_tac[] >>
     simp[Once EXTENSION] >> metis_tac[]) >>
rw[Once EXTENSION,PULL_EXISTS] >>
        rw[EQ_IMP_THM] (* 3 *)
        >- (Cases_on ‘i ∈ tbounds a'’ (* 2 *)
           >- (‘tfv (trpl i new a') = tfv new ∪ tfv a'’
                by (first_x_assum irule >> metis_tac[]) >>
              gs[] >> metis_tac[]) >>
           ‘ (trpl i new a') = a'’ by metis_tac[trpl_id] >>
           metis_tac[])
        >- (qexists ‘a’ >> simp[] >>
           ‘tfv (trpl i new a) = tfv new ∪ tfv a ’
             by metis_tac[] >>
           gs[]) >>
        qexists ‘t’ >>
        simp[] >>
        Cases_on ‘i ∈ tbounds t’ (* 2 *)
        >- (‘tfv (trpl i new t) = tfv new ∪ tfv t’
            by metis_tac[] >>
           simp[]) >>
        ‘(trpl i new t) = t’ by metis_tac[trpl_id] >>
        simp[]
QED         


Theorem tfv_trpl_SUBSET:
 (∀t i new. 
            (∀n0 s0. (n0,s0) ∈ tfv t ⇒ sbounds s0 = ∅) ⇒
            tfv t ⊆ tfv (trpl i new t)) ∧
 (∀s i new. 
            (∀n0 s0. (n0,s0) ∈ sfv s ⇒ sbounds s0 = ∅) ⇒
           sfv s ⊆ sfv (srpl i new s))
Proof
 rw[] (* 2 *)
 >- (Cases_on ‘i ∈ tbounds t’ 
    >- (drule_all_then assume_tac $ cj 1 tfv_trpl >>
    simp[]) >>
    ‘(trpl i new t)= t’  by metis_tac[trpl_id] >>
    simp[]) >>
 Cases_on ‘i ∈ sbounds s’ (* 2 *)
 >- (drule_all_then assume_tac $ cj 2 tfv_trpl >>
     simp[]) >>
 ‘(srpl i new s)= s’  by metis_tac[trpl_id] >>
 simp[]     
QED



Theorem tfv_trpl_SUBSET1:
 (∀t i new. 
            tfv t ⊆ tfv (trpl i new t)) ∧
 (∀s i new. 
           sfv s ⊆ sfv (srpl i new s))
Proof
 ho_match_mp_tac better_tm_induction >> gs[tfv_thm,trpl_def,MEM_MAP] >>
 rw[] (* 3 *)
 >- (rw[SUBSET_DEF,PULL_EXISTS] >>
    first_x_assum $ drule_all_then assume_tac >> gs[SUBSET_DEF] >> metis_tac[])
 >- gs[SUBSET_DEF] >>
 rw[SUBSET_DEF] >> first_x_assum $ drule_then assume_tac >>
 gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[]    
QED
        
Theorem wfabsap_sfv_SUBSET:
  ∀tl sl.
    wfabsap Σf sl tl ⇒
    BIGUNION {sfv s | MEM s sl} ⊆ BIGUNION {tfv t | MEM t tl}
Proof
 Induct_on ‘tl’ >> Cases_on ‘sl’ >> simp[wfabsap_def] >>
 rw[] >> first_x_assum $ drule_then assume_tac >>
 rename [‘wfabsap Σf (specsl 0 t sl) tl’] >>
 rw[SUBSET_DEF] (* 2 *)
 >- (gs[PULL_EXISTS] >> qexists ‘t’ >>
    gs[] >> Cases_on ‘x’ >> irule sfv_tfv >>
    simp[] >> CCONTR_TAC >> gs[is_bound_alt,wft_def]) >>
 gs[PULL_EXISTS] >> rename [‘x ∈ sfv s’] >>
 gs[SUBSET_DEF,PULL_EXISTS] >>
 ‘∃t'. x ∈ tfv t' ∧ MEM t' tl’ suffices_by metis_tac[] >>
 first_x_assum irule >> 
 gs[MEM_EL,LENGTH_specsl] >>
 qexists ‘srpl n t s’ >>
 pop_assum (assume_tac o GSYM) >> gs[] >>
 ‘sfv s ⊆ sfv (srpl n t s)’
  by (irule $ cj 2 tfv_trpl_SUBSET >>
     metis_tac[]) >>
 rw[] (* 2 *)
 >- gs[SUBSET_DEF]>>
 qexists ‘n’ >> simp[specsl_EL]
QED


        

Theorem wfabsap_sfv_tfv:
∀tl sl. wfabsap Σ sl tl ⇒ ∀n. n < LENGTH sl ⇒ sfv (EL n sl) ⊆ tfv (EL n tl)
Proof
Induct_on ‘tl’ >> Cases_on ‘sl’ >> simp[wfabsap_def] >>
rw[] >>
first_x_assum $ drule_then assume_tac >>
gs[LENGTH_specsl] >>
Cases_on ‘n’ >> gs[] (* 2 *)
>- (Cases_on ‘h'’ (* 3 *)
   >> gs[sort_of_def] >> metis_tac[wft_def]) >>
first_x_assum $ drule_then assume_tac >>
drule_then assume_tac specsl_EL >> gs[] >>
irule SUBSET_TRANS >>
first_x_assum $ irule_at Any >>
simp[tfv_trpl_SUBSET1]
QED



Theorem wfabsap_sfv_sort_of:
∀tl sl. wfabsap Σ sl tl ⇒ ∀n. n < LENGTH sl ⇒ sfv (EL n sl) ⊆ sfv (sort_of (EL n tl))
Proof
Induct_on ‘tl’ >> Cases_on ‘sl’ >> simp[wfabsap_def] >>
rw[] >>
first_x_assum $ drule_then assume_tac >>
gs[LENGTH_specsl] >>
Cases_on ‘n’ >> gs[]  >>
first_x_assum $ drule_then assume_tac >>
drule_then assume_tac specsl_EL >> gs[] >>
irule SUBSET_TRANS >>
first_x_assum $ irule_at Any >>
simp[tfv_trpl_SUBSET1]
QED             
(*        
Theorem tbounds_tinst:
(∀)
*)

Theorem wfabsap_sinst_tinst:
(∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {{(n,s)} ∪ sfv s | MEM (n,s) (fsymin Σf fsym)}) ⇒
∀tl sl.
 cstt σ ∧ BIGUNION {tfv t | MEM t tl} ⊆ FDOM σ ∧
 wfcod Σf σ ∧ wfabsap Σf sl tl ⇒
 wfabsap Σf (MAP (sinst σ) sl) (MAP (tinst σ) tl)
Proof
strip_tac >> 
Induct_on ‘tl’
>- (Cases_on ‘sl’ >> simp[wfabsap_def]) >>
rw[] >> gs[] >>
drule_then assume_tac wfabsap_sfv_sbounds >>
Cases_on ‘sl’ >> gs[wfabsap_def,MEM_MAP] >>
reverse (rw[]) (* 5 *)
>- (drule_then assume_tac wfcod_no_bound >>
   last_x_assum
    (qspecl_then [‘(specsl 0 h t)’] assume_tac)>>
   gs[] >>
   ‘BIGUNION {tfv t | MEM t tl} ⊆ FDOM σ’
    by (gs[SUBSET_DEF] >> metis_tac[]) >>
   gs[] >>
   ‘MAP (sinst σ) (specsl 0 h t) =
   specsl 0 (tinst σ h) (MAP (sinst σ) t) ’
    by (irule MAP_sinst_specsl >> rw[] (* 3 *)
       >- metis_tac[]
       >- gs[no_bound_def] >>
       irule SUBSET_TRANS >>
       first_x_assum $ irule_at Any >>
       rev_drule wfabsap_sfv_SUBSET >>
       rw[] >>
       irule SUBSET_TRANS >>
       first_x_assum $ irule_at Any >>
       rw[SUBSET_DEF] >>
       gs[MEM_EL,LENGTH_specsl,PULL_EXISTS] >> 
       drule_then assume_tac specsl_EL >> simp[] >>
       qexists ‘n’ >> simp[] >>
       ‘sfv (EL n t) ⊆ sfv (srpl n h (EL n t))’
        suffices_by metis_tac[SUBSET_DEF] >>
       irule $ cj 2 tfv_trpl_SUBSET >> metis_tac[]) >>
    gs[])
>- (irule $ cj 2 wft_tinst >>
   simp[] >>
   irule SUBSET_TRANS >>
   first_x_assum $ irule_at Any >>
   irule SUBSET_TRANS >>
   qexists ‘tfv h’ >> rw[SUBSET_DEF] (* 2 *)
   >- (Cases_on ‘x’ >> irule sfv_tfv >>
   simp[] >> CCONTR_TAC >> gs[is_bound_alt,wft_def]) >>
   metis_tac[]) 
>- (irule $ GSYM cstt_sort_of_tinst >> simp[] >>
   drule_then assume_tac wfcod_no_bound >> simp[] >>
   metis_tac[wft_no_bound])
>- (irule $ cj 1 wft_tinst >>
   simp[] >> gs[SUBSET_DEF]) >> 
rename [‘wfabsap Σf (specsl 0 t sl) tl’] >>
drule_then assume_tac $ cj 2 tfv_sinst >>
drule_then assume_tac wfcod_no_bound >> gs[] >> 
‘sfv y ⊆ FDOM σ’
  by (irule SUBSET_TRANS >>
     first_x_assum $ irule_at Any >>
     rev_drule wfabsap_sfv_SUBSET >>
     rw[] >>
     ‘sfv y ⊆ BIGUNION {tfv t | MEM t tl}’
      suffices_by (gs[SUBSET_DEF] >> metis_tac[]) >>
     irule SUBSET_TRANS >>
       first_x_assum $ irule_at Any >>
       rw[SUBSET_DEF] >>
       gs[MEM_EL,LENGTH_specsl,PULL_EXISTS] >> 
       drule_then assume_tac specsl_EL >> simp[] >>
       qexists ‘n’ >> simp[] >>
       ‘sfv (EL n sl) ⊆ sfv (srpl n t (EL n sl))’
        suffices_by metis_tac[SUBSET_DEF] >>
       irule $ cj 2 tfv_trpl_SUBSET >> metis_tac[]) >>
first_x_assum (qspecl_then [‘y’] assume_tac) >>
gs[] >> rename [‘(n,st) ∈ sfv y’]  >>
CCONTR_TAC >> gs[GSYM MEMBER_NOT_EMPTY] >>
gs[GSYM Bound_tsubtm] >>
‘x ∈ tbounds (σ ' (n,st))’ suffices_by
 (gs[no_bound_def] >>
 ‘tbounds (σ ' (n,st)) = ∅’
  suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
 first_x_assum irule >> gs[SUBSET_DEF]) >>
gs[GSYM Bound_tsubtm] >>
irule $ cj 1 tfv_tsubtm_closed >> metis_tac[]
QED

       


Definition slbounds_def:
slbounds [] = {} ∧
slbounds (h :: t) =
sbounds h ∪ (IMAGE PRE (slbounds t DELETE 0))
End


Theorem tsubst_eq_tinst1:
(∀n s new. tsubst (n,s) new = tinst (TO_FMAP [((n,s),new)])) ∧
∀n s new. ssubst (n,s) new = sinst (TO_FMAP [((n,s),new)])
Proof
rw[FUN_EQ_THM,tsubst_eq_tinst]
QED    
        

Definition abssl_def:
 abssl (n,s) i [] = [] ∧
 abssl (n,s) i (h::t) =
 sabs (n,s) i h:: abssl (n,s) (i + 1) t
End


Theorem trpl_tabs:
(∀tm i new n s.
(i ∉ tbounds tm) ∧
(∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
(∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = {}) ⇒
trpl i new (tabs (n,s) i tm) = tsubst (n,s) new tm) ∧
(∀st i new n s.
(i ∉ sbounds st) ∧
(∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
(∀n s. (n,s) ∈ sfv st ⇒ sbounds s = {}) ⇒
srpl i new (sabs (n,s) i st) = ssubst (n,s) new st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,trpl_def,tsubst_def,SF ETA_ss,PULL_EXISTS,tabs_def,MAP_EQ_f,MAP_MAP_o] >> rw[]
(* 4 *)
>- (Cases_on ‘n = s0 ∧ s = st’ >>
   simp[trpl_def]>> metis_tac[tsubst_id])
>> metis_tac[]
QED


Definition slabs_def:
 slabs (n,s) i [] = [] ∧
 slabs (n,s) i (h::t) =
 ssubst (n,s) (Bound i) h:: slabs (n,s) (i + 1) t
End 
        

Theorem slabs_abssl:
∀l i. (∀n s st. MEM st l ∧ (n,s) ∈ sfv st ⇒ (n0,s0) ∉ sfv s) ⇒
slabs (n0,s0) i l = abssl (n0,s0) i l
Proof
Induct_on ‘l’ >> simp[tfv_thm,slabs_def,abssl_def] >> rw[] (* 2 *)
>- metis_tac[tabs_tsubst] >>
metis_tac[]
QED
        
Theorem specsl_abssl:
∀l i n0 s0 new.
(∀m. m < LENGTH l ⇒ i + m ∉ sbounds (EL m l)) ∧
(∀n s st. MEM st l ∧ (n,s) ∈ sfv st ⇒ sbounds s = {}) ∧
(∀n s st. MEM st l ∧ (n,s) ∈ sfv st ⇒ (n0,s0) ∉ sfv s) ⇒
specsl i new (abssl (n0,s0) i l) =
MAP (ssubst (n0,s0) new) l
Proof
Induct_on ‘l’ >> simp[abssl_def,specsl_def] >>
rw[] (* 2 *)
>- (irule $ cj 2 trpl_tabs >> rw[]
    >- metis_tac[] >- metis_tac[] >>
    ‘0 < SUC (LENGTH l)’ by simp[] >>
    first_x_assum $ drule_then assume_tac >> gs[]) >>
first_x_assum irule >> rw[] >- metis_tac[] >- metis_tac[] >>
first_x_assum (qspecl_then [‘m + 1’] assume_tac) >> gs[] >>
gs[GSYM arithmeticTheory.ADD1]
QED



Theorem slbounds_sbounds:
∀l i. i ∉ slbounds l ⇔
      (∀m. m < LENGTH l ⇒ i + m ∉ sbounds (EL m l))
Proof
Induct_on ‘l’ >> simp[slbounds_def] >> rw[EQ_IMP_THM] (* 3 *)
>- (Cases_on ‘m’ >> gs[] >>
first_x_assum (qspecl_then [‘SUC i’] assume_tac) >> gs[]>>
first_x_assum $ drule_then assume_tac >>
gs[arithmeticTheory.ADD1])
>- (first_x_assum (qspecl_then [‘0’] assume_tac) >> gs[]) >>
Cases_on ‘x’ >> gs[] (* 2 *) >>
rw[] >> first_x_assum (qspecl_then [‘SUC m’] assume_tac) >>
gs[] >>
‘n + SUC m = m + SUC n’ by simp[] >> gs[]
QED        



Theorem tinst_tsubst:
(∀tm i σ.
cstt σ ∧ no_bound σ ∧
tfv tm DELETE (n,s) ⊆ FDOM σ ∧
(∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
(∀n1 s1. (n1,s1) ∈ FDOM σ ⇒ (nn,sinst σ s) ∉ tfv (σ ' (n1,s1))) ∧
(nn,sinst σ s) ∉ tfv tm ⇒
tinst σ (tsubst (n,s) (Bound i) tm) =
tsubst (nn,sinst σ s) (Bound i)
(tinst (σ |+ ((n,s),Var nn (sinst σ s))) tm)) ∧
(∀st i σ.
cstt σ ∧ no_bound σ ∧
sfv st DELETE (n,s) ⊆ FDOM σ ∧
(∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
(∀n1 s1. (n1,s1) ∈ FDOM σ ⇒ (nn,sinst σ s) ∉ tfv (σ ' (n1,s1))) ∧
(nn,sinst σ s) ∉ sfv st  ⇒
sinst σ (ssubst (n,s) (Bound i) st) =
ssubst (nn,sinst σ s) (Bound i)
(sinst (σ |+ ((n,s),Var nn (sinst σ s))) st))
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 4 *)
>- (Cases_on ‘(n,s) = (s0,st)’ >> gs[] (* 2 *)
    >- simp[tinst_def,tsubst_def] >>
    ‘tsubst (n,s) (Bound i) (Var s0 st) = (Var s0 st)’
      by (simp[tsubst_def] >>
          ‘¬(n = s0 ∧ s = st)’ by metis_tac[] >> simp[] >>
          irule $ cj 2 tsubst_id >> metis_tac[]) >>
    simp[] >> Cases_on ‘(s0,st) ∉ FDOM σ’ >> simp[] (* 2 *)
    >- (‘(Var s0 (sinst (σ |+ ((n,s),Var nn (sinst σ s))) st)) =
        Var s0 (sinst σ st)’
         by (simp[] >> irule $ cj 2 fmap_fv_inst_eq_alt >>
            ‘(n,s) ∉ sfv st’ by metis_tac[] >>
            simp[FDOM_FUPDATE] >> gs[SUBSET_DEF]) >>
       simp[] >> rw[Once EQ_SYM_EQ] >>
       irule $ cj 1 tsubst_id >>
       ‘(Var s0 (sinst σ st)) = tinst σ (Var s0 st)’
        by simp[] >>
       pop_assum SUBST_ALL_TAC >>
       CCONTR_TAC >>
       qspecl_then [‘Var s0 st’,‘σ’] assume_tac $ cj 1 tfv_sinst >>
       simp[Excl "tfv_thm",Excl "tinst_def"] >>
       ‘cstt σ ∧ tfv (Var s0 st) ⊆ FDOM σ ∧ no_bound σ’
        by gs[SUBSET_DEF]  >>
       first_x_assum $ drule_all_then assume_tac >> simp[] >>
       rw[] >>
       Cases_on ‘(n0,st0) = (s0,st)’ >> gs[SUBSET_DEF]) >>
   gs[FAPPLY_FUPDATE_THM] >>
   ‘¬(s0 = n ∧ st = s )’ by metis_tac[] >> simp[] >>
    rw[Once EQ_SYM_EQ] >>
    irule $ cj 1 tsubst_id >>
    metis_tac[]) 
>- (rw[tsubst_def,tinst_def] (* 2 *)
   >- (first_x_assum irule >> simp[] >>
      gs[SUBSET_DEF] >> metis_tac[]) >>
   rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
   first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[])
>- rw[tinst_def,tsubst_def] >>
rw[tsubst_def,tinst_def] >>
rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
first_x_assum irule >> simp[] >>
gs[SUBSET_DEF] >> metis_tac[]
QED







        
Theorem tinst_tabs:
(∀tm i σ.
cstt σ ∧ no_bound σ ∧
tfv tm DELETE (n,s) ⊆ FDOM σ ∧
(∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
(∀n1 s1. (n1,s1) ∈ FDOM σ ⇒ (nn,sinst σ s) ∉ tfv (σ ' (n1,s1))) ∧
(nn,sinst σ s) ∉ tfv tm ⇒
tinst σ (tabs (n,s) i tm) =
tabs (nn,sinst σ s) i
(tinst (σ |+ ((n,s),Var nn (sinst σ s))) tm)) ∧
(∀st i σ.
cstt σ ∧ no_bound σ ∧
sfv st DELETE (n,s) ⊆ FDOM σ ∧
(∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
(∀n1 s1. (n1,s1) ∈ FDOM σ ⇒ (nn,sinst σ s) ∉ tfv (σ ' (n1,s1))) ∧
(nn,sinst σ s) ∉ sfv st  ⇒
sinst σ (sabs (n,s) i st) =
sabs (nn,sinst σ s) i
(sinst (σ |+ ((n,s),Var nn (sinst σ s))) st))
Proof
ho_match_mp_tac better_tm_induction >> rw[] (* 4 *)
>- (Cases_on ‘(n,s) = (s0,st)’ >> gs[] (* 2 *)
    >- simp[tinst_def,tabs_def] >>
    ‘tabs (n,s) i (Var s0 st) = (Var s0 st)’
      by (simp[tabs_def] >>
          ‘¬(n = s0 ∧ s = st)’ by metis_tac[] >> simp[] >>
          irule $ cj 2 tabs_id >> metis_tac[]) >>
    simp[] >> Cases_on ‘(s0,st) ∉ FDOM σ’ >> simp[] (* 2 *)
    >- (‘(Var s0 (sinst (σ |+ ((n,s),Var nn (sinst σ s))) st)) =
        Var s0 (sinst σ st)’
         by (simp[] >> irule $ cj 2 fmap_fv_inst_eq_alt >>
            ‘(n,s) ∉ sfv st’ by metis_tac[] >>
            simp[FDOM_FUPDATE] >> gs[SUBSET_DEF]) >>
       simp[] >> rw[Once EQ_SYM_EQ] >>
       irule $ cj 1 tabs_id >>
       ‘(Var s0 (sinst σ st)) = tinst σ (Var s0 st)’
        by simp[] >>
       pop_assum SUBST_ALL_TAC >>
       CCONTR_TAC >>
       qspecl_then [‘Var s0 st’,‘σ’] assume_tac $ cj 1 tfv_sinst >>
       simp[Excl "tfv_thm",Excl "tinst_def"] >>
       ‘cstt σ ∧ tfv (Var s0 st) ⊆ FDOM σ ∧ no_bound σ’
        by gs[SUBSET_DEF]  >>
       first_x_assum $ drule_all_then assume_tac >> simp[] >>
       rw[] >>
       Cases_on ‘(n0,st0) = (s0,st)’ >> gs[SUBSET_DEF]) >>
   gs[FAPPLY_FUPDATE_THM] >>
   ‘¬(s0 = n ∧ st = s )’ by metis_tac[] >> simp[] >>
    rw[Once EQ_SYM_EQ] >>
    irule $ cj 1 tabs_id >>
    metis_tac[]) 
>- (rw[tabs_def,tinst_def] (* 2 *)
   >- (first_x_assum irule >> simp[] >>
      gs[SUBSET_DEF] >> metis_tac[]) >>
   rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
   first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[])
>- rw[tabs_def,tsubst_def] >>
rw[tabs_def,tinst_def] >>
rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
first_x_assum irule >> simp[] >>
gs[SUBSET_DEF] >> metis_tac[]
QED        


           
Theorem MAP_sinst_abssl:
 ∀l i σ nn an ast.
 BIGUNION {sfv s | MEM s l} ∪ sfv ast DELETE (an,ast) ⊆ FDOM σ ∧
 (an,ast) ∉ FDOM σ ∧
 (∀x s. x ∈ BIGUNION {sfv s | MEM s l} ∪ sfv ast ∧ x ≠ (an,ast) ⇒
   (nn,s) ∉ tfv (σ ' x)) ∧
 (∀n1 s1. (n1,s1) ∈ BIGUNION {sfv s | MEM s l} ⇒ (an,ast) ∉ sfv s1) ⇒
 abssl (nn,sinst σ ast) i
          (MAP (sinst (σ |+ ((an,ast),Var nn (sinst σ ast)))) l) =
        MAP (sinst σ) (abssl (an,ast) i l)
Proof
Induct_on ‘l’ >> simp[abssl_def] >> rw[] (* 2 *)
>- (irule sabs_sinst >>
   gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[]) >>
first_x_assum irule   >> simp[] >>
gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[]
QED




Definition cvmap_def:
cvmap s = FUN_FMAP (λ(n,s). Var n s) s
End

(*extend vmap*)        
Definition evmap_def:
evmap σ s = σ ⊌ cvmap s
End          


Theorem cstt_cvmap:
FINITE s ⇒ cstt (cvmap s)
Proof
rw[cstt_def,cvmap_def,FUN_FMAP_DEF,sort_of_def]  >>
rw[Once EQ_SYM_EQ] >>
irule $ cj 2 tinst_vmap_id >>
rw[FUN_FMAP_DEF]
QED

Theorem FDOM_cvmap:
FINITE vs ⇒ FDOM (cvmap vs) = vs
Proof
rw[cvmap_def,FUN_FMAP_DEF]
QED

Theorem FDOM_evmap:
FINITE vs ⇒ FDOM (evmap σ vs) = FDOM σ ∪ vs
Proof
rw[evmap_def] >>
drule_then assume_tac FDOM_cvmap >>
gs[]
QED



Theorem FAPPLY_cvmap:
FINITE vs ∧ (n,s) ∈ vs ⇒ (cvmap vs) ' (n,s) = Var n s
Proof
rw[cvmap_def,FUN_FMAP_DEF]
QED

Theorem cstt_FUPDATE:
FINITE vs ∧
(∀n s. (n,s) ∈ vs ⇒ (en,es) ∉ sfv s) ∧
¬(is_bound t) ∧
sort_of t = es ⇒
cstt (cvmap vs |+ ((en,es),t))
Proof 
 rw[cstt_def,FAPPLY_FUPDATE_THM] (* 2 *)
 >- (rw[Once EQ_SYM_EQ] >>
    irule $ cj 2 tinst_vmap_id >>
    rw[FDOM_FUPDATE,FDOM_cvmap] (* 2 *)
    >- metis_tac[tm_tree_WF] >>
    ‘(n,s) ≠ (en,sort_of t)’ by metis_tac[tm_tree_WF] >>
    rw[FAPPLY_cvmap,FAPPLY_FUPDATE_THM]) >>
 Cases_on ‘n = en ∧ s = sort_of t’ >> simp[] (* 2 *)
 >- (rw[Once EQ_SYM_EQ] >>
    irule $ cj 2 tinst_vmap_id >>
    rw[FDOM_FUPDATE,FDOM_cvmap] (* 2 *)
    >- metis_tac[tm_tree_WF] >>
    ‘(n,s) ≠ (en,sort_of t)’ by metis_tac[tm_tree_WF] >>
    rw[FAPPLY_cvmap,FAPPLY_FUPDATE_THM]) >>
 gs[FDOM_cvmap] >>
 rw[FAPPLY_cvmap,sort_of_def] >> 
 rw[Once EQ_SYM_EQ] >>
 irule $ cj 2 tinst_vmap_id >>
 rw[FDOM_FUPDATE,FDOM_cvmap] (* 2 *)
 >- metis_tac[tm_tree_WF] >>
 ‘(n',s') ≠ (en,sort_of t)’ by metis_tac[tm_tree_WF] >>
 rw[FAPPLY_cvmap,FAPPLY_FUPDATE_THM]
QED 


Theorem slbounds_specsl_DELETE:
  ∀sl i t.
  (∀n s st. MEM st sl ∧ (n,s) ∈ sfv st ⇒ sbounds s = ∅)  ∧
  tbounds t = {} ⇒
  slbounds (specsl i t sl) =
  slbounds sl DELETE i
Proof
Induct_on ‘sl’ >- simp[slbounds_def,specsl_def] >>
rw[] >> first_x_assum $ drule_at_then Any assume_tac>>
‘slbounds (specsl (i+1) t sl) = slbounds sl DELETE (i+1)’
 by metis_tac[] >> 
simp[slbounds_def,specsl_def] >>
‘IMAGE PRE (slbounds sl DELETE (i + 1) DELETE 0) =
 IMAGE PRE (slbounds sl DELETE 0) DELETE i’
  by
  (rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
   >- metis_tac[] >- (Cases_on ‘x'’ >> gs[]) >>
   qexists ‘x'’ >> simp[]) >>
simp[] >>
drule_at_then Any assume_tac $ cj 2 trpl_eliminate >>
‘sbounds (srpl i t h) = sbounds h DELETE i’ by metis_tac[] >>
simp[] >> rw[EXTENSION] >> metis_tac[]
QED



Theorem wfabsap_slbounds:
  ∀tl sl. wfabsap Σf sl tl ⇒ slbounds sl = ∅
Proof
Induct_on ‘tl’ (* 2 *)
>- (Cases_on ‘sl’ >> simp[slbounds_def,wfabsap_def]) >>
Cases_on ‘sl’ >> simp[slbounds_def,wfabsap_def] >>
rw[] (* 2 *)
>- metis_tac[wft_no_bound] >>
rename [‘(specsl 0 t sl)’] >>
first_x_assum $ drule_then assume_tac >>
metis_tac[slbounds_specsl_DELETE,wft_no_bound] 
QED


Theorem tsubst_tbounds_in:
  (∀tm n s i.
     (n,s) ∈ tfv tm ⇒
     i ∈ tbounds (tsubst (n,s) (Bound i) tm)) ∧
  (∀st n s i.
     (n,s) ∈ sfv st ⇒
     i ∈ sbounds (ssubst (n,s) (Bound i) st))
Proof     
ho_match_mp_tac better_tm_induction >>
simp[tbounds_thm,tsubst_def,tfv_thm,MEM_MAP,PULL_EXISTS] >>
rw[] (* 5 *)
>- rw[tbounds_thm]
>- (Cases_on ‘n = s0 ∧ s = st’ >> simp[tbounds_thm])
>> metis_tac[]
QED        


Theorem tbounds_tsubst_SUBSET:
  (∀tm n s i.
     (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ sbounds s1 = {}) ⇒ 
     tbounds tm ⊆ tbounds (tsubst (n,s) (Bound i) tm)) ∧
  (∀st n s i.
     (∀n1 s1. (n1,s1) ∈ sfv st ⇒ sbounds s1 = {}) ⇒ 
     sbounds st ⊆ sbounds (ssubst (n,s) (Bound i) st))
Proof
ho_match_mp_tac better_tm_induction >>
rw[tbounds_thm,tsubst_def] (* 3 *)
>> (gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[])
QED 


Theorem tbounds_tabs_SUBSET:
  (∀tm n s i.
     (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ sbounds s1 = {}) ⇒ 
     tbounds tm ⊆ tbounds (tabs (n,s) i tm)) ∧
  (∀st n s i.
     (∀n1 s1. (n1,s1) ∈ sfv st ⇒ sbounds s1 = {}) ⇒ 
     sbounds st ⊆ sbounds (sabs (n,s) i st))
Proof
ho_match_mp_tac better_tm_induction >>
rw[tbounds_thm,tabs_def] (* 3 *)
>> (gs[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >> metis_tac[])
QED     

Theorem tbounds_tsubst:
 (∀tm n s i.
 (n,s) ∈ tfv tm ∧
 (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ sbounds s1 = {}) ⇒
 tbounds (tsubst (n,s) (Bound i) tm) =
 {i} ∪ tbounds tm) ∧
 (∀st n s i.
 (n,s) ∈ sfv st ∧
 (∀n1 s1. (n1,s1) ∈ sfv st ⇒ sbounds s1 = {}) ⇒
 sbounds (ssubst (n,s) (Bound i) st) =
 {i} ∪ sbounds st)              
Proof             
 ho_match_mp_tac better_tm_induction >>
 simp[tbounds_thm,tsubst_def,tfv_thm,PULL_EXISTS,
      MEM_MAP] >>
 rw[] (* 5 *)
 >- rw[tbounds_thm]
 >- (Cases_on ‘n = s0 ∧ s = st’ >> simp[tbounds_thm] >>
    ‘sbounds st = {}’ by metis_tac[] >> gs[] >>
    first_x_assum irule >> metis_tac[])
 >- (‘BIGUNION {tbounds t | (∃a. t = tsubst (n,s) (Bound i) a ∧ MEM a l)} =
     {i} ∪ BIGUNION {tbounds t | MEM t l}’
     by
     (rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
      >- (Cases_on ‘(n,s) ∈ tfv a’ (* 2 *)
          >- (‘tbounds (tsubst (n,s) (Bound i) a) =
              {i} ∪ tbounds a’
               by (first_x_assum irule >> metis_tac[]) >>
              pop_assum SUBST_ALL_TAC >> gs[UNION_DEF] >>
              metis_tac[]) >>
          ‘tsubst (n,s) (Bound i) a = a’ suffices_by
            metis_tac[] >>
          irule $ cj 1 tsubst_id >> metis_tac[])
      >- (gs[PULL_EXISTS,EXTENSION] >> metis_tac[]) >>
      gs[PULL_EXISTS] >> qexists ‘t'’ >> simp[] >>
      ‘tbounds t' ⊆ tbounds (tsubst (n,s) (Bound i) t')’
       suffices_by metis_tac[SUBSET_DEF] >>
      irule $ cj 1 tbounds_tsubst_SUBSET >>
      metis_tac[]) >>
     simp[] >>
     Cases_on ‘(n,s) ∈ sfv st’ (* 2 *)
     >- (gs[EXTENSION] >> metis_tac[]) >>
     gs[EXTENSION] >> metis_tac[tsubst_id])
>- (‘sbounds (ssubst (n,s) (Bound i) st) =
    {i} ∪ sbounds st’
     by metis_tac[] >> simp[] >>
   Cases_on ‘∃t1. MEM t1 l ∧ (n,s) ∈ tfv t1’ (* 2 *) 
   >- (gs[] >>
       ‘BIGUNION {tbounds t | (∃a. t = tsubst (n,s) (Bound i) a ∧ MEM a l)} =
        {i} ∪ BIGUNION {tbounds t | MEM t l}’
     by
     (rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
      >- (Cases_on ‘(n,s) ∈ tfv a’ (* 2 *)
          >- (‘tbounds (tsubst (n,s) (Bound i) a) =
              {i} ∪ tbounds a’
               by (first_x_assum irule >> metis_tac[]) >>
              pop_assum SUBST_ALL_TAC >> gs[UNION_DEF] >>
              metis_tac[]) >>
          ‘tsubst (n,s) (Bound i) a = a’ suffices_by
            metis_tac[] >>
          irule $ cj 1 tsubst_id >> metis_tac[])
      >- (gs[PULL_EXISTS,EXTENSION] >> metis_tac[]) >>
      gs[PULL_EXISTS] >> qexists ‘t’ >> simp[] >>
      ‘tbounds t ⊆ tbounds (tsubst (n,s) (Bound i) t)’
       suffices_by metis_tac[SUBSET_DEF] >>
      irule $ cj 1 tbounds_tsubst_SUBSET >>
      metis_tac[])  >>
      gs[EXTENSION] >> metis_tac[]) >>
   ‘BIGUNION {tbounds t | (∃a. t = tsubst (n,s) (Bound i) a ∧ MEM a l)} = BIGUNION {tbounds t | MEM t l}’
    by (AP_TERM_TAC >> rw[Once EXTENSION,EQ_IMP_THM] >>
       metis_tac[tsubst_id]) >>
   gs[EXTENSION] >> metis_tac[]) >>
(rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
      >- (Cases_on ‘(n,s) ∈ tfv a’ (* 2 *)
          >- (‘tbounds (tsubst (n,s) (Bound i) a) =
              {i} ∪ tbounds a’
               by (first_x_assum irule >> metis_tac[]) >>
              pop_assum SUBST_ALL_TAC >> gs[UNION_DEF] >>
              metis_tac[]) >>
          ‘tsubst (n,s) (Bound i) a = a’ suffices_by
            metis_tac[] >>
          irule $ cj 1 tsubst_id >> metis_tac[])
      >- (gs[PULL_EXISTS,EXTENSION] >> metis_tac[]) >>
      gs[PULL_EXISTS] >> qexists ‘t'’ >> simp[] >>
      ‘tbounds t' ⊆ tbounds (tsubst (n,s) (Bound i) t')’
       suffices_by metis_tac[SUBSET_DEF] >>
      irule $ cj 1 tbounds_tsubst_SUBSET >>
      metis_tac[])
QED                  


Theorem IN_slbounds:
∀l i. i ∈ slbounds l ⇔ ∃m. m < LENGTH l ∧ i + m ∈ sbounds (EL m l)
Proof
metis_tac[slbounds_sbounds]
QED 



Theorem slabs_EL:
∀l n s m i. m < LENGTH l ⇒
            EL m (slabs (n,s) i l) = ssubst (n,s) (Bound (i + m)) (EL m l)
Proof
Induct_on ‘l’ >> simp[tsubtm_def,slabs_def] >> rw[] >>
Cases_on ‘m’ >> simp[slabs_def,arithmeticTheory.ADD1]
QED

Theorem LENGTH_slabs:
∀l n s i. LENGTH (slabs (n,s) i l) = LENGTH l
Proof
Induct_on ‘l’ >> simp[slabs_def]
QED

        

Theorem tabs_tbounds_in:
  (∀tm n s i.
     (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
     (n,s) ∈ tfv tm ⇒
     i ∈ tbounds (tabs (n,s) i tm)) ∧
  (∀st n s i.
     (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
     (n,s) ∈ sfv st ⇒
     i ∈ sbounds (sabs (n,s) i st))
Proof     
ho_match_mp_tac better_tm_induction >>
simp[tbounds_thm,tabs_def,tfv_thm,MEM_MAP,PULL_EXISTS] >>
rw[] (* 5 *)
>- rw[tbounds_thm]
>- (Cases_on ‘n = s0 ∧ s = st’ >> simp[tbounds_thm] >>
   metis_tac[])
>> metis_tac[]
QED        


Theorem abssl_EL:
∀l n s m i. m < LENGTH l ⇒
            EL m (abssl (n,s) i l) =
            sabs (n,s) (i + m) (EL m l)
Proof
Induct_on ‘l’ >> simp[tabs_def,abssl_def] >> rw[] >>
Cases_on ‘m’ >> simp[abssl_def,arithmeticTheory.ADD1]
QED 


Theorem tbounds_tabs:
 (∀tm n s i.
 (n,s) ∈ tfv tm ∧
 (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ∧
 (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ sbounds s1 = {}) ⇒
 tbounds (tabs (n,s) i tm) =
 {i} ∪ tbounds tm) ∧
 (∀st n s i.
 (n,s) ∈ sfv st ∧
 (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
 (∀n1 s1. (n1,s1) ∈ sfv st ⇒ sbounds s1 = {}) ⇒
 sbounds (sabs (n,s) i st) =
 {i} ∪ sbounds st)              
Proof
rw[] (* 2 *)
>> metis_tac[tbounds_tsubst,tabs_tsubst]
QED                  

    

Theorem LENGTH_abssl:
∀l n s i. LENGTH (abssl (n,s) i l) = LENGTH l
Proof
Induct_on ‘l’ >> simp[abssl_def]
QED

Theorem slbounds_abssl:
 ∀n s m i l.
 m < LENGTH l ∧ (n,s) ∈ sfv (EL m l) ∧
 (∀n1 s1 st. MEM st l ∧ (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ∧
 (∀n1 s1. (n1,s1) ∈ BIGUNION {sfv s0 | MEM s0 l} ⇒
          sbounds s1 = {}) ⇒
 slbounds (abssl (n,s) i l) = {i} ∪ slbounds l
Proof
 Induct_on ‘l’ >> simp[PULL_EXISTS] >> rw[EXTENSION] >>
 rw[IN_slbounds,LENGTH_abssl] >> rw[EQ_IMP_THM] (* 3 *)
 >- (Cases_on ‘m'’ >> gs[abssl_def] (* 2 *)
    >- (Cases_on ‘(n,s) ∈ sfv h’ (* 2 *)
        >- (‘sbounds (sabs (n,s) i h) = {i} ∪ sbounds h’
              by (irule $ cj 2 tbounds_tabs >>
                  gs[] >> rw[] (* 3 *) >>
                  metis_tac[MEMBER_NOT_EMPTY,EXTENSION]) >>
            pop_assum SUBST_ALL_TAC >> gs[] >>
            disj2_tac >> qexists ‘0’ >> simp[]) >>
        ‘(sabs (n,s) i h) = h’
          by metis_tac[tabs_id]>>
        gs[] >> disj2_tac>> qexists ‘0’ >> simp[]) >>
     drule_then assume_tac abssl_EL >> gs[] >>
    Cases_on ‘(n,s) ∈ sfv (EL n' l)’ (* 2 *)
    >- (‘sbounds (sabs (n,s) (i + (n' + 1)) (EL n' l)) = {(i + (n' + 1))} ∪ sbounds (EL n' l)’
        by (irule $ cj 2 tbounds_tabs >>
           metis_tac[MEMBER_NOT_EMPTY,MEM_EL]) >>
       pop_assum SUBST_ALL_TAC >>
       gs[] >> disj2_tac >>
       qexists ‘SUC n'’ >> simp[]) >>
    ‘(sabs (n,s) (i + (n' + 1)) (EL n' l)) =
     EL n' l’ by metis_tac[tabs_id] >>
    pop_assum SUBST_ALL_TAC >> disj2_tac >>
    qexists ‘SUC n'’ >> simp[])
 >- (qexists ‘m’ >> simp[] >>
    ‘m < LENGTH (h :: l)’ by simp[] >>
    drule_then assume_tac abssl_EL >>
    simp[] >>
    irule $ cj 2 tabs_tbounds_in >> simp[] >>
    ‘(EL m (h :: l)) = h ∨ MEM (EL m (h :: l)) l’
     suffices_by metis_tac[] >>
     ‘MEM (EL m (h :: l)) (h :: l)’ suffices_by simp[] >>
     metis_tac[MEM_EL]) >>
 qexists ‘m'’ >> simp[] >> rw[abssl_EL] >>
 ‘sbounds (EL m' (h::l)) ⊆ sbounds (sabs (n,s) (i + m') (EL m' (h::l)))’ suffices_by metis_tac[SUBSET_DEF] >>
 irule $ cj 2 tbounds_tabs_SUBSET >>
 ‘m' < LENGTH (h :: l)’ by simp[] >>
 rw[EXTENSION] >>
 first_x_assum irule >> qexistsl [‘n1’,‘(EL m' (h::l))’] >>
 simp[] >> Cases_on ‘m'’ >> simp[] >> gs[] >>
 metis_tac[MEM_EL]
QED


Theorem slbounds_slabs:
 ∀n s m i l.
 m < LENGTH l ∧ (n,s) ∈ sfv (EL m l) ∧
 (∀n1 s1. (n1,s1) ∈ BIGUNION {sfv s0 | MEM s0 l} ⇒
          sbounds s1 = {}) ⇒
 slbounds (slabs (n,s) i l) = {i} ∪ slbounds l
Proof
 Induct_on ‘l’ >> simp[PULL_EXISTS] >> rw[EXTENSION] >>
 rw[IN_slbounds,LENGTH_slabs] >> rw[EQ_IMP_THM] (* 3 *)
 >- (Cases_on ‘m'’ >> gs[slabs_def] (* 2 *)
    >- (Cases_on ‘(n,s) ∈ sfv h’ (* 2 *)
        >- (‘sbounds (ssubst (n,s) (Bound i) h) = {i} ∪ sbounds h’
              by (irule $ cj 2 tbounds_tsubst >>
                  gs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
            pop_assum SUBST_ALL_TAC >> gs[] >>
            disj2_tac >> qexists ‘0’ >> simp[]) >>
        ‘(ssubst (n,s) (Bound i) h) = h’
          by metis_tac[tsubst_id]>>
        gs[] >> disj2_tac>> qexists ‘0’ >> simp[]) >>
     drule_then assume_tac slabs_EL >> gs[] >>
    Cases_on ‘(n,s) ∈ sfv (EL n' l)’ (* 2 *)
    >- (‘sbounds (ssubst (n,s) (Bound (i + (n' + 1))) (EL n' l)) = {(i + (n' + 1))} ∪ sbounds (EL n' l)’
        by (irule $ cj 2 tbounds_tsubst >>
           metis_tac[MEMBER_NOT_EMPTY,MEM_EL]) >>
       pop_assum SUBST_ALL_TAC >>
       gs[] >> disj2_tac >>
       qexists ‘SUC n'’ >> simp[]) >>
    ‘(ssubst (n,s) (Bound (i + (n' + 1))) (EL n' l)) =
     EL n' l’ by metis_tac[tsubst_id] >>
    pop_assum SUBST_ALL_TAC >> disj2_tac >>
    qexists ‘SUC n'’ >> simp[])
 >- (qexists ‘m’ >> simp[] >>
    ‘m < LENGTH (h :: l)’ by simp[] >>
    drule_then assume_tac slabs_EL >>
    simp[] >>
    irule $ cj 2 tsubst_tbounds_in >> simp[]) >>
 qexists ‘m'’ >> simp[] >> rw[slabs_EL] >>
 ‘sbounds (EL m' (h::l)) ⊆ sbounds (ssubst (n,s) (Bound (i + m')) (EL m' (h::l)))’ suffices_by metis_tac[SUBSET_DEF] >>
 irule $ cj 2 tbounds_tsubst_SUBSET >>
 ‘m' < LENGTH (h :: l)’ by simp[] >>
 rw[EXTENSION] >>
 first_x_assum irule >> qexistsl [‘n1’,‘(EL m' (h::l))’] >>
 simp[] >> Cases_on ‘m'’ >> simp[] >> gs[] >>
 metis_tac[MEM_EL]
QED
        

Theorem BIGUNION_tbounds:
(∀n1 s1. (n1,s1) ∈ BIGUNION {tfv y | MEM y l0} ⇒ sbounds s1 = ∅) ∧
MEM y l0 ∧ (n,s) ∈ tfv y ⇒
BIGUNION {tbounds t | (∃y. t = tsubst (n,s) (Bound i) y ∧ MEM y l0)} =
        {i} ∪ BIGUNION {tbounds t | MEM t l0}
Proof
rw[] >> rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
>- (Cases_on ‘(n,s) ∈ tfv y'’ (* 2 *)
          >- (‘tbounds (tsubst (n,s) (Bound i) y') =
              {i} ∪ tbounds y'’
               by metis_tac[tbounds_tsubst] >> 
              pop_assum SUBST_ALL_TAC >> gs[UNION_DEF] >>
              metis_tac[]) >>
          ‘tsubst (n,s) (Bound i) y' = y'’ suffices_by
            metis_tac[] >>
          irule $ cj 1 tsubst_id >> metis_tac[])
>- (gs[PULL_EXISTS,Once EXTENSION] >>
    qexists ‘y’ >> metis_tac[tsubst_tbounds_in]) >>
gs[PULL_EXISTS] >> qexists ‘t’ >> simp[] >>
      ‘tbounds t ⊆ tbounds (tsubst (n,s) (Bound i) t)’
       suffices_by metis_tac[SUBSET_DEF] >>
      irule $ cj 1 tbounds_tsubst_SUBSET >>
      metis_tac[]
QED
Theorem BIGUNION_tbounds:
(∀n1 s1. (n1,s1) ∈ BIGUNION {tfv y | MEM y l0} ⇒ sbounds s1 = ∅) ∧
MEM y l0 ∧ (n,s) ∈ tfv y ⇒
BIGUNION {tbounds t | (∃y. t = tsubst (n,s) (Bound i) y ∧ MEM y l0)} =
        {i} ∪ BIGUNION {tbounds t | MEM t l0}
Proof
rw[] >> rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
>- (Cases_on ‘(n,s) ∈ tfv y'’ (* 2 *)
          >- (‘tbounds (tsubst (n,s) (Bound i) y') =
              {i} ∪ tbounds y'’
               by metis_tac[tbounds_tsubst] >> 
              pop_assum SUBST_ALL_TAC >> gs[UNION_DEF] >>
              metis_tac[]) >>
          ‘tsubst (n,s) (Bound i) y' = y'’ suffices_by
            metis_tac[] >>
          irule $ cj 1 tsubst_id >> metis_tac[])
>- (gs[PULL_EXISTS,Once EXTENSION] >>
    qexists ‘y’ >> metis_tac[tsubst_tbounds_in]) >>
gs[PULL_EXISTS] >> qexists ‘t’ >> simp[] >>
      ‘tbounds t ⊆ tbounds (tsubst (n,s) (Bound i) t)’
       suffices_by metis_tac[SUBSET_DEF] >>
      irule $ cj 1 tbounds_tsubst_SUBSET >>
      metis_tac[]
QED





Theorem BIGUNION_tbounds':
(∀n1 s1. (n1,s1) ∈ BIGUNION {tfv y | MEM y l0} ⇒ (n,s) ∉ sfv s1) ∧
(∀n1 s1. (n1,s1) ∈ BIGUNION {tfv y | MEM y l0} ⇒ sbounds s1 = ∅) ∧
MEM y l0 ∧ (n,s) ∈ tfv y ⇒
BIGUNION {tbounds t | (∃y. t = tabs (n,s) i y ∧ MEM y l0)} =
        {i} ∪ BIGUNION {tbounds t | MEM t l0}
Proof
rw[] >> rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
>- (Cases_on ‘(n,s) ∈ tfv y'’ (* 2 *)
          >- (‘tbounds (tabs (n,s) i y') =
              {i} ∪ tbounds y'’
               by metis_tac[tbounds_tabs] >> 
              pop_assum SUBST_ALL_TAC >> gs[UNION_DEF] >>
              metis_tac[]) >>
          ‘tabs (n,s) i y' = y'’ suffices_by
            metis_tac[] >>
          irule $ cj 1 tabs_id >> metis_tac[])
>- (gs[PULL_EXISTS,Once EXTENSION] >>
    qexists ‘y’ >> metis_tac[tabs_tbounds_in]) >>
gs[PULL_EXISTS] >> qexists ‘t’ >> simp[] >>
      ‘tbounds t ⊆ tbounds (tabs (n,s) i t)’
       suffices_by metis_tac[SUBSET_DEF] >>
      irule $ cj 1 tbounds_tabs_SUBSET >>
      metis_tac[]
QED
        
Theorem BIGUNION_tbounds:
(∀n1 s1. (n1,s1) ∈ BIGUNION {tfv y | MEM y l0} ⇒ sbounds s1 = ∅) ∧
MEM y l0 ∧ (n,s) ∈ tfv y ⇒
BIGUNION {tbounds t | (∃y. t = tsubst (n,s) (Bound i) y ∧ MEM y l0)} =
        {i} ∪ BIGUNION {tbounds t | MEM t l0}
Proof
rw[] >> rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
>- (Cases_on ‘(n,s) ∈ tfv y'’ (* 2 *)
          >- (‘tbounds (tsubst (n,s) (Bound i) y') =
              {i} ∪ tbounds y'’
               by metis_tac[tbounds_tsubst] >> 
              pop_assum SUBST_ALL_TAC >> gs[UNION_DEF] >>
              metis_tac[]) >>
          ‘tsubst (n,s) (Bound i) y' = y'’ suffices_by
            metis_tac[] >>
          irule $ cj 1 tsubst_id >> metis_tac[])
>- (gs[PULL_EXISTS,Once EXTENSION] >>
    qexists ‘y’ >> metis_tac[tsubst_tbounds_in]) >>
gs[PULL_EXISTS] >> qexists ‘t’ >> simp[] >>
      ‘tbounds t ⊆ tbounds (tsubst (n,s) (Bound i) t)’
       suffices_by metis_tac[SUBSET_DEF] >>
      irule $ cj 1 tbounds_tsubst_SUBSET >>
      metis_tac[]
QED
        


        


Theorem NOTIN_slbounds_abssl:
 (∀s1. MEM s1 l ⇒ (n,s) ∉ sfv s1) ⇒
 (abssl (n,s) i l) = l
Proof
 rw[]>> irule LIST_EQ >> rw[LENGTH_abssl] >>
 drule_then assume_tac abssl_EL >> simp[] >>
 irule $ cj 2 tabs_id >> metis_tac[MEM_EL]
QED


Theorem NOTIN_slbounds_slabs:
 (∀s1. MEM s1 l ⇒ (n,s) ∉ sfv s1) ⇒
 (slabs (n,s) i l) = l
Proof
 rw[]>> irule LIST_EQ >> rw[LENGTH_slabs] >>
 drule_then assume_tac slabs_EL >> simp[] >>
 irule $ cj 2 tsubst_id >> metis_tac[MEM_EL]
QED


Theorem wft_tsubtm:
(∀tm. wft Σf tm ⇒ ∀t0. t0 ∈ tsubtm tm ⇒ wft Σf t0) ∧
(∀st. wfs Σf st ⇒ ∀t0. t0 ∈ ssubtm st ⇒ wft Σf t0)
Proof
ho_match_mp_tac better_tm_induction >>
simp[tsubtm_def,wft_def,MEM_MAP] >> rw[] (* 6 *)
>- rw[wft_def]
>- metis_tac[]
>- rw[wft_def] 
>- metis_tac[]
>- metis_tac[] >>
gs[EVERY_MEM] >> metis_tac[]
QED



Theorem wft_wfs:
(∀tm. wft Σf tm ⇒ ∀n s. (n,s) ∈ tfv tm ⇒ wfs Σf s) ∧
(∀st. wfs Σf st ⇒ ∀n s. (n,s) ∈ sfv st ⇒ wfs Σf s)
Proof
rw[GSYM Var_tsubtm_tfv] (* 2 *)
>- (drule_all_then assume_tac $ cj 1 wft_tsubtm >>
   gs[wft_def]) >> 
drule_all_then assume_tac $ cj 2 wft_tsubtm >>
gs[wft_def]
QED        


Theorem wfabsap_wfs:
∀tl sl. wfabsap Σf sl tl ⇒
 ∀st n s. MEM st sl ∧ (n,s) ∈ sfv st ⇒ wfs Σf s
Proof 
Induct_on ‘tl’ >> simp[wfabsap_def] (* 2 *)
>- (Cases_on ‘sl’ >> simp[wfabsap_def]) >>
Cases_on ‘sl’ >> simp[wfabsap_def] >> rw[] (* 2 *)
>- metis_tac[wft_wfs]>>
last_x_assum $ drule_then assume_tac >>
drule_then assume_tac $ iffLR MEM_EL >> gs[] >>
drule_then assume_tac specsl_EL >>
first_x_assum (qspecl_then [‘EL n' (specsl 0 h' t)’] assume_tac) >> gs[] >>
‘sfv (EL n' t) ⊆ sfv (srpl n' h' (EL n' t))’
 by (irule $ cj 2 tfv_trpl_SUBSET >>
    metis_tac[MEM_EL]) >>
gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >>
first_x_assum irule >> rw[PULL_EXISTS] (* 2 *)
>- metis_tac[] >>
simp[MEM_EL,LENGTH_specsl] >>
qexists ‘n'’>> simp[]
QED

Theorem tinst_eq_cvmap:
(∀tm. (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,sort_of t) ∉ sfv s1) ⇒
   tinst (TO_FMAP [((n,sort_of t),t)]) tm =
   tinst (cvmap (tfv tm) |+ ((n,sort_of t),t)) tm) ∧
(∀st. (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,sort_of t) ∉ sfv s1) ⇒
   sinst (TO_FMAP [((n,sort_of t),t)]) st =
   sinst (cvmap (sfv st) |+ ((n,sort_of t),t)) st)   
Proof   
ho_match_mp_tac better_tm_induction >>
rw[tinst_def,FDOM_TO_FMAP,FDOM_cvmap] (* 4 *)
>- (Cases_on ‘(s0,st) = (n,sort_of t)’ >> simp[] (* 2 *)
   >- (‘¬(s0 = n ⇒ st ≠ sort_of t)’ by gs[] >>
      simp[] >> irule TO_FMAP_MEM >> simp[]) >>
   ‘s0 = n ⇒ st ≠ sort_of t’ by gs[] >> simp[] >> 
   rw[FAPPLY_FUPDATE_THM] >>
   simp[FAPPLY_cvmap] >> 
   ‘sinst (TO_FMAP [((n,sort_of t),t)]) st =
    sinst (cvmap (sfv st) |+ ((n,sort_of t),t)) st’
    by metis_tac[] >>
   simp[] >>
   irule $ cj 2 tinst_vmap_id >> rw[FDOM_cvmap] (* 2 *)
   >- metis_tac[] >>
   ‘(n',s) ≠ (n,sort_of t)’ by metis_tac[] >>
   simp[FAPPLY_FUPDATE_THM] >>
   irule FAPPLY_cvmap >> simp[])
>- (‘sinst (TO_FMAP [((n,sort_of t),t)]) st =
    sinst (cvmap (sfv st) |+ ((n,sort_of t),t)) st’
    by metis_tac[] >>
   simp[] >>
   irule $ cj 2 fmap_fv_inst_eq_alt >>
   simp[FDOM_cvmap,FDOM_FUPDATE] >>
   ‘FINITE (BIGUNION {tfv t | MEM t l} ∪ sfv st)’
    by (simp[] >> rw[PULL_EXISTS] >>
       ‘{tfv t | MEM t l} = IMAGE tfv {t | MEM t l}’
        by rw[EXTENSION] >> simp[]) >>
   simp[FDOM_cvmap] >>
   simp[SUBSET_DEF] >> rw[] >>
   Cases_on ‘x = (n,sort_of t)’ >>
   simp[FAPPLY_FUPDATE_THM] >>
   Cases_on ‘x’ >> 
   ‘(cvmap (sfv st)) ' (q,r) = Var q r ∧
    (cvmap (BIGUNION {tfv t | MEM t l} ∪ sfv st)) ' (q,r) =
    Var q r’
    suffices_by metis_tac[] >>
   rw[] (* 2 *)
   >- (irule FAPPLY_cvmap >> simp[]) >>
   irule FAPPLY_cvmap >> simp[])
>- (rw[MAP_EQ_f] >>
    ‘tinst (TO_FMAP [((n,sort_of t),t)]) a =
     tinst (cvmap (tfv a) |+ ((n,sort_of t),t)) a’
     by (first_x_assum irule >> metis_tac[]) >>
    simp[] >>
    irule $ cj 1 fmap_fv_inst_eq_alt >>
    simp[FDOM_cvmap,FDOM_FUPDATE] >> 
    ‘FINITE (BIGUNION {tfv t | MEM t l} ∪ sfv st)’
      by (simp[] >> rw[PULL_EXISTS] >>
       ‘{tfv t | MEM t l} = IMAGE tfv {t | MEM t l}’
        by rw[EXTENSION] >> simp[]) >>
    simp[FDOM_cvmap] >>
    simp[SUBSET_DEF] >> reverse (rw[]) (* 2 *)
    >- metis_tac[] >>
    Cases_on ‘x’ >> Cases_on ‘(n,sort_of t) = (q,r)’ >>
    simp[] >> simp[FAPPLY_FUPDATE_THM] >>
    simp[FAPPLY_cvmap] >> rw[Once EQ_SYM_EQ] >>
    irule FAPPLY_cvmap >> simp[] >> metis_tac[]) >>
rw[MAP_EQ_f] >>
    ‘tinst (TO_FMAP [((n,sort_of t),t)]) a =
     tinst (cvmap (tfv a) |+ ((n,sort_of t),t)) a’
     by (first_x_assum irule >> metis_tac[]) >>
    simp[] >>
    irule $ cj 1 fmap_fv_inst_eq_alt >>
    simp[FDOM_cvmap,FDOM_FUPDATE] >> 
    ‘FINITE (BIGUNION {tfv t | MEM t l})’
      by (simp[] >> rw[PULL_EXISTS] >>
       ‘{tfv t | MEM t l} = IMAGE tfv {t | MEM t l}’
        by rw[EXTENSION] >> simp[]) >>
    simp[FDOM_cvmap] >>
    simp[SUBSET_DEF] >> reverse (rw[]) (* 2 *)
    >- metis_tac[] >>
    Cases_on ‘x’ >> Cases_on ‘(n,sort_of t) = (q,r)’ >>
    simp[] >> simp[FAPPLY_FUPDATE_THM] >>
    simp[FAPPLY_cvmap] >> rw[Once EQ_SYM_EQ] >>
    irule FAPPLY_cvmap >> simp[] >> metis_tac[]
QED     










Definition tprpl_def:
  tprpl bmap (Var n s) = Var n s ∧
  tprpl bmap (Fn f s tl) = Fn f (sprpl bmap s)
  (MAP (tprpl bmap) tl)  ∧
  (tprpl bmap (Bound i) = if i ∈ FDOM bmap then bmap ' i else Bound i) ∧
  sprpl bmap (St n tl) = St n (MAP (tprpl bmap) tl)
Termination
WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,t) => term_size t
         | INR (_,st) => sort_size st)’   
End
              

Theorem FAPPLY_mk_bmap:
  n < LENGTH tl ⇒  mk_bmap tl ' n = EL n tl
Proof  
rw[mk_bmap_def,FUN_FMAP_DEF]
QED

Theorem FDOM_mk_bmap:
FDOM (mk_bmap tl) = count (LENGTH tl)
Proof
rw[mk_bmap_def,FUN_FMAP_DEF]
QED

    
Definition FMAP_MAP_DEF:
  FMAP_MAP f σ = FUN_FMAP (λx. f (σ ' x)) (FDOM σ)
End  


Theorem FAPPLY_FMAP_MAP:
∀σ f x. x ∈ FDOM σ ⇒ (FMAP_MAP f σ) ' x = f (σ ' x)
Proof
 rw[FMAP_MAP_DEF,FUN_FMAP_DEF]
QED
        
Theorem FDOM_FMAP_MAP:
FDOM (FMAP_MAP f σ) = FDOM σ
Proof
rw[FMAP_MAP_DEF]
QED



        
Theorem tprpl_FMAP_MAP_tabs:
(∀tm i bmap.
   (n,s) ∉ tfv tm  ⇒
   tprpl
   (FMAP_MAP (tabs (n,s) i) bmap) tm =
   tabs (n,s) i (tprpl bmap tm)) ∧
(∀st i bmap.
   (n,s) ∉ sfv st  ⇒
   sprpl (FMAP_MAP (tabs (n,s) i) bmap) st =
   sabs (n,s) i (sprpl bmap st))
Proof
ho_match_mp_tac better_tm_induction >>
simp[tbounds_def,tprpl_def,tabs_def,
     MAP_MAP_o,MAP_EQ_f,MEM_MAP] >> rw[] (* 7 *)
>- (‘¬(n = s0 ∧ s = st)’ by metis_tac[] >> simp[])
>- metis_tac[] 
>- gs[FAPPLY_FMAP_MAP,FDOM_FMAP_MAP,EL_MAP]
>- gs[FAPPLY_FMAP_MAP,FDOM_FMAP_MAP,EL_MAP]
>- gs[FAPPLY_FMAP_MAP,FDOM_FMAP_MAP,EL_MAP]
>- gs[FAPPLY_FMAP_MAP,FDOM_FMAP_MAP,EL_MAP,tabs_def] >>
metis_tac[]
QED
        

Definition slprpl_def:
  slprpl bmap [] = [] ∧
  slprpl bmap (h :: t) = sprpl bmap h ::
  slprpl (shift_bmap 1 bmap)  t
End


Theorem tprpl_FEMPTY:
(∀t. tprpl FEMPTY t = t) ∧
(∀s. sprpl FEMPTY s = s)
Proof
ho_match_mp_tac better_tm_induction >>
rw[tprpl_def,MAP_fix]
QED



Theorem shift_bmap_FEMPTY:
shift_bmap i FEMPTY = FEMPTY
Proof
rw[shift_bmap_def]
QED


Theorem slprpl_FEMPTY:
∀l. (slprpl FEMPTY) l = l
Proof
Induct_on ‘l’ >>
simp[slprpl_def,tprpl_FEMPTY,shift_bmap_FEMPTY]
QED                


Theorem tshift_0:
(∀t. tshift 0 t = t) ∧
(∀s. sshift 0 s = s)
Proof
ho_match_mp_tac better_tm_induction >>
simp[tshift_def,MAP_fix]
QED


Theorem shift_bmap_0:
shift_bmap 0 bmap = bmap
Proof
rw[shift_bmap_def,FUN_FMAP_DEF,fmap_EXT,IMAGE_DEF,
   tshift_0]
QED


Theorem FDOM_FINITE_lemma:
FINITE {f x | x ∈ FDOM fmap}
Proof
simp[] >>
‘{f x | x ∈ FDOM fmap} = IMAGE f (FDOM fmap)’
 by simp[EXTENSION] >> simp[]
QED


Theorem tshift_SUM:
(∀t. tshift a (tshift b t) = tshift (a + b) t) ∧
(∀s. sshift a (sshift b s) = sshift (a + b) s)
Proof
ho_match_mp_tac better_tm_induction >>
simp[tshift_def,MAP_MAP_o,MAP_EQ_f]
QED

        
Theorem shift_bmap_SUM:
  (shift_bmap a (shift_bmap b bmap)) = shift_bmap (a+b) bmap
Proof
  rw[shift_bmap_def,FUN_FMAP_DEF,fmap_EXT,IMAGE_DEF,
     FDOM_FINITE_lemma] (*2 *)
  >- (‘FINITE {b + x | x ∈ FDOM bmap} ∧
       FINITE {a + x | (∃x'. x = b + x' ∧ x' ∈ FDOM bmap)}’ by
        (‘{b + x | x ∈ FDOM bmap} =
         IMAGE (λx. b + x) (FDOM bmap) ∧
         {a + x | (∃x'. x = b + x' ∧ x' ∈ FDOM bmap)} = {a + (b + x') | x' ∈ FDOM bmap}’
         by (rw[EXTENSION] >> metis_tac[]) >>
         simp[] >>
         ‘{a + (b + x') | x' ∈ FDOM bmap} =
          IMAGE (λx. a + (b + x)) (FDOM bmap)’
         by (rw[EXTENSION] >> metis_tac[]) >>
      simp[]) >>
      rw[shift_bmap_def,FUN_FMAP_DEF,fmap_EXT,IMAGE_DEF,
         FDOM_FINITE_lemma] >>
      rw[EXTENSION] >> metis_tac[]) >>
  ‘FINITE {b + x | x ∈ FDOM bmap} ∧
       FINITE {a + x | (∃x'. x = b + x' ∧ x' ∈ FDOM bmap)}’ by
        (‘{b + x | x ∈ FDOM bmap} =
         IMAGE (λx. b + x) (FDOM bmap) ∧
         {a + x | (∃x'. x = b + x' ∧ x' ∈ FDOM bmap)} = {a + (b + x') | x' ∈ FDOM bmap}’
         by (rw[EXTENSION] >> metis_tac[]) >>
         simp[] >>
         ‘{a + (b + x') | x' ∈ FDOM bmap} =
          IMAGE (λx. a + (b + x)) (FDOM bmap)’
         by (rw[EXTENSION] >> metis_tac[]) >>
      simp[]) >>      
  ‘FINITE {b + x | x ∈ FDOM bmap} ∧
       FINITE {a + x | (∃x'. x = b + x' ∧ x' ∈ FDOM bmap)}’ by
        (‘{b + x | x ∈ FDOM bmap} =
         IMAGE (λx. b + x) (FDOM bmap) ∧
         {a + x | (∃x'. x = b + x' ∧ x' ∈ FDOM bmap)} = {a + (b + x') | x' ∈ FDOM bmap}’
         by (rw[EXTENSION] >> metis_tac[]) >>
         simp[] >>
         ‘{a + (b + x') | x' ∈ FDOM bmap} =
          IMAGE (λx. a + (b + x)) (FDOM bmap)’
         by (rw[EXTENSION] >> metis_tac[]) >>
      simp[]) >>
  ‘FINITE {a + (b + x') | x' ∈ FDOM bmap}’
   by (‘{a + (b + x') | x' ∈ FDOM bmap} =
          IMAGE (λx. a + (b + x)) (FDOM bmap)’
         by (rw[EXTENSION] >> metis_tac[]) >>
      simp[]) >>
  gs[shift_bmap_def,FUN_FMAP_DEF,fmap_EXT,IMAGE_DEF,
     FDOM_FINITE_lemma,tshift_SUM]
QED        


Theorem slprpl_EL:
∀l n bmap. n < LENGTH l ⇒
EL n (slprpl bmap l) = sprpl (shift_bmap n bmap) (EL n l)
Proof
Induct_on ‘l’ >> simp[slprpl_def] >> rw[] >>
Cases_on ‘n’ >> gs[shift_bmap_0,shift_bmap_SUM,arithmeticTheory.ADD1]
QED







Theorem tshift_tabs:
(∀tm m i. tshift m (tabs (n,s) i tm) =
        tabs (n,s) (i + m) (tshift m tm)) ∧
(∀st m i. sshift m (sabs (n,s) i st) =
        sabs (n,s) (i + m) (sshift m st))        
Proof
ho_match_mp_tac better_tm_induction >>
simp[tshift_def,tabs_def,MAP_MAP_o,MAP_EQ_f] >>
rw[] >> Cases_on ‘ n = s0 ∧ s = st ’ >>
simp[tshift_def,tabs_def,MAP_MAP_o,MAP_EQ_f]
QED
    
Theorem shift_bmap_FMAP_MAP_tabs:
    (shift_bmap m (FMAP_MAP (tabs (n,s) i) bmap)) =
    FMAP_MAP (tabs (n,s) (i+m)) (shift_bmap m bmap)
Proof
rw[fmap_EXT,shift_bmap_def,FDOM_FMAP_MAP,FAPPLY_FMAP_MAP] >>
‘FINITE (IMAGE ($+ m) (FDOM bmap))’
 by simp[] >> simp[FUN_FMAP_DEF] >>
rw[FAPPLY_FMAP_MAP,tshift_tabs]
QED


Theorem LENGTH_slprpl:
∀l bmap. LENGTH (slprpl bmap l) = LENGTH l
Proof
Induct_on ‘l’ >> rw[slprpl_def] 
QED


Theorem NOT_ok_abs:
∀l i n s st.
  MEM st l ∧ (n,s) ∈ sfv st ⇒
  ¬(ok_abs (slabs (n,s) i l))
Proof  
Induct_on ‘l’>> rw[ok_abs_def,LENGTH_slabs](* 2 *)
>- (qexists ‘0’>> gs[] >>
  ‘HD (slabs (n,s) i (h::l)) = EL 0 (slabs (n,s) i (h::l))’
   by simp[EL] >>
  pop_assum SUBST_ALL_TAC >>
  ‘0 < LENGTH (h :: l)’ by simp[] >>
  drule_all_then assume_tac slabs_EL >> simp[] >>
  drule_all_then assume_tac $ cj 2 tsubst_tbounds_in >>
  metis_tac[MEMBER_NOT_EMPTY]) >>
drule_then assume_tac $ iffLR MEM_EL>>
gs[] >>
qexists ‘SUC n'’   >> simp[] >>
‘SUC n' < LENGTH (h :: l)’ by simp[] >>
drule_then assume_tac slabs_EL >>
simp[] >>
‘i + SUC n' ∈
 sbounds (ssubst (n,s) (Bound (i + SUC n')) (EL n' l))’
 suffices_by (rw[SUBSET_DEF,count_def] >>
             qexists ‘i + SUC n'’ >> simp[]) >>
irule $ cj 2 tsubst_tbounds_in >> simp[]      
QED            



Theorem NOT_ok_abssl:
∀l i n s st.
  (∀n1 s1 s0. MEM s0 l ∧ (n1,s1) ∈ sfv s0 ⇒ (n,s) ∉ sfv s1) ∧
  MEM st l ∧ (n,s) ∈ sfv st ⇒
  ¬(ok_abs (abssl (n,s) i l))
Proof  
Induct_on ‘l’>> rw[ok_abs_def,LENGTH_abssl](* 2 *)
>- (qexists ‘0’>> gs[] >>
  ‘HD (abssl (n,s) i (h::l)) = EL 0 (abssl (n,s) i (h::l))’
   by simp[EL] >>
  pop_assum SUBST_ALL_TAC >>
  ‘0 < LENGTH (h :: l)’ by simp[] >>
  drule_all_then assume_tac abssl_EL >> simp[] >>
  ‘i ∈ sbounds (sabs (n,s) i h)’ by metis_tac[tabs_tbounds_in] >>
  metis_tac[MEMBER_NOT_EMPTY]) >>
drule_then assume_tac $ iffLR MEM_EL>>
gs[] >>
qexists ‘SUC n'’   >> simp[] >>
‘SUC n' < LENGTH (h :: l)’ by simp[] >>
drule_then assume_tac abssl_EL >>
simp[] >>
‘i + SUC n' ∈
 sbounds (sabs (n,s) (i + SUC n') (EL n' l))’
 suffices_by (rw[SUBSET_DEF,count_def] >>
             qexists ‘i + SUC n'’ >> simp[]) >>
irule $ cj 2 tabs_tbounds_in >>  metis_tac[]  
QED            
               


Theorem slabs_id:
∀l i n s.
  (∀st. MEM st l ⇒ (n,s) ∉ sfv st) ⇒
  slabs (n,s) i l = l
Proof
rw[] >> irule LIST_EQ >> simp[LENGTH_slabs] >>
rw[] >> drule_then assume_tac slabs_EL >>
simp[] >> irule $ cj 2 tsubst_id >>
metis_tac[MEM_EL]
QED





Theorem abssl_id:
∀l i n s.
  (∀st. MEM st l ⇒ (n,s) ∉ sfv st) ⇒
  abssl (n,s) i l = l
Proof
rw[] >> irule LIST_EQ >> simp[LENGTH_abssl] >>
rw[] >> drule_then assume_tac abssl_EL >>
simp[] >> irule $ cj 2 tabs_id >>
metis_tac[MEM_EL]
QED



Theorem ok_abs_abssl:
 (∀n1 s1 s0. MEM s0 l ∧ (n1,s1) ∈ sfv s0 ⇒ (n,s) ∉ sfv s1) ⇒ 
ok_abs (abssl (n,s) i l) ⇒ ok_abs l
Proof
rw[] >> metis_tac[abssl_id,NOT_ok_abssl]
QED








        


Theorem tfv_tprpl:
 (∀tm bmap.
 (∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = {}) ⇒
 tfv (tprpl bmap tm) = tfv tm ∪ BIGUNION {tfv (bmap ' i) | i|i ∈ FDOM bmap ∩ tbounds tm}) ∧
 (∀st bmap.
 (∀n s. (n,s) ∈ sfv st ⇒ sbounds s = {}) ⇒
 sfv (sprpl bmap st) = sfv st ∪ BIGUNION {tfv (bmap ' i) | i|i ∈ FDOM bmap ∩ sbounds st}) 
Proof 
ho_match_mp_tac better_tm_induction >>
simp[tfv_thm,tprpl_def,tbounds_def,MEM_MAP] >> rw[] (* 4 *)
>- (‘sfv (sprpl bmap st) =
   sfv st ∪ BIGUNION {tfv (bmap ' i) | i| i ∈ FDOM bmap ∧ i ∈ sbounds st}’ by metis_tac[]  >>
    simp[] >>
   ‘BIGUNION {tfv t | (∃a. t = tprpl bmap a ∧ MEM a l)} =
    BIGUNION {tfv (tprpl bmap a) | MEM a l}’
    by (rw[EXTENSION] >> metis_tac[]) >>
   simp[] >>
   ‘{tfv (tprpl bmap a) | MEM a l} =
    {tfv tm ∪
            BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∧ i ∈ tbounds tm} | MEM tm l}’
    by (rw[Once EXTENSION] >> rw[EQ_IMP_THM] (* 2 *)
       >- (qexists ‘a’ >> simp[] >>
          first_x_assum $ drule_then assume_tac >>
          ‘(∀n s. (n,s) ∈ tfv a ⇒ sbounds s = ∅)’
           by metis_tac[] >>
          first_x_assum $ drule_then assume_tac >>
          first_x_assum (qspecl_then [‘bmap’] assume_tac) >>
          rw[]) >>
       qexists ‘tm’ >>
       simp[] >>
       first_x_assum $ drule_then assume_tac >>
‘(∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅)’
  by metis_tac[] >>
first_x_assum $ drule_then assume_tac >> simp[]) >>
simp[] >> simp[PULL_EXISTS] >>
‘BIGUNION
          {tfv tm ∪
           BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∧ i ∈ tbounds tm} |
           MEM tm l} =
BIGUNION
          {tfv tm | MEM tm l}  ∪
BIGUNION {tfv (bmap ' i) | i | ∃tm.i ∈ FDOM bmap ∧ i ∈ tbounds tm ∧  MEM tm l}’
by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 4 *)
    >>  metis_tac[]) >>
simp[] >>
‘BIGUNION
          {tfv (bmap ' i) |
           i |
           i ∈ FDOM bmap ∧ ((∃a. i ∈ tbounds a ∧ MEM a l) ∨ i ∈ sbounds st)} =
 BIGUNION
          {tfv (bmap ' i) |
           i |
           (∃tm. i ∈ FDOM bmap ∧ i ∈ tbounds tm ∧ MEM tm l)}∪ BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∧ i ∈ sbounds st}’
by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 4 *) >>
    metis_tac[]) >>
simp[] >>
rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 4 *) >>
metis_tac[])
>- (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 4 *) >>
metis_tac[])
>- (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 4 *) >>
metis_tac[]) >>
 ‘BIGUNION {tfv t | (∃a. t = tprpl bmap a ∧ MEM a l)} =
    BIGUNION {tfv (tprpl bmap a) | MEM a l}’
    by (rw[EXTENSION] >> metis_tac[]) >>
   simp[] >>
simp[PULL_EXISTS] >>
simp[] >>
   ‘{tfv (tprpl bmap a) | MEM a l} =
    {tfv tm ∪
            BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∧ i ∈ tbounds tm} | MEM tm l}’
    by (rw[Once EXTENSION] >> rw[EQ_IMP_THM] (* 2 *)
       >- (qexists ‘a’ >> simp[] >>
          first_x_assum $ drule_then assume_tac >>
          ‘(∀n s. (n,s) ∈ tfv a ⇒ sbounds s = ∅)’
           by metis_tac[] >>
          first_x_assum $ drule_then assume_tac >>
          first_x_assum (qspecl_then [‘bmap’] assume_tac) >>
          rw[]) >>
       qexists ‘tm’ >>
       simp[] >>
       first_x_assum $ drule_then assume_tac >>
‘(∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = ∅)’
  by metis_tac[] >>
first_x_assum $ drule_then assume_tac >> simp[]) >>
simp[] >> simp[PULL_EXISTS] >>
‘BIGUNION
          {tfv tm ∪
           BIGUNION {tfv (bmap ' i) | i | i ∈ FDOM bmap ∧ i ∈ tbounds tm} |
           MEM tm l} =
BIGUNION
          {tfv tm | MEM tm l}  ∪
BIGUNION {tfv (bmap ' i) | i | ∃tm.i ∈ FDOM bmap ∧ i ∈ tbounds tm ∧  MEM tm l}’
by (rw[Once EXTENSION,EQ_IMP_THM,PULL_EXISTS] (* 4 *)
    >>  metis_tac[]) >>
simp[]
QED            


Theorem abssl_ok_abs:
∀l i n s.
 (∀n1 s1 s0. MEM s0 l ∧ (n1,s1) ∈ sfv s0 ⇒ (n,s) ∉ sfv s1) ⇒
  (ok_abs (abssl (n,s) i l) ⇔
  ok_abs l ∧ (∀st. MEM st l ⇒ (n,s) ∉ sfv st))
Proof  
 metis_tac[NOT_ok_abssl,ok_abs_abssl,abssl_id]
QED

                
Theorem mk_bmap_MAP:
  mk_bmap (MAP f l) = FMAP_MAP f (mk_bmap l)
Proof
rw[fmap_EXT,FDOM_mk_bmap,FDOM_FMAP_MAP,
   FAPPLY_mk_bmap,FAPPLY_FMAP_MAP,EL_MAP]
QED    
        
                  

Theorem FDOM_shift_bmap:
FDOM (shift_bmap i bmap) = IMAGE ($+i) (FDOM bmap)
Proof
rw[shift_bmap_def]
QED



Theorem FAPPLY_shift_bmap:
 x ∈ FDOM bmap ⇒
 (shift_bmap i bmap) ' (i + x) = tshift i (bmap ' x)
Proof
rw[shift_bmap_def,FUN_FMAP_DEF]
QED



            
Theorem tfv_tshift:
(∀t i. tfv (tshift i t) = tfv t) ∧
(∀s i. sfv (sshift i s) = sfv s)
Proof
ho_match_mp_tac better_tm_induction >>
simp[tfv_thm,tshift_def,MEM_MAP] >>  rw[] (* 2 *)
>> gs[EXTENSION] >> metis_tac[]
QED


Theorem tprpl_id:
(∀t bmap. tbounds t ∩ FDOM bmap = {} ⇒ tprpl bmap t = t) ∧
(∀s bmap. sbounds s ∩ FDOM bmap = {} ⇒ sprpl bmap s = s)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,tprpl_def,MAP_fix] >> rw[] (* 4 *)
>> (gs[EXTENSION] >> metis_tac[])
QED


Theorem EL_REVERSE1:
n < LENGTH l  ⇒
EL n (REVERSE l ⧺ [e]) = EL n (REVERSE l)
Proof
rw[EL_REVERSE] >>
‘n < LENGTH (e :: l)’ by simp[] >>
drule_then assume_tac EL_REVERSE >> gs[] >>
rw[prim_recTheory.PRE,arithmeticTheory.SUB ] >>
Cases_on ‘LENGTH l - n’ >> gs[]
QED



Theorem EL_REVERSE2:
EL (LENGTH l) (REVERSE l ⧺ [e]) = e
Proof
‘LENGTH l < LENGTH (e :: l)’ by simp[] >>
drule_then assume_tac EL_REVERSE >> gs[]
QED        

Theorem tprpl_mk_bmap_CONS:
(∀t tm tl. tbounds tm = {} ⇒
 tprpl (mk_bmap (REVERSE tl ⧺ [tm])) t =
 tprpl (mk_bmap (REVERSE tl)) (trpl (LENGTH tl) tm t)) ∧
(∀s tm tl. tbounds tm = {} ⇒
 sprpl (mk_bmap (REVERSE tl ⧺ [tm])) s =
 sprpl (mk_bmap (REVERSE tl)) (srpl (LENGTH tl) tm s)) 
Proof
ho_match_mp_tac better_tm_induction >>
rw[trpl_def,tprpl_def,MAP_EQ_f,FDOM_mk_bmap,MAP_MAP_o,
   FAPPLY_mk_bmap] >> gs[] (* 2 *)
>- (‘LENGTH tl < LENGTH (tm :: tl)’ by simp[] >>
    drule_then assume_tac EL_REVERSE >> gs[] >>
   rw[Once EQ_SYM_EQ] >> irule $ cj 1 tprpl_id >>
   simp[]) >>
‘n < LENGTH tl’ by simp[] >>
drule_then assume_tac EL_REVERSE1 >> simp[]
QED   

Theorem tabs_trpl:
(∀tm i n s. (n,s) ∉ tfv tm ⇒
tabs (n,s) i (trpl i (Var n s) tm) = tm) ∧
(∀st i n s. (n,s) ∉ sfv st ⇒
sabs (n,s) i (srpl i (Var n s) st) = st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,tabs_def,trpl_def,MAP_MAP_o,MAP_fix] >> rw[](*5 *)
>- (‘¬(n = s0 ∧ s = st)’ by metis_tac[] >>simp[])
>- metis_tac[]
>- rw[tabs_def]
>- rw[tabs_def] >> metis_tac[]
QED
      


Theorem abssl_specsl:
∀sl i n s.(∀st. MEM st sl ⇒ (n,s) ∉ sfv st) ⇒
abssl (n,s) i (specsl i (Var n s) sl) = sl         
Proof
Induct_on ‘sl’>> simp[specsl_def,abssl_def] >>
rw[] >> metis_tac[tabs_trpl]
QED      

Theorem wfabsap_LENGTH:
∀tl sl. wfabsap Σf sl tl ⇒ LENGTH sl = LENGTH tl
Proof
Induct_on ‘tl’ >> simp[wfabsap_def]  (* 2 *)
>- (Cases_on ‘sl’ >> simp[wfabsap_def]) >>
(Cases_on ‘sl’ >> simp[wfabsap_def]) >> rw[] >>
metis_tac[LENGTH_specsl]
QED


Theorem ill_formed_tabs_still_in:
(∀tm n s n0 s0. (n0,s0) ∈ tfv tm ∧ (n,s) ∈ sfv s0 ⇒
   (n,s) ∈ tfv (tabs (n,s) i tm)) ∧
(∀st n s n0 s0. (n0,s0) ∈ sfv st ∧ (n,s) ∈ sfv s0 ⇒
   (n,s) ∈ sfv (sabs (n,s) i st))
Proof   
ho_match_mp_tac better_tm_induction >> 
gs[tfv_thm,tabs_def,PULL_EXISTS,MEM_MAP] >> rw[] (* 5 *)
>- (Cases_on ‘n = n0 ∧ s = s0'’ >> simp[] >>
   metis_tac[tm_tree_WF])
>- (Cases_on ‘n = s0 ∧ s = st’ >> simp[] (* 2 *)
   >- metis_tac[tm_tree_WF,vsort_tfv_closed] >>
   metis_tac[vsort_tfv_closed])
>> metis_tac[]
QED

        

                       
val _ = export_theory();

