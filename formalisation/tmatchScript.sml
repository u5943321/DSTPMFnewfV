open HolKernel Parse boolLib bossLib;
open stringTheory pred_setTheory listTheory;
open finite_mapTheory;
val _ = new_theory "tmatch";


Datatype: term = Var string sort | Fn string sort (term list);
          sort = St string (term list)
End


Datatype:
  form = False
       | Pred string (term list)
       | IMP form form
       | FALL string sort form
       | fVar string ((string # sort) list) (term list)
End
  
Definition tfv_def:
  tfv (Var n s) = {(n,s)} ∪ sfv s ∧
  tfv (Fn n s tl) = BIGUNION (set (MAP tfv tl)) ∪ sfv s ∧
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
  sfv (St n tl) = BIGUNION {tfv t | MEM t tl}
Proof
  simp[tfv_def,PULL_EXISTS] >> simp[Once EXTENSION,PULL_EXISTS,MEM_MAP,LIST_TO_SET_MAP,IMAGE_DEF,EXTENSION]  
QED


Definition tinst_def[simp]:
  (tinst (σ:string # sort |-> term) (Var n s) =
   if (n,s) ∉ FDOM σ then Var n (sinst σ s)
   else σ ' (n,s)) ∧
  (tinst σ (Fn f s tl) =  Fn f (sinst σ s) (MAP (tinst σ) tl)) ∧
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
     
Definition tmatch_def:
  (tmatch (lcs:string # sort -> bool) (Var n s) ct (f:string # sort |-> term) =
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
   rw[] >> Cases_on ‘ct’ >> gs[sort_of_def]
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
          

        
(*closed means function term has sort with no extra variable than arguments*)

(*         
Definition tclosed_def:
  (tclosed (Var n s) ⇔ sclosed s) ∧
  (tclosed (Fn f s l) ⇔ sfv s ⊆ BIGUNION {tfv t | MEM t tl})∧
  (sclosed (St n tl) ⇔ 
           
  (wft Σf (Var n s) ⇔ wfs Σf s) ∧
  (wft Σf (Fn f s tl) ⇔
     wfs Σf s ∧
     sfv s ⊆ BIGUNION {tfv t | MEM t tl} ∧
     (∀t. MEM t tl ⇒ wft Σf t) ∧
     isfsym Σf f ∧
     IS_SOME
     (tlmatch {} (MAP (UNCURRY Var) (SND (Σf ' f))) tl FEMPTY) ∧
     sinst (THE (tlmatch {} (MAP (UNCURRY Var) (finput Σf f)) tl FEMPTY)) (foutput Σf f) = s) ∧
  (wfs Σf (St n tl) ⇔ EVERY (wft Σf) tl)
Termination
 WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,t) => term_size t
         | INR (_,st) => sort_size st)’ 
End
*)
           
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
  ho_match_mp_tac original_tm_induction >> rw[] (* 17 *)
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
     gs[SUBSET_DEF] >> metis_tac[]) (*9 remains*)   
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
  ho_match_mp_tac original_tm_induction >> rw[] (* 10 *)
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
 ho_match_mp_tac original_tm_induction >> rw[] (* 4 *)
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
  ho_match_mp_tac original_tm_induction >> rw[] (* 5 *)
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
     complete f ∧ cstt σ ∧
     (tfv t ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ tfv t ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     tmatch {} t (tinst σ t) f = SOME (FUNION f (DRESTRICT σ (tfv t)))) ∧
   (∀st f σ.
     complete f ∧ cstt σ ∧
     (sfv st ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩ sfv st ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     smatch {} st (sinst σ st) f =
     SOME (FUNION f (DRESTRICT σ (sfv st)))) ∧
   (∀l f σ.
     complete f ∧ cstt σ ∧
     (BIGUNION {tfv t | MEM t l} ⊆ FDOM σ) ∧
     (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ ∩
            BIGUNION {tfv t | MEM t l} ⇒ f ' (n,s) = σ ' (n,s)) ⇒
     tlmatch {} l (MAP (tinst σ) l) f =
     SOME (FUNION f (DRESTRICT σ
     (BIGUNION {tfv t | MEM t l}))))     
Proof
  ho_match_mp_tac original_tm_induction>> rw[] (* 5 *)
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

Theorem match_SOME_iff_inst:
  (∀t1 t2. IS_SOME (tmatch {} t1 t2 FEMPTY) ⇔
           ∃σ. cstt σ ∧ tfv t1 ⊆ FDOM σ ∧ t2 = tinst σ t1)
Proof
 rw[EQ_IMP_THM] (* 2 *)
 >- (Cases_on ‘tmatch ∅ t1 t2 FEMPTY’ >> gs[] >>
    qexists ‘x’ >>
    ‘cstt x’ by metis_tac[match_SOME_cstt,FEMPTY_complete,FEMPTY_cstt] >> simp[Once EQ_SYM_EQ] >>
    ‘tfv t1 ⊆ FDOM x’
    by
    metis_tac[tmatch_FEMPTY_property,SUBSET_ANTISYM_EQ]>>
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
           ∃σ. cstt σ ∧ tfv t1 = FDOM σ ∧ t2 = tinst σ t1)
Proof
 rw[EQ_IMP_THM] (* 2 *)
 >- (Cases_on ‘tmatch ∅ t1 t2 FEMPTY’ >> gs[] >>
    qexists ‘x’ >>
    ‘cstt x’ by metis_tac[match_SOME_cstt,FEMPTY_complete,FEMPTY_cstt] >> simp[Once EQ_SYM_EQ] >>
    ‘tfv t1 = FDOM x’
    by
    metis_tac[tmatch_FEMPTY_property]>>
    rw[] >> simp[Once EQ_SYM_EQ] >>
    irule $ cj 1 tmatch_SOME_tinst >>
    metis_tac[FEMPTY_complete]) >> 
 assume_tac (INST_TYPE [alpha |-> “:term” ]
 FEMPTY_complete) >>
 drule_then assume_tac $ cj 1 IS_SOME_match >>
 gs[]
QED




Theorem cstt_sort_of_tinst:
 cstt σ ⇒
 sort_of (tinst σ t) = sinst σ (sort_of t)
Proof
 Induct_on ‘t’ >> gs[sort_of_def] >> rw[] >>
 gs[cstt_def,sort_of_def]
QED 

Definition tsubtm_def:
  tsubtm (Var n s) = (Var n s) INSERT (ssubtm s) ∧
  tsubtm (Fn f s l) = (Fn f s l) INSERT (ssubtm s) ∪
                      BIGUNION (set (MAP tsubtm l)) ∧
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
∀t0 t. t0 ∈ ssubtm (sort_of t) ⇒ t0 ∈ tsubtm t
Proof
rw[] >> Cases_on ‘t’ >> gs[tsubtm_def,sort_of_def]
QED


Theorem tinst_subtm:
(∀t σ n st. (n,st) ∈ FDOM σ ∩ tfv t ∧ cstt σ ⇒
           σ ' (n,st) ∈ tsubtm (tinst σ t)) ∧
(∀s σ n st. (n,st) ∈ FDOM σ ∩ sfv s ∧ cstt σ ⇒
           σ ' (n,st) ∈ ssubtm (sinst σ s))
Proof                 
ho_match_mp_tac better_tm_induction >> rw[] >> gvs[]
(* 5 *)
>- metis_tac[tsubtm_REFL]
>- (rename [‘(n1,st1) ∉ FDOM σ’] >> 
   Cases_on ‘(n1,st1) ∈ FDOM σ’ (* 2 *)
   >- (gs[] >>  irule ssubtm_tsubtm >>
      gs[cstt_def]) >>
   gs[tsubtm_def])
>- (gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
   rpt disj2_tac >> qexists ‘t’ >>
   metis_tac[])
>- gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
gs[tsubtm_def,MEM_MAP,PULL_EXISTS] >>
metis_tac[]
QED





Theorem sfv_tfv:
∀t n s. (n,s) ∈ sfv (sort_of t) ⇒ (n,s) ∈ tfv t
Proof
Cases_on ‘t’ >> gs[sort_of_def,tfv_def]
QED



Theorem tfv_sinst:
(∀t σ. cstt σ ∧ tfv t ⊆ FDOM σ ⇒
 (∀n st. (n,st) ∈ tfv (tinst σ t) ⇔
       ∃n0 st0. (n0,st0) ∈ tfv t ∧ (n,st) ∈ tfv (σ ' (n0,st0)))) ∧
(∀s σ. cstt σ ∧ sfv s ⊆ FDOM σ ⇒
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
   metis_tac[sfv_tfv])
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
  cstt σ ∧ sfv s ⊆ tfv t ∧ tfv t ⊆ FDOM σ ⇒
  sfv (sinst σ s) ⊆ tfv (tinst σ t)
Proof
  rw[] >> drule_all_then assume_tac $ cj 1 tfv_sinst >>
  drule_all_then assume_tac SUBSET_TRANS >>
  drule_all_then assume_tac $ cj 2 tfv_sinst >>
  rw[SUBSET_DEF] >> Cases_on ‘x’ >> gs[] >>
  gs[SUBSET_DEF] >> metis_tac[]
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



Theorem tmatch_FEMPTY:
  ∀f. complete f ∧ cstt f ⇒
 (tmatch {} t1 t2 f = SOME σ ⇔
  ∃σ0.   (∀n s. (n,s) ∈ FDOM f ∩ FDOM σ0 ⇒ f ' (n,s) = σ0 ' (n,s)) ∧
         tmatch {} t1 t2 FEMPTY = SOME σ0 ∧ σ = FUNION f σ0)
Proof 
 rw[] >> eq_tac (* 2 *)
 >- (rw[] >> drule_all_then assume_tac $ cj 1 tmatch_SOME_tinst >>
    pop_assum (assume_tac o GSYM) >> rw[] >>
    qexists ‘DRESTRICT σ (tfv t1)’ >> rw[] (* 3 *)
    >- (drule_all_then strip_assume_tac tmatch_property >> gs[SUBMAP_DEF,DRESTRICT_DEF])
    >- (‘tmatch ∅ t1 (tinst σ t1) FEMPTY = SOME (FUNION FEMPTY (DRESTRICT σ (tfv t1)))’
        suffices_by simp[] >> 
       irule $ cj 1 IS_SOME_match >> simp[FEMPTY_complete] >>
       drule_all_then strip_assume_tac tmatch_property >>
       rw[SUBSET_UNION] >>
       irule $ cj 1 match_SOME_cstt >> metis_tac[]) >>
    ‘tmatch ∅ t1 (tinst σ t1) f = SOME (f ⊌ DRESTRICT σ (tfv t1))’
       suffices_by (rw[] >> gs[]) >>
    irule $ cj 1 IS_SOME_match >> simp[] >>
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
complete f ∧ cstt f ∧ tmatch ∅ t1 t2 f = SOME σ ∧
f ⊑ f1 ∧ complete f1 ∧ cstt f1 ∧
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
 complete f ∧ cstt f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧ LENGTH tl1 = LENGTH tl2 ⇒
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
  first_x_assum (qspecl_then [‘σ’] assume_tac) >> gs[] >>
  first_x_assum $ drule_all_then assume_tac >>
  drule_all_then assume_tac tmatch_FEMPTY >>
  first_x_assum (drule o iffLR) >> rw[] >>
  rev_drule tmatch_FEMPTY >> strip_tac >>
  first_x_assum $ drule_then assume_tac >>
  first_x_assum $ irule o iffRL >>
  qexists ‘σ0’ >> simp[] >>
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
 gs[FEMPTY_complete,FEMPTY_cstt]
QED
        
        

Theorem IS_SOME_match_FEMPTY:
 (∀t σ.
    cstt σ ∧ tfv t ⊆ FDOM σ ⇒
    tmatch ∅ t (tinst σ t) FEMPTY = SOME (DRESTRICT σ (tfv t))) ∧
 (∀st σ.
    cstt σ ∧ sfv st ⊆ FDOM σ ⇒
    smatch ∅ st (sinst σ st) FEMPTY = SOME (DRESTRICT σ (sfv st))) ∧
 ∀l σ.
   cstt σ ∧ BIGUNION {tfv t | MEM t l} ⊆ FDOM σ ⇒
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
cstt σ1 ∧ cstt σ2 ∧
complete σ1 ∧
(∀x. x ∈ FDOM σ1 ⇒ tfv (σ1 ' x) ⊆ FDOM σ2) ⇒ cstt (o_vmap σ2 σ1)
Proof
strip_tac >> rw[cstt_def] >> gs[FDOM_o_vmap,FAPPLY_o_vmap]  >>
first_x_assum $ drule_then assume_tac >>
drule cstt_sort_of_tinst >> rw[] >>
‘sinst σ2 (sinst σ1 s) = sinst (o_vmap σ2 σ1) s’
 suffices_by
  (rw[] >> pop_assum (assume_tac o GSYM) >>
  gs[cstt_def]) >> 
irule $ cj 2 inst_o_vmap  >> gs[complete_def] >>
gs[SUBSET_DEF] >> rw[] (* 2 *)
>- metis_tac[] >>
first_x_assum irule >> gs[cstt_def] >>
last_x_assum $ drule_then (assume_tac o GSYM) >>
gs[] >> Cases_on ‘x’ >> irule sfv_tfv >>
metis_tac[]
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
       complete f ∧ cstt f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧ LENGTH tl1 = LENGTH tl2 ⇒
       ∀σ. f ⊑ σ ∧ cstt σ ∧
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
       complete f ∧ cstt f ∧ LENGTH tl1 = LENGTH tl2 ⇒
       ∀σ. f ⊑ σ ∧ cstt σ ∧
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
       complete f ∧ cstt f ∧ tl1 ≠ [] ∧ tl2 ≠ [] ∧ LENGTH tl1 = LENGTH tl2 ⇒
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


(*                                                  
Theorem tlmatch_TRANS:
 IS_SOME (tlmatch {} l1 l2 FEMPTY) ∧
 IS_SOME (tlmatch {} l2 l3 FEMPTY) ⇒
 IS_SOME (tlmatch {} l1 l3 FEMPTY)
Proof
 rw[optionTheory.IS_SOME_EXISTS] >>
 drule_then strip_assume_tac tlmatch_LENGTH >>
 rev_drule_then strip_assume_tac tlmatch_LENGTH >>
 gs[] >>
 Cases_on ‘l1 = []’ >> gs[tmatch_def] >>
 ‘l2 ≠ []’ by (CCONTR_TAC >> gs[]) >>
 ‘l3 ≠ []’ by (CCONTR_TAC >> gs[]) >>
 qspecl_then [‘l1’,‘l3’] assume_tac tlmatch_FEMPTY_each >>
 first_x_assum (drule_at_then Any (assume_tac o iffLR)) >>
 first_x_assum (drule_all_then assume_tac) >>
 gs[] >> pop_assum (K all_tac) >>
 qspecl_then [‘l1’,‘l2’] assume_tac tlmatch_FEMPTY_each >>
 gs[] >>
 qspecl_then [‘l2’,‘l3’] assume_tac tlmatch_FEMPTY_each >>
 gs[] >>
 qexists ‘o_vmap x' x’ >> simp[FDOM_o_vmap] >>
 rw[] >>
 first_x_assum $ drule_then assume_tac >>
 first_x_assum $ drule_then assume_tac >>
 qabbrev_tac ‘t1 = EL n l1’ >>
 qabbrev_tac ‘t2 = EL n l2’ >>
 qabbrev_tac ‘t3 = EL n l3’ >>
 drule tmatch_FEMPTY_tinst >>
 rev_drule tmatch_FEMPTY_tinst >> rw[] >>
 qabbrev_tac ‘σ1 = (DRESTRICT x (tfv t1))’ >>
 qabbrev_tac ‘σ2 = (DRESTRICT x' (tfv (tinst σ1 t1)))’ >>
 ‘(tinst σ2 (tinst σ1 t1)) = tinst (o_vmap σ2 σ1) t1’
  by (irule $ cj 1 inst_o_vmap >>
      metis_tac[tmatch_FEMPTY_property,SUBSET_ANTISYM_EQ]) >>
 gs[] >>
 ‘(tinst (o_vmap σ2 σ1) t1) = (tinst (o_vmap x' x) t1)’
   by cheat >>
 simp[] >> irule $ cj 1 IS_SOME_match_FEMPTY >>
 simp[FDOM_o_vmap] >>
 ‘cstt (o_vmap x' x)’
   by irule o_vmap_cstt >>
      ‘(∀v. v ∈ FDOM x ⇒ tfv (x ' v) ⊆ FDOM x')’
       by simp[PULL_EXISTS]
 gs[] >> pop_assum (K all_tac) >>
*)    

(*           
            
        
Theorem upgrade_inst_ex:
  (∀t σ. cstt σ ⇒
    ∃cσ. σ ⊑ cσ ∧ cstt cσ ∧ tfv t = FDOM cσ ∧ tinst σ t = tinst cσ t) ∧
  (∀s σ. cstt σ ⇒
    ∃cσ. σ ⊑ cσ ∧ cstt cσ ∧ sfv s = FDOM cσ ∧ sinst σ s = sinst cσ s) ∧
  (∀l σ. cstt σ ⇒
    ∃cσ. σ ⊑ cσ ∧ cstt cσ ∧
    BIGUNION {tfv t | MEM t l} = FDOM cσ ∧
    ∀t. MEM t l ⇒ tinst σ t = tinst cσ t)
Proof
 ho_match_mp_tac original_tm_induction >> rw[] (* 5 *)
 >- (first_x_assum $ drule_then strip_assume_tac >>
    ‘(s0,s) ∉ FDOM cσ’ by metis_tac[tm_tree_WF] >>
    qabbrev_tac
    ‘σ1 = cσ |+ ((s0,s),Var s0 (sinst σ s))’ >>
    qexists ‘σ1’ >>
    ‘(s0,s) ∈ FDOM σ1’
     by gs[EXTENSION,Abbr‘σ1’,fmap_EXT] >> 
    gs[] >>
    ‘σ1 ' (s0,s) = Var s0 (sinst σ s)’
      by gs[Abbr‘σ1’] >> gs[] >>
    ‘cσ ⊑ σ1’
      by rw[Abbr ‘σ1’] >>
    ‘σ ⊑ σ1’ by metis_tac[SUBMAP_TRANS] >> gs[] >>
    ‘{(s0,s)} ∪ FDOM cσ = FDOM σ1’
      by gs[EXTENSION,Abbr‘σ1’] >> gs[] >>
    ‘complete cσ’ by
     metis_tac[complete_FDOM_is_cont,tfv_is_cont] >>
    ‘cstt σ1’
      by (irule cstt_SUBMAP >>
         qexists ‘cσ’ >> gs[] >>
         rw[] >>
         ‘(n,s') = (s0,s)’
           by (gs[EXTENSION] >>
               metis_tac[pairTheory.PAIR_EQ]) >>
         gs[sort_of_def] >>
         metis_tac[update_inst_lemma]) >>
    gs[] >>
    Cases_on ‘(s0,s) ∈ FDOM σ’ >> gs[] >>
    gs[SUBMAP_DEF])
 >- first_x_assum $ drule_then strip_assume_tac >>
    rename [‘σ ⊑ σ1’] >>
    first_x_assum $ drule_then strip_assume_tac >>
         
         
    

 
    qexists ‘cσ |+ ((s0,s),Var s0 (sinst σ s))’ >>
    gs[] >>
    ‘cstt (cσ |+ ((s0,s),Var s0 (sinst cσ s)))’
    by (rw[cstt_def,FAPPLY_FUPDATE,sort_of_def] >>
       rw[FAPPLY_FUPDATE,sort_of_def] (*2 *)
       >-
       (irule fmap_sfv_sinst_eq >>
       rw[fmap_EXT,DRESTRICT_DEF] (* 2 *)
       >- (rw[EXTENSION] >> metis_tac[tm_tree_WF]) >>
       rw[Once EQ_SYM_EQ] >> irule NOT_EQ_FAPPLY >>
       metis_tac[tm_tree_WF]) >>
       Cases_on ‘(n,s') = (s0,s)’ >> gs[] (* 2 *)
       >- (rw[sort_of_def] >>
          irule fmap_sfv_sinst_eq >>
          rw[fmap_EXT,DRESTRICT_DEF] (* 2 *)
          >- (rw[EXTENSION] >> metis_tac[tm_tree_WF]) >>
          Cases_on ‘x = (n,s)’ >> gs[] (* 2 *)
          >- metis_tac[tm_tree_WF] >>
          metis_tac[NOT_EQ_FAPPLY]) >>
       ‘(n,s') ≠ (s0,s)’ by simp[] >>
       ‘((cσ |+ ((s0,s),Var s0 (sinst cσ s))) ' (n,s')) =
         cσ ' (n,s')’ by metis_tac[NOT_EQ_FAPPLY] >>
       gs[cstt_def] >>
       irule fmap_sfv_sinst_eq >>  ) >>
    simp[]
       FAPPLY_FUPDATE FUPDA
e       cheat
QED          



Theorem match_SOME_iff_inst:
  (∀t1 t2. IS_SOME (tmatch {} t1 t2 FEMPTY) ⇔
           ∃σ. complete σ ∧ cstt σ ∧ FDOM  t2 = tinst σ t1)
Proof
 rw[EQ_IMP_THM] (* 2 *)
 >- (Cases_on ‘tmatch ∅ t1 t2 FEMPTY’ >> gs[] >>
    qexists ‘x’ >>
    ‘cstt x’ by metis_tac[match_SOME_cstt,FEMPTY_complete,FEMPTY_cstt] >> simp[Once EQ_SYM_EQ] >>
    ‘complete x’
     by metis_tac[match_complete,FEMPTY_complete,FEMPTY_cstt]  >> gs[] >>
    irule $ cj 1 tmatch_SOME_tinst >>
    metis_tac[FEMPTY_complete]) >> 
 assume_tac (INST_TYPE [alpha |-> “:term” ]
 FEMPTY_complete) >>
 drule_then assume_tac $ cj 1 IS_SOME_match >> gs[] >>
 gs[] >> drule upgrade_inst_ex >>
 rw[] >>
 first_x_assum (qspecl_then [‘t1’] strip_assume_tac) >>
 gs[]
             

  
  
 
  




Theorem match_SOME_iff_inst:
  (∀t1 t2. IS_SOME (tmatch {} t1 t2 FEMPTY) ⇔
           ∃σ. cstt σ ∧ t2 = tinst σ t1)
Proof
 rw[EQ_IMP_THM] (* 2 *)
 >- (Cases_on ‘tmatch ∅ t1 t2 FEMPTY’ >> gs[] >>
    qexists ‘x’ >>
    ‘cstt x’ by metis_tac[match_SOME_cstt,FEMPTY_complete,FEMPTY_cstt] >> simp[Once EQ_SYM_EQ] >>
    irule $ cj 1 tmatch_SOME_tinst >>
    metis_tac[FEMPTY_complete]) >> 
 assume_tac (INST_TYPE [alpha |-> “:term” ]
 FEMPTY_complete) >>
 drule_then assume_tac $ cj 1 IS_SOME_match >>
 gs[] >> drule upgrade_inst_ex >>
 rw[] >>
 first_x_assum (qspecl_then [‘t1’] strip_assume_tac) >>
 gs[]
QED 
 
 




Theorem IS_SOME_match:
   (∀t1 t2 lcs f σ.
     complete f ⇒
     (tmatch lcs t1 t2 f = SOME σ ⇔
        (tmatch {} t1 t2 f = SOME σ ∧
         ∀n s. (n,s) ∈ lcs ⇒ σ ' (n,s) = Var n s))) ∧
   (∀s1 s2 lcs f σ.
     complete f ⇒
     (smatch lcs s1 s2 f = SOME σ ⇔
        (smatch {} s1 s2 f = SOME σ ∧
         ∀n s. (n,s) ∈ lcs ⇒ σ ' (n,s) = Var n s))) ∧
   (∀tl1 tl2 lcs f σ.
     complete f ⇒
     (tlmatch lcs tl1 tl2 f = SOME σ ⇔
     (tlmatch {} tl1 tl2 f = SOME σ ∧
     ∀n s. (n,s) ∈ lcs ⇒ σ ' (n,s) = Var n s)))
Proof
  ho_match_mp_tac original_tm_induction>> rw[] (* 5 *)
  >- (rw[EQ_IMP_THM] (* 3 *)
      >- gs[tmatch_def] >>
         Cases_on ‘(s0,s1) ∈ lcs’ >>
         Cases_on ‘(s0,s1) ∈ FDOM f’ >> gs[]


gs[tmatch_def,AllCaseEqs()] >>
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

*)


        
        
val _ = export_theory();

