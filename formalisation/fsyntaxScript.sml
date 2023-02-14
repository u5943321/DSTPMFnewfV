open HolKernel Parse boolLib bossLib;
open finite_setTheory;
open finite_mapTheory;
open pred_setTheory;
val _ = new_theory "fsyntax";



 
        




(*

∀A B f:A->B. P[set,set,ar 1-> 0] (A,B,f:A->B)

∀A B. P[1->0](f:A->B)


 EVAL ``slreplace 0 (Var "A" (St "set" []))[St "set" [];St "set" [] ; St "fun" [Bound 1; Bound 0]]``;
val it =
   ⊢ slreplace 0 (Var "A" (St "set" []))
       [St "set" []; St "set" []; St "fun" [Bound 1; Bound 0]] =
     [St "set" []; St "set" []; St "fun" [Bound 1; Bound 0]]: thm
> EVAL ``slreplace 0 (Var "A" (St "set" []))[St "set" [] ; St "fun" [Bound 1; Bound 0]]``;
val it =
   ⊢ slreplace 0 (Var "A" (St "set" []))
       [St "set" []; St "fun" [Bound 1; Bound 0]] =
     [St "set" []; St "fun" [Var "A" (St "set" []); Bound 0]]: thm   

*)





(*key point is that does not allow bound variable in sort, and hence no dependency. only need to check exactly the bound variable number and replace it with something else
  tpreplace bmap (Var n s) = Var n (spreplace bmap s) ∧
*)        





        
  



        
      
(*
can have [set, A->0]
*)
(*
Definition slspec_def:
  slspec i t [] = [] ∧
  slspec i t (s :: sl)  =
  (sreplace (i-1) t s) :: slspec (i + 1) t sl
End  

[set,set,1->0](A,B,A->B)

EVAL “slspec 0 (Var "A" (St "set" []))
[(St "set" []);(St "set" []);(St "ar" [Bound 1;Bound 1])]”
*)

(*
Definition slspec_def:
  slspec i t [] = [] ∧
  slspec i t (s :: sl)  =
  (sreplace i t s) :: slspec (i + 1) t sl
End  


Definition slwf_def:
  (slwf Σf [] [] ⇔ T) ∧
  (slwf Σf (s:: sl) (t :: tl) ⇔
  s = sort_of t ∧ wfs Σf s ∧ slwf Σf (slspec 0 t sl) tl)
End
*)


Definition specsl_def:
  specsl i t [] = [] ∧
  specsl i t (s :: sl)  =
  (sreplace i t s) :: specsl (i + 1) t sl
End  

 
Definition wfabsap_def:
  (wfabsap Σf [] [] ⇔ T) ∧
  (wfabsap Σf (s:: sl) (t :: tl) ⇔
  wft Σf t ∧ s = sort_of t ∧ wfs Σf s ∧ wfabsap Σf (specsl 0 t sl) tl) ∧
  (wfabsap Σf (s:: sl) [] ⇔ F) ∧
  (wfabsap Σf [] (t :: tl) ⇔ F)
End

Theorem LENGTH_specsl:
∀sl t i.  LENGTH (specsl i t sl) =  LENGTH sl
Proof
Induct_on ‘sl’ >> simp[specsl_def]
QED

        

(*sreplace is not need outside of the list, sreplace and treplace can be separated since for a real term, its sort does not have bound vars.*)

           
                            




 
Theorem specsl_sbounds:
 ∀sl n t i. tbounds t = {} ∧ n < LENGTH sl ⇒
 sbounds (EL n (specsl i t sl)) =
 sbounds (EL n sl) DELETE (n + i)
Proof
 Induct_on ‘sl’ >> rw[] >>
 Cases_on ‘n < LENGTH sl’ >> simp[specsl_def] (* 2 *)
 >- (Cases_on ‘n’ >> simp[] >- 
    metis_tac[treplace_eliminate] >>
    simp[arithmeticTheory.ADD1]) >>
 ‘n = LENGTH sl’ by simp[] >>
 Cases_on ‘n’ >> gs[] >- metis_tac[treplace_eliminate] >>
 rename [‘SUC n = LENGTH sl’] >>
 gs[arithmeticTheory.ADD1]
QED 

Theorem specsl_sbounds_SUBSET:
 ∀sl n t i. tbounds t = {} ∧ n < LENGTH sl ⇒
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
 
 
        
(*        
EVAL
“slwf [(St "set" []);(St "set" []);(St "ar" [Bound 1;Bound 0])] [Var "A" (St "set" []) ;
    Var "B" (St "set" []) ;
    Var "f" (St "ar" [Var "A" (St "set" []) ;
                       Var "B" (St "set" [])])]”     
*)     

(*
Definition slspec_def:
  slspec i t [] = [] ∧
  slspec i t (s :: sl)  =
  (sreplace (i-1) t s) :: slspec (i + 1) t sl
End  
     
[set,set,1->0](A,B,A->B)

EVAL “slspec 0 (Var "A" (St "set" []))
[(St "set" []);(St "set" []);(St "ar" [Bound 1;Bound 1])]”         
*)  


(*
[] [] ∧
  wfabsap (s :: sl) (t :: tl) ⇔
*)  
        


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



    
Definition abs_def:
  abs _ _ False = False ∧
  abs v i (Pred p tl) =
  Pred p (MAP (tsubst v (Bound i)) tl) ∧
  abs v i (fVar p vl tl) =
  fVar p vl (MAP (tsubst v (Bound i)) tl) ∧
  abs v i (IMP f1 f2) =
  IMP (abs v i f1) (abs v i f2) ∧
  abs v i (FALL s b) =
  FALL (ssubst v (Bound i) s) (abs v (i + 1) b)
End

Definition abstract_def:
  abstract v = abs v 0
End

Definition mk_FALL_def:
mk_FALL n s b = FALL s (abstract (n,s) b)
End        
        

Theorem wfabsap_wft:
  ∀tl sl t. wfabsap Σf sl tl ∧ MEM t tl ⇒ wft Σf t
Proof
Induct_on ‘tl’ >> simp[wfabsap_def] >>
Cases_on ‘sl’ >> simp[wfabsap_def] >> metis_tac[]
QED
  
Inductive wff:
[~False:]
(wff (Σf,Σp) False) ∧
[~Pred:]
  ((∀t. MEM t tl ⇒ wft Σf t) ∧
ispsym Σp p ∧
IS_SOME
(tlmatch {} (MAP (UNCURRY Var) (Σp ' p)) tl FEMPTY) ⇒
wff (Σf,Σp) (Pred p tl)) ∧
[~IMP:]
  (wff (Σf,Σp) f1 ∧ wff (Σf,Σp) f2 ⇒
  wff (Σf,Σp) (IMP f1 f2)) ∧
[~fVar:]
  (wfabsap Σf sl tl ⇒
  wff (Σf,Σp) (fVar P sl tl)) ∧
[~FALL:]
 (∀f n s.
  wff (Σf,Σp) f ∧ wfs Σf s ∧
  (∀n1 s1. (n1,s1) ∈ ffv f ⇒ (n,s) ∉ sfv s1) ⇒
  wff (Σf,Σp) (mk_FALL n s f))
End

(*check quantifier order? *)                           
Definition finst_def[simp]:
  finst σ False = False ∧
  finst σ (Pred p tl) = Pred p (MAP (tinst σ) tl) ∧
  finst σ (IMP f1 f2) = IMP (finst σ f1) (finst σ f2) ∧
  (finst σ (fVar p sl tl) =
  fVar p (MAP (sinst σ) sl)
  (MAP (tinst σ) tl)) ∧
  finst σ (FALL s f) =
    FALL (sinst σ s) (finst σ f)
End        
        



Definition abs_def:
  abs _ _ False = False ∧
  abs v i (Pred p tl) =
  Pred p (MAP (tsubst v (Bound i)) tl) ∧
  abs v i (fVar p sl tl) =
  fVar p (MAP (ssubst v (Bound i)) sl) (MAP (tsubst v (Bound i)) tl) ∧
  abs v i (IMP f1 f2) =
  IMP (abs v i f1) (abs v i f2) ∧
  abs v i (FALL s b) =
  FALL (ssubst v (Bound i) s) (abs v (i + 1) b)
End



(*
Theorem sinst_sreplace:
(∀tm i t σ.
(∀n s. (n,s) ∈ tfv tm ⇒ sbounds s = {}) ∧
(∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = {}) ∧
tfv tm ⊆ FDOM σ ⇒
tinst σ (treplace i t tm) =
treplace i (tinst σ t) (tinst σ tm)) ∧
(∀st i t σ.
(∀n s. (n,s) ∈ sfv st ⇒ sbounds s = {}) ∧
(∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = {}) ∧
sfv st ⊆ FDOM σ ⇒
sinst σ (sreplace i t st) =
sreplace i (tinst σ t) (sinst σ st))
Proof
ho_match_mp_tac better_tm_induction >>
rw[] (* 4 *)
>- (‘(treplace i t (Var s0 st)) = (Var s0 st)’
    by (irule $ cj 1 treplace_id >> gs[tbounds_def]) >>
   simp[] >>
   rw[Once EQ_SYM_EQ] >>
   irule $ cj 1 treplace_id >>
   first_x_assum $ drule_then assume_tac >> gs[])
>- (rw[treplace_def,tinst_def] (* 2 *)
   >- (first_x_assum irule >> simp[] >>
      gs[SUBSET_DEF] >> metis_tac[]) >>
   rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
   first_x_assum irule >> simp[] >>
   gs[SUBSET_DEF] >> metis_tac[])
>- rw[treplace_def,tinst_def] >>
rw[treplace_def,tinst_def] >>
rw[SF ETA_ss,MAP_MAP_o,MAP_EQ_f] >>
first_x_assum irule >> simp[] >>
gs[SUBSET_DEF] >> metis_tac[]
QED
*)
           
        




Theorem fmap_ffv_finst_eq:
  (∀f σ1 σ2.
     ffv f ⊆ FDOM σ1 ∧ ffv f ⊆ FDOM σ2 ∧
     (∀x. x ∈ ffv f ⇒ σ1 ' x = σ2 ' x) ⇒
     finst σ1 f = finst σ2 f)
Proof
  Induct_on ‘f’ >> gs[finst_def] (* 3 *)
  >- (rw[MAP_EQ_f] >>
     irule $ cj 1 fmap_fv_inst_eq_alt >>
     gs[SUBSET_DEF,MEM_MAP] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
     rw[] >>
     irule $ cj 2 fmap_fv_inst_eq_alt >>
     gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]) >>
  rw[MAP_EQ_f] (* 2 *)
  >- irule $ cj 2 fmap_fv_inst_eq_alt >>
  gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]
  irule $ cj 1 fmap_fv_inst_eq_alt >>
  gs[SUBSET_DEF,MEM_MAP] >> metis_tac[]
QED  
                 
Theorem wff_finst:
  ∀f. wff (Σf,Σp) f ⇒
  (∀fsym. isfsym Σf fsym ⇒ sfv (fsymout Σf fsym) ⊆ BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
  ∀σ. cstt σ ∧ wfcod Σf σ ∧ ffv f ⊆ FDOM σ ⇒
  wff (Σf,Σp) (finst σ f)
Proof
  Induct_on ‘wff’ >> simp[] >> rw[] (* 5 *)
  >- metis_tac[wff_rules]
  >- (irule $ cj 2 wff_rules >> simp[MEM_MAP] >>
     rw[] (* 2 *)
     >- (first_x_assum drule >>
        rw[] >> irule $ cj 1 wft_tinst >>
        rw[] >> gs[SUBSET_DEF,MEM_MAP] >>
        metis_tac[]) >>
     irule IS_SOME_tlmatch_inst >> simp[] >>
     metis_tac[])
  >- (irule $ cj 3 wff_rules >> rw[])
  >- (irule $ cj 4 wff_rules >>
      irule wfabsap_sinst_tinst >> simp[]) >>
  first_x_assum drule >> rw[] >>
  rw[mk_FALL_def] >>
  ‘∃σ1. cstt σ1 ∧ wfcod Σf σ1 ∧ ffv (mk_FALL n s f) = FDOM σ1 ∧
  (wff (Σf,Σp) (FALL (sinst σ1 s) (finst σ1 (abstract (n,s) f))) ⇒ wff (Σf,Σp) (FALL (sinst σ s) (finst σ (abstract (n,s) f))))’
  by (qabbrev_tac ‘σ1 = DRESTRICT σ (ffv (mk_FALL n s f))’ >>
     qexists ‘σ1’ >>
     ‘cstt σ1’
       by (drule DRESTRICT_cstt >>
          rw[Abbr‘σ1’] >> first_x_assum irule >> simp[] >>
          rw[ffv_is_cont]) >> simp[] >>
     ‘wfcod Σf σ1’ by metis_tac[DRESTRICT_wfcod] >>
     simp[] >>
     ‘ffv (mk_FALL n s f) = FDOM σ1’
       by (rw[Abbr‘σ1’,DRESTRICT_DEF]  >>
          gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
     simp[] >>
     ‘(sinst σ1 s) = (sinst σ s)’
       by (irule $ cj 2 fmap_fv_inst_eq_alt >>
          gs[mk_FALL_def,ffv_def] >>
          ‘sfv s ⊆ FDOM σ1 ∧ sfv s ⊆ FDOM σ’
          by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
          simp[] >> rw[] >>
          ‘x ∈ FDOM σ1 ∧ x ∈ FDOM σ’
           by metis_tac[SUBSET_DEF] >>
          gs[Abbr‘σ1’,DRESTRICT_DEF]) >>
     ‘finst σ1 (abstract (n,s) f) =
      finst σ (abstract (n,s) f)’
      by (irule $ fmap_ffv_finst_eq >>
      gs[mk_FALL_def,ffv_def] >>
      ‘ffv (abstract (n,s) f) ⊆ FDOM σ1 ∧ ffv (abstract (n,s) f) ⊆ FDOM σ’
          by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
      simp[] >> rw[] >>
     ‘x ∈ FDOM σ1 ∧ x ∈ FDOM σ’
           by metis_tac[SUBSET_DEF] >>
      gs[Abbr‘σ1’,DRESTRICT_DEF]) >> simp[]) >>
  first_x_assum irule>>
  qpat_x_assum ‘ffv (mk_FALL n s f) ⊆ FDOM σ’ (K all_tac) >>
  qpat_x_assum ‘ cstt σ’ (K all_tac) >>
  qpat_x_assum ‘wfcod Σf σ’ (K all_tac) >>
  rename [‘ cstt σ’]>>
  rw[abstract_def] >>(*need lemma ffv_mk_FALL*)
  drule ffv_mk_FALL >> rw[] >> gs[] >>
  ‘sfv s ⊆ FDOM σ’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[tm_tree_WF]) >>
  ‘(n,s) ∉ FDOM σ’ by gs[EXTENSION] >>
  ‘ffv f DELETE (n,s) ⊆ FDOM σ’
   by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[tm_tree_WF]) >>
  (*‘∃nn.
   (∀x s1. x ∈ FDOM σ ⇒ (nn,s1) ∉ tfv (σ ' x))’
   by cheat >>*)
  ‘∃nn.
   (∀x s1. x ∈ ffv f ∪ sfv s ∧ x ≠ (n,s) ⇒ (nn,s1) ∉ tfv (σ ' x))’
   by
   (qabbrev_tac
   ‘names = BIGUNION {tfv (σ ' x) | x | x ∈ FDOM σ}’ >>
   qexists ‘variant (fromSet (IMAGE FST names)) "a"’ >>
   rw[] >>
   ‘x ∈ FDOM σ’ by simp[] >>
   ‘FINITE names’
    by (qpat_x_assum ‘FDOM _ = _’ (assume_tac o GSYM) >>
       rw[Abbr‘names’] (* 2 *)
       >- (‘{tfv (σ ' x) | x | x ∈ FDOM σ} =
           IMAGE (tfv o (λx. σ ' x)) (FDOM σ)’
           by rw[Once EXTENSION] >> simp[])
       >- simp[]) >>
   drule_then assume_tac variant_var_NOTIN >>
   gs[Abbr‘names’] >>
   metis_tac[]) >>
  drule_at_then Any assume_tac finst_abstract >>
  ‘finst σ (abs (n,s) 0 f) =
   abs (nn,sinst σ s) 0 (finst (σ |+ ((n,s),Var nn (sinst σ s))) f)’
    by (rw[Once EQ_SYM_EQ] >> irule finst_abstract >>
       simp[] >> metis_tac[]) >>
  simp[] >> rw[GSYM mk_FALL_def,GSYM abstract_def] >>
  irule $ cj 5 wff_rules >>
  ‘wfs Σf (sinst σ s)’
    by (irule $ cj 2 wft_tinst >> simp[]) >> simp[] >>
  ‘wff (Σf,Σp) (finst (σ |+ ((n,s),Var nn (sinst σ s))) f)’
    by
     (first_x_assum irule >>
     simp[FDOM_FUPDATE,SUBSET_INSERT_DELETE ] >> gs[] >>
     ‘wfcod Σf (σ |+ ((n,s),Var nn (sinst σ s)))’
      by (irule FUPDATE_wfcod >> simp[wft_def]) >> simp[]>>
     irule FUPDATE_cstt >>
     simp[complete_FDOM_is_cont,sort_of_def] >>
     ‘is_cont (ffv f ∪ sfv s DELETE (n,s))’
       by metis_tac[ffv_is_cont] >> simp[] >>       
     metis_tac[tm_tree_WF,vsort_tfv_closed]) >> simp[] >>
  rw[] >>
  ‘cstt (σ |+ ((n,s),Var nn (sinst σ s)))’
   by ( irule FUPDATE_cstt >>
     simp[complete_FDOM_is_cont,sort_of_def] >>
     ‘is_cont (ffv f ∪ sfv s DELETE (n,s))’
       by metis_tac[ffv_is_cont] >> simp[] >>       
     metis_tac[tm_tree_WF,vsort_tfv_closed]) >>
  drule ffv_finst >> rw[FDOM_FUPDATE,SUBSET_INSERT_DELETE]>>
  first_x_assum $ qspecl_then [‘f’,‘n1’,‘s1’] assume_tac >>
  gs[] >>
  ‘wfcod Σf (σ |+ ((n,s),Var nn (sinst σ s)))’
      by (irule FUPDATE_wfcod >> simp[wft_def]) >> simp[]>>
  drule wfcod_no_bound >> rw[] >> gs[] >>
  Cases_on ‘(n,s) = (n0,st0)’ (* 2 *)
  >- (gs[FAPPLY_FUPDATE_THM] (* 2 *)
     >- metis_tac[tm_tree_WF] >>
     rev_drule $ cj 2 tfv_sinst >> rw[] >>
     first_x_assum (qspecl_then [‘s’,‘n1’,‘s1’] assume_tac)>>
     gs[] >>
     rev_drule wfcod_no_bound >> rw[] >> gs[] >>
     ‘(n0,st0) ≠ (n,s)’ by metis_tac[tm_tree_WF] >>
     first_x_assum (qspecl_then [‘(n0,st0)’,‘sinst σ s’] assume_tac) >> gs[] >> metis_tac[vsort_tfv_closed]) >>
  gs[FAPPLY_FUPDATE_THM] >>
  first_x_assum (qspecl_then [‘(n0,st0)’,‘sinst σ s’] assume_tac) >> gs[] >> metis_tac[vsort_tfv_closed]
QED  
        

(*
Theorem tpreplace_FEMPTY:
(∀t. tpreplace FEMPTY t = t) ∧
(∀s. spreplace FEMPTY s = s)
Proof
ho_match_mp_tac better_tm_induction >>
rw[fpreplace_def,tpreplace_def,MAP_fix]
        
Theorem fpreplace_FEMPTY:
∀ϕ. (fpreplace (mk_bmap []) ϕ) = ϕ
Proof
Induct_on ‘ϕ’ >> rw[fpreplace_def,tpreplace_def]
*)

(*collect the "free" bound vars which is not associated to a quantifier*)

      

(*fbounds calculate*)

        
Definition specl_def:
specl t         

        (*rename preserve wfness*)
        

(*to prove spec of wff is wff, prove spec of mk_FALL is inst the (n,s) to be a t, (n,s) does not have non trivial map on sits subterms and so can extend to a cstt, inst with a cstt gives a wff*)

     
    
        
        

Theorem fpreplace_mk_bmap:
∀ϕ t tl.
fpreplace (mk_bmap (t::tl)) ϕ =
fpreplace (mk_bmap tl) (subst t (LENGTH tl) ϕ)
Proof
Induct_on ‘ϕ’ >> gs[fpreplace_def,subst_def,MAP_MAP_o,MAP_EQ_f]


Theorem subst_abs:
∀f.
  wff Σ f ⇒
  ∀n s i new.
  (n,s) ∈ ffv f ⇒
  subst new i (abs (n,s) i f) =
  finst (TO_FMAP [((n,s),new)]) f
Proof
(*
 Induct_on ‘wff’ >> reverse (rw[]) 
 rw[treplace_tsstt,tsubst_tsstt] (* 2 *)
 >- (irule $ cj 1 tsstt_tsstt  >> rw[Var_tsubtm_tfv]) >>
 irule $ cj 2 tsstt_tsstt >> rw[Var_tsubtm_tfv] *) cheat
QED



(*        
EVAL “slbounds [St "fun" [Bound 0;Bound 2]; St "fun" [Bound 0;Bound 1]]”


EVAL “slbounds [St "set" []; St "fun" [Bound 0;Bound 1];
St "fun" [Bound 1;Bound 2]]”     
*)




        

Theorem fpreplace_mk_bmap:
∀ϕ t tl.
fpreplace (mk_bmap (t::tl)) ϕ =
fpreplace (mk_bmap tl) (subst t (LENGTH tl) ϕ)
Proof
Induct_on ‘ϕ’ >> gs[fpreplace_def,subst_def,MAP_MAP_o,MAP_EQ_f]



(*slash u plus ⊎*)
Theorem fmap_fv_inst_eq:
  (∀t σ1 σ2.
  (∀v. v ∈ FDOM σ1 ∩ FDOM σ2 ∩ tfv t ⇒ σ1 ' v = )
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
    

Theorem cstt_DISJOINT_FUNION:
cstt σ1 ∧ cstt σ2 ∧ complete σ1 ∧ complete σ2 ∧
(∀v. v ∈ FDOM σ1 ∩ FDOM σ2 ⇒ σ1 ' v = σ2 ' v) ⇒
cstt (FUNION σ1 σ2)
Proof
rw[cstt_def] (* 2 *)
>- rw[FUNION_DEF] >>
   irule $ cj 2 fmap_fv_inst_eq_alt >>
   rw[fmap_EXT]



     
      



     
Theorem tbounds_tsubst:
 (∀tm n s i.
 (n,s) ∈ tfv tm ∧
 (∀n1 s1. (n1,s1) ∈ tfv tm ⇒
          (n,s) ∉ sfv s1 ∧ sbounds s1 = {}) ⇒
 tbounds (tsubst (n,s) (Bound i) tm) =
 {i} ∪ tbounds tm) ∧
 (∀st n s i.
 (n,s) ∈ sfv st ∧
 (∀n1 s1. (n1,s1) ∈ sfv st ⇒
          (n,s) ∉ sfv s1 ∧ sbounds s1 = {}) ⇒
 sbounds (ssubst (n,s) (Bound i) st) =
 {i} ∪ sbounds st)              
Proof             
 ho_match_mp_tac better_tm_induction >>
 simp[tbounds_thm,tsubst_def,tfv_thm,PULL_EXISTS,
      MEM_MAP] >>
 rw[] (* 5 *)
 >- rw[tbounds_thm]
 >- (Cases_on ‘n = s0 ∧ s = st’ >> simp[tbounds_thm] >>
    ‘sbounds st = {}’ by metis_tac[] >> gs[])
 >- ‘BIGUNION {tbounds t | (∃a. t = tsubst (n,s) (Bound i) a ∧ MEM a l)} =
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
      >- gs[PULL_EXISTS] >> )

Theorem tbounds_tsubst:
 (∀tm n s i.
 (n,s) ∈ tfv tm ∧
 (∀n1 s1. (n1,s1) ∈ tfv tm ⇒ (n,s) ∉ sfv s1) ⇒
 tbounds (tsubst (n,s) (Bound i) tm) =
 {i} ∪ tbounds tm) ∧
 (∀st n s i.
 (n,s) ∈ sfv st ∧
 (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ⇒
 sbounds (ssubst (n,s) (Bound i) st) =
 {i} ∪ sbounds st)              
Proof             
 ho_match_mp_tac better_tm_induction >>
 simp[tbounds_thm,tsubst_def,tfv_thm,PULL_EXISTS,
      MEM_MAP] >>
 rw[] (* 2 *)


Theorem tbounds_tsubst:
 (∀tm n s i.
 (n,s) ∈ tfv tm ∧  ⇒
 tbounds (tsubst (n,s) (Bound i) tm) =
 {i} ∪ tbounds tm) ∧
 (∀st n s i.
 (n,s) ∈ sfv st ∧
 (∀n1 s1. (n1,s1) ∈ sfv st ⇒ (n,s) ∉ sfv s1) ⇒
 sbounds (ssubst (n,s) (Bound i) st) =
 {i} ∪ sbounds st)              
Proof             
 ho_match_mp_tac better_tm_induction >>
 simp[tbounds_thm,tsubst_def,tfv_thm,PULL_EXISTS,
      MEM_MAP] >>
 rw[] (* 2 *)




Theorem slbounds_slabs:
 ∀n s m i l.
 m < LENGTH l ∧ (n,s) ∈ sfv (EL m l) ∧
 (∀n1 s1. (n1,s1) ∈ BIGUNION {sfv s0 | MEM s0 l} ⇒
          sbounds s1 = {}) ⇒
 slbounds (slabs (n,s) i l) = {i} ∪ slbounds l
Proof
 rw[IN_slbounds,LENGTH_slabs] >>
 rw[Once EXTENSION,EQ_IMP_THM] (* 3 *)
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
 >- qexists ‘m’ >> simp[] >>
    drule_then assume_tac slabs_EL

  disj2_tac >> qexists ‘m'’ >>
    simp[] >> Cases_on ‘m'’ >> gs[] 
    drule_then assume_tac slabs_EL 

    
 
 

  disj2_tac >> qexists ‘m'’ >>
    simp[] >> Cases_on ‘m'’ >> gs[] 
    drule_then assume_tac slabs_EL
 
 
      
 
   



      


   

  
 
 ‘FALL (sort_of t) ϕ’ 
 fs[mk_FALL_def] >> 
          

Theorem tpreplace_subst:
(∀tm l t.
   (∀i. i < LENGTH l ⇒ i ∉ tbounds t) ⇒ tpreplace (mk_bmap l) (treplace (LENGTH l) t tm) =
tpreplace (mk_bmap (l ⧺ [t])) tm) ∧
(∀st l t.
   (∀i. i < LENGTH l ⇒ i ∉ tbounds t) ⇒spreplace (mk_bmap l) (sreplace (LENGTH l) t st) =
spreplace (mk_bmap (l ⧺ [t])) st)
Proof
ho_match_mp_tac better_tm_induction >> rw[] >>
rw[tpreplace_def,treplace_def,MAP_MAP_o,MAP_EQ_f] 
cheat
rw[trep]
          
Theorem fpreplace_subst:
∀l ϕ t. fpreplace (mk_bmap l) (subst t (LENGTH l) ϕ) =
fpreplace (mk_bmap (l ⧺ [t])) ϕ
Proof
Induct_on ‘l’ >>
simp[mk_bmap_NIL,mk_bmap_def,subst_def,fpreplace_def,
    count_def]
>- Induct_on ‘ϕ’ >> simp[fpreplace_def] >> cheat    

        

Theorem wff_fpreplace:
(∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
∀tl sl ϕ. wfabsap Σf sl tl ∧ wff (Σf,Σp) (FALLL sl ϕ) ⇒
wff (Σf,Σp) (fprpl (mk_bmap (REVERSE tl)) ϕ)
Proof
strip_tac >> 
Induct_on ‘tl’ (* 2 *)
>- (Cases_on ‘sl’ >>
   simp[wfabsap_def,FALLL_def,fprpl_def] >>
   gs[fprpl_FEMPTY]) >>
Cases_on ‘sl’ >>
simp[wfabsap_def,FALLL_def,fprpl_def]  >>
rw[] >>
rename [‘wfabsap Σf (specsl 0 t sl) tl’] >>
‘wff (Σf,Σp) (subst_bound t (FALLL sl ϕ))’
 by (irule wff_spec >> simp[]) >>
‘(subst_bound t (FALLL sl ϕ)) = 
 FALLL (specsl 0 t sl) (subst t (LENGTH sl) ϕ)
’ by metis_tac[subst_bound_FALLL] >>
gs[] >>
first_x_assum $ drule_all_then assume_tac >>





              







                


   

        
 (P,sl) ∈ freefVars f ⇒
 (∀st. MEM st sl ⇒ (n,s)(abs (n,s) i f)
        

        





               
    

 
      

        


drule_then assume_tac wff_spec

(* FALLL t ϕ = abstract (n,sort_of h') f apply subst_bound_abstract*)




wff_spec subst_bound_abstract
           REVERSE fVar_subst_def!!!
           
   
   

  



        
 reverse (Induct_on ‘f’) >>
 
 gs[subst_def,abs_def,abstract_def,finst_def,MAP_MAP_o,MAP_EQ_f,treplace_tsstt,tsubst_tsstt,PULL_EXISTS,fbounds_def,
   MEM_MAP] (* 3 *)
 >- (rw[]
    >- (rename [‘((n,st),new)’] >>
        rw[GSYM tsubst_eq_tinst1]  >>
        irule slreplace_slabs >> fs[slbounds_sbounds]) >>
    Cases_on ‘(n,s) ∈ tfv e’ 
    >- (gs[GSYM Var_tsubtm_tfv] >>
       ‘Bound i ∉ tsubtm e’
         by (gs[Bound_tsubtm] >> metis_tac[]) >>
       drule_then assume_tac $ cj 1 tsstt_tsstt1 >>
       simp[] >>
       simp[tsubst_eq_tinst,GSYM tsubst_tsstt]) >>
    ‘Bound i ∉ tsubtm e’
   by (gs[Bound_tsubtm] >> metis_tac[]) >>
   drule_then assume_tac $ cj 1 tsstt_tsstt1 >> simp[] >>
   rw[tsubst_eq_tinst,GSYM tsubst_tsstt])
 >- (rw[] (* 2 *)   
    >- (rw[GSYM tsubst_eq_tinst1,tsubst_tsstt] >>
        rename [‘Var n st’] >>
        irule $ cj 2 tsstt_tsstt1 >> gs[Bound_tsubtm]) >>
    first_x_assum irule >>
    first_x_assum (qspecl_then [‘SUC i’] assume_tac) >>
    gs[arithmeticTheory.ADD1]) >>
 rw[] >> rw[GSYM tsubst_eq_tinst1,tsubst_tsstt] >>
 irule $ cj 1 tsstt_tsstt1 >> gs[Bound_tsubtm] >>
 metis_tac[]
QED        



    
(*
∀f:A->B. P[h:A->B](f:A->B)
λh. h = g
**********************
*)

        
val P = “"P"”
val sl = “[St "set" [];St "set" [];St "fun" [Bound 1;Bound 0]]”

    
val f = “FALL (St "fun" [Var "A" (St "set" []) ;
                         Var "B" (St "set" [])])
              (fVar "P" [St "fun" [Var "A" (St "set" []);Var "B" (St "set" [])]] [Bound 0])”


(*∀f:A->B. P[A->B](f)*)              

val phi = “Pred "=" [Bound 0;Var "g" (St "fun" [Var "A" (St "set" []) ;
                         Var "B" (St "set" [])])]”

(*λh. h = g*)                                   
val out = EVAL “
fVar_subst
("P",
[St "fun" [Var "A" (St "set" []) ;
           Var "B" (St "set" [])]],
Pred "=" [Bound 0;Var "g" (St "fun" [Var "A" (St "set" []) ;
                         Var "B" (St "set" [])])]          ) (FALL (St "fun" [Var "A" (St "set" []) ;
                         Var "B" (St "set" [])])
              (fVar "P" [St "fun" [Var "A" (St "set" []);Var "B" (St "set" [])]] [Bound 0]))”
|> SRULE []              






val _ = export_theory();

