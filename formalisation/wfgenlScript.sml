open HolKernel Parse boolLib bossLib;

val _ = new_theory "wfgenl";


Definition mk_FALLL_def:
mk_FALLL [] b = b ∧
mk_FALLL ((n,s) :: vl) b = mk_FALL n s (mk_FALLL vl b)
End




Theorem mk_FALL_FALLL0:
∀k n s sl b i. LENGTH sl = k ⇒ 
(fabs (n,s) i (FALLL sl b)) =
 FALLL (abssl (n,s) i sl) (fabs (n,s) (i + LENGTH sl) b)
Proof
Induct_on ‘k’ >> Cases_on ‘sl’ >> gs[FALLL_def,abssl_def] >>
rw[] >> simp[fabs_def,arithmeticTheory.ADD1]
QED

 
        
Theorem fVslfv_mk_FALL:
fVslfv (mk_FALL n s b) = fVslfv b
Proof
rw[mk_FALL_def,fVslfv_fabs,abst_def,fVslfv_def,fVars_def,fVars_fabs]
QED


Theorem fVslfv_mk_FALLL:
∀k vl f. LENGTH vl = k ⇒
fVslfv (mk_FALLL vl f) = fVslfv f
Proof
Induct_on ‘k’ >> Cases_on ‘vl’ >> simp[mk_FALLL_def] >>
Cases_on ‘h’ >> gs[mk_FALLL_def,fVslfv_mk_FALL]
QED




Theorem DIFF_of_UNION:
(A ∪ B) DIFF C = A DIFF C ∪ B DIFF C
Proof
rw[EXTENSION] >> metis_tac[]
QED
        




Definition absvl_def:
absvl i v [] = [] ∧
absvl i v ((n:string,s) :: t) = 
(n,sabs v i s) :: (absvl (i+1) v t)
End

Definition vl2sl0_def:
  vl2sl0 [] = [] ∧
  vl2sl0 (v :: vs) = v :: absvl 0 v (vl2sl0 vs)
End

Definition vl2sl_def:
  vl2sl vl = MAP SND (vl2sl0 vl)
End


Theorem fVars_mk_FALL:
fVars (mk_FALL n s b) = fVars b
Proof
simp[mk_FALL_def,fVars_fabs,abst_def,fVars_def]
QED


Theorem fVars_mk_FALLL:
∀vl b. fVars (mk_FALLL vl b) = fVars b
Proof
Induct_on ‘vl’ >> gs[mk_FALLL_def,fVars_mk_FALL] >>
rw[] >> Cases_on ‘h’ >> simp[mk_FALLL_def,fVars_mk_FALL]
QED




(*parallel variable to bound*)
Definition tpv2b_def:
(tpv2b v2b (Var n s) = if (n,s) ∈ FDOM v2b then Bound (v2b ' (n,s))
                     else Var n s) ∧
(tpv2b v2b (Fn f s tl) =
Fn f (spv2b v2b s) (MAP (tpv2b v2b) tl)) ∧
(tpv2b v2b (Bound i) = Bound i) ∧
spv2b v2b (St n tl) = St n (MAP (tpv2b v2b) tl)
Termination
WF_REL_TAC
   ‘measure
    (λs. case s of
           INL (_,t) => term_size t
         | INR (_,st) => sort_size st)’   
End



(*parallel variable to bound*)

           
Definition vpv2b_def:
(vpv2b v2b (n,s) = if (n,s) ∈ FDOM v2b then Bound (v2b ' (n,s))
                     else Var n s)
End                     


                
Definition mk_v2b_def:
mk_v2b vl = TO_FMAP (ZIP (vl,COUNT_LIST (LENGTH vl)))
End


Theorem FAPPLY_mk_v2b:
ALL_DISTINCT vl ⇒
∀n. n < LENGTH vl ⇒ (mk_v2b vl) ' (EL n vl) = n
Proof
rw[mk_v2b_def] >> irule TO_FMAP_MEM >>
simp[MEM_EL,PULL_EXISTS] >> qexists ‘n’ >>
‘LENGTH (COUNT_LIST (LENGTH vl)) = LENGTH vl’
 by simp[rich_listTheory.LENGTH_COUNT_LIST] >>
pop_assum $ assume_tac o GSYM >>  
drule_then assume_tac EL_ZIP >>
first_x_assum $ drule_then assume_tac >> gs[] >>
simp[rich_listTheory.EL_COUNT_LIST] >>
‘(MAP FST (ZIP (vl,COUNT_LIST (LENGTH vl)))) = vl’
 suffices_by metis_tac[] >>
‘ MAP (I ∘ FST) (ZIP (vl,COUNT_LIST (LENGTH vl))) = MAP I vl’
 by (irule $ cj 3 MAP_ZIP >> simp[]) >> gs[]
QED 




(*
Definition mk_v2b_def:
mk_v2b vl = TO_FMAP (ZIP (REVERSE vl,COUNT_LIST (LENGTH vl)))
End


Theorem FAPPLY_mk_v2b:
ALL_DISTINCT vl ⇒
∀n. n < LENGTH vl ⇒ (mk_v2b vl) ' (EL n vl) = LENGTH vl - SUC n
Proof
rw[mk_v2b_def] >> irule TO_FMAP_MEM >>
simp[MEM_EL,PULL_EXISTS] >> qexists ‘LENGTH vl - SUC n’ >>
‘LENGTH (COUNT_LIST (LENGTH vl)) = LENGTH (REVERSE vl)’
 by simp[rich_listTheory.LENGTH_COUNT_LIST] >>
pop_assum $ assume_tac o GSYM >>  
drule_then assume_tac EL_ZIP >>
first_x_assum $ drule_then assume_tac >> gs[] >>
simp[rich_listTheory.EL_COUNT_LIST] >>
‘(MAP FST (ZIP (vl,COUNT_LIST (LENGTH vl)))) = vl’
 suffices_by metis_tac[] >>
‘ MAP (I ∘ FST) (ZIP (vl,COUNT_LIST (LENGTH vl))) = MAP I vl’
 by (irule $ cj 3 MAP_ZIP >> simp[]) >> gs[]
QED 
*)

        
Definition fpv2b_def:
fpv2b v2b (Pred p tl) = Pred p (MAP (tpv2b v2b) tl) ∧
fpv2b v2b (IMP f1 f2) = IMP (fpv2b v2b f1) (fpv2b v2b f2) ∧
fpv2b v2b (fVar p sl tl) = fVar p sl (MAP (tpv2b v2b) tl) ∧
fpv2b v2b (FALL s b) = FALL (spv2b v2b s) (fpv2b v2b b)
End


(*        
Theorem mk_FALLL_FALLL:
  wfabsvlof Σ vl f ⇒
  mk_FALLL vl ( = FALLL (vl2sl vl) (
Proof
*)


Theorem vl2sl_EMPTY:
vl2sl [] = []
Proof
simp[vl2sl_def,vl2sl0_def]
QED 


Theorem TAKE_LAST:
l ≠ [] ⇒ TAKE (LENGTH l − 1) l ⧺ [LAST l] = l
Proof
rw[] >>
‘LENGTH l ≠ 0’ by simp[] >>
‘1 + (LENGTH l - 1) = LENGTH l’ by simp[] >>
drule_then assume_tac rich_listTheory.APPEND_TAKE_LASTN >>
drule_then assume_tac rich_listTheory.LASTN_1 >> gs[]
QED

Theorem mk_FALL_FALLL:
mk_FALL n s (FALLL sl b) =
FALLL (s :: (abssl (n,s) 0 sl)) (fabs (n,s) (LENGTH sl) b)
Proof
qspecl_then [‘LENGTH sl’,‘n’,‘s’,‘sl’,‘b’,‘0’] assume_tac
mk_FALL_FALLL0 >> gs[mk_FALL_def,abst_def] >>
simp[FALLL_def]
QED

Theorem MAP_SND_absvl0:
∀k l v i. LENGTH l = k ⇒
          MAP SND (absvl i v l) = abssl v i (MAP SND l)
Proof
Induct_on ‘k’
>- (rw[] >> Cases_on ‘v’ >> simp[absvl_def,abssl_def])
>- (Cases_on ‘l’ >>  gs[] >> Cases_on ‘v’ >>  Cases_on ‘h’ >> 
   simp[absvl_def,abssl_def])
QED   


Theorem MAP_SND_absvl:
∀l v i. MAP SND (absvl i v l) = abssl v i (MAP SND l)
Proof
rw[] >>
qspecl_then [‘LENGTH l’,‘l’,‘v’,‘i’] assume_tac MAP_SND_absvl0 >>
gs[]
QED   


      
Theorem vl2sl_CONS:
vl2sl (v :: vl) = (SND v) :: (abssl v 0 (vl2sl vl))
Proof
Cases_on ‘v’ >> simp[vl2sl_def,vl2sl0_def] >>
Cases_on ‘vl’
>- simp[vl2sl0_def,absvl_def,abssl_def] >>
simp[vl2sl0_def,absvl_def] >> Cases_on ‘h’ >>
simp[absvl_def] >> simp[abssl_def] >>
simp[MAP_SND_absvl]
QED


Theorem LENGTH_absvl:
∀i v.LENGTH (absvl i v l) = LENGTH l
Proof        
Induct_on ‘LENGTH l’ >> rw[] >> gs[absvl_def] >>
Cases_on ‘l’
>- simp[absvl_def] >>
Cases_on ‘v'’ >> simp[absvl_def] >> gs[] >>
Cases_on ‘h’ >> simp[absvl_def]
QED

Theorem LENGTH_vl2sl0:
LENGTH (vl2sl0 l) = LENGTH l
Proof
Induct_on ‘LENGTH l’ >> gs[vl2sl0_def] >>
Cases_on ‘l’ >- gs[] >>
gs[] >> simp[vl2sl0_def,LENGTH_absvl]
QED 

Theorem LENGTH_vl2sl:
∀l.LENGTH (vl2sl l) = LENGTH l
Proof
strip_tac >> Induct_on ‘LENGTH l’ >> rw[vl2sl_def,vl2sl0_def] >>
Cases_on ‘l’ >> gs[] >> Cases_on ‘h’ >>
rw[vl2sl_def,vl2sl0_def] >> simp[LENGTH_absvl] >>
simp[LENGTH_vl2sl0]
QED



Theorem tabs_tpv2b:
(∀tm v2b n s i.
   (n,s) ∉ FDOM v2b ⇒
   tabs (n,s) i (tpv2b v2b tm) =
   tpv2b (v2b |+ ((n,s),i)) tm) ∧
(∀st v2b n s i.
   (n,s) ∉ FDOM v2b ⇒ 
   sabs (n,s) i (spv2b v2b st) =
   spv2b (v2b |+ ((n,s),i)) st)   
Proof   
ho_match_mp_tac better_tm_induction>>
gs[tabs_def,tpv2b_def,MAP_MAP_o,MAP_EQ_f] >> rw[] >>
Cases_on ‘(s0,st) ∈ FDOM v2b’ >> gs[tabs_def,FAPPLY_FUPDATE_THM]
(* 2 *)
>-  (‘¬(s0 = n ∧ st = s)’ by (CCONTR_TAC >> gs[]) >>simp[]) >>
Cases_on ‘n = s0 ∧ s = st’ >> simp[] >>
Cases_on ‘ s0 = n ∧ st = s’ >> simp[] >> gs[]
QED



Theorem vpv2b_tpv2b:
vpv2b v2b (n,s) = tpv2b v2b (Var n s)
Proof
rw[vpv2b_def,tpv2b_def]
QED
        
        
Theorem FDOM_mk_v2b:
FDOM (mk_v2b l) = set l
Proof
simp[mk_v2b_def,FDOM_TO_FMAP] >> 
‘LENGTH l  = LENGTH (COUNT_LIST (LENGTH l))’
 by simp[rich_listTheory.LENGTH_COUNT_LIST] >>
AP_TERM_TAC >>
‘ MAP (I o FST) (ZIP (l,COUNT_LIST (LENGTH l))) = MAP I l’
 suffices_by simp[] >>
irule $ cj 3 MAP_ZIP >> simp[] 
QED 


Theorem FAPPLY_mk_v2b_APPEND:
n < LENGTH l1 ∧ ALL_DISTINCT (l1 ++ l2) ⇒
mk_v2b (l1 ++ l2) ' (EL n l1) = mk_v2b l1 ' (EL n l1)
Proof
rw[]>>
‘ALL_DISTINCT l1’ by gs[ALL_DISTINCT_APPEND] >>
drule_then assume_tac FAPPLY_mk_v2b >>
first_x_assum $ drule_then assume_tac >>
rev_drule_then assume_tac FAPPLY_mk_v2b >>
first_x_assum $ qspecl_then [‘n’] assume_tac >> gs[] >>
drule_then assume_tac rich_listTheory.EL_APPEND1 >> gs[]
QED

Theorem mk_v2b_FUPDATE:
ALL_DISTINCT vl ∧ ¬ MEM h vl ⇒ mk_v2b (vl ++ [h]) = (mk_v2b vl) |+ (h,LENGTH vl)
Proof
simp[fmap_EXT,FDOM_mk_v2b] >>
‘h INSERT set vl = {h} ∪ set vl’ by simp[Once INSERT_SING_UNION] >>
simp[] >> simp[SimpLHS,Once UNION_COMM] >> strip_tac >>
‘ALL_DISTINCT (vl ++ [h])’ by simp[ALL_DISTINCT_APPEND] >>
drule_then assume_tac FAPPLY_mk_v2b >>
simp[MEM_EL,PULL_EXISTS] >> rw[] (* 2 *)
>- (first_x_assum $ qspecl_then [‘n’] assume_tac >> gs[] >>
   ‘MEM (EL n vl) vl’ by (simp[MEM_EL] >> metis_tac[]) >>
   ‘EL n vl ≠ h’ by metis_tac[] >>
   simp[FAPPLY_FUPDATE_THM] >> metis_tac[FAPPLY_mk_v2b_APPEND]) >>
simp[FAPPLY_FUPDATE_THM] >>
‘LENGTH vl < LENGTH (vl ++ [h])’ by simp[] >>
drule_then assume_tac FAPPLY_mk_v2b >>
first_x_assum $ drule_then assume_tac >>
‘(EL (LENGTH vl) (vl ⧺ [h])) = h’ suffices_by metis_tac[] >>
‘LENGTH vl ≤ LENGTH vl’ by simp[] >>
drule_then assume_tac rich_listTheory.EL_APPEND2 >>
first_x_assum $ qspecl_then [‘[h]’] assume_tac>> gs[]
QED
   
        


        
Theorem mk_v2b_EMPTY_FUPDATE:
(mk_v2b [] |+ ((q,r),0)) = (mk_v2b [(q,r)])
Proof
simp[fmap_EXT,FDOM_mk_v2b,mk_v2b_def] >>
‘LENGTH [(q,r)] = LENGTH (COUNT_LIST 1)’
 by simp[rich_listTheory.LENGTH_COUNT_LIST] >>
irule TO_FMAP_MEM >>
qspecl_then [‘COUNT_LIST 1’,‘[(q,r)]’,‘I’] assume_tac
(GEN_ALL $ cj 3 $ MAP_ZIP) >>
gs[] >>
‘COUNT_LIST 1 = [0]’ by EVAL_TAC >>
gs[]
QED

Theorem ALL_DISTINCT_TAKE:
ALL_DISTINCT l ⇒ ∀n. n < LENGTH l ⇒ ALL_DISTINCT (TAKE n l)
Proof
simp[EL_ALL_DISTINCT_EL_EQ] >> rw[] >>
qspecl_then [‘n’,‘n1’] assume_tac EL_TAKE >>
qspecl_then [‘n’,‘n2’] assume_tac EL_TAKE >>
gs[]
QED


        
Theorem mk_FALLL_fVar:
∀k vl0.
LENGTH vl0 = k ∧ ALL_DISTINCT vl0 ⇒ 
mk_FALLL (REVERSE vl0) (fVar P sl (MAP Var' vl)) =
FALLL (vl2sl (REVERSE vl0))
(fVar P sl (MAP (vpv2b (mk_v2b vl0)) vl))
Proof
Induct_on ‘k’
>- (simp[mk_v2b_def,rich_listTheory.COUNT_LIST_def,mk_FALLL_def,
        FALLL_def,vl2sl_EMPTY] >>
   simp[MAP_EQ_f] >> rw[] >> Cases_on ‘e’ >>
   simp[vpv2b_def,FDOM_TO_FMAP]) >>
Cases_on ‘vl0’ >> gs[] >> rw[] >>
Cases_on ‘t= []’ >> gs[]
>- (Cases_on ‘h’ >>
   simp[mk_FALLL_def,FALLL_def,vl2sl_EMPTY,vl2sl_def,mk_FALL_def,
        vl2sl0_def,absvl_def,abst_def,fabs_def,
        MAP_MAP_o,MAP_EQ_f] >> rw[] >> Cases_on ‘e’ >>
   simp[vpv2b_tpv2b] >>
   qspecl_then [‘(Var q' r')’,‘(mk_v2b [])’,‘q’,‘r’,‘0’]
   assume_tac $ cj 1 tabs_tpv2b >>
   gs[FDOM_mk_v2b] >> simp[mk_v2b_EMPTY_FUPDATE]) >> 
‘LENGTH t ≠ 0’ by simp[] >>
‘SUC (LENGTH t − 1) = LENGTH t’ by simp[] >>
gs[] >>
qabbrev_tac ‘t1 = (TAKE (LENGTH t − 1) t)’ >> 
‘(REVERSE t ⧺ [h]) = LAST t :: (REVERSE t1 ⧺ [h])’
by (simp[Abbr‘t1’] >>
‘REVERSE (REVERSE t) = REVERSE
(LAST t::REVERSE (TAKE (LENGTH t − 1) t))’
by (REWRITE_TAC[REVERSE_REVERSE] >>
   simp[REVERSE_DEF] >>
   simp[TAKE_LAST]) >> gs[]) >>
gs[] >>
qabbrev_tac ‘v = LAST t’ >> Cases_on ‘v’ >>
simp[mk_FALLL_def] >>
first_x_assum $ qspecl_then [‘h :: t1’] assume_tac >>
‘¬MEM h t1 ∧ ALL_DISTINCT t1’
 by (simp[Abbr‘t1’] >> rw[] (* 2 *)
    >- (CCONTR_TAC >> gs[] >>
       drule rich_listTheory.MEM_TAKE >> gs[]) >>
    irule ALL_DISTINCT_TAKE >> simp[]) >> gs[] >> 
‘LENGTH (h::t1) = LENGTH t ’ by simp[Abbr‘t1’] >> gs[] >>
simp[mk_FALL_FALLL] >> simp[vl2sl_CONS] >>
simp[LENGTH_vl2sl] >>
AP_TERM_TAC >> simp[fabs_def,MAP_MAP_o,MAP_EQ_f] >> rw[] >>
Cases_on ‘e’ >> simp[vpv2b_tpv2b] >>
‘t = t1 ++ [(q,r)]’
 by (simp[Abbr‘t1’] >>
    qpat_x_assum ‘LAST t = (q,r)’ (assume_tac o GSYM) >> simp[] >>
    simp[TAKE_LAST]) >>
simp[] >>
‘(h::(t1 ⧺ [(q,r)])) = (h::t1) ⧺ [(q,r)]’ by simp[] >>
pop_assum SUBST_ALL_TAC >> 
‘(mk_v2b (h::t1 ⧺ [(q,r)])) =
 (mk_v2b (h::t1)) |+ ((q,r),LENGTH (h :: t1))’
 by (irule mk_v2b_FUPDATE >> simp[ALL_DISTINCT] >> rw[] (* 2 *)
    >- (CCONTR_TAC >> gs[]) >>
    ‘ALL_DISTINCT (REVERSE (t1 ⧺ [(q,r)]))’
     by simp[ALL_DISTINCT_REVERSE] >>
    qpat_x_assum ‘ALL_DISTINCT (t1 ⧺ [(q,r)])’ (K all_tac) >>
    qpat_x_assum ‘REVERSE (t1 ⧺ [(q,r)]) = (q,r)::REVERSE t1’
    SUBST_ALL_TAC >>
    gs[ALL_DISTINCT]) >>
pop_assum SUBST_ALL_TAC >>
‘LENGTH (h::t1) = LENGTH t1 + 1’ by simp[] >>
pop_assum SUBST_ALL_TAC >>
irule $ cj 1 tabs_tpv2b >> simp[FDOM_mk_v2b] >>
gs[] >> gs[ALL_DISTINCT_APPEND]
QED




Theorem mk_FALLL_fVar1:
ALL_DISTINCT vl ⇒
     mk_FALLL vl (fVar P sl (MAP Var' vl)) =
     FALLL (vl2sl vl) (fVar P sl (MAP (vpv2b (mk_v2b (REVERSE vl))) vl))
Proof     
metis_tac[mk_FALLL_fVar |> Q.SPECL [‘LENGTH vl’,‘REVERSE vl’]
              |> SRULE [EQ_REFL]]
QED              



Theorem vpv2b_mk_v2b_EL:
ALL_DISTINCT vl ∧ x < LENGTH vl ⇒
vpv2b (mk_v2b vl) (EL x vl) = Bound x
Proof
rw[] >> Cases_on ‘EL x vl’ >> rw[vpv2b_def,FDOM_mk_v2b] (* 2 *)
>- (drule_all_then assume_tac FAPPLY_mk_v2b >> gs[]) >>
gs[MEM_EL]
QED
        


Theorem fVar_MAP_vpv2b:
ALL_DISTINCT vl ⇒ (MAP (vpv2b (mk_v2b vl)) (REVERSE vl)) =
(MAP Bound (REVERSE (COUNT_LIST (LENGTH vl))))
Proof
rw[] >> 
irule LIST_EQ >> simp[rich_listTheory.LENGTH_COUNT_LIST] >>
rw[] >> simp[EL_MAP] >>
‘LENGTH (COUNT_LIST (LENGTH vl)) = LENGTH vl’ by
simp[rich_listTheory.LENGTH_COUNT_LIST] >>
‘LENGTH (REVERSE (COUNT_LIST (LENGTH vl))) = LENGTH vl’ by simp[] >>
simp[EL_MAP] >>
drule_all_then assume_tac vpv2b_mk_v2b_EL >> gs[] >>
simp[EL_REVERSE] >> simp[Once EQ_SYM_EQ] >>
‘(PRE (LENGTH vl − x)) < LENGTH vl’ by simp[] >>
drule_all_then assume_tac vpv2b_mk_v2b_EL >> gs[] >>
irule rich_listTheory.EL_COUNT_LIST >> simp[]
QED


        
Theorem mk_FALLL_fVar_FALLL:
∀vl. ALL_DISTINCT vl ⇒
mk_FALLL vl (fVar P (vl2sl vl) (MAP Var' vl)) =
FALLL (vl2sl vl) (plainfV (P,(vl2sl vl)))
Proof
rw[] >>
qspecl_then [‘vl2sl vl’,‘LENGTH vl’,‘REVERSE vl’] assume_tac (Q.GEN ‘sl’ mk_FALLL_fVar) >> gs[] >> AP_TERM_TAC >>
simp[plainfV_def] >> simp[LENGTH_vl2sl] >>
‘ALL_DISTINCT (REVERSE vl)’ by simp[] >>
drule_all_then assume_tac fVar_MAP_vpv2b >> gs[]
QED



Definition wfdpvl_def:
(wfdpvl [] f ⇔ T) ∧
(wfdpvl (v :: vs) f ⇔
  wfdpvl vs f ∧
  v ∉ fVslfv f ∧
  ∀n s. (n,s) ∈ ffv (mk_FALLL vs f) ⇒
  v ∉ sfv s)
End

Definition wfvl_def:
  wfvl Σ vl f ⇔ wfdpvl vl f ∧
                ∀v. MEM v vl ⇒ wfs Σ (SND v)
End


Theorem fVslfv_mk_FALLL1:
fVslfv (mk_FALLL vl f) = fVslfv f
Proof
metis_tac[fVslfv_mk_FALLL]
QED

Theorem mk_FALLL_fVar_wff:
∀f.
wff Σ f ∧ wfvl (FST Σ) vl f ⇒ 
wff Σ (mk_FALLL vl f)
Proof
Induct_on ‘LENGTH vl’
>- rw[mk_FALLL_def] >>
Cases_on ‘vl’ >> simp[] >>
Cases_on ‘h’ >> simp[wfvl_def,mk_FALLL_def] >>
rw[] >> Cases_on ‘Σ’ >> Cases_on ‘r'’ >>
irule $ cj 6 wff_rules >>
rename [‘(Σf,Σp,Σe)’] >> gs[] >> gs[wfdpvl_def] >>
‘wff (Σf,Σp,Σe) (mk_FALLL t f)’
 by (first_x_assum irule >> simp[] >>
    simp[wfvl_def]) >> simp[] >>
‘wfs Σf r’ by gs[DISJ_IMP_THM] >> simp[fVslfv_mk_FALLL1] >>
metis_tac[]
QED 


(*    

mk_FALLL_fVar_FALLL    

∀k vl0.
LENGTH vl0 = k ∧ ALL_DISTINCT vl0 ⇒ 
mk_FALLL (REVERSE vl0) (fVar P sl (MAP Var' vl)) =
FALLL (vl2sl (REVERSE vl0))
(fVar P sl (MAP (vpv2b (mk_v2b vl0)) vl))    


mk_FALLL_fVar1
mk_FALLL_fVar
*)

Theorem fabs_TRUE:
fabs v i TRUE = TRUE
Proof
rw[TRUE_def,fabs_def]
QED        
        

Theorem mk_FALLL_TRUE:
(mk_FALLL t TRUE) = FALLL (vl2sl t) TRUE
Proof
Induct_on ‘LENGTH t’
>- simp[vl2sl_def,vl2sl0_def,FALLL_def,mk_FALLL_def] >>
Cases_on ‘t’ >> simp[] >>
simp[vl2sl_CONS,mk_FALLL_def,FALLL_def] >>
Cases_on ‘h’ >> simp[mk_FALLL_def] >> rw[] >>
simp[mk_FALL_def,abst_def] >>
qspecl_then [‘LENGTH t'’,‘q’,‘r’,‘vl2sl t'’,‘TRUE’,‘0’]
assume_tac mk_FALL_FALLL0 >>
gs[LENGTH_vl2sl, fabs_TRUE]
QED

Theorem ffv_TRUE:
ffv TRUE = {}
Proof
simp[TRUE_def]
QED        
        

Theorem tfv_tpv2b_SUBSET:
(∀tm v2b. tfv (tpv2b v2b tm) ⊆ tfv tm) ∧
(∀st v2b. sfv (spv2b v2b st) ⊆ sfv st)
Proof
ho_match_mp_tac better_tm_induction >>
simp[tfv_thm,tpv2b_def,MEM_MAP,MAP_EQ_f] >>
rw[] (* 4 *)
>- (Cases_on ‘(s0,st) ∈ FDOM v2b’ >> simp[])
>> (gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[])
QED 
        
Theorem tlfv_MAP_Bound_EMPTY:
tlfv (MAP Bound l) = {}
Proof
rw[tlfv_def]>> Cases_on ‘l’ >> simp[] >>
disj2_tac >> simp[MEM_MAP] >>
simp[Once EXTENSION,PULL_EXISTS] >>
rw[] >> rw[EQ_IMP_THM,tfv_thm] (* 3 *)
>- simp[tfv_thm]
>- simp[tfv_thm] >>
qexists ‘Bound h’ >> simp[]
QED


Theorem slfv_alt:
slfv vl = BIGUNION {sfv v | MEM v vl}
Proof
simp[Once EXTENSION,IN_slfv] >> rw[] >>
Cases_on ‘x’ >> simp[IN_slfv] >> metis_tac[]
QED

        
Theorem tfv_tabs_SUBSET1:
(∀tm n s i.tfv (tabs (n,s) i tm) ⊆ tfv tm) ∧
(∀st n s i.sfv (sabs (n,s) i st) ⊆ sfv st)
Proof
ho_match_mp_tac better_tm_induction >>
simp[tfv_thm,tabs_def] >> rw[] (* 4 *)
>- (Cases_on ‘n = s0 ∧ s = st’ >> simp[SUBSET_DEF])
>> (gs[SUBSET_DEF,MEM_MAP] >> metis_tac[])
QED


Theorem slfv_CONS:
slfv (s :: sl) = sfv s ∪ slfv sl
Proof
simp[slfv_alt] >> rw[Once EXTENSION] >> metis_tac[]
QED





Theorem slfv_abssl:
(∀n s. (n,s) ∈ slfv sl ⇒ (q,r) ∉ sfv s) ∧
(q,r) ∈ slfv sl ⇒
sfv r ∪ slfv (abssl (q,r) 0 sl) = slfv sl DELETE (q,r)
Proof
rw[] >> gs[IN_slfv] >>
irule $ iffLR SUBSET_ANTISYM_EQ >> rw[] (* 3 *)
>- (simp[SUBSET_DEF]>> Cases_on ‘x’ >>
   simp[IN_slfv,PULL_EXISTS] >> metis_tac[vsort_tfv_closed])
>- (simp[SUBSET_DEF] >> Cases_on ‘x’ >>
   simp[IN_slfv,PULL_EXISTS,MEM_EL,LENGTH_abssl] >> rw[] >>
   drule_then assume_tac abssl_EL>> gs[] >>
   qspecl_then [‘n’,‘EL n sl’,‘q’,‘r’,‘tt’]
   assume_tac $ Q.GEN ‘i’
   $ cj 2 tfv_tabs_SUBSET >>
   qexists ‘n’ >> simp[]>>
   ‘sfv (sabs (q,r) n (EL n sl)) ⊆ sfv (EL n sl) DELETE (q,r)’
    by metis_tac[MEM_EL] >>
   gs[SUBSET_DEF] >> first_x_assum $ drule_then assume_tac >>
   gs[]) >>
gs[SUBSET_DEF] >> Cases_on ‘x’ >>
simp[IN_slfv]>> rw[] >> gs[MEM_EL]>>
drule_then assume_tac abssl_EL >> simp[LENGTH_abssl] >>
simp[PULL_EXISTS]>>
Cases_on ‘(q,r) ∈ sfv (EL n' sl)’
>- (qspecl_then [‘n'’,‘(EL n' sl)’,‘q’,‘r’] assume_tac
$ Q.GEN ‘i’ $ cj 2 tfv_tabs >>
‘sfv r ∪ sfv (sabs (q,r) n' (EL n' sl)) = sfv (EL n' sl) DELETE (q,r)’
 by (first_x_assum irule >> simp[] >>
    metis_tac[]) >>
   pop_assum (assume_tac o GSYM) >>
   ‘(q',r') ∈ sfv (EL n' sl) DELETE (q,r)’ by gs[] >>
   qpat_x_assum ‘_ = _’ SUBST_ALL_TAC >> gs[] >>
   disj2_tac >> qexists ‘n'’ >>
   first_x_assum $ qspecl_then [‘q’,‘r’,‘0’] assume_tac >>
   gs[]) >>
disj2_tac >> qexists ‘n'’ >> simp[] >>
drule_then assume_tac $ cj 2 tabs_id  >> simp[]
QED
 


Theorem wfdpvl_ffv_mk_FALLL:
∀f. wfdpvl vl f ⇒
ffv (mk_FALLL vl f) = slfv (vl2sl vl) ∪ (ffv f DIFF set vl)
Proof
Induct_on ‘LENGTH vl’
>- (rw[] >>
    simp[mk_FALLL_def,slfv_def,vl2sl_EMPTY,Uof_EMPTY]) >>
Cases_on ‘vl’ >> simp[] >>
Cases_on ‘h’ >> simp[mk_FALLL_def,wfdpvl_def] >>
rw[] >>
first_x_assum $ qspecl_then [‘t’] assume_tac >>
gs[] >>
first_x_assum $ drule_then assume_tac >>
qspecl_then [‘(mk_FALLL t f)’,‘q’,‘r’] assume_tac
ffv_mk_FALL >> gs[] >>
‘ffv (mk_FALL q r (mk_FALLL t f)) =
        slfv (vl2sl t) ∪ (ffv f DIFF set t) ∪ sfv r DELETE (q,r)’ suffices_by
 (rw[] >> simp[vl2sl_CONS] >>
 simp[slfv_CONS] >>
 reverse (Cases_on ‘(q,r) ∈ slfv (vl2sl t)’) (* 2 *)
 >- (‘abssl (q,r) 0 (vl2sl t) = vl2sl t’
      by (irule abssl_id >> gs[IN_slfv] >> metis_tac[]) >>
    simp[]>>
    irule $ iffLR SUBSET_ANTISYM_EQ >>
  simp[SUBSET_DEF,PULL_EXISTS] >> rw[] (* 4 *)
     >- metis_tac[]
     >- metis_tac[]
     >- metis_tac[] >>
     metis_tac[tm_tree_WF]) >> 
 ‘sfv r ∪ slfv (abssl (q,r) 0 (vl2sl t)) ∪
        (ffv f DIFF ((q,r) INSERT set t)) =
 sfv r ∪ (sfv r ∪ slfv (abssl (q,r) 0 (vl2sl t))) ∪
        (ffv f DIFF ((q,r) INSERT set t))’
    by (rw[Once EXTENSION] >> metis_tac[]) >>
 pop_assum SUBST_ALL_TAC >>
 ‘sfv r ∪ slfv (abssl (q,r) 0 (vl2sl t)) =
 (slfv (vl2sl t) DELETE (q,r))’ suffices_by
  (rw[]>> irule $ iffLR SUBSET_ANTISYM_EQ >>
  simp[SUBSET_DEF,PULL_EXISTS] >> rw[] (* 4 *)
     >- metis_tac[]
     >- metis_tac[]
     >- metis_tac[] >>
     metis_tac[tm_tree_WF]) >>
  gs[DISJ_IMP_THM] >>
  irule slfv_abssl >> simp[] >> metis_tac[]) >>
first_x_assum irule >> simp[fVars_mk_FALLL]>>
rw[] (* 3 *)
>- (gs[IN_fVslfv] >> metis_tac[]) >>
metis_tac[]
QED

(*
Theorem wfdpvl_alt:
wfdpvl [] f = T ∧
wfdpvl         
*)


Definition okvnames_def:
okvnames vl ⇔
∀m n. m < n ∧ n < LENGTH vl ⇒ EL n vl ∉ sfv (SND (EL m vl))
End

Theorem okvnames_CONS:
okvnames (h :: t) ⇔ okvnames t ∧
∀v. MEM v t ⇒ v ∉ sfv (SND h)
Proof
simp[okvnames_def,EQ_IMP_THM] >>
rw[] (* 3 *)
>- (first_x_assum $ qspecl_then [‘SUC m’,‘SUC n’] assume_tac
   >> gs[])
>- (gs[MEM_EL] >>
   first_x_assum $ qspecl_then [‘0’,‘SUC n’] assume_tac >>
   gs[]) >>
Cases_on ‘n < LENGTH t’ (* 2 *)
>- (Cases_on ‘m’ >> gs[] >> Cases_on ‘n’ >> gs[MEM_EL] >>
   first_x_assum irule >> qexists ‘n'’ >> simp[]) >>
Cases_on ‘m’ >> Cases_on ‘n’ >>  gs[MEM_EL] >>
metis_tac[]
QED

        
Theorem wfdpvl_expand:
∀f. wfdpvl vl f ∧ okvnames vl ⇒
∀f1. (∀n s. (n,s) ∈ ffv f1 DIFF ffv f ⇒
            ∀v. MEM v vl ⇒ v ∉ sfv s) ∧
     (∀v. MEM v vl ⇒ v ∉ fVslfv f1) ⇒
wfdpvl vl f1
Proof
Induct_on ‘vl’
>- simp[okvnames_def,wfdpvl_def] >>
Cases_on ‘h’ >> simp[wfdpvl_def,okvnames_CONS] >>
rw[] (* 2 *)
>- (first_x_assum irule >> simp[] >>
   metis_tac[]) >>
‘wfdpvl vl f1’ by
  (first_x_assum irule >> simp[] >>
   metis_tac[]) >>
‘ffv (mk_FALLL vl f) = slfv (vl2sl vl) ∪ (ffv f DIFF set vl)’
 by metis_tac[wfdpvl_ffv_mk_FALLL] >>
pop_assum SUBST_ALL_TAC >>
gs[DISJ_IMP_THM] >>
‘ffv (mk_FALLL vl f1) = slfv (vl2sl vl) ∪ (ffv f1 DIFF set vl)’
 by metis_tac[wfdpvl_ffv_mk_FALLL] >>
pop_assum SUBST_ALL_TAC >> gs[]
>- metis_tac[] >>
metis_tac[]
QED




Theorem tlfv_CONS:
tlfv (t :: tl) = tfv t ∪ tlfv tl
Proof
simp[tlfv_def] >> rw[Once EXTENSION] >> metis_tac[]
QED     

Theorem slfv_abssl_SUBSET:
slfv (abssl h i sl) ⊆ slfv sl
Proof
simp[slfv_alt,SUBSET_DEF,PULL_EXISTS,MEM_EL,LENGTH_abssl] >>
rw[] >>
Cases_on ‘h’ >> gs[LENGTH_abssl] >>
drule_then assume_tac abssl_EL >>
gs[] >>
qspecl_then [‘EL n sl’,‘q’,‘r’,‘i + n’] assume_tac
$ cj 2 tfv_tabs_SUBSET1 >> gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >>
metis_tac[]
QED

        
Theorem slfv_vl2sl_SUBSET:
slfv (vl2sl vl) ⊆ tlfv (MAP Var' vl)
Proof
Induct_on ‘LENGTH vl’
>- rw[vl2sl_EMPTY,slfv_alt] >>
Cases_on ‘vl’ >> simp[] >> rw[] >> 
simp[vl2sl_CONS,tlfv_CONS,slfv_CONS]>> rw[]  (* 2 *) 
>- (Cases_on ‘h’ >> simp[tfv_thm,SUBSET_DEF]) >>
first_x_assum $ qspecl_then [‘t’] assume_tac >>
gs[] >>
irule SUBSET_TRANS >> qexists ‘tlfv (MAP Var' t)’ >> simp[] >>
irule SUBSET_TRANS >> first_x_assum $ irule_at Any >>
simp[slfv_abssl_SUBSET]
QED



Theorem NOTIN_slfv_abssl:
(∀n s. (n,s) ∈ slfv sl ⇒ v ∉ sfv s) ⇒
v ∉ slfv (abssl v i sl)
Proof
rw[slfv_alt,PULL_EXISTS] >>
Cases_on ‘MEM v' (abssl v i sl)’ >> gs[] >>
gs[MEM_EL] >> Cases_on ‘v’ >> gs[LENGTH_abssl] >>
drule_then assume_tac abssl_EL >>
gs[] >>
qspecl_then [‘i+ n’,‘EL n sl’, ‘q’,‘r’,‘tt’] assume_tac
$ Q.GEN ‘i’ $ cj 2 tfv_tabs_SUBSET >>
‘sfv (sabs (q,r) (i + n) (EL n sl)) ⊆ sfv (EL n sl) DELETE (q,r)’ by metis_tac[] >>
gs[SUBSET_DEF] >> strip_tac >> metis_tac[]
QED


        
Theorem wfdpvl_NOTIN_slfv:
∀f. wfdpvl vl f ∧ okvnames vl ⇒ ∀v. MEM v vl ⇒ v ∉ slfv (vl2sl vl)
Proof
Induct_on ‘LENGTH vl’
>- rw[vl2sl_EMPTY] >>
Cases_on ‘vl’ >> simp[] >>
Cases_on ‘h’ >> simp[wfdpvl_def,vl2sl_CONS,slfv_CONS,okvnames_CONS] >>
rw[] (* 4 *)
>- simp[tm_tree_WF]
>- (irule NOTIN_slfv_abssl >> rw[] >>
   first_x_assum irule >>
   qexists ‘n’ >> drule_then assume_tac wfdpvl_ffv_mk_FALLL >>
   simp[])
>- metis_tac[] >>
strip_tac >>
qspecl_then [‘vl2sl t’,‘0’,‘(q,r)’] assume_tac
(slfv_abssl_SUBSET |> GEN_ALL) >>
gs[SUBSET_DEF] >> first_x_assum $ drule_then assume_tac >>
pop_assum mp_tac >> simp[] >> first_x_assum irule >>
simp[] >> metis_tac[]
QED

        
Theorem fVslfv_fVar:
  fVslfv (fVar P sl tl) = slfv sl
Proof
  rw[fVslfv_def,fVars_def,Uof_Sing]
QED
        
(*
Theorem wfdpvl_ffv_fVar:
wfdpvl vl TRUE ∧ ALL_DISTINCT vl ∧ okvnames vl ⇒
ffv (mk_FALLL (DROP n vl) )
*)

        
Theorem vpv2b_NOTIN:
(n,s) ∉ FDOM v2b ⇒ vpv2b v2b (n,s) = Var n s
Proof
simp[vpv2b_def]
QED

        
Theorem ffv_FALLL_fVar_CONS:
  ffv (FALLL asl (fVar P (s:: sl) (t :: tl))) =
  slfv asl ∪ slfv sl ∪ tlfv tl ∪ sfv s ∪ tfv t
Proof
  rw[ffv_FALLL,Once EXTENSION,slfv_alt,tlfv_def] >>
  metis_tac[]
QED 

Theorem ffv_fVar_vl2sl:
ffv (fVar P (vl2sl vl) (MAP Var' vl)) = tlfv (MAP Var' vl)
Proof
simp[] >>
‘BIGUNION {tfv t | MEM t (MAP Var' vl)} = tlfv (MAP Var' vl)’
 by simp[tlfv_def] >>
 simp[] >> simp[GSYM SUBSET_UNION_ABSORPTION] >>
 simp[GSYM slfv_alt] >>
 simp[slfv_vl2sl_SUBSET]
QED

        
Theorem DIFF_of_UNION1:
A ∪ B DIFF C = (A DIFF C) ∪ (B DIFF C)
Proof
rw[Once EXTENSION] >> metis_tac[]
QED

Theorem DIFF_SUBSET:
A DIFF B = A ⇔ A ∩ B = {}
Proof
simp[Once EXTENSION] >> simp[Once EXTENSION] >> metis_tac[]
QED

Theorem fVar_CONS_ffv_DIFF:
ffv (fVar P (vl2sl (h :: t)) (MAP Var' (h :: t))) DIFF
ffv (fVar P (vl2sl t) (MAP Var' t)) =
tfv (Var' h) DIFF tlfv (MAP Var' t)
Proof
simp[Excl "ffv_thm",ffv_fVar_vl2sl] >>
simp[tlfv_CONS] >> simp[okvnames_CONS] >>
qspecl_then [‘tlfv (MAP Var' t)’,‘tlfv (MAP Var' t)’,‘tfv (Var' h)’] assume_tac $ GEN_ALL DIFF_of_UNION1 >>
pop_assum SUBST_ALL_TAC >>
‘tlfv (MAP Var' t) DIFF tlfv (MAP Var' t) = {}’
 by simp[] >>
pop_assum SUBST_ALL_TAC>>
simp[] >> rw[]
QED


Theorem fVar_CONS_ffv_DIFF1:
ffv (fVar P (vl2sl ((q,r) :: t)) (MAP Var' ((q,r) :: t))) DIFF
ffv (fVar P (vl2sl t) (MAP Var' t)) =
tfv (Var q r) DIFF tlfv (MAP Var' t)
Proof
REWRITE_TAC[fVar_CONS_ffv_DIFF] >> simp[] 
QED



        



Theorem wfdpvl_TRUE_fVar:
wfdpvl vl TRUE ∧ ALL_DISTINCT vl ∧ okvnames vl ⇒
wfdpvl vl (fVar P (vl2sl vl) (MAP Var' vl))
Proof
Induct_on ‘LENGTH vl’
>- rw[wfdpvl_def] >>
Cases_on ‘vl’ >> simp[] >>
Cases_on ‘h’ >> simp[wfdpvl_def,vl2sl_CONS,okvnames_CONS] >>
strip_tac >> strip_tac >>
simp[fVslfv_fVar,slfv_CONS,tm_tree_WF] >>
gs[mk_FALLL_TRUE,ffv_FALLL,PULL_EXISTS,ffv_TRUE] >>
‘(q,r) ∉ slfv (abssl (q,r) 0 (vl2sl t))’
 by (irule NOTIN_slfv_abssl >> simp[IN_slfv] >>
    metis_tac[]) >> simp[] >>    
‘wfdpvl t (fVar P (r::abssl (q,r) 0 (vl2sl t)) (Var q r::MAP Var' t))’
 suffices_by
  (rw[] >>
  qspecl_then [‘(q,r) :: t’,‘vl2sl ((q,r) :: t)’,‘P’,
               ‘LENGTH t’,‘REVERSE t’] assume_tac $ GEN_ALL mk_FALLL_fVar >> gs[] >>
  ‘(mk_FALLL t
             (fVar P (r::abssl (q,r) 0 (vl2sl t)) (Var q r::MAP Var' t))) =
   mk_FALLL t (fVar P (vl2sl ((q,r)::t)) (Var q r::MAP Var' t))’  by gs[vl2sl_CONS] >>
  pop_assum SUBST_ALL_TAC>>
  pop_assum SUBST_ALL_TAC >>
  qspecl_then [‘REVERSE t’] assume_tac $
              GEN_ALL fVar_MAP_vpv2b >> gs[]>>
  ‘vpv2b (mk_v2b (REVERSE t)) (q,r) = Var q r’               
    by (irule vpv2b_NOTIN >> simp[FDOM_mk_v2b]) >>
  pop_assum SUBST_ALL_TAC >> gs[vl2sl_CONS] >>
  qspecl_then [‘MAP Bound (REVERSE (COUNT_LIST (LENGTH t)))’,
    ‘Var q r’,‘abssl (q,r) 0 (vl2sl t)’,‘r’,‘vl2sl t’,‘P’]
    assume_tac $ GEN_ALL ffv_FALLL_fVar_CONS >>
  pop_assum SUBST_ALL_TAC >>
  qspecl_then [‘(REVERSE (COUNT_LIST (LENGTH t)))’]
  assume_tac $ GEN_ALL tlfv_MAP_Bound_EMPTY  >>
  pop_assum SUBST_ALL_TAC >>
  ‘slfv (abssl (q,r) 0 (vl2sl t)) ⊆ slfv (vl2sl t)’
    by irule slfv_abssl_SUBSET >>
  ‘slfv (vl2sl t) ∪ slfv (abssl (q,r) 0 (vl2sl t)) ∪ ∅ ∪ sfv r ∪
        tfv (Var q r) =
   slfv (vl2sl t) ∪ sfv r ∪ tfv (Var q r)’
  by (simp[] >>
     ‘slfv (vl2sl t) ∪ slfv (abssl (q,r) 0 (vl2sl t)) =
      slfv (vl2sl t)’  suffices_by metis_tac[] >>
     metis_tac[SUBSET_UNION_ABSORPTION,UNION_COMM]) >>
  pop_assum SUBST_ALL_TAC >>
  ‘slfv (vl2sl t) ∪ sfv r ∪ tfv (Var q r) =
   slfv (vl2sl t) ∪ tfv (Var q r)’
   by (simp[GSYM UNION_ASSOC] >> AP_TERM_TAC >>
      rw[Once EXTENSION] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  gs[] (* 3 *)
  >- (gs[IN_slfv] >> metis_tac[])
  >- simp[tm_tree_WF] >>
  metis_tac[vsort_tfv_closed,tm_tree_WF]) >>
‘wfdpvl t (fVar P (vl2sl t) (MAP Var' t))’
 by metis_tac[] >>
drule_then assume_tac wfdpvl_expand >>
first_x_assum $ qspecl_then [‘(fVar P (r::abssl (q,r) 0 (vl2sl t)) (Var q r::MAP Var' t))’] assume_tac >>
‘ffv (fVar P (r::abssl (q,r) 0 (vl2sl t)) (Var q r::MAP Var' t)) DIFF
           ffv (fVar P (vl2sl t) (MAP Var' t)) =
 tfv (Var q r) DIFF tlfv (MAP Var' t)’
  by
 (‘(r::abssl (q,r) 0 (vl2sl t)) = vl2sl ((q,r) :: t)’
  by simp[vl2sl_CONS] >>
  pop_assum SUBST_ALL_TAC>>
  ‘(Var q r::MAP Var' t) = MAP Var' ((q,r) :: t)’
  by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  metis_tac[fVar_CONS_ffv_DIFF1]) >>
 pop_assum SUBST_ALL_TAC >>
first_x_assum irule >>
simp[] >> simp[fVslfv_fVar,slfv_CONS] >>
rpt strip_tac (* 3 *)
>- gvs[]
>- (gvs[] >> metis_tac[vsort_tfv_closed]) >>
qspecl_then [‘vl2sl t’,‘0’,‘(q,r)’] assume_tac
 $ GEN_ALL slfv_abssl_SUBSET >>
metis_tac[wfdpvl_NOTIN_slfv,SUBSET_DEF]
QED
 

Theorem wfdpvl_ALL_DISTINCT_okvnames_wff:
wfvl (FST Σ) vl TRUE ∧ ALL_DISTINCT vl ∧ okvnames vl ⇒
wff Σ (FALLL (vl2sl vl) (plainfV (P,vl2sl vl)))
Proof
rw[] >> 
‘wfdpvl vl TRUE’ by metis_tac[wfvl_def] >>
drule_then assume_tac $ GSYM mk_FALLL_fVar_FALLL >>
simp[] >>
irule mk_FALLL_fVar_wff >> reverse (rw[wfvl_def]) (* 3 *)
>- gs[wfvl_def]
>- (irule wfdpvl_TRUE_fVar >> simp[]) >>
cheat (*need to redefine wff*)
QED


Theorem wff_fVar:
wff (Σf,Σp,Σe) (fVar P sl tl) ⇔
wfabsap Σf sl tl ∧
∃vl. wfvl Σf vl TRUE ∧ vl2sl vl = sl ∧ ALL_DISTINCT vl ∧
     okvnames vl
Proof
cheat
QED

Definition wffstl_def:
wffstl Σf sl tl ⇔
wfabsap Σf sl tl ∧
∃vl. wfvl Σf vl TRUE ∧ vl2sl vl = sl ∧ ALL_DISTINCT vl ∧
     okvnames vl
End          


(*
okvnames: when select the names of the variables ,look at the whole list and avoid any name in the variables in a sort.

all distinct easy
prove vl2sl (sl2vl l) = l under some condition.

                
*)



Definition sl2vl_def:
sl2vl [] [] = [] ∧
sl2vl (n :: nl) (s :: sl) =
(n,s) :: sl2vl nl (specsl 0 (Var n s) sl)
End


Definition fresh_to_def:
fresh_to ns vs ⇔ ns ∩ IMAGE FST vs = {}
End

Theorem slfv_EMPTY:
slfv [] = {}
Proof
simp[slfv_alt]
QED                

Definition tnames_def:
tnames (Var n s) = {n:string} ∪ snames s ∧
tnames (Fn f s l) =
snames s ∪ BIGUNION (set (MAP tnames l)) ∧
tnames (Bound i) = {} ∧
snames (St n tl) = BIGUNION (set (MAP tnames tl))
Termination
WF_REL_TAC ‘measure (λs. case s of INL t => term_size t
                                | INR s => sort_size s)’             
End


Definition slnames_def:
slnames sl = Uof snames (set sl)
End


Theorem slnames_alt:
slnames sl = BIGUNION {snames s | MEM s sl}
Proof
simp[Once EXTENSION,slnames_def,Uof_def]
QED
 
Definition tlnames_def:
tlnames tl = Uof tnames (set tl)
End        



Theorem tlnames_alt:
tlnames tl = BIGUNION {tnames t | MEM t tl}
Proof
simp[Once EXTENSION,tlnames_def,Uof_def]
QED           

Theorem tnames_thm:
tnames (Var n s) = {n:string} ∪ snames s ∧
tnames (Fn f s l) =
snames s ∪ BIGUNION {tnames t | MEM t l} ∧
tnames (Bound i) = {} ∧
snames (St n tl) = BIGUNION {tnames t | MEM t tl}
Proof
simp[tnames_def,PULL_EXISTS] >> simp[Once EXTENSION,PULL_EXISTS,MEM_MAP,LIST_TO_SET_MAP,IMAGE_DEF,EXTENSION]
QED
           
Theorem tnames_trpl_SUBSET:
(∀tm i t. tnames (trpl i t tm) ⊆ tnames t ∪ tnames tm) ∧
(∀st i t. snames (srpl i t st) ⊆ tnames t ∪ snames st) 
Proof
ho_match_mp_tac better_tm_induction >>
gs[tnames_thm,trpl_def,MEM_MAP] >> rw[] (* 5 *)
>> TRY (gs[SUBSET_DEF] >> metis_tac[]) >>
gs[tnames_def]
QED

        
Theorem vl2sl_sl2vl_names_lemma:
∀sl t i. slnames (specsl i t sl) ⊆ (tnames t) ∪ slnames sl
Proof
rw[] >> 
simp[SUBSET_DEF,PULL_EXISTS,slnames_alt]>>
rw[] >> gs[LENGTH_specsl] >> gs[MEM_EL,LENGTH_specsl] >>
drule_then assume_tac specsl_EL >>
gs[PULL_EXISTS] >>
qspecl_then [‘EL n sl’,‘i + n’,‘t’] assume_tac
            $ cj 2 tnames_trpl_SUBSET >> gs[] >>
gs[SUBSET_DEF] >> metis_tac[]
QED            



Theorem slnames_CONS:
slnames (h :: t) = snames h ∪ slnames t
Proof
simp[slnames_alt,Once EXTENSION] >> metis_tac[]
QED

Theorem tfv_tnames:
(∀tm n s. (n,s) ∈ tfv tm ⇒ n ∈ tnames tm) ∧
(∀st n s. (n,s) ∈ sfv st ⇒ n ∈ snames st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,tnames_thm,PULL_EXISTS] >> rw[] >>
TRY (gs[] >> metis_tac[])
QED
 
Theorem vl2sl_sl2vl:
∀nl. LENGTH nl = LENGTH sl ∧ ALL_DISTINCT nl ∧
     (set nl) ∩ (slnames sl) = {} ⇒ vl2sl (sl2vl nl sl) = sl
Proof
Induct_on ‘LENGTH sl’
>- rw[slfv_EMPTY,sl2vl_def,vl2sl_EMPTY] >>
Cases_on ‘sl’ >> simp[] >> rw[] >>
Cases_on ‘nl’ >> gs[] >>
simp[sl2vl_def,vl2sl_CONS] >>
‘(vl2sl (sl2vl t' (specsl 0 (Var h' h) t))) =
(specsl 0 (Var h' h) t)’
 by (first_x_assum irule >> simp[LENGTH_specsl] >>
    qspecl_then [‘t’,‘Var h' h’,‘0’] assume_tac
    vl2sl_sl2vl_names_lemma >>
    ‘set t' ∩ (tnames (Var h' h) ∪ slnames t) = ∅’
      suffices_by (gs[SUBSET_DEF,EXTENSION] >> metis_tac[])>>
    gs[slnames_CONS] >>
    simp[tnames_def] >> gs[Once EXTENSION] >>
    gs[Once EXTENSION] >> metis_tac[]) >>
simp[] >>
irule abssl_specsl >> rw[] >>
‘h' ∉ slnames t’ by
(gs[Once EXTENSION] >> gs[Once EXTENSION] >>
gs[slnames_CONS] >> metis_tac[]) >>
gs[slnames_alt] >> metis_tac[tfv_tnames]
QED






Theorem fVars_TRUE:
fVars TRUE = {}
Proof
simp[TRUE_def,fVars_def]
QED             


Theorem fVslfv_TRUE:
fVslfv TRUE = {}
Proof
simp[fVslfv_def,Uof_def,fVars_TRUE]
QED

             
Theorem wfdpvl_TRUE:
(wfdpvl [] TRUE ⇔ T) ∧
(wfdpvl (h :: t) TRUE ⇔
 wfdpvl t TRUE ∧
 ∀n s. (n,s) ∈ slfv (vl2sl t) ⇒ h ∉ sfv s)
Proof
 simp[wfdpvl_def,fVslfv_TRUE] >>
 rw[EQ_IMP_THM] (* 2 *)
 >> (drule_then assume_tac wfdpvl_ffv_mk_FALLL >>
    gs[mk_FALLL_TRUE,ffv_FALLL,ffv_TRUE,slfv_alt] >>
    metis_tac[])
QED    
     

Theorem MAP_FST_sl2vl:
∀nl. LENGTH nl = LENGTH sl ⇒ MAP FST (sl2vl nl sl) = nl
Proof
Induct_on ‘LENGTH sl’ >> simp[sl2vl_def] >>
Cases_on ‘sl’ >> simp[] >> rw[] >>
Cases_on ‘nl’ >> gs[sl2vl_def] >>
first_x_assum irule >> simp[LENGTH_specsl]
QED 

     



Theorem ALL_DISTINCT_sl2vl:
∀nl. LENGTH nl = LENGTH sl ∧ ALL_DISTINCT nl ∧
     (set nl) ∩ (slnames sl) = {} ⇒
     ALL_DISTINCT (sl2vl nl sl)
Proof
Induct_on ‘LENGTH sl’ >- simp[sl2vl_def] >>
Cases_on ‘sl’ >> simp[slnames_CONS] >> rw[] >>
Cases_on ‘nl’ >> gs[sl2vl_def] >>
‘ALL_DISTINCT (sl2vl t' (specsl 0 (Var h' h) t))’
 by (first_x_assum irule >> simp[LENGTH_specsl] >>
    qspecl_then [‘t’,‘Var h' h’,‘0’] assume_tac
                vl2sl_sl2vl_names_lemma >>
    ‘set t' ∩ (tnames (Var h' h) ∪ slnames t) = {}’
     suffices_by (gs[SUBSET_DEF,Once EXTENSION] >>
     gs[Once EXTENSION] >>  gs[EXTENSION] >>
     metis_tac[]) >>
    gs[tnames_def] >> gs[slnames_alt,EXTENSION] >>
    metis_tac[]) >>
simp[] >> strip_tac >>
‘h' ∈ set (MAP FST (sl2vl t' (specsl 0 (Var h' h) t)))’
  by (gs[MEM_MAP] >> qexists ‘(h',h)’ >> simp[]) >>
‘(MAP FST (sl2vl t' (specsl 0 (Var h' h) t))) =
 t'’ suffices_by (strip_tac >> gs[]) >>
irule MAP_FST_sl2vl >> simp[LENGTH_specsl]
QED



Theorem ALL_DISTINCT_EMPTY_INTER_lemma:
¬MEM h' t' ∧ 
ALL_DISTINCT t' ∧
 (h' INSERT set t') ∩ (snames h ∪ slnames t) = ∅ ⇒
        set t' ∩ slnames (specsl i (Var h' h) t) = ∅
Proof
rw[] >>
qspecl_then [‘t’,‘Var h' h’,‘i’] assume_tac
                vl2sl_sl2vl_names_lemma >>
    ‘set t' ∩ (tnames (Var h' h) ∪ slnames t) = {}’
     suffices_by (gs[SUBSET_DEF,Once EXTENSION] >>
     gs[Once EXTENSION] >>  gs[EXTENSION] >>
     metis_tac[]) >>
    gs[tnames_def] >> gs[slnames_alt,EXTENSION] >>
    gs[SUBSET_DEF] >>
    metis_tac[]
QED    

Theorem okvnames_sl2vl:
∀nl. LENGTH nl = LENGTH sl ∧ ALL_DISTINCT nl ∧
     (set nl) ∩ (slnames sl) = {} ⇒
     okvnames (sl2vl nl sl)
Proof
Induct_on ‘LENGTH sl’
>- (rw[] >> simp[sl2vl_def,okvnames_def]) >>
Cases_on ‘sl’ >> simp[] >> rw[] >>
Cases_on ‘nl’ >> gs[slnames_CONS,sl2vl_def] >>
simp[okvnames_CONS] >>
‘okvnames (sl2vl t' (specsl 0 (Var h' h) t))’
 by (first_x_assum irule >> simp[LENGTH_specsl] >>
    metis_tac[ALL_DISTINCT_EMPTY_INTER_lemma]) >>
simp[] >> rw[] >> Cases_on ‘v’ >>
strip_tac >> ‘q ∈ snames h’ by metis_tac[tfv_tnames] >>
‘MAP FST (sl2vl t' (specsl 0 (Var h' h) t)) = t'’
 by (irule MAP_FST_sl2vl >> simp[LENGTH_specsl]) >>
‘q ∈ set (MAP FST (sl2vl t' (specsl 0 (Var h' h) t)))’ 
 by (simp[MEM_MAP] >> qexists ‘(q,r)’ >> simp[]) >>
‘q ∈ set t'’ suffices_by
(strip_tac >> gs[EXTENSION]>> metis_tac[]) >>
gs[]
QED


Theorem tfv_trpl_SUBSET2:
(∀t i new. tfv (trpl i new t) ⊆ tfv t ∪ tfv new) ∧
∀s i new. sfv (srpl i new s) ⊆ sfv s ∪ tfv new
Proof        
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,trpl_def,SUBSET_DEF] >> rw[]>>
gs[MEM_MAP] >>
TRY (metis_tac[])
QED
 
Theorem slfv_specsl:
∀sl t i. slfv (specsl i t sl) ⊆ slfv sl ∪ tfv t
Proof
simp[SUBSET_DEF,PULL_EXISTS,slfv_alt] >> rw[] >>
gs[MEM_EL,LENGTH_specsl] >>
drule_then assume_tac specsl_EL>> gs[] >>
qspecl_then [‘EL n sl’,‘i + n’,‘t’] assume_tac
            $ cj 2 tfv_trpl_SUBSET2 >>
gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >> gs[] >>
disj1_tac >> qexists ‘EL n sl’ >> metis_tac[]
QED
            
            
Theorem sfv_slfv_slnames:
(n,s) ∈ slfv t ∧ (h',h) ∈ sfv s ⇒ h' ∈ slnames t
Proof
simp[slnames_alt,PULL_EXISTS,slfv_alt] >>
rw[] >> qexists ‘v’ >> simp[] >>
metis_tac[tfv_tnames,vsort_tfv_closed]
QED


            
Theorem wfdpvl_sl2vl:
∀nl. LENGTH nl = LENGTH sl ∧ ALL_DISTINCT nl ∧
 (set nl) ∩ (slnames sl) = {} 
⇒ wfdpvl (sl2vl nl sl) TRUE
Proof
Induct_on ‘LENGTH sl’ >> gs[wfdpvl_TRUE,sl2vl_def] >>
Cases_on ‘sl’ >> simp[] >> rw[] >>
Cases_on ‘nl’ >> gs[] >>
simp[sl2vl_def] >>
simp[wfdpvl_TRUE] >>
‘wfdpvl (sl2vl t' (specsl 0 (Var h' h) t)) TRUE’
 by (first_x_assum irule >> simp[LENGTH_specsl] >>
     gs[slnames_CONS] >>
     metis_tac[ALL_DISTINCT_EMPTY_INTER_lemma]) >>
rw[] >>
‘(vl2sl (sl2vl t' (specsl 0 (Var h' h) t))) =
 (specsl 0 (Var h' h) t)’
 by (irule vl2sl_sl2vl >> simp[LENGTH_specsl] >>
     gs[slnames_CONS] >>
     metis_tac[ALL_DISTINCT_EMPTY_INTER_lemma]) >>
gs[] >> pop_assum (K all_tac) >>
qspecl_then [‘t’,‘Var h' h’,‘0’] assume_tac
slfv_specsl >>
gs[SUBSET_DEF,PULL_EXISTS] >>
first_x_assum $ drule_then assume_tac >>
gs[tm_tree_WF] (* 2 *)
>- (gs[slnames_CONS] >> strip_tac >>
   ‘h' ∈ slnames t’
     suffices_by (strip_tac >>
     gs[EXTENSION] >>  metis_tac[]) >>
   metis_tac[sfv_slfv_slnames]) >>
gs[slnames_CONS] >> strip_tac >>
metis_tac[vsort_tfv_closed,tm_tree_WF] 
QED




Theorem sl2vl_sinst:
∀nl. LENGTH nl = LENGTH sl ∧
     ALL_DISTINCT nl ∧
     (∀v. v ∈ FDOM σ ⇒ tbounds (σ ' v) = ∅) ∧
     set nl ∩ IMAGE FST (FDOM σ) = {} ∧
     ok_abs sl ∧
     (∀n s st. MEM st sl ∧ (n,s) ∈ sfv st ⇒ sbounds s = ∅) 
     ⇒
sl2vl nl (MAP (sinst σ) sl) =
MAP (λ(n,s). (n,sinst σ s)) (sl2vl nl sl)
Proof
Induct_on ‘LENGTH sl’
>- (rw[] >> simp[sl2vl_def]) >>
Cases_on ‘sl’ >> simp[] >> rw[] >>
Cases_on ‘nl’ >> gs[sl2vl_def] >>
‘(specsl 0 (Var h' (sinst σ h)) (MAP (sinst σ) t)) =
 MAP (sinst σ) (specsl 0 (Var h' h) t)’
 by
(‘(Var h' (sinst σ h)) = tinst σ (Var h' h)’
  by
    (‘(h',h) ∉ FDOM σ’
      by (strip_tac >>
         gs[EXTENSION] >>
         pop_assum mp_tac >> simp[] >>
         last_x_assum
         $ qspecl_then [‘h'’] assume_tac >> gs[]) >>
    simp[tinst_def]) >> pop_assum SUBST_ALL_TAC >>
 irule $ GSYM MAP_sinst_specsl1 >>
 rw[](* 2 *)
 >- metis_tac[] >>
(gs[SUBSET_DEF] >> metis_tac[])) >>
simp[] >>
‘sl2vl t' (MAP (sinst σ) (specsl 0 (Var h' h) t)) =
 MAP (λ(n,s). (n,sinst σ s))
 (sl2vl t' (specsl 0 (Var h' h) t))’
 by (first_x_assum irule >> simp[LENGTH_specsl] >>
     simp[MEM_EL,LENGTH_specsl,PULL_EXISTS] >>
     rw[] (* 3 *)
     >- (drule_then assume_tac specsl_EL >> gs[] >>
     qspecl_then [‘EL n' t’,‘n'’,‘(Var h' h)’]
     assume_tac $ cj 2 tfv_trpl_SUBSET2 >>
     gs[SUBSET_DEF] >>
     first_x_assum $ drule_then assume_tac >>
     gs[MEM_EL] (* 3 *) >- metis_tac[]
     >- metis_tac[ok_abs_HD] >> metis_tac[])
     >- (gs[ok_abs_def,PULL_EXISTS,SUBSET_DEF,
           LENGTH_specsl] >>
        rw[] >>
        drule_then assume_tac specsl_EL >>
        gs[] >>
        ‘sbounds (srpl n (Var h' h) (EL n t)) =
         sbounds (EL n t) DELETE n’
         suffices_by
         (rw[] >> gs[] >>
         last_x_assum $
         qspecl_then [‘SUC n’] assume_tac >> gs[] >>
         first_x_assum $ drule_then assume_tac >>
         gs[]) >>
       irule $ cj 2 trpl_eliminate >> rw[] (* 2 *)
       >- metis_tac[MEM_EL] >>
       simp[tbounds_def] >>
       last_x_assum $ qspecl_then [‘0’] assume_tac >>
       gs[] >> metis_tac[MEMBER_NOT_EMPTY]
       ) >>
     gs[EXTENSION] >> metis_tac[])
QED 




Theorem vl2sl_no_vbound:
(∀v. MEM v vl ⇒ ∀n s. (n,s) ∈ sfv (SND v) ⇒
sbounds s = {}) ⇒ 
(∀n s st. MEM st (vl2sl vl) ∧ (n,s) ∈ sfv st ⇒ sbounds s = ∅)
Proof
Induct_on ‘LENGTH vl’ >> simp[vl2sl_EMPTY] >>
Cases_on ‘vl’ >> simp[vl2sl_CONS] >>
rw[] (* 2 *)
>- metis_tac[] >>
Cases_on ‘h’ >> 
gs[MEM_EL,LENGTH_abssl] >>
drule_then assume_tac abssl_EL >> gs[] >>
pop_assum (K all_tac) >>
qspecl_then [‘EL n' (vl2sl t)’,‘q’,‘r’,‘n'’]
assume_tac $ cj 2 tfv_tabs_SUBSET1 >>
gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >>
last_x_assum irule >> simp[PULL_EXISTS] >>
first_x_assum $ irule_at Any >> simp[LENGTH_vl2sl] >>
metis_tac[]
QED

Theorem tbounds_tabs_SUBSET1:
(∀tm m s n. tbounds (tabs (m,s) n tm) ⊆ tbounds tm ∪ {n})∧
∀st m s n. sbounds (sabs (m,s) n st) ⊆ sbounds st ∪ {n}
Proof
ho_match_mp_tac better_tm_induction >>
gs[tbounds_thm,tabs_def,PULL_EXISTS,MEM_MAP] >>
rw[] >> gs[SUBSET_DEF,tabs_def] >>
TRY (metis_tac[]) >>
Cases_on ‘m = s0 ∧ s = st’ >> simp[] >>
simp[tbounds_thm] >> TRY (metis_tac[])
QED

Theorem ok_abs_vl2sl:
(∀v. MEM v vl ⇒ sbounds (SND v) = {}) ⇒
ok_abs (vl2sl vl)
Proof
Induct_on ‘LENGTH vl’
>- simp[vl2sl_EMPTY,ok_abs_def] >>
Cases_on ‘vl’ >> simp[] >> rw[] >>
simp[vl2sl_CONS] >>
simp[ok_abs_def,PULL_EXISTS] >>
Cases_on ‘h’ >> simp[LENGTH_abssl,LENGTH_vl2sl] >>
rw[] >>
Cases_on ‘n’ >> gs[] (* 2 *)
>- (first_x_assum
   $ qspecl_then [‘(q,r)’] assume_tac>>
   gs[]) >>
‘n' < LENGTH (vl2sl t)’ by gs[LENGTH_vl2sl] >>
drule_then assume_tac abssl_EL >> gs[] >>
qspecl_then [‘EL n' (vl2sl t)’,‘q’,‘r’,‘n'’]
assume_tac $ cj 2 tbounds_tabs_SUBSET1 >>
gs[SUBSET_DEF] >>
rw[] >> first_x_assum $ drule_then assume_tac >>
gs[] >>
‘ok_abs (vl2sl t)’
  by (first_x_assum irule >> simp[]) >>
last_x_assum $ K all_tac >>
gs[ok_abs_def,LENGTH_vl2sl] >>
first_x_assum $ drule_then assume_tac >>
gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >> gs[]
QED






(*        
cstt_EXT
wft_tinst




Theorem tfv_tpsubtm:
(∀tm n s t0. (n,s) ∈ tfv tm ∧ t0 ∈ ssubtm s ⇒
         term_size t0 < term_size tm) ∧
(∀st n s t0. (n,s) ∈ sfv st ∧ t0 ∈ ssubtm s ⇒
         term_size t0 < sort_size st)         
Proof
ho_match_mp_tac better_tm_induction >>
gs[term_size_def,PULL_EXISTS] >> rw[] (* 5 *)
>-  
Induct_on ‘t’ >>
simp[tfv_def,tpsubtm_def,tsubtm_def] (* 2 *)
 
>- rw[] >> Cases_on ‘s’ >> gs[tsubtm_def,MEM_MAP](*4*)
   >- (simp[PULL_EXISTS] >> disj2_tac >>
      qexists ‘t0’ >> simp[tsubtm_REFL])
   >- 

        
Theorem tfv_tpsubtm:
(∀n s t0. (n,s) ∈ tfv t ∧ MEM t0 (stms s) ⇒
         t0 ∈ tpsubtm t)
Proof
Induct_on ‘t’ >>
simp[tfv_def,tpsubtm_def,tsubtm_def] (* 2 *)
>- rw[] >> Cases_on ‘s’ >> gs[tsubtm_def,MEM_MAP](*4*)
   >- (simp[PULL_EXISTS] >> disj2_tac >>
      qexists ‘t0’ >> simp[tsubtm_REFL])
   >- 
*)
   
Theorem wft_tinst1:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
     (∀t. wft Σf t ⇒
          ∀σ. cstt σ ∧ wfcod Σf σ ⇒ wft Σf (tinst σ t))
Proof
disch_tac >>
completeInduct_on ‘term_size t’ >> rw[] >>
drule_then assume_tac cstt_EXT1 >>
   first_x_assum $ qspecl_then [‘tfv t’] assume_tac>>
   gs[] >>
   ‘(tinst σ t) = (tinst σ1 t)’
   by (irule $ cj 1 inst_eff_tinst >> metis_tac[]) >>
   simp[] >>
   irule $ cj 1 wft_tinst >> simp[] >>
   ‘gcont (tfv t) = tfv t’
    by metis_tac[gcont_of_cont,tfv_is_cont] >>
   gs[] >>
   simp[wfcod_def,PULL_EXISTS] >>
   rw[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[inst_eff_def] >>
   Cases_on ‘(n,s) ∈ FDOM σ’ (* 2 *) >> simp[] 
   >- gs[wfcod_def] >>
   simp[wft_def] >>
   Cases_on ‘s’ >>
   simp[tinst_def,wft_def,EVERY_MEM,MEM_MAP,
        PULL_EXISTS] >>
   rw[] >>
   first_x_assum irule >>
   simp[] >>
   drule_then assume_tac $ cj 1 wft_wfs >>
   first_x_assum $ drule_then assume_tac >>
   gs[wft_def,EVERY_MEM] >>
   drule_then assume_tac $ cj 1 tm_tree_size_less >>
   ‘term_size a' ≤ sort_size (St s' l)’
    suffices_by
    metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS] >>
    simp[term_size_def,term_size_eq] >>
    ‘term_size a' ≤ list_size term_size l’
      suffices_by simp[] >>
    irule MEM_list_size_leq >> simp[]
QED    



Theorem wfs_sinst1:
(∀fsym.
        isfsym Σf fsym ⇒
        sfv (fsymout Σf fsym) ⊆
        BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
     (∀s. wfs Σf s ⇒
          ∀σ. cstt σ ∧ wfcod Σf σ ⇒ wfs Σf (sinst σ s))
Proof
rw[] >> Cases_on ‘s’ >>
gs[wft_def,EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
rw[] >>
irule wft_tinst1 >> simp[]
QED 
              
Definition speclsl_def:
  speclsl i [] sl = sl ∧
  speclsl i (h :: t) sl =
  specsl i h (speclsl (i+1) t sl)
End


Theorem TO_FMAP_EMPTY:
TO_FMAP [] = FEMPTY
Proof
simp[fmap_EXT,FDOM_TO_FMAP]
QED        

Theorem cstt_FEMPTY:
cstt FEMPTY
Proof
simp[cstt_def]
QED


Definition rnvl_def:
rnvl [] [] = [] ∧
rnvl (nn :: nnl) ((vn,vs) :: vl) =
(nn,vs) ::
(rnvl nnl
(MAP (λ(n0,s0). (n0, srename (vn,vs) nn s0)) vl))
End


(*need ante*)        
Theorem specsl_MAP_abssl:
∀i h σ q r.
specsl i (Var h (sinst σ r))
          (MAP (sinst σ) (abssl (q,r) i sl)) =
MAP (sinst σ) (MAP (srename (q,r) h) sl)
Proof        
Induct_on ‘LENGTH sl’ >> rw[abssl_def,specsl_def] >>
Cases_on ‘sl’ >> gs[] >>
simp[abssl_def,specsl_def] >>
qspecl_then [‘(sabs (q,r) i h')’,‘i’,‘Var h r’,‘σ’] assume_tac $ cj 2 $ GSYM sinst_srpl1 >> 
‘(h,r) ∉ FDOM σ’ by cheat >> gs[] >>
‘srpl i (Var h (sinst σ r)) (sinst σ (sabs (q,r) i h')) =
        sinst σ (srpl i (Var h r) (sabs (q,r) i h'))’
 by cheat >> simp[] >>
AP_TERM_TAC >>
qspecl_then [‘h'’,‘i’,‘Var h r’,‘q’,‘r’] assume_tac
$ cj 2 trpl_tabs >>
‘srpl i (Var h r) (sabs (q,r) i h') = ssubst (q,r) (Var h r) h'’ by cheat >> simp[] >>
simp[tsubst_eq_tinst] >> simp[srename_def]
QED
        


Definition eqvvl_def:
(eqvvl [] [] ⇔ T) ∧
(eqvvl (v1::vl1) (v2::vl2) ⇔
SND v1 = SND v2 ∧
eqvvl vl1
(MAP (λ(n,s).(n,srename v2 (FST v1) s)) vl2))
End

Theorem eqvvl_vl2sl0:
eqvvl vl1 vl2 ⇒ vl2sl vl1 = vl2sl vl2
Proof
Induct_on ‘LENGTH vl1’ >- cheat >>
Induct_on ‘LENGTH vl2’ >- cheat >>
rw[] >> Cases_on ‘vl1’ >> Cases_on ‘vl2’ >> gs[] >>
gs[eqvvl_def,vl2sl_CONS] >>


Theorem rename_vl2sl:
vl2sl t =
(vl2sl (MAP (λ(n0,s0). (n0,srename (q,r) h s0)) t)
Proof



               
Theorem specsl_MAP_abssl:
specsl i (Var h (sinst σ r))
          (MAP (sinst σ) (abssl (q,r) i (vl2sl t))) =
        MAP (sinst σ) (vl2sl (MAP (λ(n0,s0). (n0,srename (q,r) h s0)) t))
Proof        
Induct_on ‘LENGTH t’ >>
rw[vl2sl_EMPTY,specsl_def,abssl_def] >>
Cases_on ‘t’ >> gs[] >>
simp[vl2sl_CONS,abssl_def,specsl_def] 
        
Theorem sl2vl_MAP_vl2sl:
∀nl.LENGTH nl = LENGTH vl ⇒
sl2vl nl (MAP (sinst σ) (vl2sl vl)) =
MAP (λ(n,s). (n,sinst σ s)) (rnvl nl vl)
Proof
Induct_on ‘LENGTH vl’ >>
rw[vl2sl_EMPTY,rnvl_def,sl2vl_def] >>
Cases_on ‘vl’ >> Cases_on ‘nl’ >> gs[] >>
simp[vl2sl_CONS,sl2vl_def] >>
Cases_on ‘h’ >> simp[rnvl_def] >>
‘MAP (λ(n,s). (n,sinst σ s))
          (rnvl t' (MAP (λ(n0,s0). (n0,srename (q,r) h' s0)) t)) =
 sl2vl t' (MAP (sinst σ) (vl2sl (MAP (λ(n0,s0). (n0,srename (q,r) h' s0)) t)))’
 by simp[Once EQ_SYM_EQ] >>
last_x_assum $ K all_tac >> simp[] >>
AP_TERM_TAC >> 
(* MAP_sinst_abssl *)


(*
Theorem speclsl_abssl_wf:
wfvl Σ vl TRUE ⇒
∀nl. LENGTH nl = LENGTH vl ⇒ wfabsap0 Σ (vl2sl vl)
              (MAP Var' (sl2vl nl (vl2sl vl)))
Proof     
Induct_on ‘LENGTH vl’ >> rw[wfabsap0_def,vl2sl_EMPTY,sl2vl_def] >>
Cases_on ‘vl’ >> gs[] >> rw[] >>
Cases_on ‘nl’ >> gs[] >>
simp[vl2sl_CONS,sl2vl_def,wfabsap0_def] >>
simp[sort_of_def,wft_def] >>
Cases_on ‘h’ >> simp[] >>
‘(specsl 0 (Var h' r) (abssl (q,r) 0 (vl2sl t))) =
 vl2sl (MAP (λ(n,s). (n,sinst (TO_FMAP[(q,r),Var h' r]) s)) t)’ by cheat >>
simp[] >>
 ‘wfs Σ r’
  by (gs[wfvl_def] >>
first_x_assum $ qspecl_then [‘(q,r)’] assume_tac >>
gs[]) >> simp[] >>
first_x_assum irule >> simp[] >> 
vl2sl_CONS
*)

(*          
Theorem foo:
∀nl. LENGTH nl = LENGTH vl ⇒
     cstt
     (TO_FMAP
      (ZIP (vl,MAP Var' (sl2vl nl (vl2sl vl)))))
Proof     
 Induct_on ‘LENGTH vl’ >>
 simp[vl2sl_EMPTY,sl2vl_def,
      TO_FMAP_EMPTY,cstt_FEMPTY] >>
 Cases_on ‘vl’ >> simp[] >> rw[] >>
 Cases_on ‘nl’ >> gs[] >>
 simp[vl2sl_CONS,sl2vl_def] >>
 ‘(TO_FMAP
             ((h,Var h' (SND h))::
                ZIP
                  (t,
                   MAP Var'
                     (sl2vl t'
                        (specsl 0 (Var h' (SND h)) (abssl h 0 (vl2sl t))))))) =
 TO_FMAP
 (ZIP
                  (t,
                   MAP Var'
                     (sl2vl t'
                        (specsl 0 (Var h' (SND h)) (abssl h 0 (vl2sl t)))))) |+ (h,Var h' (SND h))                      ’
 by cheat >> simp[] >>
pop_assum (K all_tac) >>
‘cstt (TO_FMAP
 (ZIP
                (t,
                 MAP Var'
                   (sl2vl t'
                      (specsl 0 (Var h' (SND h)) (abssl h 0 (vl2sl t)))))))’
 first_x_assum irule

 sl2vl_def                                             
*)   
          
       
(*
Theorem sl2vl_vl2sl_wf:
∀nl. LENGTH nl = LENGTH vl ∧ (∀v. MEM v vl ⇒ wfs Σ (SND v)) ⇒
     (∀v. MEM v (sl2vl nl (vl2sl vl)) ⇒ wfs Σ (SND v))
Proof     
Induct_on ‘vl’ >- cheat >> simp[vl2sl_CONS] >>
rw[] >> Cases_on ‘nl’ >> gs[sl2vl_def] >> 
*)


Theorem tsubst_tabs:
tsubst_
tinst_tabs
tsubst_eq_tinst        

        
Theorem MAP_ssubst_abssl:
∀n s nn x y i.
MAP (ssubst (n,s) (Var nn s)) (abssl (x,y) i sl) =
abssl (x,y) i (MAP (ssubst (n,s) (Var nn s)) sl)
Proof
Induct_on ‘sl’ >> simp[abssl_def] >>
simp[tsubst_eq_tinst] >> rw[] >>
dep_rewrite.DEP_REWRITE_TAC[tinst_tabs] >>
reverse (rw[]) 

tabs_def
tsubst_def


rw[] >> 
qspecl_then [‘x’,‘y’,‘x’,‘tm’,‘i’,‘rnmap (n,s) nn (tfv ((tabs (x,y) i tm)))’]
assume_tac $ Q.GENL [‘n’,‘s’,‘nn’] $ cj 1 $ tinst_tabs >>
gs[GSYM trename_tinst_tfv] >>
‘’
‘(sinst (rnmap (n,s) nn (tfv (tabs (n,s) i tm))) s)=
 ’
tabs_tinst

Theorem trename_reflect:
(∀tm1 tm2 nn n s. nn ∉ tnames tm1 ∪ tnames tm2 ∧
 tbounds tm1 = {} ∧ tbounds tm2 = {} ⇒
(trename (n,s) nn tm1 = trename (n,s) nn tm2 ⇔
 tm1 = tm2)) ∧
(∀st1 st2 nn n s. nn ∉ snames st1 ∪ snames st2 ∧
 sbounds st1 = {} ∧ sbounds st2 = {}⇒
(srename (n,s) nn st1 = srename (n,s) nn st2 ⇔
 st1 = st2))
Proof
ho_match_mp_tac better_tm_induction >>
rw[] (* 4 *)
>- (Cases_on ‘tm2’ >> simp[trename_alt] >>
   Cases_on ‘s0 = n ∧ st1 = s’ >> simp[] (* 2 *)
   >- (Cases_on ‘s0' = n ∧ s' = s’ >> simp[] >>
      gs[tnames_def]) >>
   Cases_on ‘s0' = n ∧ s' = s’ >> simp[] (* 2 *)
   >> gs[tnames_def,tbounds_def] >>
   Cases_on ‘s0' = n ∧ s' = s’ >> simp[])
>- (Cases_on ‘tm2’ >> gs[trename_alt,tnames_def](*2*)
   >- (Cases_on ‘s0' = n ∧ s' = s’ >> simp[]) >>
   ‘srename (n,s) nn st1 = srename (n,s) nn s' ⇔
   st1 = s'’
    by (first_x_assum irule >> gs[tbounds_def]) >>
   gs[MAP_EQ_f,MEM_MAP,DISJ_IMP_THM,FORALL_AND_THM]>>
   ‘ MAP (trename (n,s) nn) l = MAP (trename (n,s) nn) l' ⇔ l = l'’ suffices_by metis_tac[] >>
   rw[EQ_IMP_THM] >>
   irule LIST_EQ >>
   ‘LENGTH (MAP (trename (n,s) nn) l) =
    LENGTH (MAP (trename (n,s) nn) l')’
    by metis_tac[] >>
    gs[] >>
   rw[] >>
   first_x_assum $
                 qspecl_then [‘EL x l’] assume_tac>>
   ‘MEM (EL x l) l’ by metis_tac[MEM_EL] >>
   gs[] >>
   first_x_assum $
                 qspecl_then [‘EL x l'’,‘nn’,‘n’,‘s’]
   assume_tac >>
   first_x_assum $ irule o iffLR >> rw[] (* 3 *)
   >- metis_tac[MEM_EL]
   >- metis_tac[MEM_EL] 
   >- (gs[tbounds_thm,EXTENSION] >>
       metis_tac[MEM_EL])
   >- (gs[tbounds_thm,EXTENSION] >>
       metis_tac[MEM_EL]) >>
   ‘trename (n,s) nn (EL x l) = EL x (MAP (trename (n,s) nn) l) ∧
   trename (n,s) nn (EL x l') = EL x (MAP (trename (n,s) nn) l')’ suffices_by metis_tac[] >>
   qpat_x_assum ‘MAP _ _ = MAP _ _’ (K all_tac) >>
   simp[EL_MAP]) 
>- gs[tbounds_thm] >>
Cases_on ‘st2’ >> rw[EQ_IMP_THM] (* 2 *)
>- gs[trename_alt] >>
gs[trename_alt] >>
‘LENGTH (MAP (trename (n,s) nn) l) =
 LENGTH (MAP (trename (n,s) nn) l')’
 by metis_tac[] >> gs[] >>
irule LIST_EQ >> simp[] >>
rw[] >>
first_x_assum $ qspecl_then [‘EL x l’] assume_tac >>
‘MEM (EL x l) l’ by metis_tac[MEM_EL] >>
gs[] >>
first_x_assum $ qspecl_then [‘EL x l'’,‘nn’,‘n’,‘s’]
assume_tac >> first_x_assum $ irule o iffLR >>
rw[] (* 5 *)
>- (gs[tnames_def,MEM_MAP] >> metis_tac[])
>- (gs[tnames_def,MEM_MAP] >> metis_tac[MEM_EL])
>- (gs[tbounds_thm,EXTENSION] >> metis_tac[MEM_EL])
>- (gs[tbounds_thm,EXTENSION] >> metis_tac[MEM_EL])>>
 ‘trename (n,s) nn (EL x l) = EL x (MAP (trename (n,s) nn) l) ∧
   trename (n,s) nn (EL x l') = EL x (MAP (trename (n,s) nn) l')’ suffices_by metis_tac[] >>
   qpat_x_assum ‘MAP _ _ = MAP _ _’ (K all_tac) >>
   simp[EL_MAP]
QED
    
     



     
Theorem trename_tabs:
(∀tm i nn n s x y.
(n,s) ≠ (x,y) ∧ nn ≠ x ∧
sbounds y = {} ∧ nn ∉ snames y ∧
(∀n0 s0. (n0,s0) ∈ tfv tm ⇒ (x,y) ∉ sfv s0 ∧ sbounds s0 = {}) ∧
(nn ∉ tnames tm) ⇒
trename (n,s) nn (tabs (x,y) i tm) =
tabs (x,srename (n,s) nn y) i (trename (n,s) nn tm)) ∧
(∀st i nn n s x y.
(n,s) ≠ (x,y) ∧ nn ≠ x ∧
sbounds y = {} ∧ nn ∉ snames y ∧
(∀n0 s0. (n0,s0) ∈ sfv st ⇒ (x,y) ∉ sfv s0 ∧
sbounds s0 = {}) ∧
(nn ∉ snames st) ⇒
srename (n,s) nn (sabs (x,y) i st) =
sabs (x,srename (n,s) nn y) i (srename (n,s) nn st))
Proof
ho_match_mp_tac better_tm_induction >>
rw[] (* 4 *)
>- (Cases_on ‘(n,s) = (s0,st)’ >> simp[trename_alt]
   >- (gs[] >>
      ‘tabs (x,y) i (Var s0 st) = Var s0 st’
        by (simp[tabs_def] >>
           ‘¬(x = s0 ∧ y = st)’ by metis_tac[] >>
           simp[]) >> simp[] >>
      simp[trename_alt] >>
      simp[tabs_def]) >>
   ‘¬(s0 = n ∧ st = s)’ by metis_tac[] >> simp[] >>
   Cases_on ‘(x,y) = (s0,st)’ >> simp[] (* 2 *)
   >- (gs[] >> simp[tabs_def] >> simp[trename_def])>>
   ‘sbounds st = {}’ suffices_by
    (rw[] >>
    ‘y = st ⇔ (srename (n,s) nn y) = (srename (n,s) nn st)’ by (irule $ GSYM $ cj 2 trename_reflect >>
    simp[] >> gs[tnames_def]) >>
    pop_assum (assume_tac o GSYM) >> gs[] >>
    simp[tabs_def] >>
    ‘¬(x = s0 ∧ y = st)’ by metis_tac[] >> simp[] >>
    simp[trename_alt] >>
    ‘¬(s0 = n ∧ st = s)’ by metis_tac[] >> simp[]) >>
    metis_tac[])
>- (simp[tabs_def,trename_alt] >>
   ‘srename (n,s) nn (sabs (x,y) i st) =
        sabs (x,srename (n,s) nn y) i (srename (n,s) nn st)’ by (first_x_assum irule >> simp[] >>
        gs[tnames_def] >> metis_tac[]) >>
   simp[] >> simp[MAP_MAP_o,MAP_EQ_f] >>
   rw[] >> first_x_assum irule >>
   gs[tnames_def,MEM_MAP] >>
   metis_tac[])
>- gs[trename_alt,tabs_def] >>
simp[tabs_def,trename_alt,MAP_MAP_o,MAP_EQ_f] >>
rw[] >> first_x_assum irule >>
gs[] >> gs[tnames_def,MEM_MAP] >> gs[PULL_EXISTS] >>
rw[] (* 3 *) >> metis_tac[]
QED 


         
Theorem MAP_ssubst_abssl:
∀n s nn x y i.
nn ≠ x ∧ (n,s) ≠ (x,y) ∧
(∀s. MEM s sl ⇒ nn ∉ snames s) ∧
nn ∉ snames y ∧ sbounds y = {} ∧
(∀s n0 s0. MEM s sl ∧ (n0,s0) ∈ sfv s ⇒
           sbounds s0 = {} ∧ (x,y) ∉ sfv s0) ⇒ 
MAP (srename (n,s) nn) (abssl (x,y) i sl) =
abssl (x,srename (n,s) nn y) i (MAP (ssubst (n,s) (Var nn s)) sl)
Proof
Induct_on ‘sl’ >> simp[abssl_def] >>
simp[tsubst_eq_tinst] >> rw[] >>
dep_rewrite.DEP_REWRITE_TAC[tinst_tabs] >>
simp[GSYM srename_def] (* 2 *)
>- (irule $ cj 2 trename_tabs >> simp[] >>
    metis_tac[]) >>
first_x_assum irule >> simp[] >> metis_tac[]
QED    


Theorem MAP_srename_abssl:
∀n s nn x y i.
nn ≠ x ∧ (n,s) ≠ (x,y) ∧
(∀s. MEM s sl ⇒ nn ∉ snames s) ∧
nn ∉ snames y ∧ sbounds y = {} ∧
(∀s n0 s0. MEM s sl ∧ (n0,s0) ∈ sfv s ⇒
           sbounds s0 = {} ∧ (x,y) ∉ sfv s0) ⇒ 
MAP (srename (n,s) nn) (abssl (x,y) i sl) =
abssl (x,srename (n,s) nn y) i (MAP (srename (n,s) nn) sl)
Proof
Induct_on ‘sl’ >> simp[abssl_def] >>
simp[tsubst_eq_tinst] >> rw[] >>
dep_rewrite.DEP_REWRITE_TAC[tinst_tabs] >>
simp[GSYM srename_def] (* 2 *)
>- (irule $ cj 2 trename_tabs >> simp[] >>
    metis_tac[]) >>
first_x_assum irule >> simp[] >> metis_tac[]
QED    
                                       
          
Theorem tlnames_CONS:
tlnames (t :: tl) = tnames t ∪ tlnames tl
Proof
gs[tlnames_alt,EXTENSION] >> metis_tac[]
QED


Theorem NOT_IN_abssl:
∀n s i. (∀s0. MEM s0 sl ⇒ ∀n1 s1. (n1,s1) ∈ sfv s0 ⇒
       (n,s) ∉ sfv s1) ⇒
      (n,s) ∉ slfv (abssl (n,s) i sl)
Proof      
rw[MEM_EL,PULL_EXISTS] >>
simp[slfv_alt,PULL_EXISTS] >> rw[] >>
Cases_on ‘MEM v (abssl (n,s) i sl)’ >> simp[] >>
gs[MEM_EL,LENGTH_abssl] >>
drule_then assume_tac abssl_EL >> gs[] >>
qspecl_then [‘i + n'’,‘EL n' sl’,‘n’,‘s’] assume_tac
$ Q.GEN ‘i’ $ cj 2 tfv_tabs_SUBSET >>
‘sfv (sabs (n,s) (i + n') (EL n' sl)) ⊆
            sfv (EL n' sl) DELETE (n,s)’
 by (first_x_assum irule >> metis_tac[]) >>
gs[SUBSET_DEF] >> metis_tac[]
QED


Theorem wfdpvl_NOTIN_sfv:
wfdpvl (h :: t) TRUE ⇒
∀n s. (n,s) ∈ slfv (vl2sl t) ⇒ h ∉ sfv s
Proof
gs[wfdpvl_TRUE] >> metis_tac[]
QED
        
Theorem wfdpvl_MEM_NOT_slfv:
∀n s. MEM (n,s) vl ∧ wfdpvl vl TRUE ∧
      okvnames vl ⇒
      (n,s) ∉ slfv (vl2sl vl)
Proof
Induct_on ‘LENGTH vl’ >- rw[] >>
Cases_on ‘vl’ >> gs[] >>rw[vl2sl_CONS,slfv_CONS]
(* 4 *)
>- simp[tm_tree_WF]
>- (irule NOT_IN_abssl >>
   rw[] >> irule wfdpvl_NOTIN_sfv >>
   qexistsl [‘n1’,‘t’] >> simp[] >>
   simp[slfv_alt] >> metis_tac[])
>- (gs[okvnames_def] >>
   gs[MEM_EL] >> 
   first_x_assum $
   qspecl_then [‘0’,‘SUC n'’] assume_tac >> gs[]) >>
strip_tac >>
‘slfv (abssl h 0 (vl2sl t)) ⊆ slfv (vl2sl t)’
 by metis_tac[slfv_abssl_SUBSET] >>
gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >>
pop_assum mp_tac >> simp[] >> first_x_assum irule>>
simp[] >> gs[okvnames_CONS,wfdpvl_TRUE]
QED


Theorem wfvar_vl2sl_wfvar:
(∀n s. MEM (n,s) vl ⇒ sbounds s = {}) ⇒
∀n0 s0. (n0,s0) ∈ slfv (vl2sl vl) ⇒ sbounds s0 = {}
Proof
Induct_on ‘LENGTH vl’ >- rw[vl2sl_EMPTY,slfv_alt]>>
Cases_on ‘vl’ >> gs[] >> rw[] >>
gs[vl2sl_CONS,slfv_CONS] (* 2 *)
>- (Cases_on ‘h’ >> gs[] >>
   first_x_assum $ qspecl_then [‘q’,‘r’] assume_tac>>
   gs[] >>
   qspecl_then [‘r’,‘n0’,‘s0’] assume_tac
   $ cj 2 sbounds_tbounds >> gs[]) >>
‘slfv (abssl h 0 (vl2sl t)) ⊆ slfv (vl2sl t)’
 by metis_tac[slfv_abssl_SUBSET] >>
gs[SUBSET_DEF] >>
first_x_assum $ drule_then assume_tac >>
metis_tac[]
QED
   
Theorem tnames_tabs:
(∀tm n s i. tnames (tabs (n,s) i tm) ⊆ tnames tm) ∧
(∀st n s i. snames (sabs (n,s) i st) ⊆ snames st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tnames_thm,tabs_def,MEM_MAP,SUBSET_DEF] >>
rw[] (* 4 *) >> TRY (metis_tac[]) >>
Cases_on ‘n = s0 ∧ s = st’ >> gs[tnames_thm]
QED                 

Theorem slnames_abssl_SUBSET:
∀n s i. slnames (abssl (n,s) i sl) ⊆ slnames sl
Proof
Induct_on ‘LENGTH sl’ >> gs[abssl_def] >>
Cases_on ‘sl’ >> simp[] >> rw[] >>
simp[abssl_def,slnames_CONS] >> rw[] (* 2 *)
>- (simp[SUBSET_DEF] >>
   metis_tac[SUBSET_DEF,tnames_tabs]) >>
gs[SUBSET_DEF] >> metis_tac[]
QED   
                
Theorem slnames_vl2sl_SUBSET:
slnames (vl2sl vl) ⊆ tlnames (MAP Var' vl)
Proof
Induct_on ‘LENGTH vl’ >>
simp[slnames_alt,vl2sl_EMPTY] >>
Cases_on ‘vl’ >> simp[] >> rw[] >>
simp[tlnames_CONS,vl2sl_CONS] >>
rw[SUBSET_DEF,PULL_EXISTS] (* 2 *)
>- (disj1_tac >> Cases_on ‘h’ >> gs[tnames_def]) >>
disj2_tac >>
‘slnames (abssl h 0 (vl2sl t)) ⊆ slnames (vl2sl t)’
 by (Cases_on ‘h’ >>
     metis_tac[slnames_abssl_SUBSET]) >>
gs[SUBSET_DEF] >> first_x_assum irule >> simp[] >>
first_x_assum irule >> simp[slnames_alt] >>
metis_tac[]
QED
 

        
Theorem srename_vl2sl:
∀n s nn.
  nn ∉ tlnames (MAP Var' vl) ∧
  (∀vn vs. MEM (vn,vs) vl ⇒ sbounds vs = {}) ∧
  wfdpvl vl TRUE ∧ 
  ¬(MEM (n,s) vl) ⇒
  MAP (srename (n,s) nn) (vl2sl vl) =
  vl2sl
  (MAP (λ(n0,s0).(n0,srename (n,s) nn s0)) vl)
Proof
Induct_on ‘vl’
>- simp[vl2sl_EMPTY] >>
simp[vl2sl_CONS,pairTheory.FORALL_PROD] >> rw[] >>
dep_rewrite.DEP_REWRITE_TAC[MAP_srename_abssl] >>
reverse (strip_tac) (* 2 *)
>- (AP_TERM_TAC >>  first_x_assum irule >>
   gs[wfdpvl_TRUE] >>
   gs[tlnames_CONS] >> metis_tac[]) >>
gs[tlnames_CONS,tnames_def] >>
reverse (strip_tac) (* 2 *)
>- (reverse (rw[])
   >- (gs[wfdpvl_TRUE] >>
      first_x_assum irule >>
      qexists ‘n0’ >> simp[slfv_alt] >>
      metis_tac[]) >>
   irule wfvar_vl2sl_wfvar >>
   simp[slfv_alt] >> metis_tac[]) >>
rw[] >>
‘slnames (vl2sl vl) ⊆ tlnames (MAP Var' vl)’
 by metis_tac[slnames_vl2sl_SUBSET] >>
gs[SUBSET_DEF,slnames_alt] >> metis_tac[]
QED


Theorem tsubst_trename:
(∀tm n s nn.
tsubst (n,s) (Var nn s) tm = trename (n,s) nn tm) ∧
(∀st n s nn.
ssubst (n,s) (Var nn s) st = srename (n,s) nn st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tsubst_def,trename_alt,MAP_EQ_f] >>
rw[] >>
Cases_on ‘ n = s0 ∧ s = st’ >> simp[] >>
‘¬(s0 = n ∧ st = s)’ by metis_tac[] >> simp[]
QED 

Theorem tsubst_trename1:
tsubst (n,s) (Var nn s) = trename (n,s) nn ∧
ssubst (n,s) (Var nn s) = srename (n,s) nn
Proof
rw[FUN_EQ_THM,tsubst_trename]
QED



Theorem slfv_is_cont:
is_cont (slfv sl)
Proof
gs[slfv_alt] >> irule BIGUNION_is_cont >>
rw[tfv_is_cont] >> rw[tfv_is_cont]
QED

        
Theorem slfv_wfdpvl:
wfdpvl vl TRUE ∧ okvnames vl ⇒
slfv (vl2sl vl) = tlfv (MAP Var' vl) DIFF set vl
Proof
Induct_on ‘LENGTH vl’
>- simp[vl2sl_EMPTY,tlfv_def,slfv_alt] >>
Cases_on ‘vl’ >> simp[] >> rw[] >>
simp[vl2sl_CONS,slfv_CONS,tlfv_CONS] >>
Cases_on ‘h’ >> simp[] >>
‘(q,r) ∉ {(q,r)} ∪ sfv r ∪ tlfv (MAP Var' t) DIFF ((q,r) INSERT set t) ’
 by simp[] >>
‘(∀n s. (n,s) ∈ slfv (vl2sl t) ⇒ (q,r) ∉ sfv s)’
 by gs[wfdpvl_TRUE] >>
 drule_then assume_tac slfv_abssl >>
 Cases_on ‘(q,r) ∈ slfv (vl2sl t)’ >> gs[] (* 2 *)
 >- ‘slfv (vl2sl t) = tlfv (MAP Var' t) DIFF set t’
     by (first_x_assum irule >>
        gs[okvnames_CONS,wfdpvl_TRUE]) >>
    simp[] >>
‘ ({(q,r)} ∪ sfv r ∪ tlfv (MAP Var' t)) DIFF ((q,r) INSERT set t) =
(sfv r ∪ tlfv (MAP Var' t)) DIFF ((q,r) INSERT set t)’
 by (simp[EXTENSION] >> rw[EQ_IMP_THM] >>
    TRY (metis_tac[])) >>    
simp[] >>
‘tlfv (MAP Var' t) = sfv r ∪ tlfv (MAP Var' t)’
 suffices_by
  (rw[] >> gs[EXTENSION] >> metis_tac[]) >>
‘sfv r ⊆ tlfv (MAP Var' t)’
suffices_by
(gs[EXTENSION,SUBSET_DEF] >> metis_tac[]) >>
‘slfv (vl2sl t) ⊆ tlfv (MAP Var' t)’
 by gs[slfv_vl2sl_SUBSET] >>
irule_at Any SUBSET_TRANS >>
qexists ‘slfv (vl2sl t)’ >> simp[] >>
strip_tac >> TRY (metis_tac[]) >>
‘is_cont (slfv (vl2sl t))’ suffices_by
metis_tac[is_cont_def] >>
metis_tac[slfv_is_cont]
QED


 ∧
(∀st n s nn v.
(n,s) ∈ sfv st ⇒
sfv (srename (n,s) nn st) =
{(nn,s)} ∪
IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1))
    (sfv st DELETE (n,s)))

Theorem sfv_tfv_lemma:
x ∈ tfv y ∧ (n0,St s' l) ∈ tfv tm ∧
        MEM y l ⇒ x ∈ tfv tm
Proof
rw[] >> irule $ cj 1 vsort_tfv_closed >>
first_assum $ irule_at Any >>
simp[tfv_def,MEM_MAP] >>metis_tac[]
QED 
        
(*
Theorem rnmap_not_is_bound:
(∀v. v ∈ FDOM (rnmap (n,s) nn (tfv tm)) ⇒ ¬is_bound (σ ' v))
*)
    

Theorem term_size_term_var_sort_tl_less:
 (n0,St s' l) ∈ tfv tm ∧  MEM y l ⇒
 term_size y < term_size tm
Proof
 rw[] >> irule arithmeticTheory.LESS_TRANS >>
 qexists ‘sort_size (St s' l)’ >> strip_tac
 >- (rw[] >> simp[term_size_eq] >>
    drule_then assume_tac MEM_list_size_leq >>
    first_x_assum $ qspecl_then [‘term_size’] assume_tac >> gs[]) >>
 metis_tac[tm_tree_size_less]
QED 


Theorem tfv_trename1:
(∀tm n s nn.
(n,s) ∈ tfv tm ⇒
tfv (trename (n,s) nn tm) =
{(nn,s)} ∪
IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1))
    (tfv tm DELETE (n,s)))
Proof
completeInduct_on ‘term_size tm’ >>  rw[] >>
simp[trename_tinst_tfv] >>
   simp[Once EXTENSION] >>
   rw[] >> Cases_on ‘x’ >>
   qspecl_then [‘tm’,‘rnmap (n,s) nn (tfv tm)’]
assume_tac $ cj 1 tfv_tinst >>
‘cstt (rnmap (n,s) nn (tfv tm)) ∧
        tfv tm ⊆ FDOM (rnmap (n,s) nn (tfv tm)) ∧
        (∀v. v ∈ FDOM (rnmap (n,s) nn (tfv tm)) ⇒
             ¬is_bound (rnmap (n,s) nn (tfv tm) ' v))’
 by (rw[] (* 3 *)
    >- metis_tac[cstt_rnmap,tfv_FINITE,tfv_is_cont]
    >- simp[FDOM_rnmap] >>    
    gs[FDOM_rnmap] >> Cases_on ‘v’ >>
    gs[FAPPLY_rnmap,tfv_FINITE,trename_alt] >>
    Cases_on ‘q = n ∧ r = s’ >> simp[is_bound_def]) >> gs[] >>
 rw[EQ_IMP_THM] (* 3 *)
 >- (Cases_on ‘(n0,st0) = (n,s)’ (* 2 *)
    >- (gvs[] >>
       gs[FAPPLY_rnmap,trename_alt] >>
       disj2_tac >> qexists ‘(q,r)’ >>
       simp[] >>
       ‘(n,s) ∉ sfv r’ by metis_tac[tm_tree_WF,vsort_tfv_closed] >>
       simp[GSYM trename_tinst_tfv] >>
       rw[] (* 3 *)
       >- metis_tac[trename_fix]
       >> metis_tac[tm_tree_WF,vsort_tfv_closed])>>
     gs[FAPPLY_rnmap,trename_alt] >>
     qpat_x_assum ‘(q,r) ∈ _’ (mp_tac) >>
     ‘¬(n0 = n ∧ st0 = s)’ by metis_tac[] >>
     simp[] >>
     rw[] (* 2 *)
     >- (disj2_tac >>
        qexists ‘(n0,st0)’ >> simp[] >>
        simp[trename_tinst_tfv]) >>
     reverse (Cases_on ‘(n,s) ∈ sfv st0’) (* 2 *)
     >- (disj2_tac >> qexists ‘(q,r)’ >> simp[] >>
        gs[trename_fix,GSYM trename_tinst_tfv] >>
        rw[] (* 3 *)
        >- (‘(n,s) ∉ sfv r’
             by metis_tac[vsort_tfv_closed] >>
           metis_tac[trename_fix])
        >- metis_tac[vsort_tfv_closed] >>
        metis_tac[]) >>
     Cases_on ‘st0’ >> gvs[trename_alt,MEM_MAP] >>
     Cases_on ‘(n,s) ∈ tfv y’ (* 2 *)
     >- (first_x_assum $ qspecl_then
        [‘term_size y’] assume_tac >>
        ‘term_size y < term_size tm’
         by
         metis_tac[term_size_term_var_sort_tl_less]>>
        gs[] >>
        first_x_assum
        $ qspecl_then [‘y’] assume_tac >> gs[] >>
        first_x_assum $ qspecl_then [‘n’,‘s’,‘nn’]
        assume_tac >> gs[] >>
        simp[GSYM trename_tinst_tfv] >>
        disj2_tac >> qexists ‘x’ >> simp[] >>
        ‘x ∈ tfv y ∧ (n0,St s' l) ∈ tfv tm ∧
        MEM y l ⇒ x ∈ tfv tm’
         suffices_by metis_tac[] >>
        metis_tac[sfv_tfv_lemma]) >>
     disj2_tac >> qexists ‘(q,r)’ >> simp[] >>
     simp[GSYM trename_tinst_tfv] >>
     gs[trename_fix] >>
     ‘(n,s) ∉ sfv r’ by metis_tac[vsort_tfv_closed]>>
     simp[trename_fix] >>
     ‘(q,r) ∈ tfv tm’ suffices_by metis_tac[] >>
     metis_tac[sfv_tfv_lemma])
 >- (qexistsl [‘n’,‘r’] >>
    simp[FAPPLY_rnmap,trename_alt]) >>
 Cases_on ‘x'’ >>
 qexistsl [‘q'’,‘r'’] >> simp[] >>
 simp[FAPPLY_rnmap,GSYM trename_tinst_tfv] >>
 gs[] >>
 reverse (Cases_on ‘(n,s) ∈ sfv r'’)
 >- gs[GSYM trename_tinst_tfv,trename_fix] >>
 simp[trename_alt] >>
 ‘¬(q' = n ∧ r' = s)’ by metis_tac[] >>
 simp[]
QED 

Theorem Uof_eq_lemma:
(∀e. e ∈ s ⇒ f1 e = f2 e) ⇒ Uof f1 s = Uof f2 s
Proof
rw[Uof_def,EXTENSION] >> metis_tac[]
QED

(*        
Theorem sfv_srename1:
(∀sn n s nn.
(n,s) ∈ sfv (St sn tl) ⇒
sfv (srename (n,s) nn (St sn tl)) =
{(nn,s)} ∪
IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1))
    (sfv (St sn tl) DELETE (n,s)))
Proof
Induct_on ‘tl’ >> simp[PULL_EXISTS] >>
rw[]  
*)
        
Theorem sfv_srename1:
(∀st n s nn.
(n,s) ∈ sfv st ⇒
sfv (srename (n,s) nn st) =
{(nn,s)} ∪
IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1))
    (sfv st DELETE (n,s)))
Proof
rw[] >> Cases_on ‘st’ >> simp[trename_alt] >>
‘BIGUNION {tfv t | MEM t (MAP (trename (n,s) nn) l)}=
 Uof tfv (set (MAP (trename (n,s) nn) l))’ 
by simp[Uof_def] >>
pop_assum SUBST_ALL_TAC >>
‘(set (MAP (trename (n,s) nn) l)) =
 {trename (n,s) nn t | t | (n,s) ∈ tfv t ∧ MEM t l} ∪
 { t | (n,s) ∉ tfv t ∧ MEM t l }’
 by (simp[Once EXTENSION,MEM_MAP,PULL_EXISTS] >>
    rw[EQ_IMP_THM] (* 3 *)
    >-( Cases_on ‘(n,s) ∈ tfv y’ (* 2 *)
       >- (disj1_tac >> metis_tac[])   >>
       disj2_tac >> metis_tac[trename_fix])
    >- metis_tac[] >>
    metis_tac[trename_fix]) >>
rw[] >> simp[Uof_UNION] >>
‘Uof tfv {trename (n,s) nn t | t | (n,s) ∈ tfv t ∧ MEM t l} =
 Uof tfv (IMAGE (trename (n,s) nn)
 {t | (n,s)∈ tfv t ∧ MEM t l})’
 by (AP_TERM_TAC >> rw[Once EXTENSION]) >>
 simp[Uof_IMAGE] >> 
 ‘Uof (tfv ∘ trename (n,s) nn) {t | (n,s) ∈ tfv t ∧ MEM t l} =
 Uof (λt. {(nn,s)} ∪
       IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1)) (tfv t DELETE (n,s)))
        {t | (n,s) ∈ tfv t ∧ MEM t l}’
  by (irule Uof_eq_lemma >> rw[] >>
     irule tfv_trename1 >> simp[]) >>
simp[] >>
‘ Uof
          (λt.
               {(nn,s)} ∪
               IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1))
                 (tfv t DELETE (n,s))) {t | (n,s) ∈ tfv t ∧ MEM t l} =
 {(nn,s)}  ∪
 Uof  (λt. IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1))
                 (tfv t DELETE (n,s))) {t | (n,s) ∈ tfv t ∧ MEM t l}’
  by (simp[Uof_def,Once EXTENSION]  >>
     rw[] >> Cases_on ‘x’ >> simp[] >>
      simp[PULL_EXISTS] >>
      simp[pairTheory.EXISTS_PROD] >>
      simp[PULL_EXISTS] >>
      rw[EQ_IMP_THM] (* 3 *)
      >- metis_tac[] 
      >- (gs[tfv_def,MEM_MAP] >> metis_tac[]) >>
      metis_tac[]) >> simp[] >>
‘(BIGUNION {tfv t | MEM t l} DELETE (n,s)) =
 BIGUNION {tfv t | (n,s) ∉ tfv t ∧ MEM t l} ∪
 (BIGUNION {tfv t | (n,s) ∈ tfv t ∧ MEM t l}
  DELETE (n,s))’
  by (rw[EXTENSION] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
last_x_assum mp_tac >>    
POP_ASSUM_LIST (map_every (K all_tac)) >>
rw[UNION_ASSOC]>>
simp[IMAGE_BIGUNION] >>
‘BIGUNION
          (IMAGE (IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1)))
             {tfv t | (n,s) ∉ tfv t ∧ MEM t l}) =
BIGUNION {tfv t | (n,s) ∉ tfv t ∧ MEM t l}’
 by (rw[Once EXTENSION] >>
    Cases_on ‘x’ >> simp[pairTheory.EXISTS_PROD,PULL_EXISTS] >> rw[EQ_IMP_THM] (* 2 *) >> gs[trename_fix]
    >- (‘(n,s) ∉ sfv p_2’
         by metis_tac[vsort_tfv_closed] >>
       simp[trename_fix] >> metis_tac[]) >>
    qexistsl [‘t'’,‘r’] >> simp[] >>
    metis_tac[vsort_tfv_closed,trename_fix]) >>
pop_assum SUBST_ALL_TAC >>
‘Uof
          (λt.
               IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1))
                 (tfv t DELETE (n,s))) {t | (n,s) ∈ tfv t ∧ MEM t l} =
IMAGE (λ(n1,s1). (n1,srename (n,s) nn s1))
          (BIGUNION {tfv t | (n,s) ∈ tfv t ∧ MEM t l} DELETE (n,s))’
suffices_by (rw[] >> gs[Uof_def] >>
   gs[EXTENSION] >> metis_tac[]) >>
simp[Uof_def,Once EXTENSION,PULL_EXISTS] >>
rw[] >>
Cases_on ‘x’ >> simp[] >>
simp[pairTheory.EXISTS_PROD] >>
rw[EQ_IMP_THM] (* 2 *)
>- (qexistsl [‘p_2’,‘t'’] >> simp[]) >>
qexistsl [‘t'’,‘p_2’] >> simp[]
QED 
     
        
Theorem vname_tfv_closed:
(∀h n s n0. (n,s) ∈ tfv h ∧ n0 ∈ snames s ⇒ n0 ∈ tnames h) ∧
∀st n s n0. (n,s) ∈ sfv st ∧ n0 ∈ snames s ⇒ n0 ∈ snames st
Proof
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,tnames_thm,PULL_EXISTS] >>
rw[] >> TRY (metis_tac[])
QED

(*
Theorem vl2sl_tlnames_Var'_SUBSET:
slnames (vl2sl vl) ⊆ tlnames (MAP Var' vl)
Proof
Induct_on ‘LENGTH vl’ >>
simp[vl2sl_EMPTY,slnames_alt] >>
rw[] >> Cases_on ‘vl’ >> gs[] >>
simp[vl2sl_CONS,PULL_EXISTS,SUBSET_DEF] >>
rw[tlnames_CONS] (* 2 *)
>- (Cases_on ‘h’ >> gs[tnames_thm]) >>
disj2_tac >>
first_x_assum slnames_vl2sl_SUBSET
*)   
        
Theorem IN_trename_names:
(∀tm n s nn.
  (n,s) ∈ tfv tm ⇒
  nn ∈ tnames (trename (n,s) nn tm)) ∧
(∀st n s nn.
  (n,s) ∈ sfv st ⇒
  nn ∈ snames (srename (n,s) nn st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,trename_alt,tnames_thm,PULL_EXISTS,
   MEM_MAP] >>
rw[] >> gs[tnames_thm] (* 3 *)
>- (‘¬(s0 = n ∧ st = s)’ by metis_tac[tm_tree_WF] >>
   simp[tnames_thm])
>> metis_tac[]
QED
 
    
Theorem NOTIN_trename_names:
(∀tm n s nn.
  (n,s) ∉ tfv tm ∧ nn ∉ tnames tm ⇒
  nn ∉ tnames (trename (n,s) nn tm)) ∧
(∀st n s nn.
  (n,s) ∉ sfv st ∧ nn ∉ snames st ⇒
  nn ∉ snames (srename (n,s) nn st))
Proof  
ho_match_mp_tac better_tm_induction >>
gs[tfv_thm,trename_alt,tnames_thm,PULL_EXISTS,
   MEM_MAP] >>
rw[] >> gs[tnames_thm] (* 4 *)
>- (‘¬(s0 = n ∧ st = s)’ by metis_tac[tm_tree_WF] >>
   simp[tnames_thm]) >> metis_tac[]
QED   
    

Theorem srename_same_IN_iff:
nn ∉ snames s1 ∧ nn ∉ snames s2 ∧
srename (n,s) nn s1 = srename (n,s) nn s2 ⇒
((n,s) ∈ sfv s1 ⇔ (n,s) ∈ sfv s2)
Proof
metis_tac[IN_trename_names,NOTIN_trename_names]
QED

Theorem wfdpvl_rename:
wfdpvl vl TRUE ∧ okvnames vl ∧
nn ∉ tlnames (MAP Var' vl) ∧
(∀n0 s0. (n0,s0) ∈ tlfv (MAP Var' vl) ⇒
         sbounds s0 = {}) ∧
¬MEM (n,s) vl ⇒
wfdpvl (MAP (λ(n0,s0). (n0,srename (n,s) nn s0)) vl)
TRUE
Proof
Induct_on ‘LENGTH vl’ >> rw[] >>
Cases_on ‘vl’ >> simp[] >> rw[] >>
gs[wfdpvl_TRUE,tlnames_CONS] >>
rw[] >> Cases_on ‘h’ >> gs[] >>
‘wfdpvl (MAP (λ(n0,s0). (n0,srename (n,s) nn s0)) t) TRUE’ by (first_x_assum irule >> simp[] >>
          gs[okvnames_CONS] >>
          gs[tlfv_CONS] >> metis_tac[]) >>
‘(vl2sl (MAP (λ(n0,s0). (n0,srename (n,s) nn s0)) t)) = MAP (srename (n,s) nn) (vl2sl t)’
 by (irule $ GSYM srename_vl2sl >>
    simp[] >> gs[tlfv_CONS] >>
    rw[] >> first_x_assum irule >>
    qexists ‘vn’ >> simp[tlfv_def,MEM_MAP] >>
    gs[PULL_EXISTS] >>
    disj2_tac >> qexists ‘(vn,vs)’ >> simp[]) >>
gs[] >>
gvs[slfv_alt,MEM_MAP,PULL_EXISTS] >>
reverse (Cases_on ‘(n,s) ∈ sfv y’) (* 2 *)
>- (gs[trename_fix] >> strip_tac >> 
   ‘(n,s) ∉ sfv r’
    suffices_by metis_tac[trename_fix] >>
   strip_tac >>
   ‘nn ∈ snames (srename (n,s) nn r)’
    by metis_tac[IN_trename_names] >>
   ‘nn ∈ snames s'’ by metis_tac[vname_tfv_closed] >>
   ‘nn ∈ snames y’ by metis_tac[vname_tfv_closed] >>
   ‘slnames (vl2sl t) ⊆ tlnames (MAP Var' t)’
    by metis_tac[slnames_vl2sl_SUBSET] >>
   ‘nn ∈ slnames (vl2sl t)’
    by (simp[slnames_alt] >> metis_tac[]) >>
   metis_tac[SUBSET_DEF]) >> 
drule_then assume_tac sfv_srename1 >>
gvs[] (* 2 *)
>- (strip_tac >>
   ‘(n,s) ∉ sfv r’
        suffices_by (strip_tac >> gs[trename_fix] >>
             metis_tac[]) >>
      strip_tac >>
    ‘n' ∈ snames (srename (n,s) n' r)’
      by metis_tac[IN_trename_names] >>
    ‘n' ∈ snames s’
      by metis_tac[vname_tfv_closed]>>
    ‘n' ∈ snames y’
      by metis_tac[vname_tfv_closed]>>
    ‘slnames (vl2sl t) ⊆ tlnames (MAP Var' t)’
    by metis_tac[slnames_vl2sl_SUBSET] >>
    ‘n' ∈ slnames (vl2sl t)’
    by (simp[slnames_alt] >> metis_tac[]) >>
    metis_tac[SUBSET_DEF]) >> 
Cases_on ‘x’ >> gvs[]>>
strip_tac >>
‘(q,r) ∈ sfv r'’ suffices_by metis_tac[] >>
reverse (Cases_on ‘(n,s) ∈ sfv r'’)
>- (gs[trename_fix] >>
   ‘(n,s) ∉ sfv r’ by
   (strip_tac >>
   ‘nn ∈ snames (srename (n,s) nn r)’
   by metis_tac[IN_trename_names] >>
   ‘nn ∈ snames r'’ by metis_tac[vname_tfv_closed]>>
   ‘nn ∈ snames y’ by metis_tac[vname_tfv_closed] >>
    ‘slnames (vl2sl t) ⊆ tlnames (MAP Var' t)’
    by metis_tac[slnames_vl2sl_SUBSET] >>
    ‘nn ∈ slnames (vl2sl t)’
    by (simp[slnames_alt] >> metis_tac[]) >>
    metis_tac[SUBSET_DEF]) >>
    gs[trename_fix]) >>
drule_then assume_tac sfv_srename1 >> gvs[] (* 2 *)
>- (* nn ∉ tnames (Var nn r)!! CONTRA*)gs[tnames_thm]
>> Cases_on ‘x’ >> gvs[] >>
   ‘r'' = r’ suffices_by metis_tac[] >>
   ‘(n,s) ∈ sfv r ⇔ (n,s) ∈ sfv r''’
    suffices_by
    (rw[] >>
    Cases_on ‘(n,s) ∈ sfv r’ (* 2 *)
    >- (irule $ iffLR $ cj 2 trename_reflect >>
       simp[PULL_EXISTS] >>
       qexistsl [‘n’,‘nn’,‘s’] >>
       simp[] >>
       gs[tnames_thm] >>
       ‘nn ∉ snames r''’
      by (strip_tac >>
         ‘nn ∈ snames r'’
           by metis_tac[vname_tfv_closed] >>
         ‘nn ∈ snames y’
           by metis_tac[vname_tfv_closed] >>
          ‘slnames (vl2sl t) ⊆ tlnames (MAP Var' t)’
    by metis_tac[slnames_vl2sl_SUBSET] >>
    ‘nn ∈ slnames (vl2sl t)’
    by (simp[slnames_alt] >> metis_tac[]) >>
    metis_tac[SUBSET_DEF]) >> simp[] >>
    rw[] (* 2 *)
    >- (first_x_assum irule >>
       simp[tlfv_CONS] >>
       qexists ‘q’ >> simp[] >> disj2_tac >>
       ‘(q,r'') ∈ slfv (vl2sl t)’
        suffices_by
         metis_tac[slfv_vl2sl_SUBSET,SUBSET_DEF] >>
       simp[slfv_alt,PULL_EXISTS] >>
       metis_tac[vsort_tfv_closed]) >>
    first_x_assum irule >>
        simp[tlfv_CONS] >> metis_tac[]) >>
    gs[trename_fix]) >>
    ‘nn ∉ snames r''’
      by (strip_tac >>
         ‘nn ∈ snames r'’
           by metis_tac[vname_tfv_closed] >>
         ‘nn ∈ snames y’
           by metis_tac[vname_tfv_closed] >>
          ‘slnames (vl2sl t) ⊆ tlnames (MAP Var' t)’
    by metis_tac[slnames_vl2sl_SUBSET] >>
    ‘nn ∈ slnames (vl2sl t)’
    by (simp[slnames_alt] >> metis_tac[]) >>
    metis_tac[SUBSET_DEF]) >>
    irule srename_same_IN_iff >>
    gs[tnames_thm] >> metis_tac[] 
QED       
    
       

(*

0.  wfdpvl ((q,r)::t) TRUE
    1.  wfs Σf r
    2.  ∀v. MEM v t ⇒ wfs Σf (SND v)
    3.  LENGTH t' = LENGTH t
    4.  ¬MEM h' t'
    5.  ALL_DISTINCT t'
    6.  okvnames ((q,r)::t)
    7.  (h' INSERT set t') ∩ tlnames (Var q r::MAP Var' t) = ∅
    8.  MEM (n,s)
          (sl2vl t' (vl2sl (MAP (λ(n0,s0). (n0,srename (q,r) h' s0)) t)))
    9.  ¬MEM (q,r) t
   10.  MAP (srename (q,r) h') (vl2sl t) =
        vl2sl (MAP (λ(n0,s0). (n0,srename (q,r) h' s0)) t)
   ------------------------------------
        okvnames (MAP (λ(n0,s0). (n0,srename (q,r) h' s0)) t)


*)


Theorem okvnames_MAP_srename:
 okvnames vl ∧ nn ∉ tlnames (MAP Var' vl) ∧
 (∀v. MEM v vl ⇒ wfs Σ (SND v)) ⇒
 okvnames
 (MAP (λ(n0,s0).(n0,srename (n,s) nn s0)) vl)
Proof 
Induct_on ‘vl’ >> simp[okvnames_CONS] >>
rw[] (* 2 *)
>- (first_x_assum irule >> gs[tlnames_CONS]) >>
gvs[MEM_MAP] >>
Cases_on ‘h’ >> gs[] >>
Cases_on ‘y’ >> gs[] >>
gs[tlnames_CONS] >>
reverse (Cases_on ‘(n,s) ∈ sfv r’) (* 2 *)
>- (gs[trename_fix] >>
   Cases_on ‘(n,s) ∈ sfv r'’ (* 2 *)
   >- (‘nn ∈ snames (srename (n,s) nn r')’
       by metis_tac[IN_trename_names] >>
      strip_tac >>
      ‘nn ∈ snames r’
       by metis_tac[vname_tfv_closed] >>
      gs[tnames_thm]) >>
   gs[trename_fix]) >>
drule_then assume_tac sfv_srename1 >>
strip_tac >> gvs[] (* 2 *)
>- (qpat_x_assum ‘nn ∉ tlnames (MAP Var' vl)’
   mp_tac >> simp[] >>
   simp[tlnames_alt,PULL_EXISTS,MEM_MAP] >>
   qexists ‘(nn,r')’ >> simp[tnames_thm]) >>
Cases_on ‘x’ >> gvs[] >>
‘r' = r''’ suffices_by metis_tac[] >>
‘nn ∉ snames r'’
 by
   (strip_tac >>
   qpat_x_assum ‘nn ∉ tlnames (MAP Var' vl)’
   mp_tac >> simp[] >>
   simp[tlnames_alt,PULL_EXISTS,MEM_MAP] >>
   qexists ‘(q',r')’ >> simp[] >> gs[tnames_thm])>>
‘nn ∉ snames r''’   
 by
 (strip_tac >>
‘nn ∈ snames r’ by metis_tac[vname_tfv_closed] >>
gs[tnames_thm]) >>
‘(n,s) ∈ sfv r' ⇔ (n,s) ∈ sfv r''’
 by metis_tac[IN_trename_names,NOTIN_trename_names]>>
irule $ iffLR $ cj 2 trename_reflect   >>
simp[PULL_EXISTS] >>
qexistsl [‘n’,‘nn’,‘s’] >> simp[] >>
rw[] (* 2 *)
>- (first_x_assum
   $ qspecl_then [‘(q',r')’] assume_tac >> gs[] >>
   metis_tac[wft_no_bound]) >>
first_x_assum $ qspecl_then [‘(q,r)’] assume_tac >>
gs[] >>
‘wfs Σ r''’ by metis_tac[wft_wfs] >>
metis_tac[wft_no_bound] 
QED 



Theorem tnames_trename_SUBSET:
(∀tm. tnames (trename (n,s) nn tm) ⊆
            {nn} ∪ tnames tm) ∧
(∀st. snames (srename (n,s) nn st) ⊆
            {nn} ∪ snames st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[tnames_thm,trename_alt,PULL_EXISTS,MEM_MAP] >>
gs[SUBSET_DEF] >> rw[] >> TRY (metis_tac[]) >>
Cases_on ‘s0 = n ∧ st = s’ >> gs[tnames_thm] >>
metis_tac[]
QED

    
Theorem wfvl_sl2vl_vl2sl:
 (∀fsym.
           isfsym Σf fsym ⇒
           sfv (fsymout Σf fsym) ⊆
           BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ⇒
  ∀nl n s.
    wfvl Σf vl TRUE ∧ LENGTH nl = LENGTH vl ∧
    ALL_DISTINCT nl ∧
    okvnames vl ∧
    set nl ∩ tlnames (MAP Var' vl) = {} ∧
    MEM (n,s) (sl2vl nl (vl2sl vl)) ⇒
    wfs Σf s
Proof
  disch_tac >> 
  Induct_on ‘LENGTH vl’
  >- simp[vl2sl_def,vl2sl0_def,sl2vl_def] >>
  Cases_on ‘vl’ >> simp[] >> 
  simp[vl2sl_CONS,pairTheory.FORALL_PROD] >>
  rw[] >> Cases_on ‘nl’ >>
  gvs[sl2vl_def,wfvl_def,DISJ_IMP_THM,FORALL_AND_THM]
  >>
  pop_assum mp_tac >> Cases_on ‘h’ >> 
  dep_rewrite.DEP_REWRITE_TAC[specsl_abssl] >>
  simp[tsubst_trename1] >>
  reverse (rw[]) (* 4 *)
  >- (Cases_on ‘MEM (q,r) t’
     >- (‘(MAP (srename (q,r) h') (vl2sl t)) =
         vl2sl t’ by
          (drule_at_then Any assume_tac
          wfdpvl_NOTIN_slfv >>
          gs[okvnames_CONS,wfdpvl_TRUE] >>
          first_x_assum
          $ qspecl_then [‘TRUE’] assume_tac >>
          gs[] >>
          simp[MAP_fix] >>
          rw[] >> gs[slfv_alt] >>
          metis_tac[trename_fix]) >>
        gs[] >>
        first_x_assum irule >>
        gs[wfdpvl_TRUE] >>
        qexistsl [‘n’,‘t'’,‘t’] >> simp[] >>
        gs[EXTENSION,tlnames_CONS,okvnames_CONS] >>
        metis_tac[]) >>
     qspecl_then [‘t’,‘q’,‘r’,‘h'’] assume_tac
     $ Q.GEN ‘vl’ srename_vl2sl >>
     gs[] >>
     ‘MAP (srename (q,r) h') (vl2sl t) =
        vl2sl (MAP (λ(n0,s0). (n0,srename (q,r) h' s0)) t)’ by (irule $ srename_vl2sl >> simp[] >>
          gs[wfdpvl_TRUE] >> rw[] (* 2 *)
          >- (first_x_assum $ qspecl_then [‘(vn,vs)’]
             assume_tac >> gs[] >>
             metis_tac[wft_no_bound]) >>
          gs[EXTENSION,tlnames_CONS] >>
          metis_tac[]) >>
     gs[] >>
     first_x_assum $ qspecl_then
     [‘(MAP (λ(n0,s0). (n0,srename (q,r) h' s0)) t)’]
     assume_tac >> gs[] >>
     first_x_assum irule >>
     simp[MEM_MAP,PULL_EXISTS] >>
     qexistsl [‘n’,‘t'’] >> simp[] >>
     reverse (rw[]) (* 3 *)
     >- (irule wfdpvl_rename >>
        gs[wfdpvl_TRUE] >>
        ‘h' ∉ tlnames (MAP Var' t)’
         by (gs[EXTENSION,tlnames_CONS] >>
            metis_tac[]) >>
        simp[] >>
        gs[okvnames_CONS] >>
        simp[tlfv_def,PULL_EXISTS,MEM_MAP] >>
        rw[] >>
        Cases_on ‘y’ >> gvs[]  (* 2 *)
        >- (last_x_assum $ drule_then assume_tac >>
           gs[] >> metis_tac[wft_no_bound]) >>
        last_x_assum $ drule_then assume_tac >>
        gs[] >> 
        metis_tac[wft_no_vbound])
     >- (simp[MAP_MAP_o] >>
         ‘tlnames (MAP (Var' ∘ (λ(n0,s0). (n0,srename (q,r) h' s0))) t) ⊆ {h'} ∪ tlnames (MAP Var' t)’
          by (simp[SUBSET_DEF,tlnames_alt,MEM_MAP,
                  PULL_EXISTS] >>
             rw[] >> Cases_on ‘y’ >>
             gs[tnames_thm] (* 2 *)
             >- (disj2_tac >>
                qexists ‘(q',r')’ >>
                gs[tnames_thm]) >>
             ‘snames (srename (q,r) h' r') ⊆
             {h'} ∪ snames r'’
             by metis_tac[tnames_trename_SUBSET] >>
             gs[SUBSET_DEF] >>
             first_x_assum $ drule_then assume_tac >>
             gs[] >>
             disj2_tac >> qexists ‘(q',r')’ >>
             gs[tnames_thm]) >>
         ‘h' ∉ set t'’ by gs[] >>
         gs[SUBSET_DEF,EXTENSION] >>
         rw[] >>
         Cases_on ‘x ∉ tlnames (MAP (Var' ∘ (λ(n0,s0). (n0,srename (q,r) h' s0))) t)’ >> gs[] >>
         first_x_assum $ drule_then assume_tac >>
         gs[tlnames_CONS] >>
         metis_tac[])
     >- (irule okvnames_MAP_srename >>
        simp[PULL_EXISTS] >> qexists ‘Σf’ >>
        gs[okvnames_CONS] >>
        gs[EXTENSION,tlnames_CONS] >>
        metis_tac[]) >>
     Cases_on ‘y’ >> gs[] >>
     irule $ cj 2 wft_trename >> simp[] >>
     first_x_assum $ qspecl_then [‘(q',r')’]
     assume_tac >> gs[])
  >- (gs[] >> gs[wfdpvl_TRUE] >>
     first_x_assum irule >>
     simp[slfv_alt,PULL_EXISTS] >>
     metis_tac[])
  >- (‘(n,s) ∈ slfv (vl2sl t)’
       by (simp[slfv_alt,PULL_EXISTS] >>
          metis_tac[]) >>
     ‘(n,s) ∈ tlfv (MAP Var' t)’
       by metis_tac[slfv_vl2sl_SUBSET,SUBSET_DEF] >>
     gs[tlfv_def,MEM_MAP] >> Cases_on ‘y’ >> gvs[]
     (* 2 *)
     >- (first_x_assum $ drule_then assume_tac >>
        gs[] >> metis_tac[wft_no_bound]) >>
     first_x_assum $ drule_then assume_tac >>
     gs[] >> metis_tac[wft_no_vbound]) >>
  ‘ok_abs (vl2sl t)’
    by (irule ok_abs_vl2sl >>
       metis_tac[wft_no_bound]) >>
   gs[ok_abs_def,LENGTH_vl2sl] >>
   first_x_assum $ drule_then assume_tac >>
   gs[SUBSET_DEF] >>
   CCONTR_TAC >> gs[] >>
   first_x_assum $ drule_then assume_tac >> gs[]
QED   
   


Theorem nl_EX:
∀ns:string -> bool n. FINITE ns ⇒
       ∃nl. ALL_DISTINCT nl ∧ LENGTH nl = n ∧ set nl ∩ ns = {}
Proof       
Induct_on ‘FINITE’ >> simp[] >> rw[] (* 2 *)
>- cheat >>
Cases_on ‘n’ >> gs[] >>
first_x_assum $ qspecl_then [‘n'’] assume_tac >>
gs[] >>
reverse (Cases_on ‘MEM e nl’) 
>- (‘∃n1. n1 ∉ set nl ∪ ns ∪ {e}’
  suffices_by (rw[] >>
  qexists ‘n1 :: nl’ >> simp[] >>
  gs[EXTENSION] >> rw[] >>
  Cases_on ‘x ≠ n1 ∧ ¬MEM x nl’ >> gs[] >>
  metis_tac[]) >>
  qexists
  ‘variant (fromSet (set nl ∪ ns ∪ {e})) ""’ >>
  qspecl_then [‘(fromSet (set nl ∪ ns ∪ {e}))’,‘""’]
  assume_tac variant_NOT_fIN >>
  dep_rewrite.DEP_REWRITE_TAC[GSYM IN_fromSet] >>
  simp[]) >>
‘∃n1 n2. n1 ∉ set nl ∪ ns ∪ {e} ∧ n2 ∉ set nl ∪ ns ∪ {e} ∧ n1 ≠ n2’ suffices_by
 (rw[] >>
 qexists
 ‘n1 :: MAP (λx. if x = e then n2 else x) nl’ >>
 simp[MEM_MAP] >> rw[] (* 3 *)
 >- simp[]
 >- (irule ALL_DISTINCT_MAP_INJ >>
    rw[] >> simp[]) >>
 ‘set (MAP (λx. if x = e then n2 else x) nl) =
  {n2} ∪ set nl DELETE e’
   by
   (simp[EXTENSION,MEM_MAP] >> rw[EQ_IMP_THM] (* 4 *)
   >- (Cases_on ‘x' = e’ >> gs[])
   >- (Cases_on ‘x' = e’ >> gs[])
   >- (qexists ‘e’ >> simp[]) >>
   qexists ‘x’ >> simp[]) >>
 simp[] >> gs[EXTENSION] >> metis_tac[]) >>
qabbrev_tac ‘s1 = (set nl ∪ ns ∪ {e})’ >>
‘FINITE s1’ by simp[Abbr‘s1’] >>
qabbrev_tac ‘n1 = variant (fromSet s1) ""’  >>
‘n1 ∉ s1’
  by
  (simp[Abbr‘n1’] >> irule variant_NOTIN >> simp[])>>
qabbrev_tac ‘s2 = {n1} ∪ s1’ >>
‘FINITE s2’ by simp[Abbr‘s2’] >>
qabbrev_tac ‘n2 = variant (fromSet s2) ""’  >>
‘n2 ∉ s2’
  by
  (simp[Abbr‘n2’] >> irule variant_NOTIN >> simp[])>>
‘n1 ∈ s2’ by simp[Abbr‘s2’] >>
‘n2 ∉ s1’ by (simp[Abbr‘s2’] >> gs[]) >>
qexistsl [‘n2’,‘n1’] >> simp[] >>metis_tac[]
QED

   
Theorem tinst_wffstl:
wffstl Σf sl tl ∧
(∀fsym.
            isfsym Σf fsym ⇒
            sfv (fsymout Σf fsym) ⊆
            BIGUNION {tfv (Var n s) | MEM (n,s) (fsymin Σf fsym)}) ∧
cstt σ ∧ wfcod Σf σ ∧ tlfv tl ⊆ FDOM σ ⇒
wffstl Σf (MAP (sinst σ) sl) (MAP (tinst σ) tl)
Proof
rw[] >> simp[wffstl_def] >> 
‘wfabsap Σf (MAP (sinst σ) sl) (MAP (tinst σ) tl)’
  by (irule wfabsap_sinst_tinst >> simp[] >>
     gs[tlfv_def,wffstl_def]) >> simp[] >>
gs[wffstl_def] >>
‘∃nl.ALL_DISTINCT nl ∧
     LENGTH nl = LENGTH sl ∧
     (set nl) ∩ (slnames (MAP (sinst σ) sl)) = {} ∧
     (set nl) ∩ IMAGE FST (FDOM σ) = {} ∧
     set nl ∩ tlnames (MAP Var' vl) = ∅’
 by cheat >>
qexists ‘sl2vl nl (MAP (sinst σ) sl)’ >>
rw[] (* 4 *)
>- (simp[wfvl_def] >> rw[] (* 2 *)
   >- (irule wfdpvl_sl2vl >> simp[]) >>
   ‘sl2vl nl (MAP (sinst σ) (vl2sl vl)) =
MAP (λ(n,s). (n,sinst σ s)) (sl2vl nl (vl2sl vl)) ’
    by
    (irule sl2vl_sinst >> simp[LENGTH_vl2sl] >>
    rw[] (* 3 *)
    >- (irule vl2sl_no_vbound >>
    first_x_assum $ irule_at Any >>
    first_x_assum $ irule_at Any >>
    gs[wfvl_def] >>
    rw[] >> metis_tac[wft_no_vbound])
    >- metis_tac[wfcod_no_bound,no_bound_def] >>
    irule ok_abs_vl2sl >> gs[wfvl_def] >>
    metis_tac[wft_no_bound]) >>
    gs[MEM_MAP] >>
    Cases_on ‘y’ >> gs[] >>
    irule wfs_sinst1 >> simp[] >>
    irule wfvl_sl2vl_vl2sl >> simp[] >>
    qexistsl [‘q’,‘nl’,‘vl’] >> gs[LENGTH_vl2sl])
>- (irule vl2sl_sl2vl >> simp[])
>- (irule ALL_DISTINCT_sl2vl >> simp[]) >>
irule okvnames_sl2vl >> simp[]
QED

        
        
Theorem wfdpvl_ffv:
wfdpvl vl TRUE ∧ ALL_DISTINCT vl ⇒
wfdpvl vl (fVar P (vl2sl vl) (MAP Var' vl))
Proof        
Induct_on ‘LENGTH vl’
>- cheat >>
Cases_on ‘vl’ >>
simp[wfdpvl_def,fVars_def,Uof_Sing] >> strip_tac >>
strip_tac >> reverse (rw[])
>- (qspecl_then [‘h :: t’,‘vl2sl (h::t)’,‘LENGTH t’,‘REVERSE t’] assume_tac
   (mk_FALLL_fVar |> Q.GENL [‘vl’,‘sl’]) >> gs[] >>
   qspecl_then [‘(vl2sl t)’,‘(fVar P (vl2sl (h::t))
                (vpv2b (mk_v2b (REVERSE t)) h::
                   MAP (vpv2b (mk_v2b (REVERSE t))) t))’] assume_tac ffv_FALLL >>
   pop_assum SUBST_ALL_TAC >>
   pop_assum (K all_tac) >> 
   SUBST_ALL_TAC mk_FALLL_TRUE >>
   qspecl_then [‘(vl2sl t)’,‘TRUE’] assume_tac ffv_FALLL >>
   SUBST_ALL_TAC ffv_TRUE >>
   pop_assum mp_tac >> simp[] >> rw[] >>
   pop_assum SUBST_ALL_TAC >>
   ‘(n,s) ∈
        ffv
          (fVar P (vl2sl (h::t))
             (vpv2b (mk_v2b (REVERSE t)) h::
                MAP (vpv2b (mk_v2b (REVERSE t))) t)) ⇒
    h ∉ sfv s’ suffices_by (gs[] >> metis_tac[]) >>
    pop_assum (K all_tac) >>
    qspecl_then [‘REVERSE t’] assume_tac
                (Q.GEN ‘vl’ fVar_MAP_vpv2b) >>
   qspecl_then [‘t’] SUBST_ALL_TAC REVERSE_REVERSE >>
    ‘ALL_DISTINCT (REVERSE t)’ by simp[] >>
    first_x_assum $ dxrule_then assume_tac >>
    pop_assum SUBST_ALL_TAC >>
    ‘(n,s)∈ slfv (vl2sl (h::t)) ⇒ h ∉ sfv s’
     by (simp[vl2sl_CONS] >>
        Cases_on ‘(n,s) ∈ sfv (SND h)’
        >- (CCONTR_TAC >> gs[] >>
           Cases_on ‘h’ >> gs[] >>
           metis_tac[vsort_tfv_closed,tm_tree_WF]) >>
        cheat) >>
    ‘(n,s) ∈
        tlfv
             (vpv2b (mk_v2b (REVERSE t)) h::
                MAP Bound (REVERSE (COUNT_LIST (LENGTH (REVERSE t))))) ⇒
        h ∉ sfv s’
     suffices_by
     (gs[slfv_def,tlfv_def,Uof_def] >> metis_tac[]) >>
    rw[] >>
    Cases_on ‘(n,s) ∈ tfv (vpv2b (mk_v2b (REVERSE t)) h)’
    (* 2 *)
    >- (Cases_on ‘h’ >> gs[vpv2b_tpv2b] >> 
       qspecl_then [‘Var q r’,‘mk_v2b (REVERSE t)’]
       assume_tac $ cj 1 tfv_tpv2b_SUBSET >>
       ‘(n,s) ∈ tfv (Var q r)’ by
       (gs[SUBSET_DEF] >>
       first_x_assum $ qspecl_then [‘(n,s)’] assume_tac >>
       gs[]) >>
       strip_tac >> gs[] (* 2 *)
       >- metis_tac[tm_tree_WF] >>
       metis_tac[vsort_tfv_closed,tm_tree_WF]) >>
    ‘(n,s) ∈ tlfv
     (MAP Bound (REVERSE (COUNT_LIST (LENGTH t))))’
      by (gs[tlfv_def] >> metis_tac[]) >>
     ‘tlfv (MAP Bound (REVERSE (COUNT_LIST (LENGTH t)))) =
     {}’ suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
     simp[tlfv_MAP_Bound_EMPTY])
>- simp[fVslfv_def,fVars_def,Uof_Sing] >>
   simp[vl2sl_CONS] >> Cases_on ‘h’ >> simp[] >>
   ‘ffv (mk_FALLL t TRUE) = slfv (vl2sl t)’
     by simp[mk_FALLL_TRUE,ffv_FALLL,ffv_TRUE,
          slfv_alt] >>
   pop_assum SUBST_ALL_TAC >> simp[slfv_CONS,tm_tree_WF] >>
   cheat >>
   
   


   
   
   gs[mk_FALLL_TRUE,ffv_FALLL,PULL_EXISTS,ffv_TRUE] >>
   simp[slfv_alt] >> rw[] >>
   Cases_on ‘(q,r) ∉ s’ >> gs[] >> rw[] (* 2 *)
   >- metis_tac[tm_tree_WF] >>
   strip_tac >>
   qpat_x_assum ‘(q,r) ∈ sfv v’ mp_tac >> simp[] >>
   first_x_assum irule >> gs[MEM_EL,PULL_EXISTS] >>
   gs[LENGTH_abssl] >> 
   drule_then assume_tac abssl_EL>>
   gs[] >> strip_tac >>
   qspecl_then [‘(EL n (vl2sl t))’,‘q’,‘r’,‘n’] assume_tac
   $ cj 2 tfv_tabs_SUBSET1 >>
   gs[SUBSET_DEF] >>
   first_x_assum $ drule_then assume_tac >>
   pop_assum mp_tac >> simp[] >>
   first_x_assum irule >> 
   
   
   simp[slfv_def,Uof_def] >> rw[] >>
   
   Cases_on ‘(q,r) ∉ s’ >> gs[] >> rw[]  
       
       vpv2b_tpv2b   


      rw[slfv_def,Uof_UNION] 
    
   



strip_tac >> strip_tac >>


Cases_on ‘h’ >> simp[wfdpvl_def,vl2sl_CONS] >>
  
      
        
Theorem mk_FALLL_fVar_wff:
∀k vl0.
LENGTH vl0 = k ∧
wfvl (FST Σ) vl0 TRUE ⇒ 
wff Σ
(mk_FALLL (REVERSE vl0) (fVar P sl (MAP Var' vl))) =
      

Theorem mk_FALLL_fVar_wff:
wfvl (FST Σ) vl TRUE ⇒
wff Σ (mk_FALLL vl (fVar P (vl2sl vl) (MAP Var' vl)))
Proof
Induct_on ‘LENGTH vl’ >- cheat >>
Cases_on ‘vl’ >> simp[] >> Cases_on ‘h’ >>
simp[wfvl_def,mk_FALLL_def] >>
rw[] >>


        




        

Definition mk_FALLL_fVar:
mk_FALLL_fVar P vl sl tl = mk_FALLL vl (fVar P sl tl)
End

        
Definition add_head:
add_head s t (fVar P sl tl) = fVar P (s:: sl) (t :: tl)
End


Definition abstl_def:
abstl [] i tl  = tl ∧
abstl (h :: t) i tl = MAP 

        
Theorem mk_FALLL_fVar:
mk_FALLL vl (fVar P [] []) = fVar P [] [] ∧
mk_FALLL vl (fVar P (s:: sl) (t :: tl)) =
mk_FALL 
Proof


        
Theorem foo:
wfvl vs TRUE ⇒
mk_FALLL vs (fVar P (vl2sl vs) (MAP Var' vs)) =
FALLL (vl2sl vs) (plainfV (P,vl2sl vs))
Proof
Induct_on ‘LENGTH vs’ (* 2 *)
>- cheat >>
Cases_on ‘vs’ >> simp[] >>
Cases_on ‘h’ >> rename [‘(an,as)’] >>
simp[wfvl_def,vl2sl0_def,FALLL_def,vl2sl_def,mk_FALLL_def] >>
rw[] >> 
        

Definition wfabsvl_def:
(wfabsvl Σ [] f = T) ∧
(wfabsvl Σ (v :: vl) f ⇔
 wfabsvl vl f ∧ (wfs Σ 
 



 
Theorem foo:
∀sl. wfabsap (FST Σ) sl (MAP Var' vl) ⇒
mk_FALLL vl (fVar P sl (MAP Var' vl)) =
FALLL sl (plainfV(P,sl)) ∧ wff Σ (FALLL sl (plainfV(P,sl)))
Proof
Induct_on ‘LENGTH vl’
>- cheat >>
Cases_on ‘vl’ >> simp[] >> rw[] >>
Cases_on ‘sl’ >> Cases_on ‘h’ >>
gs[wfabsap_def,sort_of_def] >> simp[mk_FALLL_def] >>
‘(mk_FALLL t (fVar P (r::t') (Var q r::MAP Var' t))) =
 add_head (r,Var q r) (mk_FALLL t (fVar P (specsl 0 (Var q r) t') (MAP Var' t)))’
 by cheat >> simp[] >>
 
first_x_assum $ qspecl_then [‘t’] assume_tac >>
gs[] >> first_x_assum$ drule_then assume_tac >>

Cases_on ‘’



val _ = export_theory();

