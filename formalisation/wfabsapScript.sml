open HolKernel Parse boolLib bossLib;

val _ = new_theory "wfabsap";


Definition wfabsap0_def:
(wfabsap0 Σf [] [] ⇔ T) ∧
  (wfabsap0 Σf (s:: sl) (t :: tl) ⇔
  wft Σf t ∧ s = sort_of t ∧ wfs Σf s ∧ wfabsap0 Σf (specsl 0 t sl) tl) ∧
  (wfabsap0 Σf (s:: sl) [] ⇔ F) ∧
  (wfabsap0 Σf [] (t :: tl) ⇔ F)
End  


Definition specslwtl:
  specslwtl [] [] = [] ∧
  specslwtl (t :: tl) (s :: sl) = (t,s) :: (specslwtl tl (specsl 0 t sl))
End

Theorem wfabsap0_specslwtl:
  ∀tl sl.
  wfabsap0 Σ sl tl ⇔
  LENGTH sl = LENGTH tl ∧
  let sl1 = specslwtl tl sl
  in (∀t s. MEM (t,s) sl1 ⇒  wft Σ t ∧ wfs Σ s ∧ sort_of t = s)
Proof
  Induct_on ‘tl’
  >- (Cases_on ‘sl’ >> gs[wfabsap0_def,specslwtl]) >>
  rw[] >> Cases_on ‘sl’ >> gs[wfabsap0_def] >>
  Cases_on ‘LENGTH t = LENGTH tl’ >> gs[LENGTH_specsl] >>
  simp[specslwtl] >>
  ‘wft Σ h ∧
        h' = sort_of h ∧ wfs Σ h' ∧
        (∀t' s.
           MEM (t',s) (specslwtl tl (specsl 0 h t)) ⇒
           wft Σ t' ∧ wfs Σ s ∧ sort_of t' = s) ⇔
        ∀t' s.
          t' = h ∧ s = h' ∨ MEM (t',s) (specslwtl tl (specsl 0 h t)) ⇒
          wft Σ t' ∧ wfs Σ s ∧ sort_of t' = s’ suffices_by metis_tac[] >>
  rw[DISJ_IMP_THM] >> metis_tac[]          
QED


Theorem trpl_tprpl:
 (∀tm n t. tbounds t = {} ⇒ trpl n t tm = tprpl (shift_bmap n (mk_bmap [t])) tm) ∧
 (∀st n t. tbounds t = {} ⇒ srpl n t st = sprpl (shift_bmap n (mk_bmap [t])) st)
Proof
ho_match_mp_tac better_tm_induction >>
gs[trpl_def,tprpl_def,MAP_EQ_f,FDOM_shift_bmap,FDOM_mk_bmap] >> rw[] (* 3 *)
>- (‘0 ∈ FDOM (mk_bmap [t])’
    by simp[FDOM_mk_bmap] >>
   drule_then assume_tac FAPPLY_shift_bmap >>
   gs[] >> simp[FAPPLY_mk_bmap] >>
   metis_tac[tshift_id])
>- (‘∃x. n = n + x ∧ x < 1’ suffices_by metis_tac[] >>
   qexists ‘0’ >> simp[]) >>
gs[]
QED


Theorem tprpl_FUNION:
  (∀tm bmap1 bmap2.
  (∀i. i ∈ FDOM bmap2 ∩ tbounds tm ⇒ tbounds (bmap2 ' i) = {}) ∧
  (FDOM bmap1 ∩ FDOM bmap2 = {}) ⇒
   tprpl bmap1 (tprpl bmap2 tm) = tprpl (FUNION bmap1 bmap2) tm) ∧
  (∀st bmap1 bmap2.
  (∀i. i ∈ FDOM bmap2 ∩ sbounds st ⇒ tbounds (bmap2 ' i) = {}) ∧
  (FDOM bmap1 ∩ FDOM bmap2 = {}) ⇒
   sprpl bmap1 (sprpl bmap2 st) = sprpl (FUNION bmap1 bmap2) st)   
Proof   
 ho_match_mp_tac better_tm_induction >>
 gs[tprpl_def,MAP_MAP_o,MAP_EQ_f,tbounds_thm] >> rw[] >> TRY (metis_tac[])
 (* 3 *)
 >- (simp[FUNION_DEF] >>
    ‘n ∉ FDOM bmap1’ by (gs[EXTENSION] >> metis_tac[]) >>
    gs[] >> irule $ cj 1 tprpl_id >> gs[])
 >- simp[FUNION_DEF,tprpl_def] >>
 gs[tprpl_def]
QED 
        

(*        

Theorem tprpl_shift_bmap_minus:
(∀t n h i. i ≠ 0 ∧ i ≤ n ⇒ tprpl (shift_bmap (n − i) (mk_bmap (REVERSE l))) (trpl (i-1) h t) =
tprpl (shift_bmap n (mk_bmap (REVERSE l ⧺ [h]))) t ) ∧
(∀s n h i. i ≠ 0 ⇒ sprpl (shift_bmap (n − i) (mk_bmap (REVERSE l))) (srpl (i-1) h s) =
sprpl (shift_bmap n (mk_bmap (REVERSE l ⧺ [h]))) s) 
Proof
ho_match_mp_tac better_tm_induction >>
gs[tprpl_def,trpl_def,MAP_MAP_o,MAP_EQ_f,FDOM_shift_bmap,FDOM_mk_bmap] >>
rw[] (* 4 *)
>-  ‘i -1 < LENGTH (REVERSE l ⧺ [h])’ by simp[] >>
    ‘i -1 < LENGTH l + 1’ suffices_by simp[] >>
    simp[] FAPPLY_mk_bmap

*)

Theorem shift_bmap_SING:
tbounds h = {} ⇒ (shift_bmap n (mk_bmap [h]) ' n) = h
Proof
‘0 ∈ FDOM (mk_bmap [h])’ by simp[FDOM_mk_bmap] >>
drule_then assume_tac FAPPLY_shift_bmap  >>
first_x_assum $ qspecl_then [‘n’] assume_tac >> gs[] >>
‘0 < LENGTH [h]’ by simp[] >>
drule_then assume_tac FAPPLY_mk_bmap >> gs[] >>
metis_tac[tshift_id]
QED

Theorem EL_specslwtl:
∀n1 n tl sl.
LENGTH tl = n1 ∧ n < LENGTH sl ∧ LENGTH sl = LENGTH tl ∧
(∀t. MEM t tl ⇒ tbounds t = {}) ⇒
EL n (specslwtl tl sl) =
(EL n tl,
 sprpl (mk_bmap (REVERSE (TAKE n tl))) (EL n sl))
Proof
Induct_on ‘n1’ >> simp[] >> Cases_on ‘tl’ >> Cases_on ‘sl’ >> simp[] >>
rw[] >> Cases_on ‘n’ >> gs[specslwtl] (* 2 *)
>- (gs[ok_abs_def] >>
   first_x_assum $ qspecl_then [‘0’] assume_tac >> gs[] >>
   irule $ cj 2 $ GSYM tprpl_id >>
   gs[]) >>
rename [‘n < LENGTH tl’] >>
rename [‘LENGTH sl = LENGTH tl’] >>
first_x_assum $ qspecl_then [‘n’,‘tl’,‘(specsl 0 h sl)’] assume_tac >>
gs[LENGTH_specsl] >>
‘n < LENGTH sl’ by simp[] >>
drule_then assume_tac specsl_EL >> gs[] >>
qspecl_then [‘(EL n sl)’,‘n’,‘h’] assume_tac $ cj 2 trpl_tprpl >>
‘tbounds h = {}’ by metis_tac[] >> gs[] >>
qspecl_then [‘(EL n sl)’,‘(mk_bmap (REVERSE (TAKE n tl)))’,
‘(shift_bmap n (mk_bmap [h]))’] assume_tac $ cj 2 tprpl_FUNION >>
‘(∀i. i ∈ FDOM (shift_bmap n (mk_bmap [h])) ∩ sbounds (EL n sl) ⇒
             tbounds (shift_bmap n (mk_bmap [h]) ' i) = ∅) ∧
        FDOM (mk_bmap (REVERSE (TAKE n tl))) ∩
        FDOM (shift_bmap n (mk_bmap [h])) =
        ∅’ by 
(simp[FDOM_mk_bmap,FDOM_shift_bmap] >> rw[] (* 2 *)
>- (‘x = 0’ by simp[] >> gs[] >>
   simp[shift_bmap_SING]) >>
rw[Once EXTENSION] ) >> 
 gs[] >>
‘(mk_bmap (REVERSE (TAKE n tl)) ⊌ shift_bmap n (mk_bmap [h])) =
 (mk_bmap (REVERSE (TAKE n tl) ⧺ [h]))’
 by (simp[fmap_EXT,FDOM_mk_bmap,FDOM_shift_bmap] >>
    rw[] >- (rw[Once EXTENSION] >> ‘x < n + 1 ⇔ x< n ∨ x = n’ by simp[] >>
            ‘∀x'.x' < 1 ⇔ x' = 0’ by simp[] >> simp[])
    >- (‘x < LENGTH (REVERSE (TAKE n tl) ⧺ [h])’ by simp[] >>
       drule_then assume_tac FAPPLY_mk_bmap >> simp[] >>
       ‘x ∈ FDOM (mk_bmap (REVERSE (TAKE n tl)))’
        by simp[FDOM_mk_bmap] >>
       gs[FUNION_DEF,FAPPLY_mk_bmap,rich_listTheory.EL_APPEND1]) >>
    ‘x' = 0’ by simp[] >> gs[] >>
    ‘FDOM (mk_bmap (REVERSE (TAKE n tl))) = count n’
     by simp[FDOM_mk_bmap] >>
    ‘n ∉ FDOM (mk_bmap (REVERSE (TAKE n tl)))’ by simp[] >>
    gs[FUNION_DEF] >>
    ‘n < LENGTH (REVERSE (TAKE n tl) ⧺ [h])’ by simp[] >>
    drule_then assume_tac FAPPLY_mk_bmap >>
    simp[] >>
    ‘LENGTH (REVERSE (TAKE n tl))  ≤ n’ by simp[] >>
    drule_then assume_tac rich_listTheory.EL_APPEND2 >>
    gs[] >>
    ‘0 ∈ FDOM (mk_bmap [h])’ by simp[FDOM_mk_bmap] >>
    drule_then assume_tac FAPPLY_shift_bmap >>
    first_x_assum $ qspecl_then [‘n’] assume_tac >> gs[] >>
    ‘0 < LENGTH [h]’ by simp[] >>
    drule_then assume_tac FAPPLY_mk_bmap >> gs[] >>
    irule $ cj 1 tshift_id >> metis_tac[]) >> gs[]
QED       



Definition v2twbmap_def:
  v2twbmap (b2v:num |-> string # sort) (bmap: num |-> term) =
  FUN_FMAP
  (λv. bmap ' (CHOICE {i | i ∈ FDOM b2v ∧ b2v ' i = v}))
  (FRANGE b2v)
End


Theorem FAPPLY_v2twbmap:
INJ ($' b2v) (FDOM b2v) (FRANGE b2v) ∧ FDOM b2v = FDOM bmap ⇒
∀i. i ∈ FDOM b2v ⇒ (v2twbmap b2v bmap) ' (b2v ' i) = bmap ' i
Proof
simp[] >> rw[INJ_DEF,v2twbmap_def] >>
qspecl_then [‘(λv. bmap ' (CHOICE {i' | i' ∈ FDOM bmap ∧ b2v ' i' = v}))’,
‘(FRANGE b2v)’] assume_tac (SRULE[PULL_FORALL] FUN_FMAP_DEF) >>
gs[] >>
first_x_assum $ qspecl_then [‘b2v ' i’] assume_tac >>
gs[FRANGE_DEF] >>
‘{i' | i' ∈ FDOM bmap ∧ b2v ' i' = b2v ' i} = {i}’ suffices_by simp[] >>
rw[Once EXTENSION] >> metis_tac[]
QED

Theorem FDOM_v2twbmap:
FDOM (v2twbmap (b2v:num |-> string # sort) (bmap: num |-> term))
= (FRANGE b2v)
Proof
simp[v2twbmap_def,FUN_FMAP_DEF]
QED
        



Theorem tprpl_wvar:
  (∀tm bmap b2v.
   INJ ($' b2v) (FDOM b2v) (FRANGE b2v) ∧
   FDOM bmap = FDOM b2v ∧
  (∀i. i ∈ FDOM b2v ⇒
   tfv (Var' (b2v ' i)) ∩ tfv tm = {}) ⇒
  tprpl bmap tm = tinst (v2twbmap b2v bmap) (tprpl (FMAP_MAP Var' b2v) tm)) ∧
  (∀st bmap b2v.
     INJ ($' b2v) (FDOM b2v) (FRANGE b2v) ∧
     FDOM bmap = FDOM b2v ∧
  (∀i. i ∈ FDOM b2v ⇒
   tfv (Var' (b2v ' i)) ∩ sfv st = {}) ⇒
  sprpl bmap st = sinst (v2twbmap b2v bmap) (sprpl (FMAP_MAP Var' b2v) st))
Proof
ho_match_mp_tac better_tm_induction >>
gs[tprpl_def,tinst_def,MAP_MAP_o,MAP_EQ_f,tbounds_thm,FDOM_FMAP_MAP,
   FDOM_v2twbmap,PULL_EXISTS] >> rw[] (* 7 *)
>- (‘(s0,st) ∉ FRANGE b2v’
    by (CCONTR_TAC >> gs[FRANGE_DEF] >>
       first_x_assum $ drule_then assume_tac >> gs[]) >>
   simp[] >>
   irule $ GSYM $ cj 2 tinst_vmap_id >>
   rw[] >>   
   ‘FDOM (v2twbmap b2v bmap) ∩ sfv st = {}’
     suffices_by (gs[EXTENSION] >> metis_tac[]) >>
   simp[FDOM_v2twbmap,FRANGE_DEF] >>
   dsimp[Once EXTENSION] >>
   ‘∀x. x ∈ FDOM b2v ⇒ b2v ' x ∉ sfv st’ suffices_by metis_tac[] >>
   rw[] >>
   first_x_assum $ drule_then assume_tac >>
   Cases_on ‘b2v ' x’ >>
   gs[EXTENSION,tfv_thm] >> metis_tac[])
>- (first_x_assum irule >> rw[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[EXTENSION] >> metis_tac[EXTENSION])
>- (first_x_assum irule >> rw[] >>
   first_x_assum $ drule_then assume_tac >>
   gs[EXTENSION] >> metis_tac[EXTENSION])
>- (qspecl_then [‘b2v’,‘Var'’,‘n’] (drule_then assume_tac) FAPPLY_FMAP_MAP >>
   gs[] >> Cases_on ‘b2v ' n’ >> simp[tinst_def] >>
   ‘(q,r) ∈  FDOM (v2twbmap b2v bmap)’
    by (simp[FDOM_v2twbmap,FRANGE_DEF] >> metis_tac[]) >>
   simp[] >>
   qpat_x_assum ‘_ = (q,r)’ (assume_tac o GSYM) >> gs[] >> 
   irule $ GSYM FAPPLY_v2twbmap >> simp[]) >>
first_x_assum irule >> simp[] >> rw[] >>
rw[] >>
first_x_assum $ drule_then assume_tac >>
gs[EXTENSION] >> metis_tac[EXTENSION]
QED



Theorem tfv_tprpl_SUBSET:
 (∀t i new. 
            tfv t ⊆ tfv (tprpl bmap t)) ∧
 (∀s i new. 
           sfv s ⊆ sfv (sprpl bmap s))
Proof
 ho_match_mp_tac better_tm_induction >> gs[tfv_thm,tprpl_def,MEM_MAP] >>
 rw[] (* 3 *)
 >- (rw[SUBSET_DEF,PULL_EXISTS] >>
    first_x_assum $ drule_all_then assume_tac >> gs[SUBSET_DEF] >> metis_tac[])
 >- gs[SUBSET_DEF] >>
 rw[SUBSET_DEF] >> first_x_assum $ drule_then assume_tac >>
 gs[SUBSET_DEF,PULL_EXISTS] >> metis_tac[]    
QED


Theorem LENGTH_specslwtl:
∀n tl sl. LENGTH tl = n ∧ LENGTH sl = n ⇒
LENGTH (specslwtl tl sl) = n
Proof
Induct_on ‘n’ >> Cases_on ‘tl’ >> Cases_on ‘sl’ >>
gs[specslwtl] >> rw[] >>
first_x_assum $ qspecl_then [‘t’,‘(specsl 0 h t')’] assume_tac >>
gs[LENGTH_specsl]
QED

Theorem wfabsap0_wft:
  ∀tl sl t. wfabsap0 Σf sl tl ∧ MEM t tl ⇒ wft Σf t
Proof
Induct_on ‘tl’ >> simp[wfabsap0_def] >>
Cases_on ‘sl’ >> simp[wfabsap0_def] >> metis_tac[]
QED


      

Theorem wfabsap_wfabsap0:
∀n sl tl. LENGTH sl = n ⇒ (wfabsap0 Σ sl tl ⇒ wfabsap Σ sl tl)
Proof
Induct_on ‘n’ >>
Cases_on ‘sl’ >> Cases_on ‘tl’ >> gs[wfabsap_def] (* 3 *)
>- gs[wfabsap0_def] >- gs[wfabsap0_def] >>
strip_tac >> strip_tac >> 
drule_then assume_tac $ iffLR wfabsap0_specslwtl >> gs[] >>
gs[wfabsap0_def] >>
first_x_assum $ qspecl_then [‘(specsl 0 h' t)’] assume_tac >>
gs[LENGTH_specsl] >>
rw[] >> gs[MEM_EL,PULL_EXISTS] >>
drule_then assume_tac $ iffLR wfabsap0_specslwtl >> gs[] >>
gs[MEM_EL,PULL_EXISTS] >>
Cases_on ‘EL n (specslwtl t' (specsl 0 h' t))’ >>
first_x_assum $ qspecl_then [‘q’,‘r’,‘n’] assume_tac >>
gs[] >>
‘n < LENGTH (specslwtl t' (specsl 0 h' t))’
 by (‘LENGTH t' = LENGTH (specsl 0 h' t)’ by simp[LENGTH_specsl] >>
    drule_then assume_tac LENGTH_specslwtl >>
    first_x_assum $ qspecl_then [‘(specsl 0 h' t)’] assume_tac >>
    pop_assum mp_tac >> REWRITE_TAC[] >> strip_tac >>
    pop_assum SUBST_ALL_TAC >> REWRITE_TAC[LENGTH_specsl] >>
    metis_tac[]) >>
gs[] >>
qspecl_then [‘LENGTH t’,‘n’,‘t'’,‘(specsl 0 h' t)’] assume_tac
EL_specslwtl >> gs[] >>
‘(∀t. MEM t t' ⇒ tbounds t = ∅)’ by
   (rw[] >> drule_then assume_tac wfabsap0_wft >>
   first_x_assum $ drule_then assume_tac >>
   metis_tac[wft_no_bound]) >>
gs[] >>
drule_then assume_tac $ cj 2 wft_no_vbound >>
‘n < LENGTH t’ by simp[] >>
drule_then assume_tac specsl_EL  >> gs[] >>
CCONTR_TAC >>
‘∃i. i ∈ sbounds s0’ by metis_tac[MEMBER_NOT_EMPTY] >>
‘(n0,s0) ∈ sfv (srpl n h' (EL n t))’
 by metis_tac[tfv_trpl_SUBSET1,SUBSET_DEF] >>
‘(n0,s0) ∈ sfv (sprpl (mk_bmap (REVERSE (TAKE n t'))) (srpl n h' (EL n t)))’
suffices_by metis_tac[] >>
metis_tac[SUBSET_DEF,tfv_tprpl_SUBSET]
QED





Theorem wfabsap_IMP_wfabsap0:
∀tl sl. wfabsap Σ sl tl ⇒ wfabsap0 Σ sl tl
Proof
Induct_on ‘tl’ >> Cases_on ‘sl’ >> gs[wfabsap_def,wfabsap0_def]
QED
          
Theorem wfabsap_iff_wfabsap0:
∀tl sl.
wfabsap0 Σ sl tl ⇔ wfabsap Σ sl tl
Proof
metis_tac[ wfabsap_IMP_wfabsap0,wfabsap_wfabsap0]
QED


Theorem LENGTH_specslwtl1:
LENGTH sl = LENGTH tl ⇒ LENGTH (specslwtl tl sl) = LENGTH tl
Proof
metis_tac[LENGTH_specslwtl]
QED


Theorem EL_specslwtl1:
∀n tl sl.
       n < LENGTH sl ∧ LENGTH sl = LENGTH tl ∧
       (∀t. MEM t tl ⇒ tbounds t = ∅) ⇒
       EL n (specslwtl tl sl) =
       (EL n tl,sprpl (mk_bmap (REVERSE (TAKE n tl))) (EL n sl))
Proof
metis_tac[EL_specslwtl]
QED

Theorem EL_specslwtl_alt:

Proof        

EL_specslwtl

tprpl_wvar
QED

Theorem foo:
∀n tl sl. LENGTH tl = n ⇒ wfabsap0 Σ sl tl ⇒ ∃vl. wfabsap0 Σ sl (MAP Var' vl)
Proof
Induct_on ‘n’ >- cheat >>
Cases_on ‘tl’ >> Cases_on ‘sl’ >- cheat >>
simp[] >> rw[] >> rename [‘wfabsap0 Σ (s::sl) (t::tl)’] >>
gs[wfabsap0_specslwtl,specslwtl] >>
‘(MAP Var' vl) = MAP ’


       
drule_then assume_tac $ iffLR $ cj 2 $ wfabsap0_def >>
gs[] >>
first_x_assum $ qspecl_then [‘tl’,‘(specsl 0 t sl)’] assume_tac >>
gs[] >> drule_then assume_tac $ iffLR wfabsap0_specslwtl >>
gs[] >> irule_at Any $ iffRL wfabsap0_specslwtl >>
simp[] >> qexists ‘("",s) :: vl’>> simp[] >>
gs[LENGTH_specsl] >> gs[MEM_EL,PULL_EXISTS] >>
gs[LENGTH_specslwtl1,LENGTH_specsl] >>
simp[specslwtl] >> rpt gen_tac >> strip_tac >>
Cases_on ‘n = 0’ (* 2 *)
>- (gs[] >> simp[wft_def,sort_of_def]) >>
Cases_on ‘n’ >> gs[] >> EL_specslwtl


        
Theorem wff_mk_FALLL_wfabsap:
∀vl sl. wfabsap (FST Σ) sl (MAP Var' vl) ⇒
wff Σ (FALLL sl (fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))))
Proof
Induct_on ‘vl’ 
>- cheat >>
Cases_on ‘sl’ >- cheat >>
simp[wfabsap_def] >> rw[] >>
simp[FALLL_def] >> first_x_assum $ drule_then assume_tac >>

        
               
Theorem wfabsap0_alt:
wfabsap0 Σ sl tl ⇔
LENGTH sl = LENGTH tl ∧
∀n. n < LENGTH sl ⇒ EL n (specslwtl tl sl) =
(EL n tl,sprpl (mk_bmap (REVERSE (TAKE n tl))) (EL n sl))
Proof
simp[wfabsap0_specslwtl,MEM_EL,PULL_EXISTS] >>
Cases_on ‘LENGTH sl = LENGTH tl’ >> simp[LENGTH_specslwtl1] >>
simp[EL_specslwtl]

QED


Theorem wfabsap0_alt:
wfabsap0 Σ sl tl ⇒
∃vtl. wfabsap0 Σ sl vtl ∧ 
∀n. n < LENGTH sl ⇒ EL n (specslwtl tl sll) =
(El n tl,sprpl (mk_bmap (REVERSE (TAKE n tl))) (EL n sl))
Proof
cheat
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
        

(* 
Definition plainfV_def:
plainfV (P,sl) =
fVar P sl (MAP Bound (REVERSE (COUNT_LIST (LENGTH sl))))
End
*)

          
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
        

Theorem mk_FALLL_FALLL:
mk_FALLL vl b = FALLL (vl2sl vl)
Proof


Definition tabsl_def:
  tabsl [] i tm = tm ∧
  tabsl (v :: vs) i tm = tabs (tabsl vs tm)     

Definition fabsl_def:
        
(*
Theorem ffv_FALLL:
∀k vl f. LENGTH vl = k ⇒
(∀n. n < LENGTH vl ⇒ ∀m. n < m ∧ m < LENGTH vl ⇒
     ∀n1 s1. (n1,s1) ∈ sfv (SND (EL m vl)) ⇒ (EL n vl) ∉ sfv s1) ∧
(∀n. n < LENGTH vl ⇒ wfs (FST Σ) (SND (EL n vl))) ∧
(∀n. n < LENGTH vl ⇒ ∀n1 s1. (n1,s1) ∈ ffv f ⇒ (EL n vl) ∉ sfv s1) ⇒
ffv (mk_FALLL vl f) = ffv f ∪ slfv (MAP SND vl) DIFF (set vl)
Proof
Induct_on ‘k’ >> Cases_on ‘vl’ >> simp[mk_FALLL_def,slfv_def,Uof_EMPTY] >>
Cases_on ‘h’ >> rename [‘(n,s)’] >> gs[mk_FALLL_def] >> rw[] >>
qspecl_then [‘(mk_FALLL t f)’,‘n’,‘s’] assume_tac ffv_mk_FALL >>
‘ffv (mk_FALL n s (mk_FALLL t f)) =
        ffv (mk_FALLL t f) ∪ sfv s DELETE (n,s)’ by cheat >>
simp[] >>
first_x_assum $ qspecl_then [‘t’,‘f’] assume_tac >>
‘ffv (mk_FALLL t f) = ffv f ∪ slfv (MAP SND t) DIFF set t’
 by cheat >> gs[] >>
simp[Once INSERT_SING_UNION] >> simp[Uof_UNION,Uof_Sing] >>
simp[slfv_def] >> simp[Once DIFF_of_UNION] >> simp[UNION_ASSOC] >> 
simp[Once INSERT_SING_UNION] >> simp[] >>
rw[Once EXTENSION,EQ_IMP_THM] (* 9 *) >> TRY (metis_tac[]) >>
CCONTR_TAC >> gs[] >>
gs[MEM_EL] >>
rename [‘EL k t’] >>
last_x_assum $ qspecl_then [‘SUC k’] assume_tac >> gs[]  >>

simp[ffv_mk_FALL]
*)
        


Theorem wff_mk_FALLL:
∀k vl. LENGTH vl = k ⇒
(∀n. n < LENGTH vl ⇒ ∀m. n < m ∧ m < LENGTH vl ⇒
     ∀n1 s1. (n1,s1) ∈ sfv (SND (EL m vl)) ⇒ (EL n vl) ∉ sfv s1) ∧
(∀n. n < LENGTH vl ⇒ wfs (FST Σ) (SND (EL n vl))) ∧
(∀n. n < LENGTH vl ⇒ ∀n1 s1. (n1,s1) ∈ ffv f ⇒ (EL n vl) ∉ sfv s1) ⇒
wff Σ f ⇒ wff Σ (mk_FALLL vl f)
Proof             
Induct_on ‘k’ >> Cases_on ‘vl’ >>simp[mk_FALLL_def] >>
rw[] >> Cases_on ‘h’ >> rename [‘(n,s)’] >>
simp[mk_FALLL_def]>> Cases_on ‘Σ’ >> Cases_on ‘r’ >>
rename [‘(Σf,Σp,Σe)’] >>
irule $ cj 6 wff_rules >>
‘wff (Σf,Σp,Σe) (mk_FALLL t f)’
 by (first_x_assum irule >> simp[] >>
    gs[] >> rw[] (* 2 *)
    >- (last_x_assum $ qspecl_then [‘SUC n'’] assume_tac >> gs[] >>
       first_x_assum $ qspecl_then [‘SUC m’] assume_tac >> gs[] >>
       metis_tac[]) >>
    first_x_assum $ qspecl_then [‘SUC n'’] assume_tac >> gs[]) >>
gs[] >>
‘wfs Σf s’
 by (first_x_assum $ qspecl_then [‘0’] assume_tac >> gs[]) >> gs[] >>
simp[fVslfv_mk_FALLL] >> ffv_mk_FALLL ffv_FALLL
fVslfv_mk_FALLL 

        
Theorem wff_mk_FALLL:
∀k vl. LENGTH vl = k ⇒
(∀n. n < LENGTH vl ⇒ ∀m. n < m ∧ m < LENGTH vl ⇒
     ∀n1 s1. (n1,s1) ∈ sfv (SND (EL m vl)) ⇒ (EL n vl) ∉ sfv s1) ∧
(∀n. n < LENGTH vl ⇒ wfs (FST Σ) (SND (EL n vl))) ⇒
wff Σ f ⇒ wff Σ (mk_FALLL vl f)
Proof             
Induct_on ‘k’ >> Cases_on ‘vl’ >>simp[mk_FALLL_def] >>
rw[] >> Cases_on ‘h’ >> rename [‘(n,s)’] >>
simp[mk_FALLL_def]>> Cases_on ‘Σ’ >> Cases_on ‘r’ >>
rename [‘(Σf,Σp,Σe)’] >>
irule $ cj 6 wff_rules >>
‘wff (Σf,Σp,Σe) (mk_FALLL t f)’
 by (first_x_assum irule >> simp[] >>
    gs[] >> rw[] (* 2 *)
    >- (last_x_assum $ qspecl_then [‘SUC n'’] assume_tac >> gs[] >>
       first_x_assum $ qspecl_then [‘SUC m’] assume_tac >> gs[] >>
       metis_tac[]) >>
    first_x_assum $ qspecl_then [‘SUC n'’] assume_tac >> gs[]) >>
gs[] >>
‘wfs Σf s’
 by (first_x_assum $ qspecl_then [‘0’] assume_tac >> gs[]) >> gs[] >>
simp[fVslfv_mk_FALLL] >> ffv_mk_FALLL ffv_FALLL
fVslfv_mk_FALLL 

                  
Definition fabsl_def:
fabsl [] i b = b ∧
fabsl (h :: t) i b = fabsl t (i+1) (fabs h i b)
End

        
Theorem mk_FALLL_FALLL:
∀n vl b. LENGTH vl = n ⇒
 mk_FALLL vl b = FALLL (vl2sl vl) (fabsl (REVERSE vl) 0 b)
Proof
Induct_on ‘n’ >>
cheat >>
Cases_on ‘vl’ >> simp[] >> rw[] >> Cases_on ‘h’ >>
rw[mk_FALLL_def] >>
simp[mk_FALLL_def] 
(*
Theorem mk_FALLL_FALLL:
mk_FALLL vl b = FALLL (abssl_def         
*)

Theorem mk_FALLL_vl:
∀n vl sl.
LENGTH vl = n ∧
ALL_DISTINCT (MAP FST vl) ⇒ 
mk_FALLL vl (fVar P sl (MAP Var' vl)) = FALLL sl (plainfV (P,sl))
Proof
Induct_on ‘n’ >- cheat >>
Cases_on ‘vl’ >> Cases_on ‘sl’ >> gs[mk_FALLL_def]
>- cheat >>
gs[MEM_MAP] >> rw[] >> gs[wfabsap0_def] >>
first_x_assum $ qspecl_then [‘t’,‘t'’] assume_tac >> gs[] >>
Cases_on ‘h’ >> simp[mk_FALLL_def] 
gs[] >>
Cases_on ‘h’ >>
simp[mk_FALLL_def]

        

Theorem wff_mk_FALLL:



        
(*        
Theorem specsl_var:
  (specsl 0 t sl) = MAP (ssubst (n,HD sl) t) (specsl 0 (Var n (HD sl)) sl)
*)

Definition sl2vl_def:
sl2vl [] [] = [] ∧
sl2vl (n :: nl) (s :: sl) =
(n,s) :: sl2vl nl (specsl 0 (Var n s) sl)
End

Definition freshnl_def:
freshnl min 0 = [] ∧
freshnl min (SUC n) = (n2s (min+(SUC n))) :: freshnl min n
End

Definition nameleast_def:
  nameleast (vs:string # sort -> bool) =
  if vs ≠ {} then MAX_SET (IMAGE (s2n o FST) vs) else 0
End  


Theorem wfabsap_alt:
∀n tl sl.
LENGTH tl = n ⇒ 
(wfabsap Σ sl tl ⇔
 (∀nl. (∀name. MEM name nl ⇒ name ∉ (IMAGE FST (slfv sl ∪ tlfv tl))) ∧
      LENGTH nl = LENGTH sl ⇒
      wfabsap Σ sl (MAP Var' (sl2vl nl sl)) ∧
      tl = MAP (tinst (TO_FMAP (ZIP (sl2vl nl sl,tl)))) (MAP Var' (sl2vl nl sl))))
Proof      
Induct_on ‘n’
>- (rw[] >> Cases_on ‘sl’ >> rw[wfabsap_def,sl2vl_def,tlfv_def] >>
   cheat) >>
rw[] >> Cases_on ‘sl’ >> Cases_on ‘tl’ >> gs[sl2vl_def,wfabsap_def] >>
simp[EQ_IMP_THM] (* 8 *) >> strip_tac >> disch_tac (* 2 *)
>- ntac 2 strip_tac >>
   Cases_on ‘nl’ >> gs[] >>
   rename [‘(sl2vl (nh::ns) (sort_of th::ts))’] >>
   simp[sl2vl_def] >>
   ‘(nh,sort_of th) ∈
           FDOM
             (TO_FMAP
                (((nh,sort_of th),th)::
                   ZIP (sl2vl ns (specsl 0 (Var nh (sort_of th)) ts),t')))’
    by cheat  >> simp[] >>
    first_x_assum $ qspecl_then [‘ns’] assume_tac >>
    ‘(∀name.
           MEM name (ns) ⇒
           ∀x. name = FST x ⇒ x ∉ slfv (specsl 0 th ts) ∧ x ∉ tlfv t')’
     by cheat >>
    first_x_assum $ drule_then assume_tac >> gs[LENGTH_specsl] >>
    ‘ TO_FMAP
          (((nh,sort_of th),th)::
             ZIP (sl2vl ns (specsl 0 (Var nh (sort_of th)) ts),t')) '
        (nh,sort_of th) = th’ by cheat >>
    simp[] >> simp[wfabsap_def] >>
    simp[sort_of_def,wft_def] >> 
    first_x_assum $ qspecl_then [
    ‘(MAP Var' (sl2vl ns (specsl 0 (Var nh (sort_of th)) ts)))’,
    ‘(specsl 0 (Var nh (sort_of th)) ts)’] assume_tac >>
    ‘’            
           
Theorem wfabsap_alt:
∀n tl sl.
LENGTH tl = n ⇒ 
(wfabsap Σ sl tl ⇔
 ∀nl. (∀name. MEM name l ⇒ name ∉ (IMAGE FST (slfv sl ∪ tlfv tl))) ∧
      LENGTH nl = LENGTH sl ⇒
      wfabsap Σ sl (MAP Var' (sl2vl nl sl)) ∧
      tl = MAP (tinst σ) (MAP Var' (sl2vl nl sl)))
   let nl = freshnl (nameleast (slfv sl ∪ tlfv tl)) (LENGTH sl) ;
       vl = sl2vl nl sl;
       σ = TO_FMAP (ZIP (vl,tl))
   in wfabsap Σ sl (MAP Var' vl) ∧
      tl = MAP (tinst σ) (MAP Var' vl))
Proof
Induct_on ‘n’
>- (rw[] >> Cases_on ‘sl’ >> gs[wfabsap_def] >>
‘(sl2vl (freshnl (nameleast (slfv [] ∪ tlfv [])) 0) []) = []’
 suffices_by gs[wfabsap_def] >>
 ‘(freshnl (nameleast (slfv [] ∪ tlfv [])) 0) = []’
   suffices_by simp[sl2vl_def] >> simp[freshnl_def]) >>
rw[] >> Cases_on ‘sl’ >> Cases_on ‘tl’ >> simp[wfabsap_def] (* 3 *)
>- gs[]
>- gs[freshnl_def,MAP_MAP_o,sl2vl_def] >>
qabbrev_tac ‘htv = (sl2vl
                (freshnl (nameleast (slfv (h::t) ∪ tlfv (h'::t')))
                   (SUC (LENGTH t))) (h::t))’ >>
‘htv = vh :: vlt’ by cheat >> simp[wfabsap_def] >>
simp[sort_of_def] >>                    
    gs[] >>
   gs[wfabsap_def,sl2vl_def]
‘(freshnl (nameleast (slfv (h::t) ∪ tlfv (h'::t'))) (SUC (LENGTH t)))’
simp[sl2vl_def] 
   ‘’
   simp[freshnl_def,nameleast_def,IMAGE_]

cheat >>
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



val _ = export_theory();

