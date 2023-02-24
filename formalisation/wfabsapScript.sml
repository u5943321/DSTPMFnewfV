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

Theorem EL_specslwtl:
∀n1 n tl sl.
LENGTH tl = n1 ∧ n < LENGTH sl ∧ LENGTH sl = LENGTH tl ∧ ok_abs sl ∧
(∀t. MEM t tl ⇒ tbounds t = {}) ∧
(∀n0 s0 st. MEM st sl ∧ (n0,s0) ∈ sfv st ⇒ sbounds s0 = ∅)  ⇒
    EL n (specslwtl tl sl) =
    (EL n tl,
     sprpl (shift_bmap (n+1) (mk_bmap (REVERSE (TAKE)))) (EL n sl))
Proof
Induct_on ‘n1’ >> simp[] >> Cases_on ‘tl’ >> Cases_on ‘sl’ >> simp[] >>
rw[] >> Cases_on ‘n’ >> gs[specslwtl] (* 2 *)
>- (gs[ok_abs_def] >>
   first_x_assum $ qspecl_then [‘0’] assume_tac >> gs[] >>
   irule $ cj 2 $ GSYM tprpl_id >>
   gs[]) >>
first_x_assum $ qspecl_then [‘n'’,‘t’,‘(specsl 0 h t')’] assume_tac >>
gs[LENGTH_specsl] >> 
‘ ok_abs (specsl 0 h t')’ by
(gs[ok_abs_def] >> simp[LENGTH_specsl] >> rw[] >>
‘n < LENGTH t'’ by simp[] >>
drule_then assume_tac specsl_EL >> gs[] >>
‘SUC n < SUC (LENGTH t)’ by simp[] >>
first_x_assum $ drule_then assume_tac >> gs[] >>
first_x_assum $ qspecl_then [‘h’,‘0’] assume_tac >> gs[] >>
pop_assum (assume_tac o GSYM) >> cheat) >>
gs[] >>
‘(∀n0 s0 st.
           MEM st (specsl 0 h t') ∧ (n0,s0) ∈ sfv st ⇒ sbounds s0 = ∅)’
 by cheat >>
first_x_assum $ drule_then assume_tac >> gs[] >>
‘n' < LENGTH t'’ by simp[] >>
drule_then assume_tac specsl_EL >> gs[] >>
rename [‘ EL n (specslwtl t (specsl 0 h sl))’] >>
qspecl_then [‘(EL n sl)’,‘n’,‘h’] assume_tac $ cj 2 trpl_tprpl >>
‘tbounds h = {}’ by metis_tac[] >> gs[] >>
qspecl_then [‘(EL n sl)’,‘(shift_bmap (n + 1) (mk_bmap (REVERSE t)))’,
‘(shift_bmap n (mk_bmap [h]))’] assume_tac $ cj 2 tprpl_FUNION >>
‘(∀i. i ∈ FDOM (shift_bmap n (mk_bmap [h])) ∩ sbounds (EL n sl) ⇒
             tbounds (shift_bmap n (mk_bmap [h]) ' i) = ∅) ∧
        FDOM (shift_bmap (n + 1) (mk_bmap (REVERSE t))) ∩
        FDOM (shift_bmap n (mk_bmap [h])) =
        ∅’ by cheat >> gs[] >>
        
        
‘srpl n h (EL n sl) =
 sprpl (shift_bmap n (mk_bmap [t])) tm)’
simp[trpl_tprpl]
                                           

‘SUC n < LENGTH ’
cheat
QED  

Theorem tprpl_wvar:
  tprpl bmap t = tinst (TO_FMAP ) tprpl (mk_bmap)
        
Induct_on ‘tl’ >>  simp[] >>
Cases_on ‘sl’ >> simp[] >> rw[] >>
rw[specslwtl] >> Cases_on ‘n’ >> gs[] (* 2 *)
>- (gs[ok_abs_def] >>
   first_x_assum $ qspecl_then [‘0’] assume_tac >> gs[] >>
   irule $ cj 2 $ GSYM tprpl_id >>
   gs[]) >>
first_x_assum $ qspecl_then [‘t’,‘n'’] assume_tac >> gs[] >>

first_x_assum $ drule_then assume_tac   


               simp[EL_CONS]
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

