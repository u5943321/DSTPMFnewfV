open HolKernel Parse boolLib bossLib;

val _ = new_theory "wfabsap";


Definition specslwtl:
  specslwtl [] [] = [] ∧
  specslwtl (t :: tl) (s :: sl) = (t,s) :: (specslwtl tl (specsl 0 t sl))
End

Theorem wfabsap_specslwtl:
  ∀tl sl.
  wfabsap Σ sl tl ⇔
  LENGTH sl = LENGTH tl ∧
  let sl1 = specslwtl tl sl
  in (∀t s. MEM (t,s) sl1 ⇒  wft Σ t ∧ wfs Σ s ∧ sort_of t = s)
Proof
  Induct_on ‘tl’ >- cheat >>
  rw[] >> Cases_on ‘sl’ >> gs[wfabsap_def] >>
  Cases_on ‘LENGTH t = LENGTH tl’ >> gs[LENGTH_specsl] >>
  simp[specslwtl] >>
  ‘(∀n0 s0 st. MEM st t ∧ (n0,s0) ∈ sfv st ⇒ sbounds s0 = ∅) ’ by cheat >>
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


Theorem EL_specslwtl:
∀n1 n tl sl. LENGTH tl = n1 ∧ n < LENGTH sl ∧ LENGTH sl = LENGTH tl ∧ ok_abs sl ⇒
    EL n (specslwtl tl sl) =
    (EL n tl,sprpl (shift_bmap (n-1) (mk_bmap (REVERSE tl))) (EL n sl))
Proof
Induct_on ‘n1’ >> simp[] >> Cases_on ‘tl’ >> Cases_on ‘sl’ >> simp[] >>
rw[] >> Cases_on ‘n’ >> gs[specslwtl] (* 2 *)
>- (gs[ok_abs_def] >>
   first_x_assum $ qspecl_then [‘0’] assume_tac >> gs[] >>
   irule $ cj 2 $ GSYM tprpl_id >>
   gs[]) >>
first_x_assum $ qspecl_then [‘n'’,‘t’,‘(specsl 0 h t')’] assume_tac >>
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

